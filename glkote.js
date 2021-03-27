'use strict';
/* a jQuery-free EMCAScript 5-ish refactoring of Andrew Plotkin's glkote */
/* Zed Lopez */

/* GlkOte -- a Javascript display library for IF interfaces
 * GlkOte Library: version 2.3.0.
 * Designed by Andrew Plotkin <erkyrath@eblong.com>
 * <http://eblong.com/zarf/glk/glkote.html>
 * 
 * This Javascript library is copyright 2008-20 by Andrew Plotkin.
 * It is distributed under the MIT license; see the "LICENSE" file.
 *
 * GlkOte is a tool for creating interactive fiction -- and other text-based
 * applications -- on a web page. It is a Javascript library which handles
 * the mechanics of displaying text, arranging panes of text, and accepting
 * text input from the user.
 *
 * GlkOte is based on the Glk API. However, GlkOte's API is not identical to
 * Glk, even allowing for the differences between Javascript and C. GlkOte is
 * adapted to the realities of a web application environment -- a thin
 * Javascript layer which communicates with a distant server in intermittent
 * bursts.
 *
 * GlkOte can be used from two angles. First, in a purely client-side IF
 * application. The (included, optional) glkapi.js file facilitates this; it
 * wraps around GlkOte and provides an API that is identical to Glk, as
 * closely as Javascript allows. An IF interpreter written in Javascript,
 * running entirely within the user's web browser, can use glkapi.js just as
 * a C interpreter uses a normal Glk library. Or it could bypass glkapi.js
 * and use GlkOte directly.
 *
 * Alternatively, GlkOte could be used with a Glk library which acts as a
 * web service. The RemGlk library (not included) can be used this way.
 * In this mode, GlkOte collects user input and sends it to the web service
 * as a AJAX request. The service decodes the (JSON-format) input data,
 * executes a game turn, and returns the game response as a (JSON-format)
 * reply to the request. A proof-of-concept can be found at:
 *     https://github.com/erkyrath/remote-if-demo
 *
 * (A few calls, or arguments of calls, are marked "for autosave/autorestore
 * only". These exist for the purpose of getting a game displayed in a known
 * state, which is rather more complicated than the usual situation of 
 * letting a game start up and run.)
 *
 * For full documentation, see the docs.html file in this package.
 */

/* All state is contained in GlkoteClass. */
var GlkOteClass = function() {

  /* Module global variables */
  var is_inited = false;
  var game_interface = null;
  /* The DOM element within which all Glk DOM elements are looked up. 
     (#gameport, #windowport, etc.)

     In normal usage this is always undefined (meaning, DOM elements are
     searched for within the entire document). This is a fast case;
     jQuery optimizes for it. However, some apps (not Quixe!) want to 
     detach the Glk DOM and maintain it off-screen. That's possible if you 
     set the DOM context to the detached element. I think (although I have
     not tested) that this configuration is less well-optimized.
  */

  var dom_context = undefined;
  var dom_prefix = '';
  var windowport_id = 'windowport';
  var gameport_id = 'gameport';
  var errorpane_id = 'errorpane';
  var errorcontent_id = 'errorcontent';
  var loadingpane_id = 'loadingpane';
  var max_buffer_length = 800; /* scrollback paragraphs to retain */
  var generation = 0;
  var generation_sent = -1;
  var disabled = false;
  var loading_visible = null;
  var error_visible = false;
  var windowdic = null;
  var current_metrics = null;
  var current_devpixelratio = null;
  var currently_focused = false;
  var last_known_focus = 0;
  var last_known_paging = 0;
  var windows_paging_count = 0;
  var graphics_draw_queue = [];
  var request_timer = null;
  var request_timer_interval = null;
  var resize_timer = null;
  var retry_timer = null;
  var perform_paging = true;
  var detect_external_links = false;
  var regex_external_links = null;
  var debug_out_handler = null;

  var Dialog = null; /* imported API object (the file select/open layer) */
  var Blorb = null; /* imported API object (the resource layer) */

  /* Some handy constants */
  /* A non-breaking space character. */
  var NBSP = "\xa0";
  /* Size of the scrollbar, give or take some. */
  var approx_scroll_width = 20;
  /* Margin for how close you have to scroll to end-of-page to kill the
     moreprompt. (Really this just counters rounding error. And the
     measurement error of different fonts in a window. But as long as
     this is less than the last-line bottom margin, it won't cause
     problems.) */
  var moreprompt_margin = 4;

  /* Some constants for key event native values.*/
  var key_codes = {
    backspace: 8,
    tab:       9,
    'return':   13,
    escape:      27,
    left:     37,
    up:       38,
    right:    39,
    down:     40,
    'delete':   46,
    home:     36,
    end:      35,
    pageup:   33,
    pagedown: 34,
    insert:   45,
    func1 : 112, func2 : 113, func3 : 114, func4 : 115, func5 : 116, 
    func6 : 117, func7 : 118, func8 : 119, func9 : 120, func10 : 121, 
    func11 : 122, func12 : 123
  };
  /* All the keys that can be used as line input terminators */
  var terminator_keys = [ 'escape', 'func1',
                          'func2',
                          'func3',
                          'func4',
                          'func5',
                          'func6',
                          'func7',
                          'func8',
                          'func9',
                          'func10',
                          'func11',
                          'func12'];

  
  var keys_by_code = {};
  for (let k in key_codes) {
    keys_by_code[key_codes[k]] = k;
  }
  /* The inverse of the above. Maps native values to Glk key names. Set up at
     init time. */
  var terminator_key_values = {};

  /* The transcript-recording feature. If enabled, this sends session
     information to an external recording service. */
  var recording = false;
  var recording_state = null;
  var recording_handler = null;
  var recording_handler_url = null;
  var recording_context = {};

  /* An image cache. This maps numbers to Image objects. These are used only
     for painting in graphics (canvas) windows.
  */
  var image_cache = {};

  function remove_children(node) {
    while(node.firstChild) {
      node.removeChild(node.firstChild);
    }
  }

  function on_event(element, eventName, arg, handler) {
    
    element.addEventListener(eventName, function(e) {
      e.data = arg;
      handler.call(e.target, e);
    });
  }

  function create_element(name, attrs, children) {
    var attr, el, key;
    el = document.createElement(name);
    if (attrs) {
      for (key in attrs) {
        if (attrs.hasOwnProperty(key)) {
          switch(key) {
          case 'class':
            attrs[key].split(/\s+/).forEach(function(c) { el.classList.add(c) });
            break;
          default:
            if (el.hasAttribute(key)) {
              el.key = attrs[key];
            }
            else {
              attr = document.createAttribute(key);
              attr.value = attrs[key];
              el.setAttributeNode(attr);
            }
          } 

        }
      }
    }
    if (children && (children.length > 0)) {
      children.forEach(function(child) { el.appendChild(('string' === typeof(child)) ? document.createTextNode(child) : child ) });
    }
    return el;
  }

  function without_padding(el) {
    return {
      width: (el.offsetWidth - parseFloat(getComputedStyle(el, null).paddingLeft) - parseFloat(getComputedStyle(el, null).paddingRight)),
      height: (el.offsetHeight - parseFloat(getComputedStyle(el, null).paddingTop) - parseFloat(getComputedStyle(el, null).paddingBottom))
    };
  }

  /* This function becomes GlkOte.init(). The document calls this to begin
     the game. The simplest way to do this is to give the <body> tag an
     onLoad="GlkOte.init();" attribute.
  */
  function glkote_init(iface) {
    iface ||= window.Game;
    if (!iface) {
      glkote_error('No game interface object has been provided.');
      return;
    }
    if (!iface.accept) {
      glkote_error('The game interface object must have an accept() function.');
      return;
    }
    game_interface = iface;

    /* Set up a static table. */
    terminator_keys.forEach(function(key) {
      terminator_key_values[key_codes[key]] = key;
    });
    /* Object mapping window ID (strings) to window description objects. */
    windowdic = {};

    /* Set the top-level DOM element ids, if provided. */
    if (iface.dom_prefix) {
      dom_prefix = iface.dom_prefix;
    }
    if (iface.windowport) {
      windowport_id = iface.windowport;
    }
    if (iface.gameport) {
      gameport_id = iface.gameport;
    }
    if (iface.errorpane) {
      errorpane_id = iface.errorpane;
    }
    if (iface.errorcontent) {
      errorcontent_id = iface.errorcontent;
    }
    if (iface.loadingpane) {
      loadingpane_id = iface.loadingpane;
    }
    var el = document.getElementById(windowport_id);
    if (null == el) {
      glkote_error('Cannot find windowport element #'+windowport_id+' in this document.');
      return;
    }
    remove_children(el);
    if (perform_paging)
      document.addEventListener('keypress', evhan_doc_keypress);
    /*$(document).on('keypress', evhan_doc_keypress);*/
    /*    $(window).on('resize', evhan_doc_resize); */
    window.addEventListener('resize', evhan_doc_resize);

    /* Note the pixel ratio (resolution level; this is greater than 1 for
       high-res displays. */
    current_devpixelratio = window.devicePixelRatio || 1;

    /* We can get callbacks on any *boolean* change in the resolution level.
       Not, unfortunately, on all changes. */
    if (window.matchMedia) {
      window.matchMedia('screen and (min-resolution: 1.5dppx)').addListener(evhan_doc_pixelreschange);
      window.matchMedia('screen and (min-resolution: 2dppx)').addListener(evhan_doc_pixelreschange);
      window.matchMedia('screen and (min-resolution: 3dppx)').addListener(evhan_doc_pixelreschange);
      window.matchMedia('screen and (min-resolution: 4dppx)').addListener(evhan_doc_pixelreschange);
    }

    /* Figure out the window size and font metrics. */
    var res = measure_window();

    if ('string' === typeof(res)) {
      glkote_error(res);
      return;
    }
    current_metrics = res;

    /* Add some elements which will give us notifications if the gameport
       size changes. */
    create_resize_sensors();

    if (iface.max_buffer_length)
      max_buffer_length = iface.max_buffer_length;
    
    /* Check the options that control whether URL-like strings in the output
       are displayed as hyperlinks. */
    detect_external_links = iface.detect_external_links;
    if (detect_external_links) {
      regex_external_links = iface.regex_external_links;
      if (!regex_external_links) {
        /* Fill in a default regex for matching or finding URLs. */
        if (detect_external_links == 'search') {
          /* The searching case is hard. This regex is based on John Gruber's
             monstrosity, the "web URL only" variant:
             http://daringfireball.net/2010/07/improved_regex_for_matching_urls
             I cut it down a bit; it will not recognize bare domain names like
             "www.eblong.com". I also removed the "(?i)" from the beginning,
             because Javascript doesn't handle that syntax. (It's supposed to
             make the regex case-insensitive.) Instead, we use the 'i'
             second argument to RegExp().
          */
          regex_external_links = RegExp('\\b((?:https?://)(?:[^\\s()<>]+|\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*\\))+(?:\\(([^\\s()<>]+|(\\([^\\s()<>]+\\)))*\\)|[^\\s`!()\\[\\]{};:\'".,<>?\u00ab\u00bb\u201c\u201d\u2018\u2019]))', 'i');
        }
        else {
          /* The matching case is much simpler. This matches any string
             beginning with "http" or "https". */
          regex_external_links = RegExp('^https?:', 'i');
        }
      }
    }

    /* Check the options that control transcript recording. */
    if (iface.recording_url) {
      recording = true;
      recording_handler = recording_standard_handler;
      recording_handler_url = iface.recording_url;
    }
    if (iface.recording_handler) {
      recording = true;
      recording_handler = iface.recording_handler;
      recording_handler_url = '(custom handler)';
    }
    if (recording) {
      /* But also check whether the user has opted out by putting "feedback=0"
         in the URL query. */
      var qparams = get_query_params();
      var flag = qparams['feedback'];
      if (('undefined' != typeof(flag))  && (flag != '1')) {
        recording = false;
        glkote_log('User has opted out of transcript recording.');
      }
      else {
        /* Set up the recording-state object. */
        recording_state = {
          sessionId: (new Date().getTime())+""+( Math.ceil( Math.random() * 10000 ) ),
          input: null,
          output: null,
          timestamp: 0,
          outtimestamp: 0,
          format: (iface.recording_format == 'simple') ? 'simple' : 'glkote'
        }
        if (iface.recording_label) {
          recording_state.label = iface.recording_label;
        }
        glkote_log('Transcript recording active: session ' + recording_state.sessionId + ' "' + recording_state.label + '", destination ' + recording_handler_url);
      }
    }

    if (iface.debug_commands) {
      var debugmod = window.GiDebug;
      if (iface.debug_commands != true) {
        debugmod = iface.debug_commands;
      }
      if (!debugmod) {
        glkote_log('The debug_commands option is set, but there is no GiDebug module.');
      }
      else {
        debugmod.init(evhan_debug_command);
        debug_out_handler = debugmod.output;
        if (iface.debug_console_open) {
          debugmod.open();
        }
      }
    }

    /* Either Blorb was passed in or we don't have one. */
    if (iface.Blorb) {
      Blorb = iface.Blorb;
    }

    /* Either Dialog was passed in or we must create one. */
    if (iface.Dialog) {
      Dialog = iface.Dialog;
      /* This might be inited or not. */
    }
    else if (window.DialogClass) {
      Dialog = new window.DialogClass();
      /* Will have to init. */
    }

    /* From here, every path must call finish_init(). But it might happen async (after a delay). */
    
    /* If Dialog exists but has not yet been inited, we should init it. */
    if (Dialog && !Dialog.inited()) {
      /* Default config object for initing the Dialog library. It only cares about two fields: GlkOte and dom_prefix. (We pass along dialog_dom_prefix as dom_prefix, if supplied.) */
      var dialogiface = { GlkOte:this };
      if (iface.dialog_dom_prefix) {
        dialogiface.dom_prefix = iface.dialog_dom_prefix;
      }

      /* We might have a sync or async init call! (ElectroFS uses the async style.) */
      if (Dialog.init_async) {
        Dialog.init_async(dialogiface, function() { finish_init(iface); })
        return; /* callback will call finish_init(). */
      }
      else if (Dialog.init) {
        Dialog.init(dialogiface);
      }
    }
    
    finish_init(iface);
  }

  /* Conclude the glkote_init() procedure. This sends the VM its "init"
     event. */
  function finish_init(iface) {
    is_inited = true;
    if (!iface.font_load_delay) {
      /* Normal case: start the game (interpreter) immediately. */

      send_response('init', null, current_metrics);
    }
    else {
      /* Delay case: wait a tiny interval, then re-check the window metrics
         and *then* start the game. We might need to do this if the window
         fonts were not cached or loaded with the DOM. (Lectrote, for example,
         because of the way it loads font preferences.) */
      disabled = true;
      defer_func(function() {
        disabled = false;
        current_metrics = measure_window();
        send_response('init', null, current_metrics);
      });
    }
  }

  function glkote_inited() {
    return is_inited;
  }

  /* Work out various pixel measurements used to compute window sizes:
     - the width and height of the windowport
     - the width and height of a character in a grid window
     - ditto for buffer windows (although this is only approximate, since
     buffer window fonts can be non-fixed-width, and styles can have
     different point sizes)
     - the amount of padding space around buffer and grid window content

     This stuff is determined by creating some invisible, offscreen windows
     and measuring their dimensions.
  */
  function measure_window() {
    var metrics = {};
    var winsize, line1size, line2size, invcursize, spansize, canvassize;

    /* We assume the gameport is the same size as the windowport, which
       is true on all browsers but IE7. Fortunately, on IE7 it's
       the windowport size that's wrong -- gameport is the size
       we're interested in. */
    var gameport = (dom_context || document).getElementById(gameport_id);

    if (null == gameport) {
      return 'Cannot find gameport element #'+gameport_id+' in this document.';
    }
    /* If the HTML file includes an #layouttestpane div, we discard it.
       We used to do metrics measurements from a predefined div with
       that name. Nowadays, it's sometimes used as a hidden font-preloader. */
    remove_if_exists(dom_prefix+'layouttestpane', dom_context);

    var gameport_dim = without_padding(gameport);
    
    /* Exclude padding and border. */
    metrics.width  =    gameport_dim.width;
    metrics.height  =    gameport_dim.height;

    /* Create a dummy layout div containing a grid window and a buffer window,
       each with two lines of text. */
    var testspan = document.createTextNode('12345678');
    var line = create_element('div', {}, [ create_element('span', {'class': "Style_normal"}, [ testspan.cloneNode() ]) ]);
    var gridline1 = line.cloneNode(true);
    gridline1.classList.add('GridLine');
    var gridline2 = gridline1.cloneNode(true);
    var gridwin = create_element('div', {'class': 'WindowFrame GridWindow'}, [ gridline1, gridline2 ]);
    var gridspan = gridline1.querySelector('span');
    var bufline1 = line.cloneNode(true);
    bufline1.classList.add('BufferLine');
    var bufline2 = bufline1.cloneNode(true);
    var invcurspan = create_element('span', {'class': 'InvisibleCursor'});
    bufline2.appendChild(invcurspan);
    var bufwin = create_element('div', {'class': 'WindowFrame BufferWindow'}, [ bufline1, bufline2 ]);
    var bufspan = bufline1.querySelector('span');
    var graphcanvas = create_element('canvas', { 'width': 64, 'height': 32 });
    var graphwin = create_element('div', {'class': 'WindowFrame GraphicsWindow'}, [ graphcanvas ] );

    var layout_test_pane = create_element('div', { id:dom_prefix+'layout_test_pane', style: "position: 'absolute', visibility: 'hidden', left: '-1000px';" },
                                          ['This should not be visible', gridwin, bufwin, graphwin]);
    
    gameport.appendChild(layout_test_pane);

    var get_size = function(el) {
      return {
        width: el.getBoundingClientRect().width,
        height: el.getBoundingClientRect().height
      };
    };

    /* Here we will include padding and border. */
    winsize = get_size(gridwin);
    spansize = get_size(gridspan);
    line1size = get_size(gridline1);
    line2size = get_size(gridline2);
    metrics.gridcharheight = Math.max(1, gridline2.offsetTop - gridline1.offsetTop);
    
    metrics.gridcharwidth = Math.max(1, without_padding(gridspan).width / 8);
    /* Yes, we can wind up with a non-integer charwidth value. But we force the value to be >= 1; zero can lead to annoying NaNs later on. */

    /* Find the total margin around the character grid (out to the window's
       padding/border). These values include both sides (left+right,
       top+bottom). */
    metrics.gridmarginx = winsize.width - spansize.width;
    metrics.gridmarginy = winsize.height - (line1size.height + line2size.height);
    /* Here we will include padding and border. */
    winsize = get_size(bufwin);
    spansize = get_size(bufspan);
    line1size = get_size(bufline1);
    line2size = get_size(bufline2);
    invcursize = get_size(invcurspan);    
    metrics.buffercharheight = Math.max(1, bufline2.offsetTop - bufline1.offsetTop);
    metrics.buffercharwidth = Math.max(1, without_padding(bufspan).width / 8);
    /* Again, at least 1, but not necessarily integer. */

    /* Again, these values include both sides (left+right, top+bottom).
       We add a couple of pixels to the vertical margin to allow for
       measurement error in different fonts. */
    metrics.buffermarginx = winsize.width - spansize.width;
    metrics.buffermarginy = winsize.height - (line1size.height + line2size.height) + 2;

    /* Here we will include padding and border. */
    winsize = get_size(graphwin);
    canvassize = get_size(graphcanvas);
    /* Again, these values include both sides (left+right, top+bottom). */
    metrics.graphicsmarginx = winsize.width - canvassize.width;
    metrics.graphicsmarginy = winsize.height - canvassize.height;

    /* Now that we're done measuring, discard the pane. */
    layout_test_pane.remove();
    
    /* These values come from the game interface object.
       Specific fields like "inspacingx" will default to general terms like
       "spacing", if not supplied.
       (The complete_metrics() function in glkapi.js does this job too, but
       this implementation is older and I don't want to ditch it.) */
    metrics.outspacingx = 0;
    metrics.outspacingy = 0;
    metrics.inspacingx = 0;
    metrics.inspacingy = 0;

    if (game_interface.spacing != undefined) {
      metrics.outspacingx = game_interface.spacing;
      metrics.outspacingy = game_interface.spacing;
      metrics.inspacingx = game_interface.spacing;
      metrics.inspacingy = game_interface.spacing;
    }
    if (game_interface.outspacing != undefined) {
      metrics.outspacingx = game_interface.outspacing;
      metrics.outspacingy = game_interface.outspacing;
    }
    if (game_interface.inspacing != undefined) {
      metrics.inspacingx = game_interface.inspacing;
      metrics.inspacingy = game_interface.inspacing;
    }
    if (game_interface.inspacingx != undefined) {
      metrics.inspacingx = game_interface.inspacingx;
    }
    if (game_interface.inspacingy != undefined) {
      metrics.inspacingy = game_interface.inspacingy;
    }
    if (game_interface.outspacingx != undefined) {
      metrics.outspacingx = game_interface.outspacingx;
    }
    if (game_interface.outspacingy != undefined) {
      metrics.outspacingy = game_interface.outspacingy;
    }
    return metrics;
  }

  /* Compare two metrics objects; return whether they're "roughly"
     similar. (We only care about window size and some of the font
     metrics, because those are the fields likely to change out
     from under the library.)
  */
  function metrics_match(met1, met2) {
    for (let metric of ['width','height','gridcharwidth','gridcharheight','buffercharwidth','buffercharheight']) {
      if (met1.metric != met2.metric) {
        return false;
      }
    }
    return true;
  }

  /* Create invisible divs in the gameport which will fire events if the
     gameport changes size. (For any reason, including document CSS changes.
     We need this to detect Lectrote's margin change, for example.)

     This code is freely adapted from CSS Element Queries by Marc J. Schmidt.
     https://github.com/marcj/css-element-queries
  */
  function create_resize_sensors() {
    var gameport = (dom_context || document).getElementById(gameport_id);
    if (null == gameport) {
      return 'Cannot find gameport element #'+gameport_id+' in this document.';
    }
    var shrinkel = create_element('div', { id: dom_prefix+'resize-sensor-shrink', style: "    position:'absolute',    left:'0', right:'0',    width:'200%', height:'200%'"});
    var expandchild =  create_element('div', {
      id: dom_prefix+'resize-sensor-expand-child', style:     "position:'absolute',    left:'0', right:'0'"

    });
    var expandel = create_element('div', { id: dom_prefix+'resize-sensor-expand', style: "    position:'absolute',    left:'0', right:'0', top:'0', bottom:'0',    overflow:'hidden', visibility:'hidden',    'z-index':'-1'"}, [ expandchild ] );

    var reset = function() {
      shrinkel.scrollLeft = 100000;
      shrinkel.scrollTop = 100000;

      expandchild.style.width = '100000px';
      expandchild.style.height = '100000px';
      expandel.scrollLeft = 100000;
      expandel.scrollTop = 100000;
    }

    gameport.appendChild(shrinkel);
    gameport.appendChild(expandel);
    reset();

    var evhan = function(ev) {
      evhan_doc_resize(ev);
      reset();
    }

    /* These events fire copiously when the window is being resized.
       This is one reason evhan_doc_resize() has debouncing logic. */
    /*  shrinkel.on('scroll', evhan);*/
    shrinkel.addEventListener('scroll',evhan);
    expandel.addEventListener('scroll', evhan);
  }

  /* This function becomes GlkOte.update(). The game calls this to update
     the screen state. The argument includes all the information about new
     windows, new text, and new input requests -- everything necessary to
     construct a new display state for the user.
  */
  function glkote_update(arg) {
    
    hide_loading();

    /* This field is *only* for the autorestore case, and only on the very
       first update. It contains additional information (from save_allstate)
       which helps recreate the display. */
    var autorestore = null;
    if (arg.autorestore && generation == 0) {
      autorestore = arg.autorestore;
    }
    delete arg.autorestore; /* keep it out of the recording */

    if (recording) {
      recording_send(arg);
    }

    if (arg.debugoutput && debug_out_handler) {
      debug_out_handler(arg.debugoutput);
    }

    if (arg.type == 'error') {
      glkote_error(arg.message);
      return;
    }

    if (arg.type == 'pass') {
      return;
    }

    if (arg.type == 'retry') {
      if (!retry_timer) {
        glkote_log('Event has timed out; will retry...');
        show_loading();
        retry_timer = delay_func(2, retry_update);
      }
      else {
        glkote_log('Event has timed out, but a retry is already queued!');
      }
      return;
    }

    if (arg.type != 'update') {
      glkote_log('Ignoring unknown message type ' + arg.type + '.');
      return;
    }

    if (arg.gen == generation) {
      /* Nothing has changed. */
      glkote_log('Ignoring repeated generation number: ' + generation);
      return;
    }
    if (arg.gen < generation) {
      /* This update belongs in the past. */
      glkote_log('Ignoring out-of-order generation number: got ' + arg.gen + ', currently at ' + generation);
      return;
    }
    generation = arg.gen;

    /* Un-disable the UI, if it was previously disabled. */
    if (disabled) {
      Object.values(windowdic).filter(win => win.inputel).forEach(function(win) { win.inputel.disabled = false; });
      disabled = false;
    }

    /* Perform the updates, in a most particular order. */

    if (arg.input != null) {
      accept_inputcancel(arg.input);
    }
    if (arg.windows != null) {
      accept_windowset(arg.windows);
    }
    if (arg.content != null) {
      arg.content.forEach(accept_content);
    }
    if (arg.input != null) {
      accept_inputset(arg.input);
    }
    /* Note that a timer value of null is different from undefined. */
    if (arg.timer !== undefined) {
      accept_timerrequest(arg.timer);
    }
    if (arg.specialinput != null) {
      accept_specialinput(arg.specialinput);
    }


    /* Any buffer windows that have changed need to be scrolled down.
       Then, we take the opportunity to update topunseen. (If a buffer
       window hasn't changed, topunseen hasn't changed.) */
    Object.values(windowdic).forEach(function(win) {

      if (win.type == 'buffer' && win.needscroll) {
        /* needscroll is true if the window has accumulated any content or
           an input field in this update cycle. needspaging is true if
           the window has any unviewed content from *last* cycle; we set 
           it now if any new content remains unviewed after the first
           obligatory scrolldown. 
           (If perform_paging is false, we forget about needspaging and
           just always scroll to the bottom.) */

        win.needscroll = false;

        if (!win.needspaging) {
          var frameel = win.frameel;

          if (!perform_paging) {
            /* Scroll all the way down. */

            frameel.scrollTop = frameel.scrollHeight;
            win.needspaging = false;
          }
          else {
            /* Scroll the unseen content to the top. */
            win.pagefrommark = win.topunseen;
            window_scroll(win, 'top', 'dont_change_paging');
            win.needspaging = (frameel.scrollTop + frameel.getBoundingClientRect().height + moreprompt_margin < frameel.scrollHeight);
          }

          /* Add or remove the more prompt and previous mark, based on the
             new needspaging flag. Note that the more-prompt will be
             removed when the user scrolls down; but the prev-mark
             stays until we get back here. */

          var moreel = (dom_context || document ).getElementById(dom_prefix+'win'+win.id+'_moreprompt');
          var prevel = (dom_context || document ).getElementById(dom_prefix+'win'+win.id+'_prevmark');
          if (!win.needspaging) {
            /*                  remove_if_exists(dom_prefix+'win'+win.id+'_moreprompt', dom_context);
                                remove_id_exists(dom_prefix+'win'+win.id+'_prevmark', dom_context);*/
            moreel && moreel.remove();
            prevel && prevel.remove();
          }
          else {
            if (null == moreel) {
              var morex = win.coords.right + approx_scroll_width;
              var morey = win.coords.bottom;
              moreel = create_element('div', { id: dom_prefix+'win'+win.id+'_moreprompt', 'class': 'MorePrompt', 'style':'bottom:'+morey+'px; right:'+morex+'px;' }, [ "More" ]);

              /* 20 pixels is a cheap approximation of a scrollbar-width. */
              (dom_context || document).getElementById(windowport_id).appendChild(moreel);
            }
            if (null == prevel) {
              prevel = create_element('div', { id: dom_prefix+'win'+win.id+'_prevmark', 'class': 'PreviousMark', style: 'top: '+win.pagefrommark+'px'  });
              frameel.prepend(prevel);
            }
            prevel.style.top = (win.pagefrommark+'px');
          }
        }
      }
    });

    /* Set windows_paging_count. (But don't set the focus -- we'll do that
       momentarily.) */
    readjust_paging_focus(false);

    /* Disable everything, if that was requested (or if this is a special
       input cycle). */
    disabled = false;
    if (arg.disable || arg.specialinput) {
      disabled = true;
      Object.values(windowdic).filter(win => win.inputel).forEach(function(win) {
        win.inputel.disabled = true;
      });
    }

    /* Figure out which window to set the focus to. (But not if the UI is
       disabled. We also skip this if there's paging to be done, because
       focussing might autoscroll and we want to trap keystrokes for 
       paging anyhow.) */

    var newinputwin = 0;

    if (!disabled && !windows_paging_count) {
      Object.values(windowdic).forEach( function(win) {
        if (win.input) {
          if (!newinputwin || win.id == last_known_focus)
            newinputwin = win.id;
        }
      });
    }

    if (newinputwin) {
      /* MSIE is weird about when you can call focus(). The input element
         has probably just been added to the DOM, and MSIE balks at
         giving it the focus right away. So we defer the call until
         after the javascript context has yielded control to the browser. */
      var focusfunc = function() {
        var win = windowdic[newinputwin];
        win.inputel && win.inputel.focus();
      };
      defer_func(focusfunc);
    }

    if (autorestore) {
      if (autorestore.history) {
        Object.entries(autorestore.history).forEach( function(winid, ls) {
          var win = windowdic[winid];
          if (win != null) {
            win.history = ls.slice(0);
            win.historypos = win.history.length;
          }
        });
      }
      if (autorestore.defcolor) {
        Object.entries(autorestore.defcolor).forEach( function(winid, val) {
          var win = windowdic[winid];
          if (win != null) {
            win.defcolor = val;
          }
        });
      }

      /* For the case of autorestore (only), we short-circuit the paging
         mechanism and assume the player has already seen all the text. */
      Object.values(windowdic).filter(win => (win.type == 'buffer')).forEach(function(win) {
        window_scroll(win, 'bottom');
      });
      
      if (!(autorestore.metrics 
            && autorestore.metrics.width == current_metrics.width 
            && autorestore.metrics.height == current_metrics.height)) {
        /* The window metrics don't match what's recorded in the
           autosave. Trigger a synthetic resize event. */
        current_metrics.width += 2;
        evhan_doc_resize();
      }
    }
    /* Done with the update. Exit and wait for the next input event. */
  }

  /* Handle all the window changes. The argument lists all windows that
     should be open. Any unlisted windows, therefore, get closed.

     Note that if there are no changes to the window state, this function
     will not be called. This is different from calling this function with
     an empty argument object (which would mean "close all windows").
  */
  function accept_windowset(arg) {
    Object.values(windowdic).forEach(function(win) { win.inplace = false; });
    arg.forEach(accept_one_window);
    /* Close any windows not mentioned in the argument. */
    Object.values(windowdic).filter(win => !win.inplace).forEach(close_one_window);
  }

  /* Handle the update for a single window. Open it if it doesn't already
     exist; set its size and position, if those need to be changed.
  */
  function accept_one_window(arg) {
    var frameel, win;

    if (!arg) {
      return;
    }

    win = windowdic[arg.id];
    if (win == null) {
      /* The window must be created. */
      win = { id: arg.id, type: arg.type, rock: arg.rock };
      windowdic[arg.id] = win;
      var typeclass;
      if (win.type == 'grid') {
        typeclass = 'GridWindow';
      }
      if (win.type == 'buffer') {
        typeclass = 'BufferWindow';
      }
      if (win.type == 'graphics') {
        typeclass = 'GraphicsWindow';
      }

      var rockclass = 'WindowRock_' + arg.rock;
      frameel = create_element('div', { id: dom_prefix+'window'+arg.id, 'class': 'WindowFrame HasNoInputField ' + typeclass + ' ' + rockclass });
      frameel.dataset.winid = arg.id;
      on_event(frameel, 'mousedown', arg.id, evhan_window_mousedown);

      if (perform_paging && win.type == 'buffer') {
        on_event(frameel,'scroll', arg.id, evhan_window_scroll);
      }
      if (win.type == 'grid' || win.type == 'graphics') {
        on_event(frameel,'click', win.id, evhan_input_mouse_click);
      }
      if (win.type == 'buffer') {
        frameel.dataset.ariaLive = 'polite';
        frameel.dataset.ariaAtomic ='false';
        frameel.dataset.ariaRelevant='additions';
      }

      win.frameel = frameel;
      win.gridheight = 0;
      win.gridwidth = 0;
      win.input = null;
      win.inputel = null;
      win.terminators = {};
      win.reqhyperlink = false;
      win.reqmouse = false;
      win.needscroll = false;
      win.needspaging = false;
      win.topunseen = 0;
      win.pagefrommark = 0;
      win.coords = { left:null, top:null, right:null, bottom:null };
      win.history = new Array();
      win.historypos = 0;

      (dom_context||document).getElementById(windowport_id).appendChild(frameel);
    }
    else {
      frameel = win.frameel;
      if (win.type != arg.type)
        glkote_error('Window ' + arg.id + ' was created with type ' + win.type + ', but now is described as type ' + arg.type);
    }

    win.inplace = true;

    if (win.type == 'grid') {
      /* Make sure we have the correct number of GridLine divs. */
      var ix;
      if (arg.gridheight > win.gridheight) {
        for (ix=win.gridheight; ix<arg.gridheight; ix++) {
          var el = create_element('div',
                                  { id: dom_prefix+'win'+win.id+'_ln'+ix, 'class': 'GridLine' }, [NBSP]);
          win.frameel.appendChild(el);
          
        }
      }
      if (arg.gridheight < win.gridheight) {
        for (ix=arg.gridheight; ix<win.gridheight; ix++) {
          remove_if_exists(dom_prefix+'win'+win.id+'_ln'+ix, dom_context);
        }
      }
      win.gridheight = arg.gridheight;
      win.gridwidth = arg.gridwidth;
    }

    if (win.type == 'graphics') {
      var el = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_canvas');
      if (null == el) {
        win.graphwidth = arg.graphwidth;
        win.graphheight = arg.graphheight;
        win.defcolor = '#FFF';
        el = create_element('canvas', { id: dom_prefix+'win'+win.id+'_canvas' });
        /* The pixel-ratio code here should work correctly on Chrome and
           Safari, on screens of any pixel-ratio. I followed
           http://www.html5rocks.com/en/tutorials/canvas/hidpi/ .
        */
        win.backpixelratio = 1;

        var ctx = canvas_get_2dcontext(el);
        if (ctx) {
          /* This property is still namespaced as of 2016. */
          win.backpixelratio = ctx.webkitBackingStorePixelRatio
            || ctx.mozBackingStorePixelRatio
            || ctx.msBackingStorePixelRatio
            || ctx.oBackingStorePixelRatio
            || ctx.backingStorePixelRatio 
            || 1;
        }
        win.scaleratio = current_devpixelratio / win.backpixelratio;
        //glkote_log('### created canvas with scale ' + win.scaleratio + ' (device ' + current_devpixelratio + ' / backstore ' + win.backpixelratio + ')');
        el.width = ( win.graphwidth * win.scaleratio);
        el.height = (win.graphheight * win.scaleratio);
        el.width = (win.graphwidth + 'px');
        el.style.height = win.graphheight + 'px';
        win.frameel.style.backgroundColor = win.defcolor;
        if (ctx) {
          /* Set scale to win.scaleratio */
          ctx.setTransform(win.scaleratio, 0, 0, win.scaleratio, 0, 0);
        }
        win.frameel.appendChild(el);
      }
      else {
        if (win.graphwidth != arg.graphwidth || win.graphheight != arg.graphheight) {
          win.graphwidth = arg.graphwidth;
          win.graphheight = arg.graphheight;
          el.width =(win.graphwidth * win.scaleratio);
          el.height =(win.graphheight * win.scaleratio);
          el.style = 'width:'+win.graphwidth + 'px; height: '+win.graphheight + 'px;';
          /* Clear to the default color, as if for a "fill" command. */
          var ctx = canvas_get_2dcontext(el);
          if (ctx) {
            ctx.setTransform(win.scaleratio, 0, 0, win.scaleratio, 0, 0);
            ctx.fillStyle = win.defcolor;
            ctx.fillRect(0, 0, win.graphwidth, win.graphheight);
            ctx.fillStyle = '#000000';
          }
          win.frameel.style.backgroundColor =  win.defcolor;
          /* We have to trigger a redraw event for this window. But we can't do
             that from inside the accept handler. We'll set up a deferred
             function call. */
          var funcarg = win.id;
          defer_func(function() { send_window_redraw(funcarg); });
        }
      }
    }

    /* The trick is that left/right/top/bottom are measured to the outside
       of the border, but width/height are measured from the inside of the
       border. (Measured by the browser's DOM methods, I mean.) */

    var right = current_metrics.width - (arg.left + arg.width);
    var bottom = current_metrics.height - (arg.top + arg.height);
    win.coords.left = arg.left;
    win.coords.top = arg.top;
    win.coords.right = right;
    win.coords.bottom = bottom;
    frameel.style.left = arg.left+'px';
    frameel.style.top = arg.top+'px';
    frameel.style.right = right+'px';
    frameel.style.bottom = bottom+'px';
  }

  function remove_if_exists(id, dom_context) {
    var el;
    if (el = (dom_context||document).getElementById(id)) {
      el.remove();
    }
  }
  
  /* Handle closing one window. */
  function close_one_window(win) {
    win.frameel.remove();
    delete windowdic[win.id];
    win.frameel = null;
    remove_if_exists(dom_prefix+'win'+win.id+'_moreprompt', dom_context);
  }

  var alignment_hash = {
    inlineup: 'ImageInlineUp',
    inlinedown: 'ImageInlineDown',
    inlinecenter: 'ImageInlineCenter',
    marginleft: 'ImageMarginLeft',
    marginright: 'ImageMarginRight',
  };
  
  /* Handle the content changes for a single window. */
  function accept_content(arg) {
    var win = windowdic[arg.id];

    /* Check some error conditions. */
    if (win == null) {
      glkote_error('Got content update for window ' + arg.id + ', which does not exist.');
      return;
    }
    if (win.input && win.input.type == 'line') {
      glkote_error('Got content update for window ' + arg.id + ', which is awaiting line input.');
      return;
    }

    win.needscroll = true;

    if (win.type == 'grid') {
      /* Modify the given lines of the grid window (and leave the rest alone). */
      var lines = arg.lines;
      var ix, sx;
      /*            for (ix=0; ix<lines.length; ix++) {
                    var linearg = lines[ix];*/
      for (let linearg of lines) {
        var linenum = linearg.line;
        var content = linearg.content;
        var lineel = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_ln'+linenum);

        if (null === lineel) {
          glkote_error('Got content for nonexistent line ' + linenum + ' of window ' + arg.id + '.');
          continue;
        }

        if (!content || !content.length) {
          lineel.text = NBSP;
        }
        else {
          remove_children(lineel);
          for (sx=0; sx<content.length; sx++) {
            var rdesc = content[sx];
            var rstyle, rtext, rlink;
            if ('object' === typeof(rdesc) ) {
              if (rdesc.special !== undefined) {
                continue;
              }
              rstyle = rdesc.style;
              rtext = rdesc.text;
              rlink = rdesc.hyperlink;
            }
            else {
              rstyle = rdesc;
              sx++;
              rtext = content[sx];
              rlink = undefined;
            }
            var el = create_element('span', { 'class': 'Style_' + rstyle } );
            if (rlink == undefined) {
              insert_text_detecting(el, rtext);
            }
            else {
              var ael = create_element('a', { 'href': '#', 'class': 'Internal' } );
              ael.text =(rtext);
              ael.addEventListener('click', build_evhan_hyperlink(win.id, rlink));
              el.appendChild(ael);
            }
            lineel.appendChild(el);
          }
        }
      }
    }

    if (win.type == 'buffer') {
      /* Append the given lines onto the end of the buffer window. */
      var text = arg.text;

      var ix, sx;

      /* This can happen if we're waiting for char input. (Line input
         would make this content update illegal -- but we already checked
         that.) The inputel is inside the cursel, which we're about to
         rip out. We remove it, so that we can put it back later. */
      win.inputel && win.removeChild(inputel);
      remove_if_exists(dom_prefix+'win'+win.id+'_cursor',dom_context);
      var cursel = null;

      if (arg.clear) {
        remove_children(win.frameel);
        win.topunseen = 0;
        win.pagefrommark = 0;
      }

      /* Accept a missing text field as doing nothing. */
      if (text === undefined) {
        text = [];
      }
      /* Each line we receive has a flag indicating whether it *starts*
         a new paragraph. (If the flag is false, the line gets appended
         to the previous paragraph.)

         We have to keep track of a flag per paragraph div. The blankpara
         flag indicates whether this is a completely empty paragraph (a
         blank line). We have to drop a NBSP into empty paragraphs --
         otherwise they'd collapse -- and so this flag lets us distinguish
         between an empty paragraph and one which truly contains a NBSP.
         (The difference is, when you append data to a truly empty paragraph,
         you have to delete the placeholder NBSP.)

         We also give the paragraph div the BlankPara class, in case
         CSS cares.
      */

      /*            for (ix=0; ix<text.length; ix++) {
                    var textarg = text[ix];*/
      for (let textarg of text) {
        var content = textarg.content;
        var divel = null;
        if (textarg.append) {
          if (!content || !content.length) {
            continue;
          }
          divel = buffer_last_line(win);
        }
        if (divel == null) {
          /* Create a new paragraph div */
          divel = create_element('div', { 'class': 'BufferLine BlankPara' });
          divel.dataset.blankpara = true;
          win.frameel.appendChild(divel);
        }
        if (textarg.flowbreak) {
          divel.classList.add('FlowBreak');
        }

        if (!content || !content.length) {
          if (divel.dataset.blankpara == "true") {
            divel.appendChild(create_element('span', { 'class':'BlankLineSpan' }, [ NBSP ]));
          }
          continue;
        }
        if (divel.dataset.blankpara == "true") {
          divel.dataset.blankpara = "false";
          divel.classList.remove('BlankPara');
          remove_children(divel);
        }
        var content_length = content.length
        for (sx=0; sx<content.length; sx++) {
          var rdesc = content[sx];
          var rstyle, rtext, rlink;
          if ('object' === typeof(rdesc)) {
            if (rdesc.special !== undefined) {
              if (rdesc.special == 'image') {
                /* This is not as restrictive as the Glk spec says it should
                   be. Margin-aligned images which do not follow a line
                   break should disappear. This will undoubtedly cause
                   headaches for portability someday. */
                var imgurl = rdesc.url;
                if (Blorb && Blorb.get_image_url) {
                  var newurl = Blorb.get_image_url(rdesc.image);
                  if (newurl)
                    imgurl = newurl;
                }
                var el = create_element('img', { src:imgurl, width:''+rdesc.width, height:''+rdesc.height, alt:(rdesc.alttext ? rdesc.alttext : ('Image '+rdesc.image))});
                el.classList.add(alignment_hash.hasOwnProperty(rdesc.alignment) ? alignment_hash[rdesc.alignment] : 'ImageInlineUp');
                if (rdesc.hyperlink != undefined) {
                  var ael = create_element('a', { 'href': '#', 'class': 'Internal' } );
                  ael.appendChild(el);
                  ael.addEventListener('click', build_evhan_hyperlink(win.id, rdesc.hyperlink));
                  el = ael;
                }
                divel.appendChild(el);
                continue;
              }
              glkote_log('Unknown special entry in line data: ' + rdesc.special);
              continue;
            }
            rstyle = rdesc.style;
            rtext = rdesc.text;

            rlink = rdesc.hyperlink;
          }
          else {
            rstyle = rdesc;
            sx++;
            rtext = content[sx];
            rlink = undefined;
          }
          var el = create_element('span', { 'class': 'Style_' + rstyle } );
          if (rlink == undefined) {
            insert_text_detecting(el, rtext);
          }
          else {
            var ael = create_element('a', { 'href': '#', 'class': 'Internal' } );
            ael.text =rtext;
            ael.addEventListener('click', build_evhan_hyperlink(win.id, rlink));
            el.appendChild(ael);
          }
          divel.appendChild(el);
        }
      }

      /* Trim the scrollback. If there are more than max_buffer_length
         paragraphs, delete some. (It would be better to limit by
         character count, rather than paragraph count. But this is
         easier.) (Yeah, the prev-mark can wind up included in the count --
         and trimmed out. It's only slightly wrong.) */


      /* what's going on here? */
      
      var parals = win.frameel.children;
      if (parals.length) {
        var totrim = parals.length - max_buffer_length;
        if (totrim > 0) {
          var ix, obj;
          var offtop = parals[totrim].offsetTop;
          win.topunseen -= offtop;
          win.topunseen = Math.max(win.topunseen, 0);
          win.pagefrommark -= offtop;
          win.pagefrommark = Math.max(win.pagefrommark, 0);
          for (ix=0; ix<totrim; ix++) {
            parals[ix].remove();
          }
        }
      }

      /* Stick the invisible cursor-marker inside (at the end of) the last
         paragraph div. We use this to position the input box. */
      var divel = buffer_last_line(win);
      if (divel) {
        var cursel = create_element('span', { id: dom_prefix+'win'+win.id+'_cursor', 'class': 'InvisibleCursor' } );
        divel.appendChild(cursel);

        if (win.inputel) {
          /* Put back the inputel that we found earlier. */
          var inputel = win.inputel;
          /* This calculation is antsy. (Was on Prototype, anyhow, I haven't
             retested in jquery...) On Firefox, buffermarginx is too high (or
             getWidth() is too low) by the width of a scrollbar. On MSIE,
             buffermarginx is one pixel too low. We fudge for that, giving a
             result which errs on the low side. */

          var width = without_padding(win.frameel).width - (current_metrics.buffermarginx + cursel.offsetLeft + 2);
          width = Math.max(width, 1);
          inputel.style = "position: 'absolute'; left: '0px'; top: '0px'; width:"+ width+"'px';";
          cursel.appendChild(inputel);
        }
        cursel = null;
      }
    }

    if (win.type == 'graphics') {
      /* Perform the requested draw operations. */
      var draw = arg.draw;
      var ix;
      
      /* Accept a missing draw field as doing nothing. */
      if (draw === undefined) {
        draw = [];
      }
      /* Unfortunately, image-draw actions might take some time (if the image
         data is not cached). So we can't do this with a simple synchronous loop.
         Instead, we must add drawing ops to a queue, and then have a function
         callback that executes them. (It's a global queue, not per-window.)
         
         We assume that if the queue is nonempty, a callback is already waiting
         out there, so we don't have to set it up.
      */

      var docall = (graphics_draw_queue.length == 0);
      /*            for (ix=0; ix<draw.length; ix++) {
                    var op = draw[ix];*/
      for (let op of draw) {
        /* We'll be paranoid and clone the op object, throwing in a window
           number. */

        var newop = Object.assign({ winid:win.id }, op);
        graphics_draw_queue.push(newop);
      }
      if (docall && graphics_draw_queue.length > 0) {
        perform_graphics_ops(null);
      }
    }
  }

  /* Handle all necessary removal of input fields.

     A field needs to be removed if it is not listed in the input argument,
     *or* if it is listed with a later generation number than we remember.
     (The latter case means that input was cancelled and restarted.)
  */
  function accept_inputcancel(arg) {
    var hasinput = {};
    arg.filter(argi => argi.type).forEach(function(argi) { hasinput[argi.id] = argi; });

    Object.values(windowdic).filter(win => win.input).forEach(function(win) {
      var argi = hasinput[win.id];
      if (argi == null || argi.gen > win.input.gen) {
        /* cancel this input. */
        win.input = null;
        win.frameel.classList.add('HasNoInputField');
        win.frameel.classList.remove('HasInputField');
        if (win.inputel) {
          win.inputel.remove();
          win.inputel = null;
        }
      }
    });
  }
  
  /* Handle all necessary creation of input fields. Also, if a field needs
     to change position, move it.
  */
  function accept_inputset(arg) {
    var hasinput = {};
    var hashyperlink = {};
    var hasmouse = {};
    arg.forEach(function(argi) {
      if (argi.type) {
        hasinput[argi.id] = argi;
      }
      if (argi.hyperlink) {
        hashyperlink[argi.id] = true;
      }
      if (argi.mouse) {
        hasmouse[argi.id] = true;
      }
    });

    Object.values(windowdic).forEach(function(win) {
      win.reqhyperlink = hashyperlink[win.id];
      win.reqmouse = hasmouse[win.id];
      var argi = hasinput[win.id];
      if (argi == null) {
        return;
      }
      win.input = argi;

      win.frameel.classList.add('HasInputField');
      win.frameel.classList.remove('HasNoInputField');

      /* Maximum number of characters to accept. */
      var maxlen = 1;
      if (argi.type == 'line') {
        maxlen = argi.maxlen;
      }
      /* We're only going to emplace the inputel when it's freshly created. If it's lingering from a previous input, we leave it in place in the DOM. This *should* reduce soft-keyboard flashing problems without screwing up the DOM semantics. */
      var newinputel = false;
      var inputel = win.inputel;

      if (inputel == null) {
        newinputel = true;
        var classes = 'Input';
        if (argi.type == 'line') {
          classes += ' LineInput';
        }
        else if (argi.type == 'char') {
          classes += ' CharInput';
        }
        else {
          glkote_error('Window ' + win.id + ' has requested unrecognized input type ' + argi.type + '.');
        }
        inputel = create_element('input', { id: dom_prefix+'win'+win.id+'_input',
                                            'class': classes, type: 'text', maxlength: maxlen, autocapitalize: 'off', ariaLive: 'off' });
        if (argi.type == 'line') {
          inputel.addEventListener('keypress', evhan_input_keypress);
          inputel.addEventListener('keydown', evhan_input_keydown);
          if (argi.initial) {
            inputel.value = argi.initial;
          }
          win.terminators = {};
          if (argi.terminators) {
            argi.terminators.forEach(function(argterm) { win.terminators[argterm] = true; });
          }
        }
        else if (argi.type == 'char') {
          inputel.addEventListener('keypress', evhan_input_char_keypress);
          inputel.addEventListener('keydown', evhan_input_char_keydown);
        }
        on_event(inputel,'focus', win.id, evhan_input_focus);
        on_event(inputel,'blur', win.id, evhan_input_blur);
        inputel.dataset.winid = win.id;
        win.inputel = inputel;
        win.historypos = win.history.length;
        win.needscroll = true;
      }

      if (win.type == 'grid') {
        var lineel = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_ln'+argi.ypos);
        if (null == lineel) {
          glkote_error('Window ' + win.id + ' has requested input at unknown line ' + argi.ypos + '.');
          return;
        }
        var xpos = lineel.offsetLeft + Math.round(argi.xpos * current_metrics.gridcharwidth);
        var width = Math.round(maxlen * current_metrics.gridcharwidth);
        /* This calculation is antsy. See below. (But grid window line input
           is rare in IF.) */
        var maxwidth = without_padding(win.frameel).width - (current_metrics.buffermarginx + xpos + 2);
        if (width > maxwidth){
          width = maxwidth;
        }
        inputel.style.position = 'absolute';
        inputel.style.left = xpos + 'px';
        inputel.style.top = lineel.offsetTop + 'px';
        inputel.style.width = width + 'px';
        newinputel && win.frameel.appendChild(inputel);
      }

      if (win.type == 'buffer') {
        var cursel = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_cursor');
        /* Check to make sure an InvisibleCursor exists on the last line.
           The only reason it might not is if the window is entirely blank
           (no lines). In that case, append one to the window frame itself. */
        if (null == cursel) {
          cursel = create_element('span', { id: dom_prefix+'win'+win.id+'_cursor', 'class': 'InvisibleCursor' } );
          win.frameel.appendChild(cursel);
        }
        /* This calculation is antsy. (Was on Prototype, anyhow, I haven't
           retested in jquery...) On Firefox, buffermarginx is too high (or
           getWidth() is too low) by the width of a scrollbar. On MSIE,
           buffermarginx is one pixel too low. We fudge for that, giving a
           result which errs on the low side. */
        var width = Math.max(without_padding(win.frameel).width - (current_metrics.buffermarginx + cursel.offsetLeft + 2), 1);
        inputel.style.position = 'absolute';
        inputel.style.left = '0px';
        inputel.style.top = '0px';
        inputel.style.width = width+'px';
        newinputel && cursel.appendChild(inputel);
      }
    });
  }

  /* Handle the change in the timer request. The argument is either null
     (cancel the timer) or a positive value in milliseconds (reset and restart
     the timer with that interval).
  */
  function accept_timerrequest(arg) {
    /* Cancel timer, if there is one. Note that if the game passes us a
       timer value equal to our current interval, we will still reset and
       restart the timer. */
    if (request_timer) {
      window.clearTimeout(request_timer);
      request_timer = null;
      request_timer_interval = null;
    }
    /* if no arg, there's no new timer */
    if (arg) {
      /* Start a new timer. */
      request_timer_interval = arg;
      request_timer = window.setTimeout(evhan_timer_event, request_timer_interval);
    }
  }

  function accept_specialinput(arg) {
    if (arg.type == 'fileref_prompt') {
      var replyfunc = function(ref) {
        send_response('specialresponse', null, 'fileref_prompt', ref);
      };
      try {
        var writable = (arg.filemode != 'read');
        Dialog.open(writable, arg.filetype, arg.gameid, replyfunc);
      }
      catch (ex) {
        GlkOte.log('Unable to open file dialog: ' + ex);
        /* Return a failure. But we don't want to call send_response before
           glkote_update has finished, so we defer the reply slightly. */
        replyfunc = function(ref) {
          send_response('specialresponse', null, 'fileref_prompt', null);
        };
        defer_func(replyfunc);
      }
    }
    else {
      glkote_error('Request for unknown special input type: ' + arg.type);
    }
  }

  function has_class(el,classname) {
    return (el && el.className && (el.className.indexOf(classname) != -1))
  }
  
  /* Return the element which is the last BufferLine element of the
     window. If none, return null.
  */

  function buffer_last_line(win) {
    var divel = win.frameel.lastChild;
    return has_class(divel, 'BufferLine') ? divel : null;
  }

  /* Return the vertical offset (relative to the parent) of the top of the 
     last child of the parent.
     (Possibly broken in MSIE7? It worked in the old version, though.)
  */
  function buffer_last_line_top_offset(win) {
    var divel = buffer_last_line(win);
    return divel ? divel.offsetTop : 0;
  }

  /* Set windows_paging_count to the number of windows that need paging.
     If that's nonzero, pick an appropriate window for the paging focus.

     The canfocus flag determines whether this function can jump to an
     input field focus (should paging be complete).

     This must be called whenever a window's needspaging flag changes.
  */
  function readjust_paging_focus(canfocus) {
    windows_paging_count = 0;
    var pageable_win = 0;

    if (perform_paging) {
      Object.values(windowdic).forEach(function(win) {
        if (win.needspaging) {
          windows_paging_count += 1;
          if (!pageable_win || win.id == last_known_paging)
            pageable_win = win.id;
        }
      });
    }
    
    if (windows_paging_count) {
      /* pageable_win will be set. This is our new paging focus. */
      last_known_paging = pageable_win;
    }

    if (!windows_paging_count && canfocus) {
      /* Time to set the input field focus. This is the same code as in
         the update routine, although somewhat simplified since we don't
         need to worry about the DOM being in flux. */

      var newinputwin = 0;
      if (!disabled && !windows_paging_count) {
        Object.values(windowdic).forEach(function(win) {
          if (win.input) {
            if (!newinputwin || win.id == last_known_focus)
              newinputwin = win.id;
          }
        });
      }
      
      if (newinputwin) {
        var win = windowdic[newinputwin];
        if (win.inputel) {
          win.inputel.focus();
        }
      }
    }
  }

  /* Return the game interface object that was provided to init(). Call glkote_get_interface
     if a subsidiary library (e.g., dialog.js) needs to imitate some
     display setting. Do not try to modify the object; it will probably
     not do what you want.
  */

  /* Return the library interface object that we were passed or created.
     Call this if you want to use, e.g., the same Dialog object that GlkOte
     is using.
  */
  var glkote_libraries = { 'Dialog': Dialog, 'Blorb': Blorb };
  function glkote_get_library(val) {
    return glkote_libraries[val] || null;
  }
  
  /* Get the DOM element ids used for various standard elements. The argument
     should be one of 'windowport', 'gameport', 'errorpane', 'errorcontent',
     'loadingpane'.
     By default you will get the same string back. However, if a different
     element ID was set in GlkOte's configuration, you'll get that.
  */
  function glkote_get_dom_id(val) {
    switch (val) {
    case 'windowport': return windowport_id;
    case 'gameport': return gameport_id;
    case 'errorpane': return errorpane_id;
    case 'errorcontent': return errorcontent_id;
    case 'loadingpane': return loadingpane_id;
    }
    /* Unrecognized id name; just return the same value back. */
    return val;
  }

  /* Stash extra information needed for autosave only.
   */
  function glkote_save_allstate() {
    var obj = {
      metrics: {
        width: current_metrics.width,
        height: current_metrics.height
      },
      history: {}
    };

    Object.entries(windowdic).forEach(function(winid, win) {
      if (win.history && win.history.length)
        obj.history[winid] = win.history.slice(0);
      if (win.defcolor) {
        if (obj.defcolor === undefined)
          obj.defcolor = {};
        obj.defcolor[winid] = win.defcolor;
      }
    });
    
    return obj;
  }

  /* Log the message in the browser's error log, if it has one. (This shows
     up in Safari, in Opera, and in Firefox if you have Firebug installed.)
  */
  function glkote_log(msg) {
    if (window.console && console.log) {
      console.log(msg);
    }
    else if  (window.opera && opera.postError) {
      opera.postError(msg); }
  }

  /* Display the red error pane, with a message in it. This is called on
     fatal errors.
  */
  function glkote_error(msg) {
    if (!msg) {
      msg = '???';
    }
    var el = document.getElementById(errorcontent_id);
    if (el) {
      
      remove_children(el);
      el.appendChild(document.createTextNode(msg));
      
      el = document.getElementById(errorpane_id);
      if (el.className == 'WarningPane') {
        el.className = null;
      }
      el.style.display = 'inherit';   /* el.show() */
      error_visible = true;
      
      hide_loading();
    }
  }

  /* Displays a blue warning pane, with a message in it.

     Unlike glkote_error, a warning can be removed (call glkote_warning with
     no argument). The warning pane is intrusive, so it should be used for
     for conditions that interrupt or suspend normal play. An error overrides
     a warning.

     (Quixe uses this to display an "end of session" message.)
  */
  function glkote_warning(msg) {
    if (error_visible) {
      return;
    }
    if (!msg) {
      var error_pane = document.getElementById(errorpane_id);
      error_pane.style.display = 'none';
      return;
    }

    var el = document.getElementById(errorcontent_id);
    if (el) { 
      remove_children(el);
      el.appendChild(document.createTextNode(msg));
      var error_pane = document.getElementById(errorpane_id);
      error_pane.classList.add('WarningPane');
      error_pane.style.display = 'inherit';
      hide_loading();
    }
  }

  /* Cause an immediate input event, of type "external". This invokes
     Game.accept(), just like any other event.
  */
  function glkote_extevent(val) {
    send_response('external', null, val);
  }

  /* If we got a 'retry' result from the game, we wait a bit and then call
     this function to try it again.
  */
  function retry_update() {
    retry_timer = null;
    glkote_log('Retrying update...');
    send_response('refresh', null, null);
  }

  /* Hide the loading pane (the spinny compass), if it hasn't already been
     hidden.
  */
  function hide_loading() {
    if (loading_visible == false) {
      return;
    }
    loading_visible = false;

    var el = document.getElementById(loadingpane_id);
    if (el) {
      el.style.display = 'none';  /* el.hide() */
    }
  }

  /* Show the loading pane (the spinny compass), if it isn't already visible.
   */
  function show_loading() {
    if (loading_visible == true) {
      return;
    }
    loading_visible = true;

    var el = document.getElementById(loadingpane_id);
    if (el) {
      el.style.display = 'inherit';   /* el.show() */
    }
  }
  /* Add text to a DOM element. If GlkOte is configured to detect URLs,
     this does that, converting them into 
     <a href='...' class='External' target='_blank'> tags.
  */
  function insert_text_detecting(el, val) {
    if (!detect_external_links) {
      el.appendChild(document.createTextNode(val));
      return;
    }

    if (detect_external_links == 'match') {
      /* For 'match', we test the entire span of text to see if it's a URL.
         This is simple and fast. */
      if (regex_external_links.test(val)) {
        var ael = create_element('a', { 'href': val, 'class': 'External', 'target': '_blank' } );
        ael.text = val;
        el.appendChild(ael);
        return;
      }

      /* If not, fall through. */
    }
    else if (detect_external_links == 'search') {
      /* For 'search', we have to look for a URL within the span -- perhaps
         multiple URLs. This is more work, and the regex is more complicated
         too. */
      while (true) {
        var match = regex_external_links.exec(val);
        if (!match) {
          break;
        }
        /* Add the characters before the URL, if any. */
        if (match.index > 0) {
          var prefix = val.substring(0, match.index);
          el.appendChild(document.createTextNode(prefix));
        }
        /* Add the URL. */
        var ael = create_element('a', { 'href': match[0], 'class': 'External', 'target': '_blank' } );
        ael.text = match[0];
        el.appendChild(ael);
        /* Continue searching after the URL. */
        val = val.substring(match.index + match[0].length);
      }
      if (!val.length) {
        return;
      }
      /* Add the final string of characters, if there were any. */
    }

    /* Fall-through case. Just add the text. */
    el.appendChild(document.createTextNode(val));
  }

  /* Get the CanvasRenderingContext2D from a canvas element. 
   */
  function canvas_get_2dcontext(canvas) {
    if (canvas && canvas.getContext) {
      return canvas.getContext('2d');
    }
    return undefined;
  }

  /* This is responsible for drawing the queue of graphics operations.
     It will do simple fills synchronously, but image draws must be
     handled in a callback (because the image data might need to be pulled
     from the server).

     If the loadedimg argument is null, this was called to take care of
     new drawing ops. On an image draw, we call back here with loadedimg
     as the Image DOM object that succeeded (or failed).
  */
  function perform_graphics_ops(loadedimg, loadedev) {
    if (graphics_draw_queue.length == 0) {
      glkote_log('perform_graphics_ops called with no queued ops' + (loadedimg ? ' (plus image!)' : ''));
      return;
    }
    //glkote_log('### perform_graphics_ops, ' + graphics_draw_queue.length + ' queued' + (loadedimg ? ' (plus image!)' : '') + '.'); /*###*/

    /* Look at the first queue entry, execute it, and then shift it off.
       On error we must be sure to shift anyway, or the queue will jam!
       Note that if loadedimg is not null, the first queue entry should
       be a matching 'image' draw. */

    while (graphics_draw_queue.length) {
      var op = graphics_draw_queue[0];
      var win = windowdic[op.winid];
      if (!win) {
        glkote_log('perform_graphics_ops: op for nonexistent window ' + op.winid);
        graphics_draw_queue.shift();
        continue;
      }
      var el = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_canvas');
      var ctx = canvas_get_2dcontext(el);
      if (!ctx) {
        glkote_log('perform_graphics_ops: op for nonexistent canvas ' + win.id);
        graphics_draw_queue.shift();
        continue;
      }

      var optype = op.special;
      
      switch (optype) {
      case 'setcolor':
        /* Set the default color (no visible changes). */
        win.defcolor = op.color;
        break;
      case 'fill':
        /* Both color and geometry are optional here. */
        ctx.fillStyle = (op.color === undefined) ? win.defcolor : op.color;
        if (op.x === undefined) {
          /* Fill the whole canvas frame. Also set the background color,
             so that future window resizes look nice. */
          ctx.fillRect(0, 0, win.graphwidth, win.graphheight);
          win.frameel.style.backgroundColor = ctx.fillStyle;
        }
        else {
          ctx.fillRect(op.x, op.y, op.width, op.height);
        }
        ctx.fillStyle = '#000000';
        break;
      case 'image':
        /* This is the tricky case. If this is a successful load callback,
           loadedimg already contains the desired image. If it doesn't, we
           check the cache. If that doesn't have it, we have to create a new
           Image and set up the loading callbacks. */
        if (!loadedimg) {
          var oldimg = image_cache[op.image];
          if (oldimg && oldimg.width > 0 && oldimg.height > 0) {
            loadedimg = oldimg;
            loadedev = true;
            //glkote_log('### found image in cache');
          }
          else {
            /* This cached image is broken. I don't know if this can happen,
               but if it does, drop it. */
            delete image_cache[op.image];
          }
        }
        if (!loadedimg) {
          var imgurl = op.url;
          if (Blorb && Blorb.get_image_url) {
            var newurl = Blorb.get_image_url(op.image);
            if (newurl)
              imgurl = newurl;
          }
          //glkote_log('### setting up callback with url');
          var newimg = new Image();


          
          newimg.addEventListener('load', function(ev) { perform_graphics_ops(newimg, ev); });
          newimg.addEventListener('error', function(ev) { perform_graphics_ops(newimg, null); });
          /* Setting the src attribute will trigger one of the above
             callbacks. */
          newimg.src = imgurl;
          return;
        }
        /* We were called back with an image. Hopefully it loaded ok. Note that
           for the error callback, loadedev is null. */
        if (loadedev) {
          image_cache[op.image] = loadedimg;
          ctx.drawImage(loadedimg, op.x, op.y, op.width, op.height);
        }
        loadedev = null;
        loadedimg = null;
        /* Either way, continue with the queue. */
        break;
      default:
        glkote_log('Unknown special entry in graphics content: ' + optype);
        break;
      }

      graphics_draw_queue.shift();
    }
    //glkote_log('### queue empty.');
  }

  /* Run a function (no arguments) in timeout seconds. */
  function delay_func(timeout, func)
  {
    return window.setTimeout(func, timeout*1000);
  }

  /* Run a function (no arguments) "soon". */
  function defer_func(func)
  {
    return window.setTimeout(func, 0.01*1000);
  }
  /* Add a line to the window's command history, and then submit it to
     the game. (This is a utility function used by various keyboard input
     handlers.)
  */
  function submit_line_input(win, val, termkey) {
    var historylast = null;
    if (win.history.length)
      historylast = win.history[win.history.length-1];

    /* Store this input in the command history for this window, unless
       the input is blank or a duplicate. */
    if (val && val != historylast) {
      win.history.push(val);
      if (win.history.length > 20) {
        /* Don't keep more than twenty entries. */
        win.history.shift();
      }
    }

    send_response('line', win, val, termkey);
  }

  /* Invoke the game interface's accept() method, passing along an input
     event, and also including all the information about incomplete line
     inputs.

     This is called by each event handler that can signal a completed input
     event.

     The val and val2 arguments are only used by certain event types, which
     is why most of the invocations pass three arguments instead of four.
  */
  function send_response(type, win, val, val2) {
    if (disabled && type != 'specialresponse')
      return;

    if (generation <= generation_sent
        && !(type == 'init' || type == 'refresh')) {
      glkote_log('Not sending repeated generation number: ' + generation);
      return;
    }

    var winid = 0;
    if (win) {
      winid = win.id;
    }
    var res = { type: type, gen: generation };
    generation_sent = generation;

    if (type == 'line') {
      res.window = win.id;
      res.value = val;
      if (val2)
        res.terminator = val2;
    }
    else if (type == 'char') {
      res.window = win.id;
      res.value = val;
    }
    else if (type == 'hyperlink') {
      res.window = win.id;
      res.value = val;
    }
    else if (type == 'mouse') {
      res.window = win.id;
      res.x = val;
      res.y = val2;
    }
    else if (type == 'external') {
      res.value = val;
    }
    else if (type == 'specialresponse') {
      res.response = val;
      res.value = val2;
    }
    else if (type == 'debuginput') {
      res.value = val;
    }
    else if (type == 'redraw') {
      res.window = win.id;
    }
    else if (type == 'init') {
      res.metrics = val;
      res.support = ['timer', 'graphics', 'graphicswin', 'hyperlinks'];
    }
    else if (type == 'arrange') {
      res.metrics = val;
    }

    /* Save partial inputs, unless this is an event which disables
       or ignores the UI. */
    if (!(type == 'init' || type == 'refresh'
          || type == 'specialresponse' || type == 'debuginput')) {
      Object.values(windowdic).forEach(function(win) {
        var savepartial = (type != 'line' && type != 'char') 
            || (win.id != winid);
        if (savepartial && win.input && win.input.type == 'line'
            && win.inputel && win.inputel.value) {
          var partial = res.partial;
          if (!partial) {
            partial = {};
            res.partial = partial;
          };
          partial[win.id] = win.inputel.value;
        }
      });
    }

    if (recording) {
      recording_state.input = res;
      recording_state.timestamp = (new Date().getTime());
    }
    game_interface.accept(res);
  }

  /* ---------------------------------------------- */

  /* Take apart the query string of the current URL, and turn it into
     an object map.
     (Adapted from querystring.js by Adam Vandenberg.)
  */
  function get_query_params() {
    var map = {};

    var qs = location.search.substring(1, location.search.length);
    if (qs.length) {
      var args = qs.split('&');

      qs = qs.replace(/\+/g, ' ');
      for (var ix = 0; ix < args.length; ix++) {
        var pair = args[ix].split('=');
        var name = decodeURIComponent(pair[0]);
        
        var value = (pair.length==2)
            ? decodeURIComponent(pair[1])
            : name;
        
        map[name] = value;
      }
    }

    return map;
  }

  /* This is called every time the game updates the screen state. It
     wraps up the update with the most recent input event and sends them
     off to whatever is handling transcript recordings.
  */
  function recording_send(arg) {
    recording_state.output = arg;
    recording_state.outtimestamp = (new Date().getTime());

    var send = true;

    /* If the format is not "glkote", we should massage state.input and
       state.output. (Or set send=false to skip this update entirely.) */
    if (recording_state.format == 'simple') {
      var input = recording_state.input;
      var output = recording_state.output;

      var inputtype = null;
      if (input)
        inputtype = input.type;

      if (inputtype == 'line' || inputtype == 'char') {
        recording_state.input = input.value;
      }
      else if (inputtype == 'init' || inputtype == 'external' || inputtype == 'specialresponse' || !inputtype) {
        recording_state.input = '';
      }
      else {
        /* Do not send 'arrange' or 'redraw' events. */
        send = false;
      }

      /* We keep track of which windows are buffer windows. */
      if (output.windows) {
        recording_context.bufferwins = {};
        output.windows.filter(w => (output.windows[ix].type == 'buffer')).forEach(function(w) { recording_context.bufferwins[w.id] = true; });
        /*              for (var ix=0; ix<output.windows.length; ix++) {
                        if (output.windows[ix].type == 'buffer')
                        recording_context.bufferwins[output.windows[ix].id] = true;
                        }*/
      }

      /* Accumulate all the text that's sent to buffer windows. */
      var buffer = '';

      if (output.content) {
        for (var ix=0; ix<output.content.length; ix++) {
          var content = output.content[ix];
          if (recording_context.bufferwins && recording_context.bufferwins[content.id]) {
            if (content.text) {
              for (var jx=0; jx<content.text.length; jx++) {
                var text = content.text[jx];
                if (!text.append) {
                  buffer = buffer + '\n';
                }
                if (text.content) {
                  for (var kx=0; kx<text.content.length; kx++) {
                    var el = text.content[kx];
                    /* Why did I allow the LINE_DATA_ARRAY to have two
                       possible formats? Sigh */
                    if ('string' === typeof(el)) {
                      kx++;
                      buffer = buffer + text.content[kx];
                    }
                    else {
                      if (el.text) {
                        buffer = buffer + el.text;
                      }
                    }
                  }
                }
              }
            }
          }
        }      
      }

      recording_state.output = buffer;
    }


    if (send)
      recording_handler(recording_state);

    recording_state.input = null;
    recording_state.output = null;
    recording_state.timestamp = 0;
    recording_state.outtimestamp = 0;
  }

  /* Send a wrapped-up state off to an AJAX handler. The state is a JSONable
     object containing input, output, and timestamps. The format of the input
     and output depends on the recording parameters.

     (The timestamp field refers to the input time, which is what you generally
     care about. The outtimestamp will nearly always follow very closely. If
     there's a long gap, you know your game has spent a long time computing.)

     If the AJAX request returns an error, this shuts off recording (rather
     than trying again for future commands).
  */
  function recording_standard_handler(state) {

    var request = new XMLHttpRequest();
    request.open('POST', recording_handler_url, true);
    request.setRequestHeader('Content-Type', 'application/json; charset=UTF-8');
    request.onerror = function(jqxhr, textstatus, errorthrown) {
      glkote_log('Transcript recording failed; deactivating. Error ' + textstatus + ': ' + errorthrown);
      recording = false;
    };
    request.send(JSON.stringify(state));
  }

  /* ---------------------------------------------- */

  /* DOM event handlers. */

  /* Detect the browser window being resized.

     This event is triggered by several causes:

     - A real window DOM resize event. (This should include "make font
     bigger/smaller".)
     - Autorestore. (The window might be a different size than the autosave
     data expects, so we trigger this.)
     - The magic gameport resize sensors created in create_resize_sensors().
  */
  function evhan_doc_resize(ev) {
    /* We don't want to send a whole flurry of these events, just because
       the user is dragging the window-size around. So we set up a short
       timer, and don't do anything until the flurry has calmed down. */

    if (resize_timer != null) {
      window.clearTimeout(resize_timer);
      resize_timer = null;
    }

    resize_timer = delay_func(0.20, doc_resize_real);
  }

  /* This executes when no new resize events have come along in the past
     0.20 seconds. (But if the UI is disabled, we delay again, because
     the game can't deal with events yet.)

     Note that this sends a Glk "arrange" event, not a "redraw" event.
     Those will follow soon if needed.

     (What actually happens, and I apologize for this, is that the
     "arrange" event causes the game to send new window sizes. The
     accept handler sees a size change for a graphics window and queues
     up a "redraw" event via send_window_redraw.)

     ### We really should distinguish between disabling the UI (delay
     resize events) from shutting down the UI (ignore resize events).
  */
  function doc_resize_real() {
    resize_timer = null;

    if (disabled) {
      resize_timer = delay_func(0.20, doc_resize_real);
      return;
    }

    var new_metrics = measure_window();
    if (metrics_match(new_metrics, current_metrics)) {
      /* If the metrics haven't changed, skip the arrange event. Necessary on
         mobile webkit, where the keyboard popping up and down causes a same-size
         resize event. */
      return;
    }
    current_metrics = new_metrics;
    send_response('arrange', null, current_metrics);
  }

  /* Send a "redraw" event for the given (graphics) window. This is triggered
     by the accept handler when it sees a graphics window change size.

     (Not actually an event handler, but I put it down here with
     doc_resize_real.)
  */
  function send_window_redraw(winid) {
    var win = windowdic[winid];

    /* It's not likely that the window has been deleted since this function
       was queued up. But we'll be paranoid. */
    if (!win || win.type != 'graphics') {
      return;
    }
    send_response('redraw', win, null);
  }

  /* Event handler: the devicePixelRatio has changed. (Really we only get
     this for changes across particular thresholds, but I set up a bunch.)
  */
  function evhan_doc_pixelreschange(ev) {
    var ratio = window.devicePixelRatio || 1;
    if (ratio != current_devpixelratio) {
      current_devpixelratio = ratio;
      //glkote_log('### devicePixelRatio changed to ' + current_devpixelratio);

      /* If we have any graphics windows, we need to redo their size and
         scale, and then hit them with a redraw event. */
      Object.entries(windowdic).forEach(function(winid, win) {
        if (win.type == 'graphics') {
          var el = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_canvas');
          win.scaleratio = current_devpixelratio / win.backpixelratio;
          //glkote_log('### changed canvas to scale ' + win.scaleratio + ' (device ' + current_devpixelratio + ' / backstore ' + win.backpixelratio + ')');
          var ctx = canvas_get_2dcontext(el);
          el.width = win.graphwidth * win.scaleratio;
          el.height = win.graphheight * win.scaleratio;
          el.style.width = win.graphwidth + 'px';
          el.style.height = win.graphheight + 'px';
          if (ctx) {
            /* Set scale to win.scaleratio */
            ctx.setTransform(win.scaleratio, 0, 0, win.scaleratio, 0, 0);
            ctx.fillStyle = win.defcolor;
            ctx.fillRect(0, 0, win.graphwidth, win.graphheight);
            ctx.fillStyle = '#000000';
          }
          win.frameel.style.backgroundColor =  win.defcolor;
          /* We have to trigger a redraw event for this window. But we can't do
             a bunch of them from the same handler. We'll set up a deferred
             function call. */
          defer_func(function() { send_window_redraw(winid); });
        }  
      });
    }
  }

  /* Event handler: keypress events on input fields.

     Move the input focus to whichever window most recently had it.
  */
  function evhan_doc_keypress(ev) {
    /* Don't mess with command key combinations. This is not a perfect
       test, since option-key combos are ordinary (accented) characters
       on Mac keyboards, but it's close enough. */

    if (disabled || ev.altKey || ev.metaKey || ev.ctrlKey) {
      return;
    }
    if (has_class(ev.target, 'CanHaveInputFocus') || (ev.target.tagName.toLowerCase() == 'input')) {
      /* If the focus is on an element which insists it's input-like,
         don't mess with that either. This is necessary for input fields
         in shadow DOM and plugins. */
      /* If the focus is already on an input field, don't mess with it. */
      return;
    }
    var keycode = ev ? ev.which : 0;
    var win;

    if (windows_paging_count) {
      win = windowdic[last_known_paging];
      if (win) {
        if (!((keycode >= 32 && keycode <= 126) || keycode == key_codes['return'])) {
          /* If the keystroke is not a printable character (or Enter),
             we return and let the default behavior happen. That lets
             pageup/pagedown/home/end work normally. */
          return;
        }
        ev.preventDefault();
        /* Scroll the unseen content to the top. */
        window_scroll(win, 'top');
        return;
      }
    }

    win = windowdic[last_known_focus];
    if (!win || !win.inputel) {
      return;
    }
    win.inputel.focus();

    if (win.input.type == 'line') {
      if (keycode == key_codes['return']) {
        /* Grab the Return/Enter key here. This is the same thing we'd do if
           the input field handler caught it. */
        submit_line_input(win, win.inputel.value, null);
        /* Safari drops an extra newline into the input field unless we call
           preventDefault() here. */
        ev.preventDefault();
        return;
      }

      if (keycode) {
        /* For normal characters, we fake the normal keypress handling by
           appending the character onto the end of the input field. If we
           didn't call preventDefault() here, Safari would actually do
           the right thing with the keystroke, but Firefox wouldn't. */
        /* This is completely wrong for accented characters (on a Mac
           keyboard), but that's beyond my depth. */
        if (keycode >= 32) {
          var val = String.fromCharCode(keycode);
          win.inputel.value = win.inputel.value + val;
        }
        ev.preventDefault();
        return;
      }

    }
    else {
      /* In character input, we only grab normal characters. Special keys
         should be left to behave normally (arrow keys scroll the window,
         etc.) (This doesn't work right in Firefox, but it's not disastrously
         wrong.) */
      //### grab arrow keys too? They're common in menus.
      var res = null;
      if (keycode == key_codes['return']) {
        res = 'return';
      }
      else if (keycode == key_codes.backspace) {
        res = 'delete';
      }
      else if (keycode) {
        res = String.fromCharCode(keycode);
      }
      if (res) {
        send_response('char', win, res);
      }
      ev.preventDefault();
      return;
    }
  }

  /* Event handler: mousedown events on windows.

     Remember which window the user clicked in last, as a hint for setting
     the focus. (Input focus and paging focus are tracked separately.)
  */
  function evhan_window_mousedown(ev) {
    var winid = ev.data;
    var win = windowdic[winid];
    if (win) {
      if (win.inputel) {
        last_known_focus = win.id;
      }
      
      if (win.needspaging) {
        last_known_paging = win.id;
      }
      else if (win.inputel) {
        last_known_paging = 0;
      }
    }
  }

  function el_offset(el) {
    if (!el.getClientRects().length) {
      return { top: 0, left: 0 };
    }

    let rect = el.getBoundingClientRect();
    let win = el.ownerDocument.defaultView;
    return { top: rect.top + win.pageYOffset, left: rect.left + win.pageXOffset };   
  } 

  /* Event handler: mouse click events on graphics or grid windows
   */
  function evhan_input_mouse_click(ev) {
    var winid = ev.data;
    var win = windowdic[winid];
    if (win && win.reqmouse && (0 == ev.button)) {
      var xpos = 0;
      var ypos = 0;

      switch(win.type) {
      case 'grid':
        /* Measure click position relative to the zeroth line of the grid. */
        var lineel = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_ln'+0);
        if (lineel) {
          var linepos = el_offset(lineel);
          xpos = Math.floor((ev.clientX - linepos.left) / current_metrics.gridcharwidth);
          ypos = Math.floor((ev.clientY - linepos.top) / current_metrics.gridcharheight);
        }
        xpos = Math.min(xpos, win.gridwidth-1);
        ypos = Math.min(ypos, win.gridheight-1);
        break;
      case 'graphics':
        /* Measure click position relative to the canvas. */
        var canel = (dom_context||document).getElementById(dom_prefix+'win'+win.id+'_canvas');
        if (canel) {
          var pos = el_offset(canel);
          xpos = Math.min(ev.clientX - pos.left, win.graphwidth-1);
          ypos = Math.min(ev.clientY - pos.top, win.graphheight-1);
        }
        break;
      default:
        return;
      }
      xpos = Math.max(xpos, 0);
      ypos = Math.max(ypos, 0);
      ev.preventDefault();
      send_response('mouse', win, xpos, ypos);
    }
  }

  /* Event handler: keydown events on input fields (character input)

     Detect the arrow keys, and a few other special keystrokes, for
     character input. We don't grab *all* keys here, because that would
     include modifier keys (shift, option, etc) -- we don't want to
     count those as character input.
  */
  function evhan_input_char_keydown(ev) {
    var keycode = ev ? ev.keyCode : 0; //### ev.which?
    if (keycode) {
      var res = null;

      /* We don't grab Return/Enter in this function, because Firefox lets
         it go through to the keypress handler (even if we try to block it),
         which results in a double input. */
      if (keys_by_code.hasOwnProperty(keycode)) {
        res = keys_by_code[keycode];
        var winid = this.dataset.winid;
        var win = windowdic[winid];
        if (!win || !win.input) {
          return true;
        }
        send_response('char', win, res);
        return false;
      }
    }
    return true;
  }

  /* Event handler: keypress events on input fields (character input)

     Detect all printable characters. (Arrow keys and such don't generate
     a keypress event on all browsers, which is why we grabbed them in
     the keydown handler, above.)
  */
  function evhan_input_char_keypress(ev) {
    var keycode = ev ? ev.which : 0;
    if (keycode) {
      var res = (keycode == key_codes['return']) ? 'return' : String.fromCharCode(keycode);

      var winid = this.dataset.winid
      var win = windowdic[winid];
      if (!win || !win.input) {
        return true;
      }
      send_response('char', win, res);
    }
    return false;
  }

  /* Event handler: keydown events on input fields (line input)

     Divert the up and down arrow keys to scroll through the command history
     for this window. */
  function evhan_input_keydown(ev) {
    var keycode = 0;
    if (ev) {
      keycode = ev.keyCode; //### ev.which?
    }
    if (!keycode) {
      return true;
    }
    if (keycode == key_codes.up || keycode == key_codes.down) {
      var winid = this.dataset.winid
      var win = windowdic[winid];
      if (!win || !win.input) {
        return true;
      }
      if (keycode == key_codes.up && win.historypos > 0) {
        win.historypos -= 1;
        this.value =  (win.historypos < win.history.length) ?          win.history[win.historypos] : '';
      }

      if (keycode == key_codes.down && win.historypos < win.history.length) {
        win.historypos += 1;
        this.value =  (win.historypos < win.history.length) ?        win.history[win.historypos] : '';
      }
      return false;
    }
    else if (terminator_key_values[keycode]) {
      var winid = this.dataset.winid;
      var win = windowdic[winid];
      if (!win || !win.input) {
        return true;
      }
      if (win.terminators[terminator_key_values[keycode]]) {
        /* This key is listed as a current terminator for this window,
           so we'll submit the line of input. */
        submit_line_input(win, win.inputel.value, terminator_key_values[keycode]);
        return false;
      }
    }

    return true;
  }

  /* Event handler: keypress events on input fields (line input)

     Divert the enter/return key to submit a line of input.
  */
  function evhan_input_keypress(ev) {
    var keycode = ev ? ev.which : 0;
    if (keycode == key_codes['return']) {
      var winid = this.dataset.winid;
      var win = windowdic[winid];
      if (!win || !win.input) {
        return true;
      }
      submit_line_input(win, this.value, null);
      return false;
    }

    return true;
  }

  /* Event handler: focus events on input fields

     Notice that the focus has switched to a line/char input field.
  */
  function evhan_input_focus(ev) {
    var winid = ev.data;
    if (windowdic.hasOwnProperty(winid)) {
      currently_focused = true;
      last_known_focus = winid;
      last_known_paging = winid;
      return true;
    }
    return false;
  }

  /* Event handler: blur events on input fields

     Notice that the focus has switched away from a line/char input field.
  */
  function evhan_input_blur(ev) {
    var winid = ev.data;
    if (windowdic.hasOwnProperty(winid)) {
      currently_focused = false;
    }
  }

  /* Event handler: scrolling in buffer window 
   */
  function evhan_window_scroll(ev) {
    var winid = ev.data;
    var win = windowdic[winid];
    
    if (win && win.needspaging) {
      window_scroll(win);
    }
  }

  function window_scroll(win, where, dont_change_paging) {
    var frameel, frameheight, newtopunseen, moreel;
    frameel = win.frameel;
    frameheight = frameel.offsetHeight;
    if (where == 'bottom') {
      frameel.scrollTop = frameel.scrollHeight - frameheight;
    }
    else if (where == 'top') {
      frameel.scrollTop = win.topunseen - current_metrics.buffercharheight;
    }
    newtopunseen = Math.min(frameel.scrollTop + frameheight, buffer_last_line_top_offset(win));
    win.topunseen = Math.max(win.topunseen, newtopunseen);
    if (win.needspaging && !dont_change_paging) {
      /* The scroll-down might have cleared needspaging already. But 
         if not... */
      if (frameel.scrollTop + frameheight + moreprompt_margin >= frameel.scrollHeight) {
        win.needspaging = false;
        remove_if_exists(dom_prefix+'win'+win.id+'_moreprompt', dom_context);
        readjust_paging_focus(true);
      }
    }
    
  }

  /* Event handler constructor: report a click on a hyperlink
     (This is a factory that returns an appropriate handler function, for
     stupid Javascript closure reasons.)

     Generate the appropriate event for a hyperlink click. Return false,
     to suppress the default HTML action of hyperlinks.
  */
  function build_evhan_hyperlink(winid, linkval) {
    return function() {
      var win = windowdic[winid];
      if (win && win.reqhyperlink) {
        send_response('hyperlink', win, linkval);
      }
      return false;
    };
  }

  /* Event handler for the request_timer timeout that we set in 
     accept_timerrequest().
  */
  function evhan_timer_event() {
    if ((!request_timer) || (!request_timer_interval)) {
      /* This callback should have been cancelled before firing, so we
         shouldn't even be here. */
      return;
    }

    /* It's a repeating timer, so set it again. */
    request_timer = window.setTimeout(evhan_timer_event, request_timer_interval);
    
    if (disabled) {
      /* Can't handle the timer while the UI is disabled, so we punt.
         It will fire again someday. */
      return;
    }

    send_response('timer');
  }

  /* Event handler for the GiDebug command callback. 
   */
  function evhan_debug_command(cmd) {
    send_response('debuginput', null, cmd);
  }

  /* ---------------------------------------------- */

  /* End of GlkOte namespace function. Return the object which will
     become the GlkOte global. */
  return {
    classname: 'GlkOte',
    version:  '2.3.0',
    init:     glkote_init,
    inited:   glkote_inited,
    update:   glkote_update,
    extevent: glkote_extevent,
    getinterface: function() { return game_interface; },
    getlibrary: glkote_get_library,
    getdomid: glkote_get_dom_id,
    getdomcontext: function() { return dom_context; },
    setdomcontext: function(v) { dom_context = v; },
    save_allstate : glkote_save_allstate,
    log:      glkote_log,
    warning:  glkote_warning,
    error:    glkote_error
  };

};

/* GlkOte is an instance of GlkOteClass, ready to init. */
var GlkOte = new GlkOteClass();

// Node-compatible behavior
try { exports.GlkOte = GlkOte; exports.GlkOteClass = GlkOteClass; } catch (ex) {};

/* End of GlkOte library. */

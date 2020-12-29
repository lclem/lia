(function (global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined' ? factory(require('codemirror'), require('codemirror/addon/search/searchcursor'), require('codemirror/addon/dialog/dialog.css'), require('codemirror/addon/dialog/dialog.js'), require('codemirror/addon/display/panel.js'), require('codemirror/addon/search/search.js'), require('codemirror/addon/search/jump-to-line.js'), require('codemirror/addon/hint/show-hint.js'), require('codemirror/addon/selection/mark-selection')) :
  typeof define === 'function' && define.amd ? define(['codemirror', 'codemirror/addon/search/searchcursor', 'codemirror/addon/dialog/dialog.css', 'codemirror/addon/dialog/dialog.js', 'codemirror/addon/display/panel.js', 'codemirror/addon/search/search.js', 'codemirror/addon/search/jump-to-line.js', 'codemirror/addon/hint/show-hint.js', 'codemirror/addon/selection/mark-selection'], factory) :
  (global = global || self, factory(global.CodeMirror));
}(this, function (CodeMirror) { 'use strict';

  CodeMirror = CodeMirror && CodeMirror.hasOwnProperty('default') ? CodeMirror['default'] : CodeMirror;

  // CodeMirror, copyright (c) by Marijn Haverbeke and others
  // Distributed under an MIT license: http://codemirror.net/LICENSE

  (function(mod) {
    if (typeof exports == "object" && typeof module == "object") // CommonJS
      mod(require("../../lib/codemirror"));
    else if (typeof define == "function" && define.amd) // AMD
      define(["../../lib/codemirror"], mod);
    else // Plain browser env
      mod(CodeMirror);
  })(function(CodeMirror) {

  CodeMirror.defineMode("agda", function(_config, modeConfig) {

    function switchState(source, setState, f) {
      setState(f);
      return f(source, setState);
    }
    var digitRE = /\d/;
    var hexitRE = /[0-9A-Fa-f]/;
    var octitRE = /[0-7]/;
    var idRE = /[a-z_A-Z0-9'\xa1-\uffff\[\],]/;
    var symbolRE = /[-!#$%&*+.\/<=>?@\\^|~:]/;
    var specialRE = /[.();@{}]/;
    // ".", ";", "{", "}", "(", ")", "\"", "@")
    var whiteCharRE = /[ \t\v\f]/; // newlines are handled in tokenizer

    /*
    // from agda-mode (UNUSED)
    //  ========================================================================================
    const floatRegex = /-?(?:0|[1-9]\d*)(?:\.\d+)?(?:[eE][+-]?\d+)?(?=[.;{}()@"\s]|$)/u;
    const integerRegex = /-?(?:0|[1-9]\d*|0x[0-9A-Fa-f]+)(?=[.;{}()@"\s]|$)/u;

    const keywordsRegex = new RegExp(
      "(?:[_=|→:?\\\\λ∀]|->|\\.{2,3}|abstract|as|codata|coinductive|constructor|" +
        "data|do|eta-equality|field|forall|hiding|import|in|inductive|" +
        "infix|infixl|infixr|instance|let|macro|module|mutual|no-eta-equality|" +
        "open|overlap|pattern|postulate|primitive|private|public|quote|" +
        "quoteContext|quoteGoal|quoteTerm|record|renaming|rewrite|" +
        "syntax|tactic|to|unquote|unquoteDecl|unquoteDef|using|variable|where|with|" +
        'Set(?:\\d+|[₀₁₂₃₄₅₆₇₈₉]+)?)(?=[.;{}()@"\\s]|$)',
      "u"
    );

    const escapeDec = "0|[1-9]\\d*";
    const escapeHex = "x(?:0|[1-9A-Fa-f][0-9A-Fa-f]*)";
    const escapeCode =
      "[abtnvf&\\\\'\"]|NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|" +
      "SO|SI|DLE|DC[1-4]|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|SP|DEL";
    const escapeChar = new RegExp(
      "\\\\(?:" + escapeDec + "|" + escapeHex + "|" + escapeCode + ")",
      "u"
    );
    //  ========================================================================================
    */

    function normal(source, setState) {
      if (source.eatWhile(whiteCharRE)) {
        return null;
      }

      var ch = source.next();
      if (specialRE.test(ch)) {
        if (ch == '{' && source.eat('-')) {
          var t = "comment";
          if (source.eat('#')) {
            t = "meta";
          }
          return switchState(source, setState, ncomment(t, 1));
        }
        return null;
      }

      if (ch == '\'') {
        if (source.eat('\\')) {
          source.next();  // should handle other escapes here
        }
        else {
          source.next();
        }
        if (source.eat('\'')) {
          return "string";
        }
        return "string error";
      }

      if (ch == '"') {
        return switchState(source, setState, stringLiteral);
      }

      if (idRE.test(ch)) {
        source.eatWhile(idRE);
        if (source.eat('.')) {
          return "qualifier";
        }
        return "variable";
      }

      if (digitRE.test(ch)) {
        if (ch == '0') {
          if (source.eat(/[xX]/)) {
            source.eatWhile(hexitRE); // should require at least 1
            return "integer";
          }
          if (source.eat(/[oO]/)) {
            source.eatWhile(octitRE); // should require at least 1
            return "number";
          }
        }
        source.eatWhile(digitRE);
        var t = "number";
        if (source.match(/^\.\d+/)) {
          t = "number";
        }
        if (source.eat(/[eE]/)) {
          t = "number";
          source.eat(/[-+]/);
          source.eatWhile(digitRE); // should require at least 1
        }
        return t;
      }

      if (ch == "." && source.eat("."))
        return "keyword";

      if (symbolRE.test(ch)) {
        if (ch == '-' && source.eat(/-/)) {
          source.eatWhile(/-/);
          if (!source.eat(symbolRE)) {
            source.skipToEnd();
            return "comment";
          }
        }
        var t = "variable";
        if (ch == ':') {
          t = "variable-2";
        }
        source.eatWhile(symbolRE);
        return t;
      }

      return "error";
    }

    function ncomment(type, nest) {
      if (nest == 0) {
        return normal;
      }
      return function(source, setState) {
        var currNest = nest;
        while (!source.eol()) {
          var ch = source.next();
          if (ch == '{' && source.eat('-')) {
            ++currNest;
          }
          else if (ch == '-' && source.eat('}')) {
            --currNest;
            if (currNest == 0) {
              setState(normal);
              return type;
            }
          }
        }
        setState(ncomment(type, currNest));
        return type;
      };
    }

    function stringLiteral(source, setState) {
      while (!source.eol()) {
        var ch = source.next();
        if (ch == '"') {
          setState(normal);
          return "string";
        }
        if (ch == '\\') {
          if (source.eol() || source.eat(whiteCharRE)) {
            setState(stringGap);
            return "string";
          }
          if (source.eat('&')) ;
          else {
            source.next(); // should handle other escapes here
          }
        }
      }
      setState(normal);
      return "string error";
    }

    function stringGap(source, setState) {
      if (source.eat('\\')) {
        return switchState(source, setState, stringLiteral);
      }
      source.next();
      setState(normal);
      return "error";
    }

    var wellKnownWords = (function() {
      var wkw = {};
      function setType(t) {
        return function () {
          for (var i = 0; i < arguments.length; i++)
            wkw[arguments[i]] = t;
        };
      }

      // reserved keywords
      // those appear in bold green
      setType("keyword")(
        "abstract", /*"as",*/ "codata", "coinductive", "constructor", "data", "do", "eta-equality",
        "field", "forall", "hiding", "import", "in", "inductive", "infix", "infixl", "infixr", "instance",
        "let", "macro", "module", "mutual", "no-eta-equality", "open", "overlap",
        "pattern", "postulate", "primitive", "private", "public", "quote", "quoteContext", "quoteGoal", "quoteTerm",
        "record", "renaming", "rewrite", "syntax", "tactic", "unquote", "unquoteDecl", "unquoteDef", "using", "variable", "where", "with");

      // setType("builtin")(".", ";", "{", "}", "(", ")", "\"", "@");

      // builtin symbols
      // those appear in green
      setType("builtin")(
        "Set", "Set1", "Set2", "{", "}", "=", "|", "->", "→", ":", "?", "\\", "λ", "∀", "..", "...", "(", ")");

      var override = modeConfig.overrideKeywords;
      if (override) for (var word in override) if (override.hasOwnProperty(word))
        wkw[word] = override[word];

      return wkw;
    })();

    return {
      startState: function ()  { return { f: normal }; },
      copyState:  function (s) { return { f: s.f }; },

      token: function(stream, state) {
        var t = state.f(stream, function(s) { state.f = s; });
        var w = stream.current();
        return wellKnownWords.hasOwnProperty(w) ? wellKnownWords[w] : t;
      },

      blockCommentStart: "{-",
      blockCommentEnd: "-}",
      lineComment: "--"
    };

  });

  CodeMirror.defineMIME("text/x-agda", "agda");
  CodeMirror.defineMIME("text/agda", "agda");

  });

  const hint = (cm, self, data) =>
    cm.replaceRange(data.symbol, self.from, self.to);

  const cmObj = (k, v) => ({
    text: "\\" + k,
    symbol: v,
    displayText: `${v} \\${k}`,
    hint: hint,
  });

  const toTable = pairs =>
    pairs.reduce((a, p) => {
      a.push.apply(
        a,
        Array.from(p[1].replace(/\s/g, "")).map(v => cmObj(p[0], v))
      );
      return a;
    }, []).sort((a,b) => a.text.localeCompare(b.text));

  // Subset of agda-input-translations + TeX-Input
  // TODO Add some more from TeX-Input
  // https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L191
  const translations = toTable([
    ["ell", "ℓ"],
    // Equality and similar symbols.
    // ["eq", "=∼∽≈≋∻∾∿≀≃⋍≂≅ ≌≊≡≣≐≑≒≓≔≕≖≗≘≙≚≛≜≝≞≟≍≎≏≬⋕"],
    // ["eqn", "≠≁ ≉     ≄  ≇≆  ≢                 ≭    "],
    // ["=", "="],
    ["=n", "≠"],
    ["~", "∼"],
    ["~n", "≁"],
    ["~~", "≈"],
    ["~~n", "≉"],

    // ["~~~", "≋"],
    // [":~", "∻"],
    ["~-", "≃"],
    ["~-n", "≄"],
    ["-~", "≂"],
    ["~=", "≅"],
    ["~=n", "≇"],
    ["~~-", "≊"],
    ["==", "≡"],
    ["==n", "≢"],
    // ["===", "≣"],
    // [".=", "≐"],
    // [".=.", "≑"],
    // [":=", "≔"],
    // ["=:", "≕"],
    // ["=o", "≗"],
    // ["(=", "≘"],
    // ["and=", "≙"],
    // ["or=", "≚"],
    // ["*=", "≛"],
    // ["t=", "≜"],
    // ["def=", "≝"],
    // ["m=", "≞"],
    // ["?=", "≟"],

    // Inequality and similar symbols.
    //["leq", "<≪⋘≤≦≲ ≶≺≼≾⊂⊆ ⋐⊏⊑ ⊰⊲⊴⋖⋚⋜⋞"],
    //["leqn", "≮  ≰≨≴⋦≸⊀ ⋨⊄⊈⊊  ⋢⋤ ⋪⋬   ⋠"],
    //["geq", ">≫⋙≥≧≳ ≷≻≽≿⊃⊇ ⋑⊐⊒ ⊱⊳⊵⋗⋛⋝⋟"],
    //["geqn", "≯  ≱≩≵⋧≹⊁ ⋩⊅⊉⊋  ⋣⋥ ⋫⋭   ⋡"],
    ["<=", "≤"],
    [">=", "≥"],
    ["<=n", "≰"],
    [">=n", "≱"],
    ["le", "≤"],
    ["ge", "≥"],
    ["len", "≰"],
    ["gen", "≱"],
    ["<n", "≮"],
    [">n", "≯"],
    ["<~", "≲"],
    [">~", "≳"],
    // ["<~n", "⋦"],
    // [">~n", "⋧"],
    // ["<~nn", "≴"],
    // [">~nn", "≵"],
    ["sub", "⊂"],
    ["sup", "⊃"],
    ["subn", "⊄"],
    ["supn", "⊅"],
    ["sub=", "⊆"],
    ["sup=", "⊇"],
    ["sub=n", "⊈"],
    ["sup=n", "⊉"],
    // ["squb", "⊏"],
    // ["squp", "⊐"],
    // ["squb=", "⊑"],
    // ["squp=", "⊒"],
    // ["squb=n", "⋢"],
    // ["squp=n", "⋣"],

    // Set membership etc.
    // ["member", "∈∉∊∋∌∍⋲⋳⋴⋵⋶⋷⋸⋹⋺⋻⋼⋽⋾⋿"],
    ["in", "∈"],
    ["inn", "∉"],
    ["ni", "∋"],
    ["nin", "∌"],

    // Intersections, unions etc.
    // ["intersection", "∩⋂∧⋀⋏⨇⊓⨅⋒∏ ⊼      ⨉"],
    // ["union", "∪⋃∨⋁⋎⨈⊔⨆⋓∐⨿⊽⊻⊍⨃⊎⨄⊌∑⅀"],

    ["and", "∧"],
    ["or", "∨"],
    ["And", "⋀"],
    ["Or", "⋁"],
    // ["i", "∩"],
    // ["un", "∪"],
    // ["u+", "⊎"],
    // ["u.", "⊍"],
    // ["I", "⋂"],
    // ["Un", "⋃"],
    // ["U+", "⨄"],
    // ["U.", "⨃"],
    ["glb", "⊓"],
    ["lub", "⊔"],
    // ["Glb", "⨅"],
    // ["Lub", "⨆"],

    // Entailment etc.
    // ["entails", "⊢⊣⊤⊥⊦⊧⊨⊩⊪⊫⊬⊭⊮⊯"],
    ["|-", "⊢"],
    ["vdash", "⊢"],
    // ["|-n", "⊬"],
    // ["-|", "⊣"],
    // ["|=", "⊨"],
    // ["|=n", "⊭"],
    // ["||-", "⊩"],
    // ["||-n", "⊮"],
    // ["||=", "⊫"],
    // ["||=n", "⊯"],
    // ["|||-", "⊪"],

    // Divisibility, parallelity.
    ["|", "∣"],
    ["|n", "∤"],
    ["||", "∥"],
    ["||n", "∦"],

    // Some symbols from logic and set theory.
    ["all", "∀"],
    ["ex", "∃"],
    ["exn", "∄"],
    ["0", "∅"],
    ["C", "∁"],

    // Corners, ceilings and floors.
    // ["c", "⌜⌝⌞⌟⌈⌉⌊⌋"],
    // ["cu", "⌜⌝  ⌈⌉  "],
    // ["cl", "  ⌞⌟  ⌊⌋"],
    // ["cul", "⌜"],
    ["cuL", "⌈"],
    // ["cur", "⌝"],
    ["cuR", "⌉"],
    // ["cll", "⌞"],
    ["clL", "⌊"],
    // ["clr", "⌟"],
    ["clR", "⌋"],

    // Various operators/symbols.
    ["qed", "∎"],
    ["x", "×"],
    ["o", "∘"],
    ["comp", "∘"],
    [".", "∙"],
    ["*", "⋆"],
    // [".+", "∔"],
    // [".-", "∸"],
    // [":", "∶⦂ː꞉˸፥፦：﹕︓"],
    // [",", "ʻ،⸲⸴⹁⹉、︐︑﹐﹑，､"],
    // [";", "؛⁏፤꛶；︔﹔⍮⸵;"],
    ["::", "∷"],
    // ["::-", "∺"],
    // ["-:", "∹"],
    // ["+ ", "⊹"],
    // ["surd3", "∛"],
    // ["surd4", "∜"],
    // ["increment", "∆"],
    ["inf", "∞"],
    // ["&", "⅋"],
    ["top", "⊤"],
    ["bot", "⊥"],
    ["neg", "¬"],

    // Circled operators.
    // ["o+", "⊕"],
    // ["o--", "⊖"],
    // ["ox", "⊗"],
    // ["o/", "⊘"],
    // ["o.", "⊙"],
    // ["oo", "⊚"],
    // ["o*", "⊛"],
    // ["o=", "⊜"],
    // ["o-", "⊝"],
    // ["O+", "⨁"],
    // ["Ox", "⨂"],
    // ["O.", "⨀"],
    // ["O*", "⍟"],

    // Boxed operators.
    // ["b+", "⊞"],
    // ["b-", "⊟"],
    // ["bx", "⊠"],
    // ["b.", "⊡"],

    // Various symbols.
    // ["integral", "∫∬∭∮∯∰∱∲∳"],
    // ["angle", "∟∡∢⊾⊿"],
    // ["join", "⋈⋉⋊⋋⋌⨝⟕⟖⟗"],

    // Arrows.
    // ["l", "←⇐⇚⇇⇆↤⇦↞↼↽⇠⇺↜⇽⟵⟸↚⇍⇷ ↹     ↢↩↫⇋⇜⇤⟻⟽⤆↶↺⟲ "],
    // ["r", "→⇒⇛⇉⇄↦⇨↠⇀⇁⇢⇻↝⇾⟶⟹↛⇏⇸⇶ ↴    ↣↪↬⇌⇝⇥⟼⟾⤇↷↻⟳⇰⇴⟴⟿ ➵➸➙➔➛➜➝➞➟➠➡➢➣➤➧➨➩➪➫➬➭➮➯➱➲➳➺➻➼➽➾⊸"],
    // ["u", "↑⇑⟰⇈⇅↥⇧↟↿↾⇡⇞          ↰↱➦ ⇪⇫⇬⇭⇮⇯                                           "],
    // ["d", "↓⇓⟱⇊⇵↧⇩↡⇃⇂⇣⇟         ↵↲↳➥ ↯                                                "],
    // ["ud", "↕⇕   ↨⇳                                                                    "],
    // ["lr", "↔⇔         ⇼↭⇿⟷⟺↮⇎⇹                                                        "],
    // ["ul", "↖⇖                        ⇱↸                                               "],
    // ["ur", "↗⇗                                         ➶➹➚                             "],
    // ["dr", "↘⇘                        ⇲                ➴➷➘                             "],
    // ["dl", "↙⇙                                                                         "],
    ["l-", "←"],
    ["<-", "←"],
    ["l=", "⇐"],
    ["r-", "→"],
    ["->", "→"],
    ["r=", "⇒"],
    ["=>", "⇒"],
    // ["u-", "↑"], ["u=", "⇑"],
    // ["d-", "↓"], ["d=", "⇓"],
    // ["ud-", "↕"], ["ud=", "⇕"],
    ["lr-", "↔"],
    ["<->", "↔"],
    // ["lr=", "⇔"],
    ["<=>", "⇔"],
    // ["ul-", "↖"], ["ul=", "⇖"],
    // ["ur-", "↗"], ["ur=", "⇗"],
    // ["dr-", "↘"], ["dr=", "⇘"],
    // ["dl-", "↙"], ["dl=", "⇙"],

    // ["l==", "⇚"],
    // ["l-2", "⇇"],
    ["l-r-", "⇆"],
    // ["r==", "⇛"],
    // ["r-2", "⇉"],
    // ["r-3", "⇶"],
    // ["r-l-", "⇄"],
    // ["u==", "⟰"],
    // ["u-2", "⇈"],
    // ["u-d-", "⇅"],
    // ["d==", "⟱"],
    // ["d-2", "⇊"],
    // ["d-u-", "⇵"],

    // ["l--", "⟵"],
    // ["<--", "⟵"],
    // ["l~", "↜⇜"],
    // ["r--", "⟶"],
    // ["-->", "⟶"],
    // ["r~", "↝⇝⟿"],
    // ["lr--", "⟷"],
    // ["<-->", "⟷"],
    // ["lr~", "↭"],

    // ["l-n", "↚"],
    // ["<-n", "↚"],
    // ["l=n", "⇍"],
    // ["r-n", "↛"],
    // ["->n", "↛"],
    // ["r=n", "⇏"],
    // ["=>n", "⇏"],
    // ["lr-n", "↮"],
    // ["<->n", "↮"],
    // ["lr=n", "⇎"],
    // ["<=>n", "⇎"],

    // ["l-|", "↤"],
    // ["ll-", "↞"],
    ["r-|", "↦"],
    ["mapsto", "↦"],
    // ["rr-", "↠"],
    // ["u-|", "↥"],
    // ["uu-", "↟"],
    // ["d-|", "↧"],
    // ["dd-", "↡"],
    // ["ud-|", "↨"],

    // ["l->", "↢"],
    // ["r->", "↣"],

    // ["r-o", "⊸"],
    // ["-o", "⊸"],

    // ["dz", "↯"],

    // Ellipsis.
    ["...", "⋯⋮⋰⋱"],

    // Blackboard bold letters.
    ["bC", "ℂ"],
    ["bH", "ℍ"],
    ["bN", "ℕ"],
    ["bP", "ℙ"],
    ["bQ", "ℚ"],
    ["bR", "ℝ"],
    ["bZ", "ℤ"],

    // Parentheses.
    //["(", "([{⁅⁽₍〈⎴⟅⟦⟨⟪⦃〈《「『【〔〖〚︵︷︹︻︽︿﹁﹃﹙﹛﹝（［｛｢"],
    //[")", ")]}⁆⁾₎〉⎵⟆⟧⟩⟫⦄〉》」』】〕〗〛︶︸︺︼︾﹀﹂﹄﹚﹜﹞）］｝｣"],
    ["[[", "⟦"],
    ["]]", "⟧"],
    ["<", "⟨"],
    [">", "⟩"],
    ["<<", "⟪"],
    [">>", "⟫"],
    ["{{", "⦃"],
    ["}}", "⦄"],

    // ["(b", "⟅"],
    // [")b", "⟆"],
    // ["lbag", "⟅"],
    // ["rbag", "⟆"],
    // ["(|", "⦇"], // Idiom brackets
    // ["|)", "⦈"],
    // ["((", "⦅"], // Banana brackets
    // ["))", "⦆"],

    // Primes.
    ["'", "′″‴⁗"],
    ["'1", "′"],
    ["`", "‵‶‷"],

    // Fractions.
    // ["frac", "¼½¾⅓⅔⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞⅟"],

    // Bullets.
    // ["bu", "•◦‣⁌⁍"],
    // ["bub", "•"],
    // ["buw", "◦"],
    // ["but", "‣"],

    // Musical symbols.
    // ["note", "♩♪♫♬"],
    ["b", "♭"],
    ["#", "♯"],

    // Other punctuation and symbols.
    ["\\", "\\"],
    // ["en", "–"],
    // ["em", "—"],
    // ["!!", "‼"],
    // ["??", "⁇"],
    // ["?!", "‽⁈"],
    // ["!?", "⁉"],

    // Shorter forms of many greek letters plus ƛ.
    ["Ga", "α"], ["GA", "Α"],
    ["Gb", "β"], ["GB", "Β"],
    ["Gg", "γ"], ["GG", "Γ"],
    ["Gd", "δ"], ["GD", "Δ"],
    ["Ge", "ε"], ["GE", "Ε"],
    ["Gz", "ζ"], ["GZ", "Ζ"],
    ["eta", "η"],
    ["Gth", "θ"], ["GTH", "Θ"],
    ["Gi", "ι"], ["GI", "Ι"],
    ["Gk", "κ"], ["GK", "Κ"],
    ["Gl", "λ"], ["GL", "Λ"], ["Gl-", "ƛ"],
    ["Gm", "μ"], ["GM", "Μ"],
    ["Gn", "ν"], ["GN", "Ν"],
    ["pi", "π"], ["Pi", "Π"],
    ["varphi", "φ"], ["Phi", "Φ"],
    ["phi", "ϕ"], ["Varphi", "Φ"],
    ["Gx", "ξ"], ["GX", "Ξ"],
    ["Gr", "ρ"], ["GR", "Ρ"],
    ["Gs", "σ"], ["GS", "Σ"],
    ["Gt", "τ"], ["GT", "Τ"],
    ["Gu", "υ"], ["GU", "Υ"],
    ["Gf", "φ"], ["GF", "Φ"],
    ["Gc", "χ"], ["GC", "Χ"],
    ["Gp", "ψ"], ["GP", "Ψ"],
    ["Go", "ω"], ["GO", "Ω"],

    // (Sub / Super) scripts
    ["_0", "₀"], ["_1", "₁"], ["_2", "₂"], ["_3", "₃"], ["_4", "₄"],
    ["_5", "₅"], ["_6", "₆"], ["_7", "₇"], ["_8", "₈"], ["_9", "₉"],

    ["_a", "ₐ"], ["_e", "ₑ"], ["_h", "ₕ"], ["_i", "ᵢ"], ["_j", "ⱼ"],
    ["_k", "ₖ"], ["_l", "ₗ"], ["_m", "ₘ"], ["_n", "ₙ"], ["_o", "ₒ"],
    ["_p", "ₚ"], ["_r", "ᵣ"], ["_s", "ₛ"], ["_t", "ₜ"], ["_u", "ᵤ"],
    ["_x", "ₓ"],

    ["^0", "⁰"], ["^1", "¹"], ["^2", "²"], ["^3", "³"], ["^4", "⁴"],
    ["^5", "⁵"], ["^6", "⁶"], ["^7", "⁷"], ["^8", "⁸"], ["^9", "⁹"],

    ["^a", "ᵃ"], ["^b", "ᵇ"], ["^c", "ᶜ"], ["^d", "ᵈ"], ["^e", "ᵉ"],
    ["^f", "ᶠ"], ["^g", "ᵍ"], ["^h", "ʰ"], ["^i", "ⁱ"], ["^j", "ʲ"],
    ["^k", "ᵏ"], ["^l", "ˡ"], ["^m", "ᵐ"], ["^n", "ⁿ"], ["^o", "ᵒ"],
    ["^p", "ᵖ"], ["^r", "ʳ"], ["^s", "ˢ"], ["^t", "ᵗ"], ["^u", "ᵘ"],
    ["^v", "ᵛ"], ["^w", "ʷ"], ["^x", "ˣ"], ["^y", "ʸ"], ["^z", "ᶻ"],

    ["^A", "ᴬ"], ["^B", "ᴮ"], ["^D", "ᴰ"], ["^E", "ᴱ"], ["^G", "ᴳ"],
    ["^H", "ᴴ"], ["^I", "ᴵ"], ["^J", "ᴶ"], ["^K", "ᴷ"], ["^L", "ᴸ"],
    ["^M", "ᴹ"], ["^N", "ᴺ"], ["^O", "ᴼ"], ["^P", "ᴾ"], ["^R", "ᴿ"],
    ["^T", "ᵀ"], ["^U", "ᵁ"], ["^V", "ⱽ"], ["^W", "ᵂ"],
  ]);

  // Returns CodeMirror hint function.
  const createHint = table => (editor, _options) => {
    const to = editor.getCursor();
    const str = editor.getLine(to.line).slice(0, to.ch);
    const from = { line: to.line, ch: str.lastIndexOf("\\") };

    const combo = editor.getRange(from, to);
    const list = table.filter(o => o.text.startsWith(combo));
    return { list: list, from: from, to: to };
  };

  console.info("agda-input: registering agda-input hint helper");

  CodeMirror.registerGlobalHelper(
    "hint",
    "agda-input",
    // only enable in agda mode for now
    (mode, cm) => mode && mode.name === "agda",
    createHint(translations)
  );

}));

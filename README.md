# pyfoma-js

Standalone JavaScript port of [Pyfoma](https://github.com/mhulden/pyfoma).

This is a packaged (and slightly enhanced) version of the code from
the Foma website, originally written by Mans Hulden and found at
https://github.com/fomafst/fomafst.github.io/blob/master/pyfomajs/pyfoma.js


## Installation

    npm install pyfoma-js

## Usage

You can use this directly from JavaScript or from TypeScript.  When
you install from npm you will get an ES6 module in
`node_modules/pyfoma-js/dist/index.js` which you could simply import
in your code, for example:

```html
<script type="module">
  import { FST } from "./node_modules/pyfoma-js/dist/index.js";
  const fst = FST.regex("(cat):(dog|fox|wolf|sea lion|octopus)");
  for (const dog of fst.generate("cat")) {
     document.body.innerHTML += `<p>${dog}</p>`;
  }
</script>
```

Of course, you can put it anywhere you like, or also use something
like [Vite](https://vite.dev) to bundle it with your own JavaScript
code, which has the advantage of only including functions and methods
you actually use (the kids call this "tree-shaking").

If you need to directly support older browsers then you'll have to use
[Babel](https://babeljs.io/docs/usage) or whatever the latest trendy
tool is, perhaps [SWC](https://swc.rs/) or
[Oxc](https://oxc.rs/docs/guide/usage/transformer/lowering.html).

## Demo site

The original demo site code from https://fomafst.github.io/pyfomajs/
is included here as an example of using `pyfoma-js` in a web
application.  To run it locally, run:

```
npm install
npm run demo
```

## API

The interface is largely similar to the [Python
library](https://mhulden.github.io/pyfoma/), with the same friendly
regular expression syntax for rules, but some limitations.

Notably, the `rlg` method for creating lexicons is not supported, but
the [`lexd`
formalism](https://github.com/mhulden/pyfoma/blob/main/docs/examples/lexd-intro.ipynb)
is, and you will probably be happier using that anyway.

See the [reference
documentation](https://dhdaines.github.io/pyfoma-js/doc) for more
information.

# Espree

Espree started out as a fork of [Esprima](http://esprima.org) v1.2.2, the last stable published released of Esprima before work on ECMAScript 6 began. Espree is now built on top of [Acorn](https://github.com/marijnh/acorn), which has a modular architecture that allows extension of core functionality. The goal of Espree is to produce output that is similar to Esprima with a similar API so that it can be used in place of Esprima.

## Usage

Install:

```
npm i espree --save
```

And in your Node.js code:

```javascript
var espree = require("espree");

var ast = espree.parse(code);
```

There is a second argument to `parse()` that allows you to specify various options:

```javascript
var espree = require("espree");

var ast = espree.parse(code, {

    // attach range information to each node
    range: true,

    // attach line/column location information to each node
    loc: true,

    // create a top-level comments array containing all comments
    comments: true,

    // attach comments to the closest relevant node as leadingComments and
    // trailingComments
    attachComment: true,

    // create a top-level tokens array containing all tokens
    tokens: true,

    // try to continue parsing if an error is encountered, store errors in a
    // top-level errors array
    tolerant: true,

    // specify parsing features (default only has blockBindings: true)
    // setting this option replaces the default values
    ecmaFeatures: {

        // enable parsing of arrow functions
        arrowFunctions: true,

        // enable parsing of let/const
        blockBindings: true,

        // enable parsing of destructured arrays and objects
        destructuring: true,

        // enable parsing of regular expression y flag
        regexYFlag: true,

        // enable parsing of regular expression u flag
        regexUFlag: true,

        // enable parsing of template strings
        templateStrings: true,

        // enable parsing of binary literals
        binaryLiterals: true,

        // enable parsing of ES6 octal literals
        octalLiterals: true,

        // enable parsing unicode code point escape sequences
        unicodeCodePointEscapes: true,

        // enable parsing of default parameters
        defaultParams: true,

        // enable parsing of rest parameters
        restParams: true,

        // enable parsing of for-of statement
        forOf: true,

        // enable parsing computed object literal properties
        objectLiteralComputedProperties: true,

        // enable parsing of shorthand object literal methods
        objectLiteralShorthandMethods: true,

        // enable parsing of shorthand object literal properties
        objectLiteralShorthandProperties: true,

        // Allow duplicate object literal properties (except '__proto__')
        objectLiteralDuplicateProperties: true,

        // enable parsing of generators/yield
        generators: true,

        // enable parsing spread operator
        spread: true,

        // enable parsing classes
        classes: true,

        // enable parsing of new.target
        newTarget: true,

        // enable parsing of modules
        modules: true,

        // enable React JSX parsing
        jsx: true,

        // enable return in global scope
        globalReturn: true,

        // allow experimental object rest/spread
        experimentalObjectRestSpread: true
    }
});
```

## Esprima Compatibility Going Forward

The primary goal is to produce the exact same AST structure and tokens as Esprima, and that takes precedence over anything else. (The AST structure being the [ESTree](https://github.com/estree/estree) API with JSX extensions.) Separate from that, Espree may deviate from what Esprima outputs in terms of where and how comments are attached, as well as what additional information is available on AST nodes. That is to say, Espree may add more things to the AST nodes than Esprima does but the overall AST structure produced will be the same.

Espree may also deviate from Esprima in the interface it exposes.

## Contributing

Issues and pull requests will be triaged and responded to as quickly as possible. We operate under the [ESLint Contributor Guidelines](http://eslint.org/docs/developer-guide/contributing), so please be sure to read them before contributing. If you're not sure where to dig in, check out the [issues](https://github.com/eslint/espree/issues).

Espree is licensed under a permissive BSD 2-clause license.

## Build Commands

* `npm test` - run all linting and tests
* `npm run lint` - run all linting
* `npm run browserify` - creates a version of Espree that is usable in a browser

## Known Incompatibilities

In an effort to help those wanting to transition from other parsers to Espree, the following is a list of noteworthy incompatibilities with other parsers. These are known differences that we do not intend to change.

### Esprima 1.2.2

* None.

### Esprima 2.x

* Esprima/Harmony uses a different comment attachment algorithm that results in some comments being added in different places than Espree. The algorithm Espree uses is the same one used in Esprima 1.2.2.

## Frequently Asked Questions

### Why are you forking Esprima?

[ESLint](http://eslint.org) has been relying on Esprima as its parser from the beginning. While that was fine when the JavaScript language was evolving slowly, the pace of development has increased dramatically and Esprima has fallen behind. ESLint, like many other tools reliant on Esprima, has been stuck in using new JavaScript language features until Esprima updates, and that has caused our users frustration.

We decided the only way for us to move forward was to create our own parser, bringing us inline with JSHint and JSLint, and allowing us to keep implementing new features as we need them. We chose to fork Esprima instead of starting from scratch in order to move as quickly as possible with a compatible API.

### Have you tried working with Esprima?

Yes. Since the start of ESLint, we've regularly filed bugs and feature requests with Esprima. Unfortunately, we've been unable to make much progress towards getting our needs addressed.

We are actively working with Esprima as part of its adoption by the jQuery Foundation. We are hoping to reconcile Espree with Esprima at some point in the future, but there are some different philosophies around how the projects work that need to be worked through. We're committed to a goal of merging Espree back into Esprima, or at the very least, to have Espree track Esprima as an upstream target so there's no duplication of effort. In the meantime, we will continue to update and maintain Espree.

### Why don't you just use Facebook's Esprima fork?

`esprima-fb` is Facebook's Esprima fork that features JSX and Flow type annotations. This fork is no longer maintained.

### Why don't you just use Acorn?

Acorn is a great JavaScript parser that produces an AST that is compatible with Esprima. Unfortunately, ESLint relies on more than just the AST to do its job. It relies on Esprima's tokens and comment attachment features to get a complete picture of the source code. We investigated switching to Acorn, but the inconsistencies between Esprima and Acorn created too much work for a project like ESLint.

We are building on top of Acorn, however, so that we can contribute back and help make Acorn even better.

### What ECMAScript 6 features do you support?

All of them.

### How do you determine which experimental features to support?

In general, we do not support experimental JavaScript features. We may make exceptions from time to time depending on the maturity of the features.

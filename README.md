# nanocaml
`nanocaml` is an implementation of [nanopass](http://nanopass.org/) for OCaml using a PPX preprocessor.

## What
Nanopass compilers are compilers that utilize many tiny "passes". Most modern compilers are built with a [handful of passes](https://gcc.gnu.org/onlinedocs/gccint/Passes.html), but nanopass compilers take this to the extreme.

The Nanopass Framework is a toolkit available for Scheme/Racket as a domain specific language aimed at writing nanopass compilers. This framework automates much of the boilerplate involved in writing the various ASTs and functions involved in a compiler's passes. `nanocaml` makes all of this available in OCaml.

## Why
Nanopass compilers have proven to be extremely easy to design and extend. Being that OCaml is already a great language for writing compilers (with tools like OCamllex/OCamlyacc built-in to the standard distribution), `nanocaml` is just the cherry on top for an already great set of tools for creating compilers.

Compared to other implementations of the Nanopass Framework, `nanocaml` allows compiler writers to utilize OCaml's static type system in order to typecheck passes without any testing. This increases the safety net for the programmer and enables a quicker workflow by eliminating the need to run the compiler and its test suite whenever incremental changes are made.

## How
`nanocaml` is designed as a simple OCaml preprocessor that takes advantage of many existing features in the language. A `nanocaml` language is defined using a module with the `%language` extension point, an `entry` type (the type of the whole AST) and a set of AST types composed of polymorphic variants. Passes are written using `let%pass` and return a record with the relevant AST processors (e.g. `expr : L0.expr -> L1.expr`). For examples of `nanocaml` compilers, see the `examples/` directory.

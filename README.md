# clojure-in-clojure

An experimental re-implementation of Clojure on Clojure.

## Status

- reader - feature complete
- compiler - work in progress (~ 50%)

## Why?

At the moment this project is mostly an excuse to write a non-trivial
amount of Clojure and to gain a better understanding of the current
Clojure implementation.

## How?

The current approach is to attempt a fairly direct translation of the
Java implementation of Clojure, in order to make it easier to spot
omissions or mistakes. Once everything works (and backed by extensive
tests) the code can be refactored to more idiomatic Clojure.

## License

Copyright (C) 2012 Cosmin Stejerean

Distributed under the Eclipse Public License, the same as Clojure.

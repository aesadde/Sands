# Sands Abstract  Machine

This is an incomplete implementation of Moran and Sands' abstract machine for
improvement theory in call-by-need semantics. The abstract machine and the
whole theory is described in their [1999
paper](http://dl.acm.org/citation.cfm?id=292547&dl=ACM&coll=DL&CFID=685253895&CFTOKEN=44765828).

The machine was implemented as part of some experiments I conducted while
working on my masters thesis. The machine is able to interpret a reduced set of
GHC Core (GHC's intermediate language).

## WARNING

The code is very disorganized and 'hacky'.
In particular, the generation of `uniq` ids for the Core names is done
manually. This needs to change if this is going to work in the future.

The interpreter completely ignore type annotations. A more powerful
implementation would need to be written to correctly handle types. We could use
the dead [GHC Core
interpreter](https://phabricator.haskell.org/rGHC6e93da5e0a775b2bfb9c9f2bd31a36cc828521cb)
as an example in order to make a better implementation of this abstract
machine.


## TODOS

* Move away from IO (a State monad is probably better in this case).
* Eliminate redundant code
* Move to GHC 8.0


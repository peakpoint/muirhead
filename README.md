# Muirhead's Inequality in Lean

Proving Muirhead's inequality via Birkhoff's theorem.

## Implementation Details

* `matrix.support` is the non-zero entries of a matrix.
Previously, I tried `finset.filter` but now I using `finsupp`.

## TODO:

* make `matrix/doubly_stochastic/birkhoff.lean` and prove Birkhoff's theorem using Hall
* make `ineq/majorize.lean` and define majorization
* make `ineq/muirhead.lean`

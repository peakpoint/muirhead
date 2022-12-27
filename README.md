# Muirhead's Inequality in Lean

Proving Muirhead's inequality via Birkhoff's theorem.

## Implementation Details

* `matrix.support` is the non-zero entries of a matrix.
Previously, I tried `finset.filter` but now I using `finsupp`.

* `matrix.doubly_stochastic.mem_convex_hull` is Birkhoff's theorem.
Every doubly stochastic matrix is in the convex hull of the permutation matrices.

## TODO:

* prove some variations (reverse direction)?
* make `ineq/majorize.lean` and define majorization
* make `ineq/muirhead.lean`

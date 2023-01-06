# Muirhead's Inequality in Lean

Proving Muirhead's inequality via Birkhoff's theorem.

## Implementation Details

* `matrix.support` is the non-zero entries of a matrix.
Previously, I tried `finset.filter` but now I using `finsupp`.

* `matrix.doubly_stochastic.mem_convex_hull` is Birkhoff's theorem.
Every doubly stochastic matrix is in the convex hull of the permutation matrices.

* `majorize.exists_doubly_stochastic` states that if `p` majorizes `q`,
then there exists doubly stochastic `M` such that `q = M p`.

## TODO:

* prove some variations?
* reverse directions?
* make `ineq/muirhead.lean`

## References/Helpful Notes

* <https://www.math.hkust.edu.hk/excalibur/v11_n1_20161130.pdf>

* <https://web.archive.org/web/20170706160002/http://imomath.com/index.php?options=596&lmm=0>

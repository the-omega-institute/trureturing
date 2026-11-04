---
slug: ma2013-dsspectral
bibkey: mourad2013spectra
doi: 10.48550/arXiv.1310.1273
url: https://arxiv.org/abs/1310.1273v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/MouradAbbasC51Refutation
---

# Mourad–Abbas Conjecture 5.1 is false

## Problem

Bassam Mourad and Hassan Abbas, *On the symmetric doubly stochastic matrices
that are determined by their spectra*, arXiv:1310.1273v1, printed page 10,
Conjecture 5.1:

> For $0<a\leq n$, the only elements of $\Delta_n^s(a)$ that are DS in
> $\Delta_n^s$ are points on the line segments $[I_n,C_n]$, $[I_n,P]$ and
> $[C_n,P]$ where $P$ is a vertex of $\Delta_n^s$.

Here $\Delta_n^s$ is the full polytope of real symmetric nonnegative matrices
with every row and column sum equal to one, and $\Delta_n^s(a)$ is its
trace-$a$ slice. A matrix is DS if every similar member of that full polytope
is permutationally similar to it. Similarity means conjugation by an arbitrary
invertible real matrix. All segments include their endpoints.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Real matrices of order $n\geq2$ | `Matrix (Fin n) (Fin n) ℝ`, order binder in `claim` | Unrestricted real entries; order bound makes $C_n$ meaningful. |
| Symmetric doubly stochastic matrices | `DeltaSymm`, using `doublyStochastic` and `Matrix.IsSymm` | Full polytope, with nonnegativity and both stochastic sums. |
| Trace $a$, $0<a\leq n$ | `traceSlice` and the real bounds in `claim` | No restriction to the constructed family. |
| $C_n$ | `C` | Zero diagonal, off-diagonal $1/(n-1)$, with real subtraction. |
| Permutation similarity | `IsPermutationallySimilar` | One permutation with $B=P^TAP$. |
| Every similar symmetric doubly stochastic $B$ | `IsDS`, using `IsConj` | All real $B$ of the same order, with no orthogonality or irreducibility assumption. |
| Only points of the three segment types | Conclusion of `claim`, using `segment ℝ` | Necessary condition; no converse is added. |
| $P$ is a vertex of $\Delta_n^s$ | `(DeltaSymm n).extremePoints ℝ` | Extreme point of the full polytope, rather than the trace slice. |

The source conventions use existing Matrix, stochasticity, symmetry,
conjugation, permutation-matrix, segment and extreme-point owners directly.
The six public definitions retain their source expressions; family
constructions and proof helpers are private.

## Motivation

The positive-trace restriction does not eliminate reducible spectrally
determined matrices. Equal blocks yield counterexamples in unbounded orders
and through an interval of real parameters. The external named problem is
preregistered in [#21726](https://github.com/the-omega-institute/trureturing/issues/21726).
The settling declaration has admission basis
`open-problem-resolution (#21726; Refuted)` and conservatively carries
`proof_shape: bind-only` after expansion of its helpers.

## Gap

The bounded literature screen recorded in #21726 found no proof or refutation
in the source and the inspected passages of nine related arXiv texts, Flor's
nonnegative-idempotent classification, and the inspected accepted manuscript
at DOI 10.1016/j.laa.2019.01.017. Flor's classification is established
background, not a new classification claim. Metadata and search-result
absence are not proofs of priority. The published journal version at DOI
10.1080/03081087.2014.903590 and several later full texts were inaccessible;
some citation services were rate limited and some broader searches were
limited to their first page. Literature completeness is
`ASSUMED-UNVERIFIED`.

## Route

For integers $k\geq4$, $r\geq2$, and real $0<t<1/k^2$, set $N=rk$ and
$\lambda=(kt-1)/(k-1)$. Take $r$ diagonal blocks of size $k$, each with
diagonal $t$ and off-diagonal $(1-t)/(k-1)$, with zero cross-block entries.
Equivalently, $A=\lambda I_N+(1-\lambda)\bigoplus_{j=1}^r J_k$.

For every similar $B\in\Delta_N^s$, its affine shift
$E=(B-\lambda I_N)/(1-\lambda)$ is a symmetric nonnegative stochastic
idempotent with trace $r$. Summing weighted squared row differences gives
$\sum_{i,j}E_{ij}(E_{j\ell}-E_{i\ell})^2=0$ for each column $\ell$.
Nonnegativity forces equal rows whenever $E_{ij}>0$. Each positive-support
class is uniform. The inequality $1+k\lambda<0$ bounds each support size
by $k$, and the trace and total dimension force every size to equal $k$.
The quotient and its fibers assemble a single permutation, proving DS.

A cross-block zero excludes $[I_N,C_N]$ and forces the $A=P$ endpoint of
any $[C_N,P]$ representation. Four distinct vertices within a block give a
nonzero symmetric four-cycle perturbation with zero row and column sums.
It proves that $A$ is not extreme, and that every possible $P$ on an
identity ray through $A$ is not extreme. Thus none of the proposed segments
contains $A$. The settling result selects $k=4$, $r=2$, $t=1/40$, giving
order eight and trace $1/5$.

## Falsifier

A matrix in this family satisfying one of the conjectured closed-segment
alternatives under the stated strict bounds would contradict the family
exclusions. A proof of the unchanged universal `claim` would contradict
`result : ¬ claim`. Computed boundary examples do not satisfy the strict
upper bound and are outside the family theorem's hypotheses.

## Evidence

The Lean module is `D5/S0/Certificates/MouradAbbasC51Refutation.lean`.
Its single public theorem is `result : ¬ claim`; the general mechanism is
proved by its private helpers on that theorem's proof path. The axiom
closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.

The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).
No other new public theorem or published owner declaration is delivered.

### Exact computation

Experiment: [mourad-abbas-c51 at immutable revision
10e7685b6ec8d6cb777ff4900b831634de180820](https://github.com/the-omega-institute/trureturing-experiments/tree/10e7685b6ec8d6cb777ff4900b831634de180820/docs/reports/mourad-abbas-c51).
The pinned program is `docs/reports/mourad-abbas-c51/check.py`, SHA-256
`63271ba871f6df28a09775beea24e0527fde677a5025e6c8041fa234bd3a828a`.
Its bytes were checked against that revision. Command:
`python3 docs/reports/mourad-abbas-c51/check.py` from the experiments clone,
exit 0. The script checks 25 rational family instances: $k=4,5,6,7$,
$r=2,3$, $t=j/(4k^2)$ for $j=1,2,3$, plus $(k,r,t)=(4,2,1/40)$.
It also checks the three boundary instances $k=4,5,6$ at $t=1/k^2$ and the
exact characteristic polynomial of the nominated order-eight matrix.
These computations do not prove universal spectral determination.

## Triage

`theorem`: Conjecture 5.1 is refuted by `result`. The following items have
separate evidence kinds and scopes.

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved, kernel-checked private `positive_edge_rows_equal`, `uniform_projection`, `partition_coordinates`, `similar_family_rigidity` | The affine shift of every similar symmetric doubly stochastic mate is a stochastic idempotent; positive-support row equality, support size and trace force equal $k$-blocks and one aligning permutation. |
| Extent | Proved, kernel-checked private `family_isDS`, `family_exclusion`, `family_trace_slice` | Arbitrary integers $k\geq4$, $r\geq2$ and every real $0<t<1/k^2$, in unbounded orders $rk$; not merely the selected order-eight instance. |
| Segment obstruction | Proved, kernel-checked private `four_cycle_not_extreme`, `segment_exclusion`, `family_exclusion` | A cross-block zero excludes mixtures with $C_N$ except the endpoint. Four-cycle perturbations make $A$ and every possible identity-ray vertex nonextreme. All closed-segment endpoints are covered. |
| Boundary control | Computed, the exact experiment above, exit 0 and the stated SHA-256 | At $t=1/k^2$ for exactly $k=4,5,6$, blocks of sizes $k-1,k+1$ give actual non-permutation-similar cospectral symmetric stochastic mates. A uniform boundary theorem is open here. |
| Concrete spectrum | Computed, the exact experiment above, exit 0 and the stated SHA-256 | The nominated $N=8$ matrix has characteristic polynomial $(x-1)^2(x+3/10)^6$. Lean uses affine idempotence and unit conjugation; no newly formalized characteristic-polynomial computation is claimed. |
| Surviving neighbours | Open; source and bounded literature reading | Whether irreducibility repairs the conjecture is unresolved. The source's order-three classification and its two other final-section questions are neither settled nor contradicted. |

The source's established segment and direct-sum statements and its
order-three classification remain intact. Its conjecture appears after
those results, so no earlier theorem uses it as a proved premise. For
$k=2$ or $3$, the four-distinct-vertices perturbation used here is unavailable;
no refutation by this mechanism is asserted in those sizes. Removing this
reducible family by imposing irreducibility supplies no proof of the repaired
conjecture.

## ASSUMED-UNVERIFIED

Literature completeness, settlement priority and equivalence with any
unread changes in the published journal article remain
`ASSUMED-UNVERIFIED`. The finite boundary checks do not settle all $k$;
irreducible spectral determination and the source's other questions remain
open. No empirical or exhaustive-literature claim follows from Lean's
verification of the encoded arXiv-v1 assertion.

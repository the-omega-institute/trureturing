---
slug: blecher-2025-example-5-5-no-anticommuting-pair
bibkey: blecher2025commutativity
doi: 10.1016/j.exmath.2025.125742
url: https://arxiv.org/abs/2509.17673v2
triage: theorem
motivation_gids:
  - D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result
---

# Blecher's question about a nonzero anticommuting product

## Problem

David P. Blecher, *Commutativity of operator algebras*, Example 5.5 asks for a noncommutative reversible operator algebra in which every pair satisfying $xy=-yx$ has $xy=0$. The source is arXiv v2, with the canonical repository citation at https://arxiv.org/abs/2509.17673v2 and the Example 5.5 locator at https://arxiv.org/html/2509.17673v2#S5.Thmtheorem5. The formal claim quantifies over a complex submodule $A$ of $M_{16}(\mathbb C)$, matrix-multiplication closure, a noncommuting pair, and equality of the entrywise-transpose Euclidean operator norm at every matrix level. It concludes that a pair with $xy=-yx$ and $xy\ne0$ exists.

### Statement echo

The Lean definition `D5.S3.HilbertOperators.BlecherNoAnticommutingPair.claim` has seven universal binders in the first three clauses and the norm clause. They are $A : \operatorname{Submodule}(\mathbb C,\operatorname{Matrix}(\operatorname{Fin}(16),\operatorname{Fin}(16),\mathbb C))$, $x$ and $y$ in the ambient matrix algebra, $k : \mathbb N$, and $x : \operatorname{Fin}(k)\to\operatorname{Fin}(k)\to\operatorname{Matrix}(\operatorname{Fin}(16),\operatorname{Fin}(16),\mathbb C)$ with indices $i,j : \operatorname{Fin}(k)$. The symmetric clause is exactly

$$\left\lVert \operatorname{Matrix.comp}(\operatorname{Fin}(k),\operatorname{Fin}(k),\operatorname{Fin}(16),\operatorname{Fin}(16),\mathbb C,\left(\lambda i\,j \mapsto (x\ i\ j)^\mathsf T\right))\right\rVert = \left\lVert \operatorname{Matrix.comp}(\operatorname{Fin}(k),\operatorname{Fin}(k),\operatorname{Fin}(16),\operatorname{Fin}(16),\mathbb C,x)\right\rVert.$$

The settling declaration is `D5.S3.HilbertOperators.BlecherNoAnticommutingPair.result : ¬ claim`. Its Blueprint display expands the negation over this full proposition through `ClaimBody()`.

## Motivation

Blecher's example shows a noncommutative reversible algebra with a nonzero anticommuting product. Example 5.5 asks whether the nonzero product is forced by noncommutativity and reversibility. A counterexample inside a finite matrix algebra settles the stated existence question at the requested operator-norm level.

The preregistration is [issue #35141](https://github.com/the-omega-institute/trureturing/issues/35141). Its stated source clause, the quantifier range $m\ge2$, the signed-probe construction, and the bounded literature screen are the conventions used by this delivery.

## Gap

The source question does not provide a construction with noncommutativity, reversibility, and zero product for every anticommuting pair. The formal gap is the existence of one closed submodule of $M_{16}(\mathbb C)$ satisfying the norm equalities while violating the final existential conclusion.

## Route

For the public refutation, take the $m=2$ member of the uniform construction. Represent $(r,Z)\in\mathbb C^{1\times m}\oplus M_m(\mathbb C)$ in $m^2$ blocks of size $m+2$. Each block uses a signed permutation probe $J$. Its top-middle row recovers $r$, diagonal probes recover the diagonal entries of $Z$, and unsigned and signed swap probes recover both entries of every off-diagonal pair. The representation is complex-linear, injective, and satisfies

$$\rho(r,Z)\rho(s,W)=\rho(0,r^{\mathsf T}s).$$

Two basis rows give a noncommuting pair. If $r^{\mathsf T}s=-(s^{\mathsf T}r)$, a nonzero coordinate of $r$ forces the corresponding coordinate of $s$ to vanish and then forces $s=0$, so the product is zero. For every probe, if $B$ is the block and $U$ its fixed signed permutation unitary, the identity is $U B^{\mathsf T} U=B$: the same unitary multiplies the transpose on the left and right. Their direct sum and its matrix-level block diagonals preserve the Euclidean operator norm, giving the exact amplification equality.

The uniform scope is every natural $m\ge2$, with ambient size $m^2(m+2)$. The public refutation scope is the single specialization $m=2$, with ambient size $16$. The public theorem consumes the uniform construction at that specialization and supplies the submodule range and closure witness required by `claim`.

## Falsifier

The refutation would fail if the four signed-probe readings did not separate every coordinate of $Z$, if the representation failed to be injective or multiplicative, if the two basis rows commuted, if an anticommuting pair in the image could have a nonzero product, or if the signed unitary failed to recover the transpose at some matrix level. Each condition is discharged on the live proof path of `result` through the private uniform construction.

The theorem does not assert minimal ambient dimension, symmetry for Blecher's original Example 5.5 family, or an embedding into a direct sum of commutative and anticommutative algebras.

## Evidence

`D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result` is the designated certified-instance refutation of `claim`. A scoped official-Mathlib build of the module completed with exit code 0. The measured axiom closure of its public declarations is contained in `{propext, Classical.choice, Quot.sound}`. The private uniform construction is the only additional mathematical scope consumed by the public theorem.

The Reg audit has no target. `result` is a utility refutation with `utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim; result=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result; claim=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim`, and the designated refutation result is exempt from the four-slot escape registration under CLAUDE.md §3.9. No Reg mirror is required for this module.

The source prerequisite is `Library/HilbertOperators/blecher2025commutativity.md`, whose DOI and URL are exactly `10.1016/j.exmath.2025.125742` and `https://arxiv.org/abs/2509.17673v2`. The measured immediate directory capacities are 20 Lean files in `D5/S3/HilbertOperators`, 40 Blueprint files in `Blueprint/D5/S3/HilbertOperators`, and 62 Library files in `Library/HilbertOperators`, each below the configured 96-entry limit.

The scoped Scribe source uses the real Lean objects `Submodule`, `Matrix`, `Fin`, `Matrix.comp`, and `Matrix.transpose`. The result node displays the complete proposition via `ClaimBody()`, including the exact entrywise-transpose norm equation above.

## Triage

| Item | Status | Evidence and scope |
| --- | --- | --- |
| Noncommutative image | proved | `faithfulCounterexample` supplies two image elements whose products differ. Public scope $m=2$; uniform construction scope $m\ge2$. |
| Multiplicative closure | proved | `representation_mul` gives the product $(r,Z)(s,W)=(0,r^{\mathsf T}s)$, and `result` turns the range into a closed submodule. Public scope $m=2$. |
| Every anticommuting image pair has zero product | proved | `outer_eq_neg_swapped` and the range argument in `faithfulCounterexample` establish the implication for all uniform $m\ge2$ and hence for $m=2$. |
| Amplified transpose norm equality | proved | `amplified_norm` uses the signed unitary identity at every natural level $k$, for every array whose entries lie in the image. The public claim uses the $m=2$ specialization. |
| Topological closedness of the image | proved in the finite-dimensional operator-space argument | The image is a finite-dimensional range and is closed. This property is used in the mathematical interpretation of the witness and is outside the public `claim` type. |
| Ambient-dimension minimality | open | No theorem or computation establishes that 16 is minimal. |
| Symmetry of Blecher's original Example 5.5 family | open | The result concerns the new signed-probe representation. |
| Embedding into a commutative/anticommutative direct sum | open | No such embedding statement is formalized. |
| Literature priority beyond the bounded screen in #35141 | ASSUMED-UNVERIFIED | The source and the recorded bounded search were checked. Completeness outside that screen is unverified. |

The public scope is exactly one refutation at $m=2$, ambient size $2^2(2+2)=16$. The uniform scope is the private construction for all $m\ge2$, ambient size $m^2(m+2)$, which is consumed by the public refutation only at $m=2$.

Per-declaration proof shapes and live consumers are recorded in the attempt-owned re-review artifact. The construction declarations that introduce the signed-probe representation and the transpose unitary are content. Coordinate, involution, readout, and matrix identities are bind-only helpers with named consumers on the live path. No bind-only helper is orphaned.

## ASSUMED-UNVERIFIED

Literature completeness and priority outside the bounded screen recorded in issue #35141 are ASSUMED-UNVERIFIED. Ambient-dimension minimality, properties of Blecher's original family, and the direct-sum embedding question remain outside the formal claim. The finite-dimensional closedness statement is an auxiliary interpretation of the range and is not part of `claim`.

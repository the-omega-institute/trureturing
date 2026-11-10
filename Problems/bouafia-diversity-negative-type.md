---
slug: bouafia-diversity-negative-type
bibkey: bouafia2026treemagnitude
doi: 10.48550/arXiv.2605.03681
url: https://arxiv.org/abs/2605.03681v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation
---

# Irreversible diversity-weight deletion on negative-type metrics

## Problem

Philippe Bouafia, *Magnitude and diversity of trees*, arXiv:2605.03681v1,
Section 4.1, p. 18, immediately after Theorem 4, asks:

> Does DiversityMaximizingMeasure correctly compute the maximizing-diversity measure of all finite subsets of ℝⁿ? Of all finite metric spaces of negative type?

This dossier settles only the second question, **Refuted**. The source's negative
type means that the square-root distance embeds isometrically into a Hilbert
space. The input is any nonempty finite metric space, with similarity
$Z_{ij}=e^{-d(i,j)}$. Algorithm 1 repeatedly solves on its retained support,
extends the weighting by zero, discards nonpositive weights if another solve
is necessary, and normalizes at the first nonnegative solve.

The printed stopping test is reversed relative to Theorem 4's proof. The
convention here is the proof's sentence: “At the end of the repeat loop, the
vector w is non-zero and non-negative.” The counterexample uses that intended
stop and does not exploit the printed test.

### Statement echo

| Source clause or domain condition | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every nonempty finite metric space | `claim`, positive `n` and arbitrary `MetricSpace (Fin n)` | Finite labeling; the empty space has no probability measure. |
| Square-root distance embeds isometrically into a Hilbert space | `NegativeType` | An injective distance-preserving map into some finite-dimensional real Hilbert space; the finite image spans such a space. |
| Exponential similarity | `similarity` | Scale-one exponential of negative distance. |
| Zero extension of the inverse solve | `weighting` | Literal principal `Matrix.submatrix` inverse times the constant-one vector. |
| Start with every point and retain strictly positive weights | `active` | Both recursion cases are explicit. |
| First nonnegative solve | `stopped`, `FirstStop` | No earlier stop; all visited supports nonempty and all visited principal determinants nonzero. |
| Return the normalized weighting | `mass`, `output` | `claim` requires positive normalization. |
| Minimum similarity energy over every original-space probability | `DiversityMaximizing` | Feasibility in `Convexity.StdSimplex` and the full double-sum comparison. |
| Algorithm correctly computes an output | `claim` | A first stop exists, and every first stop has positive mass and maximizing output. |
| Negative answer to the universal question | `result` | The negation of the complete `claim`. |

The explicit nonsingularity and existence conditions strengthen the specified
operational correctness obligation; the witness satisfies them. No source
hypothesis is replaced by a certificate predicate. The metric is a scaled
Hamming metric, without a claim that it is ordinary Euclidean distance.

## Motivation

The tree proof uses an entrywise sign for a conditional covariance matrix.
Negative type supplies a Hilbert embedding of the square-root metric but
need not supply that sign. Simultaneous deletion can remove a point whose
re-entry improves the eventual feasible probability.

## Gap

Preregistration [#25745](https://github.com/the-omega-institute/trureturing/issues/25745)
quotes the source and fixes the full finite-domain conventions. The source
Library note is `Library/Geometry/bouafia2026treemagnitude.md`.

The bounded literature screen in the preregistration reads Bouafia v1,
Kališnik–Lešnik arXiv:2609.26560 and Dajani arXiv:2610.38031 in their relevant
contexts. No settlement of the finite negative-type deletion question was
found in those sources. Huntsman, arXiv:2509.19565v3, Appendix G, supplies prior
art for the general deletion/re-entry mechanism; that mechanism is not a
novelty claim here. OpenAlex's citation enumeration and Semantic Scholar
were rate limited; the author's non-arXiv bibliography was inaccessible.
Bibliographic completeness is `ASSUMED-UNVERIFIED`.

## Route

Take binary vectors
$(0,0,0,0,0)$, $(1,1,0,0,1)$, $(0,0,1,0,1)$,
$(0,1,0,1,1)$ and $(0,0,1,1,1)$, indexed from zero.
Set $c=\log(20/19)$ and $d(i,j)=cH_{ij}$, where

$$
H=\begin{pmatrix}
0&3&2&3&3\\3&0&3&2&4\\2&3&0&3&1\\3&2&3&0&2\\3&4&1&2&0
\end{pmatrix}.
$$

The map $x_i\mapsto\sqrt c\,x_i$ preserves square-root distances, so this
is negative type. Similarity is $(19/20)^{H_{ij}}$. The first weighting has
signs $(+,+,-,-,+)$, leaving $A=\{0,1,4\}$. The second weighting is
$(3192200,4564000,0,0,4564000)/11018319$, has positive mass
$12320200/11018319$, and normalizes to

$$p=(15961,22820,0,0,22820)/61601.$$

Both solves are nonsingular. Put
$p'=(999/1000)p+(1/1000)e_3$. It is a probability and

$$p^TZp-p'^TZp'=\frac{1707687919}{246404000000000}>0.$$

## Falsifier

Correctness on every finite negative-type metric implies optimality of the
first-stop output for this five-point metric. `result` contradicts that
optimality using the explicit improving probability. No singular inverse,
zero denominator or failure to terminate supplies the contradiction.

## Evidence

The settling declaration is
`D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result`.
The module has ten public definitions and only this public theorem. Its
private certificates establish the embedding, both inverse identities,
first stop, output and strict energy gap. All have live consumers.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact computation

[Exact checker and evidence limits](https://github.com/the-omega-institute/trureturing-experiments/tree/4251681e070bcb815a745273efdbaf15b373c10c/docs/reports/bouafia-diversity-negative-type)
are pinned to experiments commit `4251681e070bcb815a745273efdbaf15b373c10c`.
The program is `docs/reports/bouafia-diversity-negative-type/check.py`,
SHA-256 `e5ecd757601c16502d86a31e5de5f69daf50eb98a196a8a5c265b77a0e3b9f22`.
Executing those pinned bytes with Python 3.14, command
`python3 /Users/auric/.sshx/ba2ebdaccf374164b538e24e/attempt-1/experiment-check.py`,
exits 0 with `ALL_CHECKS_OK`. It uses exact rational and symbolic arithmetic.
It checks the fixed rational witness and the family $19/20\le q<1$, including
signed Bernstein bounds on the closed interval, determinant formulas,
the two solve identities, the residual, Schur entry and scale-zero limits.
These computations do not constitute a uniform-family Lean theorem.

## Triage

1. **Kernel-checked fixed refutation.** `result` proves the universal assertion
   false. Its private `negative_type`, `inverse0`, `inverse1`, `first_stop`,
   `mass1`, `output1`, `energy_gap` and `not_maximizing` certify the five-point
   negative-type instance, a genuine first stop at the second solve, both
   nonsingular inverses, positive denominator and strictly suboptimal output.
   The returned vector's feasibility also follows in prose: its displayed
   entries are nonnegative and $15961+22820+22820=61601$.
2. **Kernel-checked deletion and improvement.** `active1` identifies the
   retained indices as $\{0,1,4\}$, so indices 2 and 3 are deleted together.
   `output1` identifies $p$; `competitor` constructs a feasible probability;
   `energy_gap` proves its strictly smaller energy. The equality
   $p'=(999/1000)p+(1/1000)e_3$ follows in prose by multiplying the displayed
   coordinates, with common denominator $61601000$.
3. **Computed interval failure.** The exact checker verifies failure for
   every $19/20\le q<1$, with index-3 unnormalized residual
   $$-\frac{(1-q)^2(1+q)(1+q+q^2)}{1+q^2+2q^4}.$$
   Its factorization is strictly negative on that interval. The family
   conclusion is symbolic computational evidence, not a Lean family theorem.
4. **Computed Schur sign.** The removed-block off-diagonal is
   $$\frac{2q^5(q-1)(q+1)}{1+q^2+2q^4}<0.$$
   The exact checker establishes the formula. Its sign follows in prose from
   $0<q<1$. Thus negative type does not supply the entrywise covariance sign
   of the tree argument. The deletion/re-entry diagnosis is prior art in
   Huntsman; this is a finite exponential-kernel witness.
5. **Computed principal minors and limit.** All 31 nonempty principal minors
   are positive at $q=19/20$. The checker verifies the limiting probability
   $p_0=(1/4,3/8,0,0,3/8)$ and the positive-scale residual coefficient $-3/2$
   at order $(1-q)^2$. Optimality of $p_0$ for the scale-zero distance problem
   has the following prose proof: $Hp_0=(9/4,9/4,2,9/4,9/4)$ and, for
   zero-sum $a$, $a^THa=-2\|\sum_i a_ix_i\|^2\le0$. Hence for any probability
   $u$, $u^THu-p_0^THp_0=2(u-p_0)^THp_0+(u-p_0)^TH(u-p_0)\le0$; the first
   term is $-u_2/2$. This distance-energy maximization is distinct from the
   positive-scale similarity-energy minimization. No Lean theorem for the
   family or scale-zero limit is asserted.
6. **Open boundaries.** The ordinary Euclidean-distance question, minimality
   of five points, a generally correct re-entry algorithm for the exponential
   kernel and continuum-support questions are open in this delivery.
   Bouafia's restricted weighted-tree Theorem 4 is outside the refuted
   extension; no new verification of that theorem is claimed.

### What the settlement shows

The fixed refutation is kernel-checked by `result`: irreversible simultaneous
deletion loses a useful coordinate, even with genuine inverses and a positive
terminal normalization. The interval residual and negative Schur entry are
computed evidence explaining this failure. The source's weighted-tree
conclusion retains its stated scope; no established source theorem is
claimed refuted, and no later source result depends on the open extension.
A final original-space optimality test detects this witness's defect, but
correctness of a replacement re-entry procedure remains open.

## ASSUMED-UNVERIFIED

Literature completeness, non-arXiv author bibliography and priority beyond the
inspected sources remain unverified. The mathematical settlement is the
single fixed-scale Lean refutation. The exact family, Schur and limit claims
have the distinct computational or prose evidence described above.

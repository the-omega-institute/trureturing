---
slug: porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff
bibkey: portoetal2024tradeoffnonlocalitycontextuality
doi: 10.1088/1367-2630/ad7167
url: https://arxiv.org/abs/2405.02964v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result
---

# The normalized nonlocality–contextuality trade-off holds for every binary $n$-cycle

## Problem

L. E. A. Porto, G. Ruffolo, R. Rabelo, M. Terra Cunha and P. Kurzyński, *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*, state the following conjecture in the arXiv v2 source `final_version.tex`, lines 373–375 (the source file has md5 `7b93583e359377061bc3289b38eedc53`):

> Consider a bipartite generalized Bell scenario where Bob has an $n$-cycle contextuality setup. For any normalized generalized-Bell inequality $S_{GBell}$ and any normalized noncontextuality inequality $S_{NC}$ of Bob's local experiment, every $\mathcal{NSND}$ behavior satisfies expression \eref{eq: trade-off_inequalities}.

The module reads the binary scenario as `Behavior n := Fin 2 → Fin n → Bool → Bool → Bool → ℝ`, with two Alice settings and the ordered outcomes of the two measurements in each cyclic Bob context. `BobBehavior n` is the corresponding table without Alice's setting, and `bobMarginal p` sums over Alice's outcome at setting $0$. `IsNSND p` requires nonnegativity, normalization in every $(x,i)$ context, agreement of the shared Bob marginal in consecutive contexts, independence of Bob's joint marginal from Alice's setting, and independence of Alice's marginal from Bob's context.

`IsGeneralizedLocal p` is membership in the real convex hull of products `productBehavior α r`, where `IsAliceResponse α` is a nonnegative normalized response for both Alice settings and `IsND r` is a nonnegative normalized nondisturbing Bob table. `IsNoncontextual r` is the convex hull of the deterministic tables induced by assignments `s : Fin n → Bool`. An affine functional is represented by a pair `(linear map, offset)`. `IsNormalizedGBell f` requires its affine value to be at most $0$ on every generalized-local behavior, at most $1$ on every `IsNSND` behavior, and equal to $1$ on some `IsNSND` behavior. `IsNormalizedNC t` imposes the analogous noncontextual bound on Bob tables, the upper bound on every `bobMarginal p` from an `IsNSND p`, and attainment of $1$ by such a marginal.

Thus the formal `claim` is: for every $n$ with $3 \le n$, every such affine pairs $f$ and $t$ satisfying `IsNormalizedGBell f` and `IsNormalizedNC t`, and every `p` satisfying `IsNSND p`,
$f.1\,p+f.2+\bigl(t.1\,(\operatorname{bobMarginal} p)+t.2\bigr)\le 1$

## Motivation

The source studies generalized Bell scenarios with two dichotomic Alice measurements and an $n$-cycle of dichotomic Bob measurements. It proves this normalized trade-off by vertex enumeration for $n=3,4,5$ and asks whether the same bound holds for every cycle length. The bound limits the combined values of arbitrary normalized generalized-Bell and Bob-local noncontextuality inequalities, so it separates the possibility of jointly observing nonlocality and local contextuality from the stronger possibility of making both violations arbitrarily large.

## Gap

The bounded literature check recorded in issue [#24437](https://github.com/the-omega-institute/trureturing/issues/24437) reports that the arXiv v2 and published source retain the conjecture; the cited works checked there do not settle it, and no prior theorem in the searched scope supplied the all-$n$ trade-off. The cycle-polytope vertices from Araújo et al. and the midpoint lemma used in the source are ingredients, rather than a previously found theorem of the required form. The repository had no existing settlement for this source.

`not-found-in-searched-scope`.

## Route

1. For `bob_nd`, the hypothesis is exactly `hp : IsNSND p` for `{n : ℕ}` and `{p : Behavior n}`; it proves `IsND (bobMarginal p)` by summing the nonnegativity, normalization, shared-marginal, and Alice-setting conditions of `hp`. For `product_nsnd`, the hypotheses are `hα : IsAliceResponse α` and `hr : IsND r`; it proves `IsNSND (productBehavior α r)`. For every `γ : Fin n → Bool`, `vertex_nd` proves `IsND (vertex γ)`.

2. `oddSigns γ` is the condition `∏ i, if γ i then (-1 : ℝ) else 1 = -1`; `vertex γ i b c` is $1/2$ when `Bool.xor b c = γ i` and is $0$ otherwise, and `generators n` is the union of deterministic tables with the odd-sign vertices. `even_signs_assignment` takes `γ : Fin n → Bool` and the exact parity hypothesis `∑ i, γ i = false`, and constructs an assignment whose consecutive Boolean differences are `γ`. With the same parity hypothesis, `even_vertex_noncontextual` proves `IsNoncontextual (vertex γ)`. `cycle_generators` takes `hn : 3 ≤ n`, `r : BobBehavior n`, and `hr : IsND r`; it applies the imported circulation decomposition with the derived condition $0<n$ and rewrites every even-parity vertex as a noncontextual convex combination, proving `r ∈ convexHull ℝ (generators n)`.

3. `midpoint_noncontextual` takes `γ, η : Fin n → Bool`, `hγ : oddSigns γ`, `hη : oddSigns η`, and `hne : γ ≠ η`; it proves that the equal midpoint of `vertex γ` and `vertex η` is `IsNoncontextual`. The proof flips one differing coordinate in each odd pattern to obtain two even patterns and uses `even_vertex_noncontextual`.

4. `unique_positive_generator` takes a generator hypothesis `hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n)`, a midpoint hypothesis `hmid : ∀ γ η : Fin n → Bool, oddSigns γ → oddSigns η → γ ≠ η → IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η)`, a functional pair `t`, and `ht : IsNormalizedNC t`. It yields an odd pattern `γ` with `t.1 (vertex γ) + t.2 = 1` and, for every odd `η ≠ γ`, `t.1 (vertex η) + t.2 ≤ 0`.

5. `generator_dominance` takes `r : BobBehavior n` with `hr : r ∈ convexHull ℝ (generators n)`, `t` with `ht : IsNormalizedNC t`, an odd-pattern candidate `γ`, the equality `hmax : t.1 (vertex γ) + t.2 = 1`, and `hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0`. It produces `v : ℝ` with $0\le v$, `t.1 r + t.2 ≤ v`, and the coordinate inequalities $v\,vertex\,γ(i,b,c)\le r(i,b,c)$ for every $i,b,c$.

6. `slice_dominance` takes `hgen` as above, `p : Behavior n` with `hp : IsNSND p`, an index `i₀ : Fin n`, `x : Fin 2`, an outcome `a : Bool`, `t` with `ht : IsNormalizedNC t`, and `γ`, `hmax`, `hother` as in `generator_dominance`. It yields `w : ℝ` with $0\le w$, the slice bound
$t.1\bigl(i,b,c\mapsto p(x,i,a,b,c)\bigr)+\Bigl(\sum_b\sum_c p(x,i₀,a,b,c)\Bigr)t.2\le w$
and $w\,vertex\,γ(i,b,c)\le p(x,i,a,b,c)$ for every $i,b,c$. Its zero-mass branch uses nonnegativity to make the slice vanish; its positive-mass branch divides by the slice mass and invokes `generator_dominance`.

7. `common_local_part` takes `hn : 3 ≤ n`, `hgen`, `p` with `hp : IsNSND p`, `t` with `ht : IsNormalizedNC t`, the strict positivity `hc : 0 < t.1 (bobMarginal p) + t.2`, and `γ`, `hmax`, `hother` as above. It returns an `α : AliceResponse` with `IsAliceResponse α` and the coordinate domination
$\bigl(t.1(\operatorname{bobMarginal}p)+t.2\bigr)\,\bigl(\alpha(x,a)\,vertex\,γ(i,b,c)\bigr)\le p(x,i,a,b,c)$
for every $x,i,a,b,c$. The product of this response with `vertex γ` is `IsGeneralizedLocal` by the convex-hull definition and is `IsNSND` by `product_nsnd`.

8. `dominated_local_tradeoff` takes `p,l : Behavior n`, `hp : IsNSND p`, `hl : IsNSND l`, `hloc : IsGeneralizedLocal l`, `c` with `hc : 0 < c` and `hc1 : c ≤ 1`, the coordinate condition `hdom : ∀ x i a b d, c * l x i a b d ≤ p x i a b d`, and `hf : IsNormalizedGBell f`. It proves `f.1 p + f.2 ≤ 1 - c`. The $c=1$ branch uses equal total masses to identify $l=p$; the $c<1$ branch forms the residual `r` and verifies all five `IsNSND` clauses before applying the affine bounds.

9. `result` fixes `n`, `hn : 3 ≤ n`, normalized `f,t`, and `p` with `hp : IsNSND p`. If `t.1 (bobMarginal p) + t.2 ≤ 0`, it uses the `IsNSND` upper bound in `hf` directly. Otherwise it obtains `γ`, `hmax`, and `hother` from `unique_positive_generator` using `cycle_generators` and `midpoint_noncontextual`, obtains the dominated product from `common_local_part`, and applies `dominated_local_tradeoff` with `c = t.1 (bobMarginal p) + t.2` and the bound `c ≤ 1` from `ht`. Adding $c$ gives the claimed sum bound.

## Falsifier

The settlement would not answer the source conjecture under an interpretation different from the module's compiled objects. In particular, it would fail to match if the source's two Alice settings or cyclic Bob contexts were changed, if Boolean edge signs did not represent the source's dichotomic outcomes, if generalized locality required Bob's hidden behavior to be noncontextual rather than merely nondisturbing, or if normalization were taken over a different behavior set. The module fixes these choices explicitly: `Behavior` has two Alice settings, `finRotate n i` supplies the neighboring Bob measurement, generalized-local products use arbitrary `IsND` Bob tables, and `IsNormalizedGBell` and `IsNormalizedNC` use the stated affine upper bounds and attained maxima.

The result is for binary probability tables with two Alice settings and $n\ge3$. It does not formalize the source's quantifier version, the source's separate maximal-contextuality-implies-locality statement as a declaration, scenarios with more Alice measurements, the Peres–Mermin square, or quantum realizability. A numerical or finite vertex check that only confirms particular $n$ would not settle the all-$n$ claim; a falsifier must provide an $n\ge3$, normalized `f`, normalized `t`, and `IsNSND p` violating the exact displayed inequality.

## Evidence

The canonical source is `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.lean.json`.
Declaration statements:
- `result`: `sha256:137f8b3e3f236d9ec0af64730543205fe37bcd1b35bc77ed1029d65f39843e5a`;
- `claim`: `sha256:f957b3179d25ffeea4c82ca615a9bd6bd2967ffe2a7dbf23184101c2c0ae8692`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2024 article, preregistered in issue #24437 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\in\mathbb N$ with $3\le n$, every pair `f` and `t` of affine functionals satisfying `IsNormalizedGBell f` and `IsNormalizedNC t`, and every `p` satisfying `IsNSND p`, the exact module expression
$f.1\,p+f.2+\bigl(t.1\,(\operatorname{bobMarginal}p)+t.2\bigr)\le1$
holds.

**Computed, not formalized**. None.

**Argued, not formalized.**

- **Decisive mechanism.** Under the exact hypotheses of `cycle_generators` (`hn : 3 ≤ n`, `r : BobBehavior n`, `hr : IsND r`), every Bob table is generated by deterministic tables and odd Boolean edge vertices after even vertices are replaced using `even_vertex_noncontextual`. Under the exact hypotheses of `midpoint_noncontextual` (two odd patterns and `γ ≠ η`), their midpoint is noncontextual. `unique_positive_generator` then gives one odd vertex attaining the normalized contextual value $1$ and makes every other odd vertex nonpositive. `generator_dominance`, `slice_dominance`, and `common_local_part` convert this into a common generalized-local product dominated coordinatewise by $p$; `dominated_local_tradeoff` supplies the Bell-value bound. These named lemmas are formal proof components, while this paragraph is the structural interpretation of what they establish together.

- **Range and sharpness.** The formal quantifier covers every $n\ge3$, including cycle lengths beyond the source's $3,4,5$ computation, within the exact binary and two-setting definitions. `result` proves only the upper bound; it does not prove that the value $1$ is attained by a simultaneous pair for each $n$, nor does it prove a separate sharpness theorem.

- **Neighbouring source statements.** The source's quantifier relation involving nonlocal, contextual, and nonclassical fractions; its no-joint-witness consequence; and its separate maximal-contextuality-implies-locality result are not declarations of this module. Their status for the all-$n$ formal setting remains open here. The source's Peres–Mermin counterexample concerns a different compatibility scenario and is unaffected by this binary cycle result. Claims about quantum realizability and physical resource advantages are also outside the formal type.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in issue #24437 and does not establish exhaustive worldwide novelty or priority. The correspondence between the source's signed dichotomic notation and the module's Boolean encoding is the stated formal reading; no separate physical-realization theorem is included. The source's vertex enumeration for $n=3,4,5$, the quantifier reformulation, the no-joint-witness consequence, maximal-contextuality consequences, sharpness beyond the exact inequality, and all quantum or operational interpretations remain unformalized. Any cited prior polytope or midpoint results were used as literature context rather than independently reproved here.

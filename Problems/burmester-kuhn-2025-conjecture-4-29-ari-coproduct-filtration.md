---
slug: burmester-kuhn-2025-conjecture-4-29-ari-coproduct-filtration
bibkey: burmesterkuhn2025postlie
doi: 10.48550/arXiv.2504.19661
url: https://arxiv.org/html/2504.19661v1
triage: theorem
motivation_gids:
  - D5/S1/Words/PostLie/AriCoproductFiltration.result
---

# The original ari coproduct preserves every right-factor level filtration

## Problem

Annika Burmester and Ulf Kühn, *On post-Lie structures for free Lie
algebras*, arXiv:2504.19661v1, Conjecture 4.29, state:

> For k ≥ 0 we define the k-level of a word v_{k_1}⋯v_{k_d} by
> d − #{j | k_j=k}, and extend this to an increasing filtration on
> Q⟨V⟩. For w∈Q⟨V⟩, write as usual Δ_a(w)=w_(1)⊗w_(2). Then,
> we always have k-level(w_(2)) ≤ k-level(w).

Let $H=\mathbb Q\langle v_0,v_1,\ldots\rangle$ be the algebra of finite
ordinary rational word polynomials, including its unit. For a word $w$,
let $\lambda_k(w)$ count letters different from $v_k$ and put

$$
F_r^k=\operatorname{span}_{\mathbb Q}
 \{w:\lambda_k(w)\le r\}.
$$

The precise filtration assertion is, for every $k,r\in\mathbb N$ and
every $P\in F_r^k$,

$$
\Delta_a(P)\in\operatorname{range}
 \bigl(\operatorname{id}_H\otimes\iota_r^k:
 H\otimes_{\mathbb Q}F_r^k\longrightarrow H\otimes_{\mathbb Q}H\bigr),
$$

where $\iota_r^k$ is the natural submodule inclusion. All tensor products
are ordinary algebraic tensor products. A Sweedler expression is read
through this subspace assertion, rather than through a chosen tensor
decomposition. The resolution is **Proved** by
`D5/S1/Words/PostLie/AriCoproductFiltration.result`, with
`claim : Prop` and `result : claim`.

| Source clause | Formal counterpart |
| --- | --- |
| Original rational word algebra on all nonnegative indices | `AriWordOperations.H = RationalWordPolynomial Nat`, with `Word = FreeMonoid Nat` and the existing ordinary monoid-algebra basis |
| Every natural $k$, including zero | The unrestricted `k : Nat` in `claim`; the generator $v_0$ and mixed-zero multiplicities retain their source conventions |
| Increasing level filtration at every $r$ | `level k w = w.countP' (· ≠ k)` and `filtration k r`, the rational span of all words of level at most $r$ |
| Every finite rational polynomial in that span | `P : H` with membership in `filtration k r`; no length, weight, homogeneity, coefficient-sign or cancellation restriction |
| Original ari product and dual coproduct | `letterAction`, `primitiveUnshuffle`, `star`, `transposeProperty`, and the proved uniquely characterized `delta` |
| Full ordinary pairing | `pairing`, `tensorPairing`, `delta_transpose` and `delta_basis_coefficient`, including empty words and both unit tensor terms |
| Membership in the actual right-factor tensor image | `rightFiltrationImage k r = LinearMap.range (TensorProduct.map id (filtration k r).subtype)` and `result` |

The source operations and locators are documented in
[the source note](../Library/Words/burmesterkuhn2025postlie.md).
The claim is the entire target preregistered in
[#23147](https://github.com/the-omega-institute/trureturing/issues/23147).

## Motivation

The assertion controls how the original ari coproduct distributes letters
away from a chosen generator in its right tensor factor. The source uses
this filtration assertion in the context of Theorem 4.30. The present
result proves the filtration assertion itself; no independent
formalization of that theorem or of every surrounding post-Lie structure
is asserted.

The carrier is the existing rational word polynomial algebra. The
construction preserves the ordinary coefficient-one word basis and its
full tensor pairing, so the result applies to the source algebra without
replacing it by a divided-power algebra or a finite truncation.

## Gap

Conjecture 4.29 asks for a uniform assertion on all words and their rational
linear combinations. Checking generator cases or bounded lengths cannot
supply that assertion. A coefficient support bound must also give actual
membership in the tensor-submodule image, and a proposed dual operation
must exist in the ordinary algebraic tensor product.

The finite action presentation is the first equality in the full proof of
Proposition 4.19, with generator Lie factors. The source derives it from
Definition 4.8 and its enveloping extension, Definition 1.9. Proposition
2.1 supplies the ordered primitive-unshuffle formula for the product.
Definition 1.20 and Remark 1.22 supply the full ordinary transpose
characterization. These proved source presentations are used directly;
no separate magmatic or free-Lie realization, assumed comparison map or
assumed coproduct preservation is introduced.

## Route

Definition 4.2 has $\beta(0,0)=1$, zero mixed-zero values, and
$\beta(a,l)=\binom{a-1}{l-1}$ when $a,l>0$. For a nonempty word
$A=v_{a_1}\cdots v_{a_m}$ and $s>0$, the source's finite formula is

$$
A\triangleright_a v_s=
\sum_{0\le l_i\le a_i}
 (-1)^{\sum_i a_i+\sum_i l_i}\prod_i\beta(a_i,l_i)
 [\cdots[[v_{s+\sum_i(a_i-l_i)},v_{l_1}],v_{l_2}],\ldots,v_{l_m}].
$$

The empty word acts identically; a nonempty word acts by zero on $v_0$.
`AriWordOperations` implements these conventions. It uses only the valid
nonzero-multiplicity implication from Remark 4.3, including preservation
of zero positions.

The concatenation algebra homomorphism $\pi_k:H\to\mathbb Q[t]$ sends
$v_k$ to $t$ and every other generator to zero. For every $d\ge0$, its
$t^d$ coefficient is exactly the ordinary coefficient of $v_k^d$.
Commutativity of the target annihilates every commutator. Consequently a
nonempty left input in a generator action has no pure-$v_k$ output.
`AriProjection` proves this coefficient statement, including degree zero,
and the resulting level lower bound.

`AriWordProduct` assigns each input position independently to one of the
ordered slots of the right word and retains the original order inside
each slot. Coincident assignments are counted with multiplicity. Each
right letter different from $v_k$ contributes at least one such letter
to every supported term. Concatenation adds the level, while finite sums
and rational cancellation cannot introduce support outside the bound.
Thus, for all words $A,B,w$,

$$
[w](A\star_a B)\ne0\quad\Longrightarrow\quad
\lambda_k(B)\le\lambda_k(w).
$$

Use the original weights $\gamma(0)=1$ and $\gamma(i)=i$ for $i>0$.
The action and product preserve total weight. Words of weight at most
$N$ have length and every index at most $N$; bounded lists over
$\operatorname{Fin}(N+1)$ therefore give an exact finite weight window.
`AriCoproductFiltration` constructs the ordinary tensor transpose in that
window and proves its coefficient formula for every pair, including pairs
outside the window and empty factors. It proves the full arbitrary-three-
polynomial pairing characterization and uniqueness, identifying `delta`
with the source operation.

The support bound places every nonzero tensor basis term over a right
word of the required level. Each such term is the image of an actual
tensor with a right member of `filtration k r`. Submodule closure, basis
spans and rational linearity prove the stated image membership for every
$P\in F_r^k$.

## Falsifier

A failure of the defining source correspondence, an incorrect unshuffle
multiplicity, a nonzero pure-word coefficient in a nonempty action, or a
pair outside the claimed finite window with nonzero transpose coefficient
would invalidate the route. A single original $k,r,P$ violating the actual
image inclusion would refute the claim. The formal result retains all
these quantifiers and proves the actual image membership.

The positive proof is not a finite-instance verification or a designated
refutation; it receives no refutation audit exemption. A different
Appendix A.7 uri assertion, a single-generator consequence, a bounded
length assertion or an assumed filtration-preserving coproduct does not
resolve this problem.

## Evidence

The four D5 modules and their corresponding Scribes contain the source
operations, the projection/support argument, the finite ordinary transpose
and the full filtration result. The terminal declaration is
`D5/S1/Words/PostLie/AriCoproductFiltration.result`; its proposition is
`D5/S1/Words/PostLie/AriCoproductFiltration.claim`.

The module-owned Reg mirrors supply four-slot source-equivalence
registrations for all public theorem targets. The current scoped report
contains 26 `declared_validated` records: 11 for `AriWordOperations`, four
for `AriProjection`, five for `AriWordProduct`, and six for
`AriCoproductFiltration`, with no registration errors. The reported axiom
union is `Classical.choice`, `Quot.sound`, and `propext`. Unknown
continuations record residual unknown information; they do not assert
undecidability or replace registration evidence.

The typed Scribe resolution binds this one problem to the actual `result`
as `Proved`. Canonical frozen state records carry the declaration
identities. A scoped kernel report establishes the selected mathematical
scope, not complete repository admission. Full required CI and independent
final review remain separate checks.

## Triage

This is the whole external named conjecture under
`admission_basis: open-problem-resolution`, with conservative
`proof_shape: bind-only` synthesis. Its positive conclusion is universal;
`utility: none` records that it is not an ordinary positive finite
certified instance. The retained auxiliary declarations supply the live
mathematical chain to `result`; no stronger input hypothesis is added.

The bounded literature screen covered relevant passages of
arXiv:2508.05024v1, 2603.05038v1, 2609.25168v1 and 2610.37351v1 without
identifying an exact settlement. MathDB 368177 concerns the distinct
Appendix A.7 uri assertion. These are bounded search conclusions, not a
claim of worldwide absence or priority. Other people's exact registered
targets remain excluded in every registration state.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are ASSUMED-UNVERIFIED;
rate-limited citation APIs do not establish absence. No complete
classification of related post-Lie structures or independent
formalization of the paper's magmatic construction is claimed.

Standalone `content-check` and `markdown-check` reject the canonical
scoped-v1 report at their raw-v3-only schema boundary, before evaluating
the candidate. This limitation is tracked in
[#20682](https://github.com/the-omega-institute/trureturing/issues/20682).
Those checks have not passed; full current-input admission belongs to the
supported required CI route. The draft's mathematical result does not
itself certify final review, merge, first dev push, priority or solve credit.

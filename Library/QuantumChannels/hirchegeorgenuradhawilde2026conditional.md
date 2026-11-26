---
bibkey: hirchegeorgenuradhawilde2026conditional
authors: Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde
year: 2026
title: "Conditional contraction coefficients and their applications to quantum networks"
doi: null
url: https://arxiv.org/abs/2608.27171v1
claim: "For a quantum channel N and a generalized divergence D, the conditional contraction coefficient is η^Δ_D(N) := sup over |R| and ρ_RA ≠ σ_RA of [D((id ⊗ N)(ρ_RA)‖(id ⊗ N)(σ_RA)) − D(ρ_R‖σ_R)] / [D(ρ_RA‖σ_RA) − D(ρ_R‖σ_R)] (Eq. (2.14)), optimized over pairs with a strictly positive finite denominator (Remark 2). The hockey-stick divergence is E_γ(ρ‖σ) := Tr(ρ − γσ)_+ (Eq. (5.1)). For the trace distance (γ = 1), η^c_Tr(N) and η^Δ_Tr(N) are optimized by orthogonal states (Proposition 8). §9 asks whether, for the hockey-stick divergence, the optimization can be restricted to orthogonal states, which would imply monotonicity of the coefficient in γ."
strata_touched:
  - D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
  - D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation
  - D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport
  - D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport
  - D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse
  - D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearCurve
  - D5/S3/Quantum/Divergence/FaithfulConditionalGap
  - D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension
  - D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose
license: citation-only
triage: anchor
---

# Hirche, George, Nuradha and Wilde, conditional contraction coefficients

C. Hirche, I. George, T. Nuradha and M. M. Wilde, *Conditional contraction coefficients and their applications to quantum networks*, arXiv:2608.27171 [quant-ph] (v1 of 27 August 2026, the only version listed).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2608.27171v1

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2608.27171v1:
- p. 8, Definition 2, Eqs. (2.12)–(2.14);
- p. 9, Remark 2;
- p. 37, §5, Eqs. (5.1)–(5.2);
- p. 40, Proposition 8 and Remark 6;
- p. 72, §9, the first open problem.
- p. 72, §9, the second open problem (faithful-divergence separation).
- p. 72, §9, the fourth bullet (nonlinear strong data processing with references).

## Source statements

Definition 2, Eq. (2.13) (p. 8), gives the complete coefficient as the supremum of joint output-to-input divergence ratios over arbitrary finite reference systems and pairs with equal reference marginals.

Definition 2 (p. 8): "the conditional contraction coefficient as η∆_D(N) := sup_{|R|, ρRA≠σRA} [D((id ⊗ N)(ρRA)∥(id ⊗ N)(σRA)) − D(ρR∥σR)] / [D(ρRA∥σRA) − D(ρR∥σR)]. (2.14)"

Remark 2 (p. 9): "The optimization is should be over states such that ∞ > D(ρRA∥σRA) − D(ρR∥σR) > 0, which is a strictly stronger constraint than just ρRA ≠ σRA. … As a general rule, in this paper, all ratio optimizations are over strictly positive and finite denominators."

§5 (p. 37): "The hockey-stick divergence is defined as [52] Eγ(ρ∥σ) := Tr(ρ − γσ)+ (5.1) = sup_{0≤M≤I} Tr[M(ρ − γσ)], (5.2) where (A)+ denotes the positive part of a Hermitian matrix A."

Proposition 8 (p. 40): "For a channel N : A → B, the coefficients ηc_Tr(N) and η∆_Tr(N) are optimized by orthogonal states".

§9 (p. 72): "When considering the hockey-stick divergence, can the optimization in the contraction coefficient be restricted to orthogonal states, similar to Proposition 8? This would directly imply that the associated contraction coefficient is monotone in γ, which in turn would have applications similar to the results in [7]."

## Reading used by the repository

The first question is read for the conditional coefficient η^Δ_{E_γ} with γ ≥ 1. That orthogonal-reduction result does not address the complete coefficient η^c.

For finite systems A and B and a channel N : A → B, the ratio set S_γ(N) consists of the ratios [E_γ((id ⊗ N)ρ‖(id ⊗ N)σ) − E_γ(ρ_R‖σ_R)] / [E_γ(ρ‖σ) − E_γ(ρ_R‖σ_R)]. These range over every finite reference system R and all density matrices ρ, σ on R ⊗ A with a strictly positive denominator. S^⊥_γ(N) is its subset from pairs with ρσ = 0.

The repository proves two statements:
- S_γ(N) = S^⊥_γ(N) for every γ ≥ 1;
- S_γ(N) = S_δ(N) for all γ, δ ≥ 1, so η^Δ_{E_γ}(N) does not depend on γ ≥ 1.

In the formal numerator, the subtracted reference marginals are taken of the output states (id ⊗ N)ρ and (id ⊗ N)σ; they equal ρ_R and σ_R because N is trace preserving.

## Complete hockey-stick contraction

`CompleteHockeyStickRefutation.refutes_monotonicity_and_orthogonal_reduction`
gives a binary measure-and-prepare channel with complete coefficient at most
$3/5$ at $\gamma=1$ and at least $9/10$ at $\gamma=2$. The orthogonal-input
complete coefficient is at most $3/5$ for every $\gamma\ge 1$. This answers
Remark 6 on $[1,\infty)$ and the complete-coefficient case of the first
question in §9. Both upper bounds quantify over all finite quantum references.
The lower bound uses two-dimensional input, output and reference systems.

Eriksson, *Common support and complete contraction with quantum side information*,
v3, §6.4, gives an earlier complete Umegaki ratio above its trace endpoint for
a different channel. Integrating the two ordered hockey-stick divergences
gives the qualitative failure of endpoint monotonicity as a consequence of
that earlier result. The Lean theorem gives an explicit rational witness at
$\gamma=2$ with no relative-entropy step. [Eriksson, v3](https://airr.science/papers/ARR-2026-564FZ70CSN83KACD/versions/v3/)

`CompleteHockeyStickBasisSupport.result` gives a sufficient condition for a
unit complete coefficient at every fixed $\gamma>1$. For a finite channel with
at least two computational basis states, intersect the supports of their
outputs. If the intersection is zero, equal-marginal witnesses approach
retention one with a reference of input dimension. The simplex uses Eriksson's
common-support construction in §6 with input blocks calibrated directly for
the fixed hockey-stick parameter. A fixed-parameter CQ saturation
statement also follows from Eriksson’s §§6.2–6.3 estimates. For $t>1$,
completing the square in the two active input coordinates gives
$E_t(\rho\Vert\sigma)\le4nt\beta/(t-1)$. His graph effect has
$p\sim4n\beta$ and $q=o(\beta)$, so $p-tq$ gives a limiting ratio
of at least $(t-1)/t$. For any fixed $\gamma>1$, mixing the first
input toward the second by weight $(\gamma-1)/(t-1)$ on the first
input preserves the ratio for $t\ge\gamma$. Sending $t$ to infinity
gives the saturation statement. [Eriksson, v3](https://airr.science/papers/ARR-2026-564FZ70CSN83KACD/versions/v3/)

`CompleteHockeyStickChoiSupport.result` proves unit complete contraction for
each fixed $\gamma>1$ when the normalized Choi support of a finite channel
contains no full reference factor over a nonzero output vector. A finite
family of reference-unitary translates of the Choi state has zero common
support. Computational-basis preparation of the corresponding Bell states
transfers the ratios from the fixed-parameter simplex theorem while
preserving the common reference marginal. Eriksson v3, Theorem 6.1, gives
the Umegaki criterion for finite classical-input channels and provides the
simplex mechanism used in the basis-support step.
[Eriksson, v3](https://airr.science/papers/ARR-2026-564FZ70CSN83KACD/versions/v3/)

The exhibited positive-weight bound in George, Hirche, Nuradha and Wilde,
*Quantum Doeblin Coefficients: Interpretations and Applications*, v3,
Proposition 31, gives an upper bound of $1-p$ for a channel with a
replacement component of weight $p$ at every $\gamma\ge 1$. Their §9.2
Question 1 concerns the bound using the Hermitian Doeblin coefficient.
[arXiv:2503.22823v3](https://arxiv.org/abs/2503.22823v3)

`CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support`
constructs a pure replacement of weight $0<p<1$ and a finite CPTP residual
whenever the normalized Choi support contains every reference basis slice
over a common nonzero output vector. The construction bounds the Gram
matrix of slice preimages under the positive Choi square root, subtracts
the weighted replacement Choi matrix, and normalizes the positive residual.
Trace preservation gives Kraus completeness for the residual and hence
the channel decomposition on all input matrices.

`CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support`
applies Proposition 31's exhibited-weight bound for every $\gamma\ge 1$.
`CompleteHockeyStickChoiConverse.coefficient_lt_one_iff` combines this
implication with Choi support saturation. For every finite CPTP channel
with nonempty input and each fixed $\gamma>1$, the complete coefficient
is strictly below one exactly when the full reference slice condition holds.
Both branches use the static Choi matrix of the channel.

## Complete nonlinear hockey-stick curve

The fourth bullet of §9 proposes nonlinear strong data-processing inequalities
with reference systems. The ordinary curve in Nuradha, George and Hirche,
Eq. (4.1), maximizes output divergence under an input divergence budget.
The complete curve uses every finite reference and joint density pairs with
equal reference marginals. [arXiv:2512.16778v1](https://arxiv.org/abs/2512.16778v1)

`quadratic_loss_near_zero` fixes $\gamma>1$ and assumes that the Kraus products
span the input matrix algebra and the normalized Choi support contains no
full reference fiber over a nonzero output vector. For the complete curve
$F_\gamma$, there are $c,C,\delta>0$ with
$c a^2\le a-F_\gamma(a)\le C a^2$ for $0<a\le\delta$.

The span gives a matrix-unit lift bound independent of the reference dimension.
Ordered reference marginals of the two parts of the input difference give
purifications related by a contraction. Lifting that contraction and splitting
its overlap with an output effect bounds the output divergence at every finite
reference dimension. In the other direction, the Choi orbit gives a preparation
with zero common output support. Eriksson's simplex and graph effect
(§§6.2–6.3), calibrated at the fixed hockey-stick parameter, yield output
divergence at least $a/(1+D a)$ on one finite reference for all small budgets.
The curve estimate applies in this channel class near zero. [Eriksson, v3](https://airr.science/papers/ARR-2026-564FZ70CSN83KACD/versions/v3/)

## Faithful-divergence separation

The second bullet of §9, printed p. 72, asks:

> Can we find a concrete example such that η_D^c(N) < η_D^Δ(N) for some faithful divergence D? A particularly interesting case would be that of the relative entropy. Although it would be natural to conjecture that such an example exists, the unbounded reference systems make it difficult to confirm.

This is a separate question from the hockey-stick orthogonal reduction. The divergence is a nonnegative real-valued family on all finite quantum density-state pairs, faithful in the sense that it vanishes exactly on equal states, and monotone under every finite CPTP map, including maps between different dimensions. Both coefficient optimizations include every finite quantum reference. Complete ratios require equal reference marginals and positive input divergence; conditional ratios subtract the reference divergence and require a positive denominator. Empty admissible sets contribute coefficient zero.

`FaithfulConditionalGap.result` answers this existential affirmatively using squared trace distance and a binary measure-and-prepare CPTP channel with transition matrix $W=((3/4,1/4),(1/4,3/4))$. It proves

$$
\eta^c_D(N)\le\frac14<\frac5{12}\le\eta^\Delta_D(N).
$$

The uniform complete bound includes arbitrary finite quantum references, including off-diagonal reference blocks. The conditional witness consists of actual density states on $\mathrm{Fin}\,3\times\mathrm{Fin}\,2$. The squared trace-distance result applies without a reference cutoff and establishes the displayed coefficient bounds. The [problem dossier](../../Problems/hirche-george-nuradha-wilde-2026-faithful-conditional-gap.md) gives the construction, quantifiers and audit boundary.

### Relative entropy on the finite support branch

`UmegakiChannelSupportedExtension.conditionalCoefficient_eq_completeCoefficient`
rules out the relative-entropy instance of the strict separation in the second
bullet of §9. For each finite CPTP channel, the complete and conditional
Umegaki coefficients of Definition 2, Eqs. (2.13) and (2.14), coincide on the
finite support branch with the strictly positive finite denominators of Remark
2. Both coefficients range over all finite reference dimensions and arbitrary
joint density states satisfying the respective conditions. Support containment
of the joint input pair makes the joint divergence finite. Amplified and erasure
data processing carry containment to the joint output and the marginal
pairs. Trace preservation identifies the output reference marginals with the
input reference marginals.

The companion metric result proves
$$
c_0 = \eta^c_{D}(N) = \eta^\Delta_{D}(N) = \sup_{t\in[0,1]} c_t,
\qquad 0 \le c_t \le \eta^c_D(N) \quad (t\in[0,1]),
$$
where $D$ denotes Umegaki relative entropy. At each $t$, the metric ratios use
faithful joint input bases and complex directions of zero partial trace with
positive input inverse form. At the actual channel output the direction belongs
to the range of the corresponding arithmetic operator, so the numerator is
the real Hilbert–Schmidt pairing against its supported Moore–Penrose preimage.
The supremum over the interval is attained at $t=0$.

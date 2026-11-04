---
slug: hertz-jabbour-cerf-2017-covariance-corrected-entropy-power-uncertainty
bibkey: hertzjabbourcerf2017entropypower
doi: 10.1088/1751-8121/aa852f
url: https://arxiv.org/abs/1702.07286v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result
---

# The covariance-corrected entropy-power uncertainty relation fails for mixed states

## Problem

A. Hertz, M. G. Jabbour and N. J. Cerf, *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*, J. Phys. A: Math. Theor. 50, 385301 (2017), arXiv:1702.07286v2, Section III.B, `EP-Unc-Rel-8.tex`, lines 285–290:

> We obtain our tight entropic uncertainty relation simply by substituting $I(x{\rm :}p)$ with $I_G(x{\rm :}p)$ in Eq. (\ref{conj1form1}), namely
>
> $h(x)+h(p) -  {1\over 2} \ln \left(  \sigma_x^2 \sigma_p^2  / |\gamma|  \right)  \ge \ln(\pi e \hbar).$
>
> We will show below (under some assumptions) that this inequality holds for all states, regardless of whether the Wigner function is positive everywhere or not.

The equation has TeX label `conjecture`. Section III.C, line 455, specifies the mixed-state assumption:

> As mentioned above, this proof does not imply that the pure Gaussian states are the only minimum-uncertainty states, and we also need to assume the concavity of our uncertainty functional in order to extend the proof to mixed states.

Here $h(x)$ and $h(p)$ are the Shannon differential entropies of the quadrature distributions, and $\gamma$ has diagonal entries $\sigma_x^2,\sigma_p^2$ and symmetrized cross covariance $\sigma_{xp}$. These conventions are defined in Sections II.A–B, lines 108–117 and 155–166, and in [the literature note](../Library/Entropy/hertzjabbourcerf2017entropypower.md).

Issue [#26413](https://github.com/the-omega-institute/trureturing/issues/26413) fixes the universal reading to be refuted in units $\hbar=1$. For every natural number $n$, take real families $w_i,\mu_{xi},\mu_{pi},a_i,b_i,c_i$ indexed by $\mathrm{Fin}\,n$, with $w_i\ge0$, $\sum_iw_i=1$, $a_i>0$, $c_i>0$ and $\Delta_i=a_ic_i-b_i^2\ge1/4$. The definition `gaussianWigner` gives

$G_i(x,p)=\dfrac{1}{2\pi\sqrt{\Delta_i}}\exp\!\left(-\dfrac{c_i(x-\mu_{xi})^2-2b_i(x-\mu_{xi})(p-\mu_{pi})+a_i(p-\mu_{pi})^2}{2\Delta_i}\right)$.

Let $W(x,p)=\sum_iw_iG_i(x,p)$, $W_x(x)=\int W(x,p)\,dp$, $W_p(p)=\int W(x,p)\,dx$, and $h(f)=-\int f\ln f$. The module defines the means as the phase-space integrals of $xW$ and $pW$, and $\gamma_{xx},\gamma_{pp},\gamma_{xp}$ as the integrals of $(x-\bar x)^2W$, $(p-\bar p)^2W$ and $(x-\bar x)(p-\bar p)W$, respectively. All integrals use Lebesgue volume.

The proposition `claim` asserts that, whenever $W_x\ln W_x$, $W_p\ln W_p$ and $(x^2+p^2)W$ are integrable,

$F(W):=h(W_x)+h(W_p)-\frac12\ln\!\left(\dfrac{\gamma_{xx}\gamma_{pp}}{\gamma_{xx}\gamma_{pp}-\gamma_{xp}^2}\right)\ge\ln(\pi e)$.

Normalization excludes the empty mixture. Refuting this subclass of the source's all-state assertion suffices to refute its universal mixed-state reading; the source's conditional variational argument is not being represented as an unconditional proof.

## Motivation

Hertz, Jabbour and Cerf (2017, arXiv:1702.07286v2) seek a correlation-sensitive uncertainty relation saturated by every pure Gaussian state, including rotated squeezed states. Their correction is the mutual information of the Gaussian distribution with the same covariance. Whether it can be subtracted for arbitrary states determines whether the proposed improvement over the usual entropic uncertainty relation is valid beyond Gaussian states.

## Gap

The bounded literature check in #26413 records:

- the stated conjecture in the 2017 v2 source and its repetition, with assumptions, in A. Hertz and N. J. Cerf, *Continuous-variable entropic uncertainty relations* (2019), arXiv:1809.01052v2, Section 3.4;
- literature-search-seat readings of 19 citing records from INSPIRE record 3040016, and a Crossref listing of 20 citations with no linked correction;
- orchestrator searches for covariance-corrected entropy-power counterexamples and Gaussian-mixture violations, with no settlement found;
- an orchestrator reading of the abstract of arXiv:2609.24670 concerning the distinct Wigner-entropy conjecture, and a repository duplicate search with no problem record found.

These are attributed preregistration readings, not an exhaustive literature search reproduced here. `not-found-in-searched-scope`.

## Route

Write $g_m(x)=\pi^{-1/2}e^{-(x-m)^2}$, the Gaussian density with mean $m$ and variance $1/2$, and let $W_d$ be the equal mixture of the two Gaussian Wigner densities with means $\pm(d,d)$ and covariance $I/2$.

1. **Components and marginals.** For all real $u,v,x,p$, `component_factor` identifies the component with covariance entries $a=c=1/2$, $b=0$ as $g_u(x)g_v(p)$. For every real $d$, `marginals` gives $W_{d,x}=W_{d,p}=q_d=(g_d+g_{-d})/2$.
2. **Moments and finiteness.** For every real $d$, `moments` gives zero means and $\gamma_{xx}=\gamma_{pp}=d^2+1/2$, $\gamma_{xp}=d^2$; `second_integrable` gives integrability of $(x^2+p^2)W_d$, and `mixture_entropy_integrable` gives integrability of $q_d\ln q_d$.
3. **Bounded mixing cost.** For each real $m$, `gaussian_entropy` gives integrability of $g_m\ln g_m$ and $h(g_m)=\frac12\ln(\pi e)$. The lemma `binary_entropy_bound` assumes that $f,g$ are everywhere nonnegative, integrable with integral one, and that all three entropy integrands $f\ln f$, $g\ln g$ and $((f+g)/2)\ln((f+g)/2)$ are integrable; it gives $h((f+g)/2)\le(h(f)+h(g))/2+\ln2$. Applying it to $g_d,g_{-d}$ yields `entropy_upper`, for every real $d$: $2h(q_d)\le\ln(\pi e)+2\ln2$.
4. **Strict violation.** For every real $d$ with $d^2\ge16$, `correction_violation` gives $2\ln2<\frac12\ln R(d)$ with $R(d)=(d^2+1/2)^2/(d^2+1/4)$; at $d=6$, $R(6)=5329/145$. The theorem `result` instantiates `claim` with $n=2$, both weights $1/2$, both mean families $(6,-6)$, and constant covariance entries $a=c=1/2$, $b=0$. Each component determinant is $1/4$; the integrability lemmas discharge all three analytic premises. The covariance ratio is $5329/145$, so the entropy bound makes $F(W_6)<\ln(\pi e)$, contradicting `claim`.

## Falsifier

The refutation would not answer the source if its densities, marginals or covariance convention described different objects. The module uses explicit Gaussian phase-space functions, their actual marginal integrals and their central moment integrals. The correspondence with the source is the standard Wigner representation of a convex mixture of two displaced vacuum states, whose symmetrized quadrature moments are these phase-space moments. This physical identification is an interpretation of the analytic encoding, not an additional Lean theorem about density operators.

The witness has finite entropy integrands and finite second moments. Its component covariance determinants equal $1/4$, while its mixture covariance has $\gamma_{xx}=\gamma_{pp}=73/2$, $\gamma_{xp}=36$ and determinant $145/4>0$. Thus neither a singular logarithm nor a violation of the ordinary covariance uncertainty condition accounts for the counterexample. The witness is mixed and Wigner-positive; it supplies no pure-state counterexample.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:9b27aa0120ed2ab1640384c616d0da6dab78c96a7b66d729ba264d87cbf364d7`;
- `claim`: `sha256:58791f335a38cb9b35b687c903395e390e7b37c2f42fc77c79444ee892ade439`.

## Triage

Tier 1 conjecture of a 2017 J. Phys. A paper, preregistered in issue #26413 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal proposition `claim` is false: not every finite Gaussian mixture with nonnegative normalized weights, positive component diagonal covariances, component determinants at least $1/4$, integrable marginal entropy integrands and integrable phase-space second-moment integrand satisfies $F(W)\ge\ln(\pi e)$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and family.* For every real $d$, `marginals`, `moments` and `entropy_upper` give $F(W_d)-\ln(\pi e)\le\ln4-\frac12\ln R(d)$, and for $d^2\ge16$ the private `correction_violation` makes this bound strictly negative; `result` states only the instance $d=6$. Since $R(d)=d^2+3/4+1/(16(d^2+1/4))$ tends to infinity, the bound tends to minus infinity; this unboundedness is argued from the parameterized helpers and is not a statement of `result`. Separating two fixed-width peaks adds at most the binary label entropy to each marginal, while the Gaussian covariance correction grows without bound.
- *Concavity fails even for equal component covariances.* The component factorization `component_factor`, for all real means and coordinates with covariance $I/2$, and `gaussian_entropy`, for each real mean with variance $1/2$, give $F=\ln(\pi e)$ for each displaced component. The strict estimate of `correction_violation` at $d=6$, together with `entropy_upper` at $d=6$, puts their equal mixture below their average value. This contradicts concavity of $F$. Although the component covariances agree, their means differ; the additional covariance of their means is $d^2\begin{pmatrix}1&1\\1&1\end{pmatrix}$.
- *The common-moment restriction survives.* Appendix A.3 of Hertz, Jabbour and Cerf (2017, arXiv:1702.07286v2), line 650, says: “We consider the mixture of two states that have the same first- and second-order moments.” For two such states with finite second moments and positive covariance determinant, the covariance correction is constant along every convex mixture. At each weight $0\le\lambda\le1$ for which the component and mixture marginal entropy integrands are integrable, pointwise concavity of $-t\ln t$ on $t\ge0$, integrated for each marginal, therefore gives $F(\lambda\rho_1+(1-\lambda)\rho_2)\ge\lambda F(\rho_1)+(1-\lambda)F(\rho_2)$. Equal covariance alone does not ensure constant mixture covariance. Line 660 drops the common-mean condition using displacement invariance; a common displacement cannot make two distinct means equal, and separate displacements change their mixture. The counterexample therefore excludes that broader same-covariance reading.
- *Nearby inequalities.* For a Gaussian state with positive definite covariance, inserting its Gaussian marginal entropies gives $F=\ln(2\pi e)+\frac12\ln\det\gamma$; thus $\det\gamma\ge1/4$ gives the proposed bound, with equality at $\det\gamma=1/4$. For a state with positive quadrature variances and $\gamma_{xp}=0$, the correction vanishes, leaving the usual entropic uncertainty relation, cited in Section II.B of the source to Bialynicki-Birula and Mycielski (1975, Commun. Math. Phys. 44, 129). A restriction to pure states in general remains open here, and this counterexample does not adjudicate the separate Wigner-entropy conjecture labelled `conj1form1`.
- *Effect on the paper.* The unrestricted mixed-state conclusion in Section III.C loses its concavity premise. The equivalent entropy-power expression labelled `conjecture-bis` in Section III.B has the same defect: with $N_x=e^{2h(x)}/(2\pi e)$ and similarly for $N_p$, taking logarithms of its positive sides recovers exactly the refuted inequality. The relative-entropy expression labelled `conjecture2` is equivalent as well, since $D(x\mathbin{\Vert}x_G)=\frac12\ln(2\pi e\gamma_{xx})-h(x)$ and similarly for $p$. Neither reformulation restores a universal mixed-state bound. Section III.D's proposed universal extension includes the refuted $n=1$ case, and Appendix B uses the same concavity premise; no separate multimode theorem is formalized here. Gaussian equality cases and the variational stationary-point calculation are not contradicted by this mixed-state witness. Applications of the conjectured strengthened bound to general separability tests require an independently valid replacement or a justified restriction of state class.

## ASSUMED-UNVERIFIED

The bounded literature check in #26413 does not establish exhaustive worldwide novelty or priority. The 2019 review, the 19 INSPIRE citing-record readings, Crossref's citation and correction readings, the abstract of arXiv:2609.24670, the latest-version assertion and the preregistration's external search results are attributed to its authors and were not independently reproduced. The 2017 v2 TeX quotations and their locations were checked directly.

The statements in “Argued, not formalized” are not additional formalized conclusions. The family-wide violation and unboundedness argument, failure of concavity as a separately stated proposition, restricted concavity, Gaussian-state calculation, reformulation equivalences and consequences for dependent claims are not the type of `result`.

The correspondence of Gaussian phase-space densities with physical Gaussian density operators, coherent-state mixtures and symmetrized quadrature moments is not formalized in this module. No conclusion about the inequality on all pure states, the separate joint Wigner-entropy conjecture, a separate $n>1$ case or states with negative Wigner functions is supplied by `result`. The source's numerical tests and variational calculations were read but not reproduced.

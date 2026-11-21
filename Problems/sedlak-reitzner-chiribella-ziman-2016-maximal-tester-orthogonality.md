---
slug: sedlak-reitzner-chiribella-ziman-2016-maximal-tester-orthogonality
bibkey: sedlakreitznerchiribellaziman2016testers
doi: 10.1103/PhysRevA.93.052323
url: https://arxiv.org/abs/1511.00976v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/AncillaFreeTesterRobustnessEquality.testerRobustness
---

# Maximal incompatibility of one-step testers forces orthogonal normalizations

## Problem

M. Sedlák, D. Reitzner, G. Chiribella and M. Ziman ask at the end of §V.C of *Incompatible measurements on quantum causal networks*, Phys. Rev. A 93, 052323 (2016), v2 p. 10, `ti_pra_07.tex` line 701. [Paper](https://arxiv.org/pdf/1511.00976v2#page=10) · [Library note](../Library/Observer/sedlakreitznerchiribellaziman2016testers.md)

> In summary, we have seen that  orthogonal  testers  are always maximally incompatible.   It is an open problem whether maximally incompatible testers must be orthogonal.

For positive integers $d_0,d_1,p,q$, let $A=(A_j)_{j\in\operatorname{Fin}(p)}$ and $B=(B_k)_{k\in\operatorname{Fin}(q)}$ be complex one-step testers on output dimension $d_1$ and input dimension $d_0$. Their effects are positive semidefinite and sum to $I_{d_1}\otimes\rho$ and $I_{d_1}\otimes\sigma$, respectively, for input density matrices $\rho,\sigma$. Use the infimum of $\lambda\in[0,1]$ for which the two mixtures with separate arbitrary testers $E,F$ at common weight $\lambda$ are the marginals of a joint tester. In the preregistered Lean claim the density and tester predicates and the positivity and normalization hypotheses all appear explicitly. The conclusion is the conjunction

$$
\big(R_{\rm t}(A,B)=\tfrac12 \iff \rho\sigma=0\big)
\ \land\
\big(\rho\sigma=0 \iff \forall j,k,\ A_jB_k=0\big).
$$

The effectwise equivalence is Proposition 12. The source proves the implication from orthogonality to maximal incompatibility. ElonSG preregistered the conjunction, including the requested converse, in trureturing on 2026-10-30. [Preregistration #24241](https://github.com/the-omega-institute/trureturing/issues/24241)

## Motivation

The criterion determines when the universal noise weight $1/2$ is required from the input normalization states alone, across all positive dimensions and finite nonempty outcome sets. The formalization reuses the frozen tester, compatibility and robustness definitions. The same definitions are used in the already merged §VI.C equality for common-normalization ancilla-free testers and their canonical POVMs. [§VI.C dossier](sedlak-reitzner-chiribella-ziman-2016-ancilla-free-tester-robustness.md) · [Merged PR #23794](https://github.com/the-omega-institute/trureturing/pull/23794)

## Gap

The source leaves the converse open for general one-step effects with separate arbitrary noise testers. Jointly diagonal testers in §V.D, Proposition 13, and the strict finite-dimensional bound for a common normalization in §VI.B give restricted cases. The two normalizations and the effects in §V.C can be noncommuting. [Paper](https://arxiv.org/pdf/1511.00976v2#page=10)

## Route

Ragini–Sazim (2024) give a covering SDP for tester incompatibility in Appendix A, especially (A18)–(A28). Its one-step primal has positive joint entries $C_{jk}$ with row and column sums dominating $A_j$ and $B_k$, and total $I_{d_1}\otimes H$. It minimizes the trace of the scaled input normalization $H$. With their additive noise parameter $r=\lambda/(1-\lambda)$, the covering objective is $1+r=1/(1-\lambda)$. Issue #24241 already gives a proof of the converse by dual saturation in this cover at objective $2$. [Ragini–Sazim](https://doi.org/10.1088/1367-2630/ad93f6) · [Preregistration #24241](https://github.com/the-omega-institute/trureturing/issues/24241)

The Lean proof constructs a feasible cover directly. For $M\ge p^2,q^2$ and $0\le\varepsilon\le\min(1/p,1/q)$, it sets

$$
C_{jk}=\frac{A_j}{q}+\frac{B_k}{p}
  -\varepsilon(A_jB_k+B_kA_j)+\frac{M\varepsilon^2}{pq}I,\qquad
H=\rho+\sigma-\varepsilon(\rho\sigma+\sigma\rho)+M\varepsilon^2 I_{d_0}.
$$

Here the identity in each entry acts on output times input. The entry estimate uses positivity of the square of the difference of two Hermitian effects. The row and column estimates use positive sandwiches and the quadratic correction. With $t=\operatorname{Re}\operatorname{tr}H$, the cover yields compatibility at $1-t^{-1}$. For $t>1$, divide the cover by $t$ to get a joint tester and divide the two marginal slacks by $t-1$ to get the noise testers. At $t=1$ the slacks vanish and the cover already gives compatibility at zero.

For $\rho\sigma\ne0$, write $\delta=\operatorname{Re}\operatorname{tr}(\rho\sigma)>0$, set $M=\max(p,q)^2$ and choose $\varepsilon=\delta/(M d_0)$. The resulting live estimate is

$$
t=2-\frac{\delta^2}{\max(p,q)^2 d_0},\qquad
1\le t,\qquad R_{\rm t}(A,B)\le 1-t^{-1}<\tfrac12.
$$

This is `nonorthogonal_upper_bound`, which `result` uses to rule out maximality for nonorthogonal normalizations. Taking $\varepsilon=0$ gives compatibility at $1/2$. For orthogonal normalizations, the support and kernel projections of $\rho$ bound the trace of any joint normalization below by $2(1-\lambda)$, forcing $\lambda\ge1/2$. Positivity and the tester sum identities give the effectwise equivalence. The constructive proof works with actual witnesses and the infimum definition of robustness.

## Falsifier

A counterexample to the requested implication would be a finite pair of positive tester families with the indicated normalized sums, $\rho\sigma\ne0$, and a certified $R_{\rm t}(A,B)=1/2$ for separate arbitrary noise testers. Under those same hypotheses the displayed upper bound supplies a feasible weight strictly below $1/2$.

## Evidence

The source locator and wording were checked against the v2 TeX. The independently compiled constructive source reports only `propext`, `Classical.choice` and `Quot.sound` for `result`, the explicit cover, the cover-to-compatibility conversion, the strict bound and the effectwise equivalence. [Source TeX](https://arxiv.org/e-print/1511.00976v2)

An independent bounded check dated 2026-11-20 UTC screened citing records from Semantic Scholar and INSPIRE, targeted arXiv searches and public project records. It found the published Ragini–Sazim framework and the prior SDP proof of the converse in #24241. The screened publications contained no explicit statement and resolution of the unrestricted §V.C converse, and the public project records contained no merged exact result. Jenčová–Plávala (2020), §VI, Proposition 3 classifies binary measurements on qubit channels in the general probabilistic theory (GPT) framework, where effects are compared by their statistics on deterministic channels. Sedlák et al. require joint marginals equal to the fixed tester operators. For example, effects that are scalar multiples of each tester's normalization lift can give constant outcome distributions with a joint GPT measurement while orthogonal input states give operator-tester robustness one half. [Jenčová–Plávala](https://doi.org/10.1103/PhysRevA.102.042208) · [Preregistration #24241](https://github.com/the-omega-institute/trureturing/issues/24241)

## Triage

Theorem, with `admission_basis: open-problem-resolution`. The `Proved` resolution maps to `Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality.result : claim`, at GID `D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality.result`. The explicit cover, witness conversion and strict quantitative estimate are on the derivation path of the resolution.

## ASSUMED-UNVERIFIED

The literature finding is bounded to the records checked. Some index queries were rate-limited, and some citing records could be screened only by metadata. The status of unpublished work and worldwide literature priority remain unverified.

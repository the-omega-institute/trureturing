# Compact Pseudo-Orbit Selectors

## Abstract

Compactness gives a finite error window for a continuous true-orbit retraction, and exact shift equivariance turns it into global and two-sided limit shadowing for one fixed map.

For a compact metric space M and homeomorphism f, e(x,i)=dist(x(i+1),f(x(i))) and P_delta={x:Z->M : e(x,i)<=delta for every integer i}. Space is the entire closed subtype of the product topology. The sequence space is not assigned a replacement metric. These conventions and the continuous true-orbit-fixing map are those of Alfonso Artigue, Shadowing maps, arXiv:2504.00171v1, Sections 2.1 and 2.2. The compactness argument below is a separate derivation; no novelty or resolution of the converse of Proposition 5.2 is asserted.

Each link error is continuous. The domain is the intersection of its closed sublevel sets, hence is closed and compact. shift(k) is the homeomorphism x(i) to x(k+i), with inverse shift(-k), on that same domain. orbit(f,p)(i)=(f^i)(p) uses integer powers of the homeomorphism, so negative times are included. Its zero coordinate is p, its next coordinate is f of the current one, its shifts are true orbits of the corresponding iterates, and it lies in P_delta whenever delta>=0. A full sequence with every error zero equals the true orbit of its zero coordinate.

In the displayed statements, Space(f,delta)=P_delta, trueOrbit(f,delta,p) is the true orbit included in that domain, and inclusion(gamma,delta,x) is the continuous inclusion P_gamma to P_delta when gamma<=delta. TendstoCofiniteZero(g) means Tendsto g cofinite (nhds 0). The function e(x) sends i to e(x,i), and tracingError(f,Q,x) sends i to dist((f^i)(Q(x)),x(i)).

**Theorem 1.1 (A finite edge window derived from compactness).**

$$\begin{aligned}\forall M: Type, [\operatorname{MetricSpace}(M)] [\operatorname{CompactSpace}(M)]\\\forall f: \operatorname{Homeomorph}(M, M), \forall delta\in \mathbb{R}, \\(0\le delta) \Rightarrow\\\forall Q: \operatorname{Space}(f, delta)\to M, \\(\operatorname{Continuous}(Q)) \Rightarrow\\(\forall p\in M, \operatorname{Q}(\operatorname{trueOrbit}(f, delta, p))= p) \Rightarrow\\\forall eps\in \mathbb{R}, eps> 0\Rightarrow\exists T\in \mathbb{N}, \exists eta\in \mathbb{R}, 0< eta\land \forall x\in \operatorname{Space}(f, delta), \\(\forall i\in \mathbb{Z}, \operatorname{natAbs}(i)\le T\Rightarrow \operatorname{e}(x, i)\le eta) \Rightarrow\\\operatorname{dist}(\operatorname{Q}(x), \operatorname{x}(0))< eps\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alfonso Artigue (2025). *Shadowing maps*. URL: <https://arxiv.org/abs/2504.00171v1>.

*Commentary.*

The tolerance eta and natural window radius T depend on eps and the fixed selector, not on the sequence. Assuming failure, choose x(n) with all errors in radius n at most 1/(n+1) and discrepancy at least eps. CompactSpace.tendsto_subseq applies to the closed subtype: a countable product of metric spaces is first countable. For each fixed integer edge, the increasing subsequence index eventually contains that edge in the tested window. Continuity of the link error and convergence of the reciprocal bounds force its limit to be zero. The limit is therefore a genuine bi-infinite orbit. Continuity of Q and its true-orbit identity force the limiting discrepancy to zero, contradicting eps>0. Compactness proves the window; no local-window or shadowing condition is assumed.

**Theorem 1.2 (The same window at every integer center).**

$$\begin{aligned}\forall M: Type, [\operatorname{MetricSpace}(M)] [\operatorname{CompactSpace}(M)]\\\forall f: \operatorname{Homeomorph}(M, M), \forall delta\in \mathbb{R}, \\(0\le delta) \Rightarrow\\\forall Q: \operatorname{Space}(f, delta)\to M, \\(\operatorname{Continuous}(Q)) \Rightarrow\\(\forall p\in M, \operatorname{Q}(\operatorname{trueOrbit}(f, delta, p))= p) \Rightarrow\\(\forall x\in \operatorname{Space}(f, delta), \operatorname{Q}(\operatorname{shift}(1, x))= \operatorname{f}(\operatorname{Q}(x))) \Rightarrow\\\forall eps\in \mathbb{R}, eps> 0\Rightarrow\exists T\in \mathbb{N}, \exists eta\in \mathbb{R}, 0< eta\land \forall x\in \operatorname{Space}(f, delta), \forall k\in \mathbb{Z}, \\(\forall i\in \mathbb{Z}, \operatorname{natAbs}(i)\le T\Rightarrow \operatorname{e}(x, k+i)\le eta) \Rightarrow\\\operatorname{dist}(\operatorname{orbit}(f, \operatorname{Q}(x), k), \operatorname{x}(k))< eps\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.finite_window_all_times` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the one-step identity Q(shift(1,x))=f(Q(x)) is assumed. Integer induction, using invertibility for the negative step, proves Q(shift(k,x))=(f^k)(Q(x)) for every integer k. Apply the compactness window to shift(k,x). Its edge i is the original edge k+i and its zero coordinate is x(k). The input is still an arbitrary member of the same full P_delta, with no condition on errors outside the tested window.

**Theorem 1.3 (Global and limit tracing by one fixed selector).**

$$\begin{aligned}\forall M: Type, [\operatorname{MetricSpace}(M)] [\operatorname{CompactSpace}(M)]\\\forall f: \operatorname{Homeomorph}(M, M), \forall delta\in \mathbb{R}, \\(0< delta) \Rightarrow\\\forall Q: \operatorname{Space}(f, delta)\to M, \\(\operatorname{Continuous}(Q)) \Rightarrow\\(\forall p\in M, \operatorname{Q}(\operatorname{trueOrbit}(f, delta, p))= p) \Rightarrow\\(\forall x\in \operatorname{Space}(f, delta), \operatorname{Q}(\operatorname{shift}(1, x))= \operatorname{f}(\operatorname{Q}(x))) \Rightarrow\\(\forall eps\in \mathbb{R}, eps> 0\Rightarrow\exists gamma\in \mathbb{R}, 0< gamma\le delta\land\\\forall x\in \operatorname{Space}(f, gamma), \forall k\in \mathbb{Z}, \operatorname{dist}(\operatorname{orbit}(f, \operatorname{Q}(\operatorname{inclusion}(gamma, delta, x)), k), \operatorname{x}(k))< eps)\land\\(\forall x\in \operatorname{Space}(f, delta), \operatorname{TendstoCofiniteZero}(\operatorname{e}(x))\Rightarrow\\(\forall eps\in \mathbb{R}, eps> 0\Rightarrow\exists N\in \mathbb{N}, \forall k\in \mathbb{Z}, N\le \operatorname{natAbs}(k)\Rightarrow \operatorname{dist}(\operatorname{orbit}(f, \operatorname{Q}(x), k), \operatorname{x}(k))< eps)\land\\\operatorname{TendstoCofiniteZero}(\operatorname{tracingError}(f, Q, x)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.global_and_limit_shadowing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean statement quantifies over Q once, before both conclusions. For global accuracy eps choose gamma=min(delta,eta)>0. Every sequence with all errors <=gamma satisfies the window at every integer center. The statement quantifies directly over every x in P_gamma and evaluates Q on the continuous inclusion into P_delta. Neither Q nor the original domain is reconstructed after choosing eps or x.

For the limit conclusion x is any member of the original P_delta. From cofinite convergence of its errors, choose A with e(x,i)<=eta whenever natAbs(i)>=A. For natAbs(k)>=A+T and natAbs(i)<=T, the integer triangle inequality gives natAbs(k+i)>=A. The all-center window therefore bounds the tracing error at k by eps. Finite exceptional sets of integers are equivalent to a sufficiently large natAbs threshold; this converts the explicit tail conclusion back to cofinite convergence. The same map thus satisfies the L-shadowing-map implication on every smaller global tolerance, while the two-sided limit conclusion holds on its entire original domain. Infinitely many, or all, errors may be nonzero.

This module assumes the existence of a continuous orbit retraction with exact shift equivariance. It does not construct the interval retraction R, the perturbed map T, or the every-rho witnesses against self-tuning. The original self-tuning distance remains the sum over all integer i of mu^natAbs(i) times dist(x(i),y(i)); no result about that weighted scalar or the full converse counterexample is supplied here.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.finite_window`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.finite_window_all_times`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector.global_and_limit_shadowing`

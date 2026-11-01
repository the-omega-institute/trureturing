# Finite polynomial deformation retraction

## Abstract

The finite basic perturbation lemma transfers an actual square-zero differential through an actual contraction, with polynomial corrections and explicit primitives.

**Theorem 1.1 (The full finite perturbation inference).**

Lean statement: `D5/S3/HomologicalAlgebra/FinitePerturbation.finite_perturbation`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FinitePerturbation.finite_perturbation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a commutative ring, U and V R-modules, d0,h,delta endomorphisms of V, i:U to V and p:V to U linear. Assume d0 squared is zero, pi is identity, d0 i and p d0 are zero, d0 h+h d0=1-ip, h squared=hi=ph=0, and the actual operator D=d0+delta squares to zero. For N at least one, assume only (h delta)^N=0. Then (delta h)^(N+1)=delta(h delta)^N h=0.

Set K=sum from j=0 to N-1 of (-h delta)^j and J=sum from j=0 to N of (-delta h)^j. Both inverse identities hold for K and 1+h delta, and for J and 1+delta h. Moreover Kh=hJ and delta K=J delta. Composition is from right to left; H is Kh=hJ. Set I=Ki, P=pJ, H=Kh, dU=p delta Ki. The conclusions are dU squared=0, DI=I dU, PD=dU P, PI=1, DH+HD=1-IP, H squared=0, HI=0, and PH=0. The zero module and arbitrary dimensions are allowed. No convergence, inverse existence axiom or finiteness of V is used.

The inference is the classical basic perturbation lemma of Gugenheim, Lambe and Stasheff, not a mathematical novelty claim. The reusable content is the noncommutative identity d0 T+T d0+T(ip)T=0 for T=delta K=J delta, obtained by multiplying its residual on the left by 1+delta h and on the right by 1+h delta and cancelling the proved finite inverses. Geometric sums reuse Mathlib. In a relative BRST application, the original carrier, square-zero differential, quartet contraction, termination bound and degree argument must all be supplied by their actual constructions. This theorem asserts no no-ghost result, Monster construction, physical positivity, string dynamics or spacetime reconstruction.

**Definition 1.2 (Explicit lifts, primitives and boundary detection).**

Lean statement: `D5/S3/HomologicalAlgebra/FinitePerturbation.Conclusion`

*Formalization.* `D5/S3/HomologicalAlgebra/FinitePerturbation.Conclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the same input identities and nilpotence bound, if the constructed dU is zero, every Iu is closed and P(Iu)=u. For every closed x, x-I(Px)=D(Hx). Such an x is in the image of D exactly when Px=0; the reverse implication uses the explicit primitive Hx. Thus the maps identify cohomology representatives without assuming a cohomology result. The physical claim that dU vanishes remains an application obligation.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FinitePerturbation.Conclusion`
- Truth anchor: `D5/S3/HomologicalAlgebra/FinitePerturbation.finite_perturbation`

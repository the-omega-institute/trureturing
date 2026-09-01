# Local Euler Transition Non-Reconstruction

## Abstract

Local Euler determinants do not determine cross-prime frame transitions.

**Theorem 1.1 (Local determinants forget frame transitions).**

$$\forall chi \in Nat.Primes \to \operatorname{Complex}\left(\right),\; \operatorname{let} p_2: Nat.Primes = \operatorname{prime}\left(2\right), \operatorname{let} p_3: Nat.Primes = \operatorname{prime}\left(3\right), \operatorname{let} localOperator: Nat.Primes \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) = (p: Nat.Primes \mapsto \operatorname{diagonal}\left((branch: \operatorname{Fin}\left(2\right) \mapsto \operatorname{ite}\left(branch = 0, 1, chi\left(p\right)\right))\right)), \exists firstFrame \in Nat.Primes \to \operatorname{GL}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right), secondFrame \in Nat.Primes \to \operatorname{GL}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right),\; \left(\forall p \in Nat.Primes, x \in \operatorname{Complex}\left(\right),\; \operatorname{det}\left(\operatorname{identityMatrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) - \operatorname{smul}\left(x, firstFrame\left(p\right) \cdot localOperator\left(p\right) \cdot \operatorname{inverse}\left(firstFrame\left(p\right)\right)\right)\right) = \left(1 - x\right) \cdot \left(1 - x \cdot chi\left(p\right)\right)\right) \land \left(\left(\forall p \in Nat.Primes, x \in \operatorname{Complex}\left(\right),\; \operatorname{det}\left(\operatorname{identityMatrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Complex}\left(\right)\right) - \operatorname{smul}\left(x, secondFrame\left(p\right) \cdot localOperator\left(p\right) \cdot \operatorname{inverse}\left(secondFrame\left(p\right)\right)\right)\right) = \left(1 - x\right) \cdot \left(1 - x \cdot chi\left(p\right)\right)\right) \land \operatorname{inverse}\left(firstFrame\left(p_3\right)\right) \cdot firstFrame\left(p_2\right) \ne \operatorname{inverse}\left(secondFrame\left(p_3\right)\right) \cdot secondFrame\left(p_2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction.local_euler_determinants_do_not_determine_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local operator at every prime is the diagonal two-branch operator with eigenvalues one and chi at that prime.

Two general-linear frame families produce the same local Euler determinant for every prime and scalar parameter, while their inverse-frame transition products from the smallest prime two to the next prime three are unequal.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction.local_euler_determinants_do_not_determine_transition`

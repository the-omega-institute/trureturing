# A Global Characteristic Obstruction for Carlitz Five-Orbits

## Abstract

A constructed integer in the closed-five-orbit ideal confines every prime characteristic.

The residual is the actual nested Carlitz residual already defined in CarlitzFiveOrbit. A ring endomorphism sigma is iterated by composition. The theorem keeps every field, every prime characteristic and every closed five-orbit in its quantified domain.

**Theorem 1.1 (The finite characteristic support forced by all five equations).**

$$\forall K \in \operatorname{Type}\left(\right), (\operatorname{Field}\left(K\right)) \Rightarrow (\forall p \in \mathbb{N}, ((\operatorname{CharP}\left(K, p\right)) \land (\operatorname{NatPrime}\left(p\right))) \Rightarrow (\forall sigma \in \operatorname{RingHom}\left(K, K\right), \forall theta \in K, ((\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right)\right)\right) = theta) \land (\operatorname{residual}\left(\operatorname{sigma}\left(theta\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right) - theta, \operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(\operatorname{sigma}\left(theta\right)\right)\right)\right) - theta\right) = 0)) \Rightarrow (p \mid 8 \cdot 25 \cdot 19 \cdot 263 \cdot 519555805809266011)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FunctionField/CarlitzFiveCharacteristic.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every field K and natural prime p with CharP K p, every ring endomorphism sigma of K, and every theta in K, assume sigma^5(theta)=theta and the residual at sigma^i(theta)-theta, i=1,2,3,4, is zero. Then p divides 8*25*19*263*519555805809266011. Primality of the last explicit factor is not a premise or conclusion of this theorem.

Applying sigma supplies the other four cyclic-origin residual equations. An explicitly authored degree-ten integer polynomial with 508 terms has a cyclic weighted residual sum equal to 4673196650932024062540600. Ring normalization verifies the integer identity. Its factorization has an extra factor nine, which is removed by a second 340-term cyclic certificate equal to one in characteristic three.

Both certificates enter the deduction. Neither a Groebner-basis result, a list of tested characteristics, nor the desired characteristic support is assumed. The conclusion is a global exclusion statement for the literal orbit equations, not an extrapolation from a scan.

The unified Wieferich dossier gives additional ordinary proofs of the two newly constructed characteristic families and their exact extension-degree classes. Those conclusions are separate from this theorem. The integer Wall-Sun-Sun existence problem remains a separate unresolved subproblem within the same lifting-and-elimination family.

## References

- Truth anchor: `D5/S3/Arith/FunctionField/CarlitzFiveCharacteristic.result`
- Dependency: [D5/S3/Arith/FunctionField/CarlitzFiveOrbit](CarlitzFiveOrbit.md)

# Global and Local Pell Behavior

## Abstract

A concrete Pell orbit is globally unbounded and locally pure-periodic.

**Theorem 1.1 (A concrete Pell orbit is globally unbounded).**

$$u = \operatorname{PellOrbit}\left(3, 2, 1, (1, 0)\right), \forall N \in \mathbb{N}, \exists n \in \mathbb{N}, \exists i \in \operatorname{Fin}\left(2\right), N < {u_{n}}_{i}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.sqrt_three_pell_orbit_is_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the multiplication matrix of 2 + sqrt(3) and start at the integral seed (1, 0). Its second coordinate is the standard Pell y-sequence from pinned Mathlib.

Mathlib's lower bound n <= y_n supplies a coordinate above every prescribed natural bound, without a limit or a new induction proving growth.

**Lemma 1.2 (The unit one orbit is a necessary degeneracy).**

$$\neg\operatorname{OrbitUnbounded}\left(\operatorname{PellOrbit}\left(3, 1, 0, (1, 0)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.unit_one_pell_orbit_is_not_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit coordinates (1, 0), the Pell multiplication matrix is the identity. Starting from the nonzero seed (1, 0) therefore gives a constant orbit, which is not unbounded.

**Theorem 1.3 (Global growth and local cycles coexist).**

$$u = \operatorname{PellOrbit}\left(3, 2, 1, (1, 0)\right), \operatorname{OrbitUnbounded}\left(u\right) \land \forall p, k \in \mathbb{N}, \operatorname{Prime}\left(p\right) \Rightarrow \exists T \in \mathbb{N}, 0 < T \land \forall n \in \mathbb{N}, \forall i \in \operatorname{Fin}\left(2\right), \operatorname{mod}\left({u_{n + T}}_{i}, p^{k}\right) = \operatorname{mod}\left({u_{n}}_{i}, p^{k}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.global_unboundedness_and_prime_power_local_periodicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct is the global unboundedness result for the single named integer matrix orbit.

For every prime p and exponent k, reduction of that same orbit modulo p^k is identified with the mapped matrix orbit. The existing local Pell periodicity theorem then gives a positive pure period, including p = 2 and k = 0.

## References

- Truth anchor: `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.global_unboundedness_and_prime_power_local_periodicity`
- Truth anchor: `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.sqrt_three_pell_orbit_is_unbounded`
- Truth anchor: `D5/S3/PrimeForms/PellFamilies/GlobalPellUnboundedness.unit_one_pell_orbit_is_not_unbounded`
- Dependency: [D5/S3/PrimeForms/PellFamilies/LocalPellPeriodicity](LocalPellPeriodicity.md)

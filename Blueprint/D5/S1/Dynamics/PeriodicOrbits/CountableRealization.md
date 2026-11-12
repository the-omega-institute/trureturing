# Countable and signed realization

## Abstract

Actual countable cycles realize all positive indices simultaneously.

This construction extends the existing finite divisor-table supplier to a single all-length carrier. It supplies the cycle-realization step required by the complete Jaidee manuscript, but the actual block valuation/transform identification, bounded half-residue arithmetic and formal zeta Euler identities need their own proofs. See the complete scope and attribution in `D5/L/Scale/jaidee2026blockdold`. The fixed_card registration is declared_validated in its current scoped report. Every other newly authored audit target remains unfinished under issue 29392; that status does not cover the other theorems.

**Theorem 1.1 (countable_and_locally_finite).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.countable_and_locally_finite`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.countable_and_locally_finite` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

For every natural multiplicity function c, the single carrier of triples (positive length d, copy j in Fin(c d), phase in ZMod d) is countable. The rotation preserves length and copy and advances the phase. At each positive time n the actual fixed set is finite, via an explicit equivalence to the existing finite divisor carrier for n.

**Theorem 1.2 (fixed_card).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.fixed_card`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.fixed_card` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

For every c and every positive n, the cardinality of the actual fixed set of the nth iterate equals the sum over d dividing n of d*c(d). The same carrier and permutation are used at all indices. At time zero an infinite carrier need not have a finite fixed set; no zero-time claim is made.

**Theorem 1.3 (delta_fixed_card).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.delta_fixed_card`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.delta_fixed_card` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

At each positive n the integer Mobius transform of the actual fixed-point counts equals n*c(n). This uses exact Mobius inversion, not an assumed orbit-count formula.

**Theorem 1.4 (realization_iff).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.realization_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.realization_iff` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

A natural sequence a is realized at every positive time by one canonical countable-cycle permutation if and only if every positive-index integer Mobius transform is nonnegative and divisible by its index. The converse chooses c(d)=delta(a,d)/d using nonnegativity and exact divisibility. This goes beyond a separate finite-prefix or divisor-table model for each bound.

**Theorem 1.5 (finite_carrier_of_support).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.finite_carrier_of_support`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.finite_carrier_of_support` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

If the nonzero multiplicities are supported on divisors of one positive exponent M, the whole carrier is finite by an explicit equivalence to the finite divisor carrier. This supplies actual finite carriers when bounded sample arithmetic establishes finite support.

**Theorem 1.6 (necessary).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.necessary`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.necessary` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

For any map on any type with finite fixed sets at every positive time, the integer Mobius transform of its actual fixed counts is nonnegative and divisible by the index. Neither a finite total carrier nor injectivity nor global countability is assumed. The proof restricts the map to the finite nth fixed set and reuses OrbitCounting; PeriodicRepair consumes this result to exclude all maps for a positive half-residue sample.

**Theorem 1.7 (signed_realization).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.signed_realization`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.signed_realization` (`✓ std3`). ∎

*Citation.* Yash Puri and Thomas Ward (2001). *Arithmetic and growth of periodic orbits*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL4/WARD/short.tex>.

*Commentary.*

Every integer sequence whose Mobius transforms are divisible by their positive indices is the difference of the actual fixed counts of two single countable-cycle permutations, simultaneously at all positive times. The positive and negative parts of the integral orbit quotients give the two multiplicity functions. This does not assert positivity or finite total support.

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.countable_and_locally_finite`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.delta_fixed_card`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.finite_carrier_of_support`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.fixed_card`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.necessary`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.realization_iff`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/CountableRealization.signed_realization`
- Dependency: [D5/S1/Dynamics/PeriodicOrbits/FiniteRealization](FiniteRealization.md)

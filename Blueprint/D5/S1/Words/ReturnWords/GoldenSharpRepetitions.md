# GoldenSharpRepetitions

## Abstract

Uniform replication and golden-word asymptotic invariants.

**Theorem 1.1 (Periodic golden factors).**

$$\forall \operatorname{a}: \operatorname{Nat}, \forall \operatorname{p}: \operatorname{Nat}, \forall \operatorname{L}: \operatorname{Nat}, (\operatorname{GoldenPeriodic} \operatorname{a} \operatorname{p} \operatorname{L})\Rightarrow\forall \operatorname{j}: \operatorname{Nat}, (\operatorname{j} < \operatorname{L})\Rightarrow\operatorname{goldenWord} (\operatorname{a} + \operatorname{j}) = \operatorname{goldenWord} (\operatorname{a} + \operatorname{Nat.mod} \operatorname{j} \operatorname{p})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.periodic_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A letter in a periodic golden factor equals the letter at its residue modulo the period.

**Theorem 1.2 (long period ratio tendsto).**

$$\operatorname{Tendsto} (\operatorname{k} : \operatorname{Nat} \mapsto ((\operatorname{Nat.fib} (\operatorname{k} + 4) + \operatorname{Nat.fib} (\operatorname{k} + 6) - 2 : \operatorname{Nat}) : \operatorname{Real}) / (\operatorname{Nat.fib} (\operatorname{k} + 4) : \operatorname{Real})) \operatorname{atTop} (\operatorname{nhds} (2 + \operatorname{Real.goldenRatio}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.long_period_ratio_tendsto` (`✓ std3`). ∎

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.3 (golden indStar eq sharp).**

$$\operatorname{indStar} \operatorname{goldenWord} = \operatorname{ENNReal.ofReal} (2 + \operatorname{Real.goldenRatio})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_indStar_eq_sharp` (`✓ std3`). ∎

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.4 (orbitCard eq of irrational).**

$$\forall \operatorname{a}: \operatorname{Real}, (\operatorname{Irrational} \operatorname{a})\Rightarrow\forall \operatorname{N}: \operatorname{Nat}, \operatorname{orbitCard} \operatorname{a} \operatorname{N} = \operatorname{N}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.orbitCard_eq_of_irrational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.5 (fract fib odd).**

$$\forall \operatorname{q}: \operatorname{Nat}, (\operatorname{Odd} \operatorname{q})\Rightarrow\operatorname{Int.fract} ((\operatorname{Nat.fib} \operatorname{q} : \operatorname{Real}) \cdot \operatorname{Real.goldenRatio}) = \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.fract_fib_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.6 (fract fib even).**

$$\forall \operatorname{q}: \operatorname{Nat}, (\operatorname{Even} \operatorname{q})\Rightarrow\operatorname{Int.fract} ((\operatorname{Nat.fib} \operatorname{q} : \operatorname{Real}) \cdot \operatorname{Real.goldenRatio}) = 1 - \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.fract_fib_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.7 (golden eta odd).**

$$\forall \operatorname{q}: \operatorname{Nat}, (2 \leq \operatorname{q})\Rightarrow(\operatorname{Odd} \operatorname{q})\Rightarrow\operatorname{etaPos} \operatorname{Real.goldenRatio} (\operatorname{Nat.fib} (\operatorname{q} + 2)) = \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q}} \land \operatorname{etaNeg} \operatorname{Real.goldenRatio} (\operatorname{Nat.fib} (\operatorname{q} + 2)) = \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q} + 1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_eta_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.8 (golden eta even).**

$$\forall \operatorname{q}: \operatorname{Nat}, (2 \leq \operatorname{q})\Rightarrow(\operatorname{Even} \operatorname{q})\Rightarrow\operatorname{etaPos} \operatorname{Real.goldenRatio} (\operatorname{Nat.fib} (\operatorname{q} + 2)) = \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q} + 1} \land \operatorname{etaNeg} \operatorname{Real.goldenRatio} (\operatorname{Nat.fib} (\operatorname{q} + 2)) = \operatorname{Inv.inv}\left(\operatorname{Real.goldenRatio}\right)^{\operatorname{q}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_eta_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.9 (rotation gap length mem threegap).**

$$\forall \operatorname{a}: \operatorname{Real}, \forall \operatorname{N}: \operatorname{Nat}, [\operatorname{Fact} (\operatorname{Irrational} \operatorname{a})],[\operatorname{NeZero} \operatorname{N}],\forall \operatorname{i}: \operatorname{Fin} \operatorname{N}, \operatorname{rotationCut} \operatorname{a} \operatorname{N} \operatorname{i.succ} - \operatorname{rotationCut} \operatorname{a} \operatorname{N} \operatorname{i.castSucc} \in \operatorname{gaps} (- \operatorname{a}) \operatorname{N}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.rotation_gap_length_mem_threegap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.10 (negative returns swap).**

$$\forall \operatorname{a}: \operatorname{Real}, (\operatorname{Irrational} \operatorname{a})\Rightarrow\forall \operatorname{N}: \operatorname{Nat}, (2 \leq \operatorname{orbitCard} \operatorname{a} \operatorname{N})\Rightarrow\operatorname{etaPos} (- \operatorname{a}) \operatorname{N} = \operatorname{etaNeg} \operatorname{a} \operatorname{N} \land \operatorname{etaNeg} (- \operatorname{a}) \operatorname{N} = \operatorname{etaPos} \operatorname{a} \operatorname{N}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.negative_returns_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.11 (golden negative slope orbit).**

$$\forall \operatorname{N}: \operatorname{Nat}, \operatorname{orbit} (- \operatorname{goldenMechanicalSlope}) \operatorname{N} = \operatorname{orbit} (- \operatorname{Real.goldenRatio}) \operatorname{N}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_negative_slope_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.12 (golden slope fract eq).**

$$\forall \operatorname{p}: \operatorname{Nat}, \operatorname{Int.fract} ((\operatorname{p} : \operatorname{Real}) \cdot \operatorname{goldenMechanicalSlope}) = \operatorname{Int.fract} ((\operatorname{p} : \operatorname{Real}) \cdot \operatorname{Real.goldenRatio})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_slope_fract_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

**Theorem 1.13 (golden fibonacci long period exists).**

$$\forall \operatorname{q}: \operatorname{Nat}, (2 \leq \operatorname{q})\Rightarrow\exists \operatorname{a} , \operatorname{D5.S1.Words.Powers.GoldenPeriodic} \operatorname{a} (\operatorname{Nat.fib} \operatorname{q}) (\operatorname{Nat.fib} \operatorname{q} + \operatorname{Nat.fib} (\operatorname{q} + 2) - 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_fibonacci_long_period_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.fract_fib_even`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.fract_fib_odd`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_eta_even`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_eta_odd`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_fibonacci_long_period_exists`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_indStar_eq_sharp`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_negative_slope_orbit`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.golden_slope_fract_eq`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.long_period_ratio_tendsto`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.negative_returns_swap`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.orbitCard_eq_of_irrational`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.periodic_mod`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenSharpRepetitions.rotation_gap_length_mem_threegap`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S0/Tower/GoldenGapWord](../../../S0/Tower/GoldenGapWord.md)
- Dependency: [D5/S1/Deficit/Displacement/GoldenSubstStartSharpness](../../Deficit/Displacement/GoldenSubstStartSharpness.md)
- Dependency: [D5/S1/Recurrence/RotationOrbitGapsPartition](../../Recurrence/RotationOrbitGapsPartition.md)
- Dependency: [D5/S1/Words/Complexity/CassaigneIndexTransport](../Complexity/CassaigneIndexTransport.md)
- Dependency: [D5/S1/Words/Complexity/CassaigneRecurrenceTransport](../Complexity/CassaigneRecurrenceTransport.md)
- Dependency: [D5/S1/Words/FibonacciMapFirstStart](../FibonacciMapFirstStart.md)
- Dependency: [D5/S1/Words/GoldenMechanicalWord](../GoldenMechanicalWord.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/Powers/GoldenCubePeriodsSupport](../Powers/GoldenCubePeriodsSupport.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturn](GoldenArcFirstReturn.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore](GoldenArcFirstReturnCore.md)
- Dependency: [D5/S3/Axis/AxisConvergence](../../../S3/Axis/AxisConvergence.md)

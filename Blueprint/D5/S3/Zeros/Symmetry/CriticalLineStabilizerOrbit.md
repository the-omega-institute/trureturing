# Critical-Line Stabilizers and Off-Line Orbits

## Abstract

Critical localization fixes every mirror index; outside it, a four-point orbit appears without loss of the zero symmetries.

**Theorem 1.1 (Critical localization is stabilizer enlargement).**

$$\forall Z: \operatorname{ZeroData},\ ({\forall n\in \mathbb{N},\ \Re(Z.zero(n)) = \operatorname{criticalAbscissa}} \Leftrightarrow {\forall n\in \mathbb{N},\ Z.conjugation(Z.reflection(n)) = n}) \land (\neg {\forall n\in \mathbb{N},\ \Re(Z.zero(n)) = \operatorname{criticalAbscissa}} \Rightarrow {\exists n\in \mathbb{N},\ \operatorname{card}\{n, Z.reflection(n), Z.conjugation(n), Z.conjugation(Z.reflection(n))\} = 4}) \land \operatorname{Commute}(Z.reflection, Z.conjugation)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/CriticalLineStabilizerOrbit.critical_line_stabilizer_orbit_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each supplied duplicate-free exhaustive ZeroData enumeration, all indexed zeros lie on the critical line exactly when conjugation after reflection fixes every index. If localization does not hold, one indexed zero has the full four-element reflection-conjugation orbit.

The real-unit-interval nonvanishing theorem rules out a conjugation-fixed nontrivial zero, so the existing four-point orbit theorem applies to the off-line witness. Reflection and conjugation commute independently of localization, showing that the complete set symmetry remains present in both alternatives. The statement intentionally uses direct localization of supplied ZeroData rather than a global Riemann-hypothesis proposition.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalLineStabilizerOrbit.critical_line_stabilizer_orbit_dichotomy`
- Dependency: [D5/S3/Analytic/Zeta/RealUnitIntervalZetaNonvanishing](../../Analytic/Zeta/RealUnitIntervalZetaNonvanishing.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZeroOrbitCardinality](ZeroOrbitCardinality.md)

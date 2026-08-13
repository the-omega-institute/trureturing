# Fixed-Modulus Noncongruence of the Golden-Addition Deficit

## Abstract

No fixed modulus at least two determines the golden-addition deficit.

**Theorem 1.1 (Congruent input pairs can have different deficits).**

$$\forall m \geq 2,\quad \exists v_1, v_2, v_1', v_2' \in \mathbb{N},\quad v_1\equiv v_1' (\operatorname{mod} m) \land v_2\equiv v_2' (\operatorname{mod} m),\quad c(v_1, v_2)\neq c(v_1', v_2')$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus m at least two, there are two pairs of natural inputs that agree coordinatewise modulo m but whose normalized golden-addition deficits differ. This strengthens the source's finite certificate for moduli 2 through 60 to a structural theorem for every fixed modulus.

The existing displacement theorem identifies each model-set reading with an integer golden Beatty shift plus a linear conjugate term. The linear terms cancel in the additive coboundary, so the analytic deficit equals the Beatty deficit. Pinned Mathlib then supplies density of irrational multiples on the additive circle. Applying that theorem to the golden rotation restricted to any arithmetic progression produces congruent inputs in a positive-deficit phase interval and in a zero-deficit interval.

This is an honest partial closure of proposition 6.28(ii). It does not formalize the prime-classification blindness interpretation, the zero-slice frequency 1/phi, or the positive-slice frequency 1/phi^2; those independently testable claims remain unresolved and the source atom remains partial and open.

## References

- Truth anchor: `D5/S1/Deficit/FixedModulusNoncongruence.deficit_not_determined_by_fixed_modulus`
- Dependency: [D5/S1/Deficit/DeficitInteger](DeficitInteger.md)
- Dependency: [D5/S1/Deficit/DoubleFaceLength](DoubleFaceLength.md)
- Dependency: [D5/S1/Deficit/GoldenPhaseDeficit](GoldenPhaseDeficit.md)
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](ZeckendorfDisplacementReading.md)

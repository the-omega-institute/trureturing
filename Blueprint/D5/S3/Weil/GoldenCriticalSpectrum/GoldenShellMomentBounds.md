# Golden Shell Moment Bounds

## Abstract

Golden shell membership bounds every nonnegative transverse defect moment between the shell transcript and its one-step rescaling.

**Theorem 1.1 (Golden Shells Bound Transverse Moments).**

$$({\operatorname{goldenShellStep}\left(\right)}^{s} \times \operatorname{G}\left(s\right) \le \operatorname{zetaPerp}\left(s\right)) \land (\operatorname{zetaPerp}\left(s\right) \le \operatorname{G}\left(s\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assign each nonnegative defect multiplicity to the unique golden shell whose adjacent scales enclose that defect. For every nonnegative real exponent, the actual defect moment lies below the shell transcript moment and above its one-shell golden rescaling.

Extended nonnegative real sums retain the statement for infinite index families without adding a convergence hypothesis; the shell membership inequalities are the only external assumptions.

**Theorem 1.2 (A Shell-Zero Singleton Attains One Quarter).**

$$\operatorname{G}\left(2\right) = \frac{1}{4} \land \operatorname{zetaPerp}\left(2\right) = \frac{1}{4}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_valid_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton of multiplicity one at defect one half lies in shell zero. At exponent two, both the transcript moment and the actual defect moment evaluate to one quarter.

This explicit calculation witnesses that the hypotheses and conclusion are simultaneously inhabited.

**Theorem 1.3 (An Outside-Shell Singleton Breaks the Upper Bound).**

$$\operatorname{G}\left(1\right) = \frac{1}{2}, \operatorname{zetaPerp}\left(1\right) = 2, \operatorname{zetaPerp}\left(1\right) > \operatorname{G}\left(1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_outside_shell_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton assigned to shell zero but placed at defect two violates the shell upper endpoint. At exponent one, its actual moment is two while its transcript moment is one half.

The numerical separation shows that the shell membership premise carries mathematical content.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_bounds`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_outside_shell_witness`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenShellMomentBounds.golden_shell_moment_valid_witness`

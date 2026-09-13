# The Closed Form of the Harmonic-Mean-Numerator Recurrence

## Abstract

Stephan's three-residue closed form for the harmonic-mean-numerator recurrence.

**Definition 1.1 (The harmonic-mean-numerator recurrence).**

$$\operatorname{a}\left(0\right) = 0 \land (\operatorname{a}\left(1\right) = 2 \land (\operatorname{a}\left(2\right) = 3 \land \left(\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n + 3\right) = \operatorname{toNat}\left(\operatorname{num}\left(\frac{2 \cdot \operatorname{a}\left(n + 2\right) \cdot \operatorname{a}\left(n + 1\right)}{\operatorname{a}\left(n + 1\right) + \operatorname{a}\left(n + 2\right)}\right)\right)\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.a` (`✓ std3`).

*Citation.* Ralf Stephan (2010). *OEIS A107928, a(n) is the numerator of harmonic mean of a(n-1) and a(n-2)*. URL: <https://oeis.org/A107928>.

*Commentary.*

a(0) = 0 is the offset-1 sentinel; the harmonic mean is taken in the rationals and Rat.num is its reduced numerator. The displayed toNat converts that integer numerator to a natural number.

**Theorem 1.2 (Stephan's three-residue closed form).**

$$\forall m \in \mathrm{Nat},\; 1 \le m \Rightarrow (\operatorname{a}\left(3 \cdot m\right) = 12 \cdot 8^{m - 1} \land (\operatorname{a}\left(3 \cdot m + 1\right) = 3 \cdot 8^{m} \land \operatorname{a}\left(3 \cdot m + 2\right) = 2 \cdot 8^{m}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.stephan_a107928` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a107928-harmonic-mean-numerator-closed-form` (proved) by `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.stephan_a107928`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a107928-harmonic-mean-numerator-closed-form","declaration_gid":"D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.stephan_a107928","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ralf Stephan (2010). *OEIS A107928, a(n) is the numerator of harmonic mean of a(n-1) and a(n-2)*. URL: <https://oeis.org/A107928>.

*Commentary.*

Block induction propagates the pair (a(3m+1), a(3m+2)) = (3*8^m, 2*8^m). The coprime reductions and the block invariant are carried inside the proof. The exponent m-1 uses natural-number subtraction.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.stephan_a107928`

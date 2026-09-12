# Parity of the Iterated-Exponential Family

## Abstract

Every compositional iterate count gives fixed-point EGF coefficients odd exactly at positive odd indices.

The OEIS entries A396803, A396805 and A396806 specify A=X*exp(A^{[k]}) for k=3, 5 and 6, respectively. Here A^{[k]} is the k-fold compositional iterate, not an ordinary power; the zeroth iterate is the identity series X. Each entry carries further residue conjectures that are not proved here.

For natural k, the natural sequence aK(k,n) is the coefficientwise limit of a contracting stage sequence starting at n. Agreement below degree d becomes agreement below degree d+1 after one step, so coefficient n stabilizes at stage n+1. The series AK(k) encodes aK(k,n) as an exponential generating series over Q: its ordinary coefficient at degree n is aK(k,n)/n!. All series are formal; no analytic convergence is asserted.

In the formulas, k and n are natural numbers, f and g are rational power series, constantCoeff extracts the constant coefficient, and iterateComp(f,k) denotes compositional iteration. The expression subst(exp(Q),h) means the exponential series with h substituted for X. A_equation and fixed_unique identify AK(k), and hence its EGF coefficient sequence aK(k,n), with the defining equation's unique zero-constant solution.

**Theorem 1.1 (The defining series equation).**

$$\forall k: \mathbb{N}, (\operatorname{constantCoeff}\left(\operatorname{AK}\left(k\right)\right) = 0) \land (\operatorname{AK}\left(k\right) = X * \operatorname{subst}\left(\operatorname{exp}\left(\mathbb{Q}\right), \operatorname{iterateComp}\left(\operatorname{AK}\left(k\right), k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.A_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, AK(k) has constant coefficient zero and satisfies A=X*exp(A^{[k]}). The stabilized coefficient sequence is a fixed point of the integral coefficient transformation.

**Theorem 1.2 (Uniqueness of the formal solution).**

$$\forall k: \mathbb{N}, \forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall g: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(f\right) = 0) \implies ((\operatorname{constantCoeff}\left(g\right) = 0) \implies ((f = X * \operatorname{subst}\left(\operatorname{exp}\left(\mathbb{Q}\right), \operatorname{iterateComp}\left(f, k\right)\right)) \implies ((g = X * \operatorname{subst}\left(\operatorname{exp}\left(\mathbb{Q}\right), \operatorname{iterateComp}\left(g, k\right)\right)) \implies (f = g))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.fixed_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two rational series with zero constant coefficient satisfying the equation agree in every degree by contraction. In particular, each such series equals AK(k), which A_equation supplies.

**Theorem 1.3 (Parity for every iterate count).**

$$\forall k: \mathbb{N}, \forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{aK}\left(k, n\right)\right) \iff \operatorname{Odd}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.odd_iff_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural iterate count and positive index n, aK(k,n) is odd exactly when n is odd. The coefficient transformation preserves the sequence n modulo two, and induction carries this congruence through all stages to the stabilized sequence.

**Theorem 1.4 (A396803 parity).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{aK}\left(3, n\right)\right) \iff \operatorname{Odd}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_three` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396803-iterate-exponential-parity` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_three`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396803-iterate-exponential-parity","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_three","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396803, A396805 and A396806: iterated-exponential parity*. URL: <https://oeis.org/A396803>.

*Commentary.*

Specializing odd_iff_odd at k=3 proves the positive-index parity conjecture for the third compositional iterate. The further residue conjecture modulo three is not proved here.

**Theorem 1.5 (A396805 parity).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{aK}\left(5, n\right)\right) \iff \operatorname{Odd}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_five` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396805-iterate-exponential-parity` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_five`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396805-iterate-exponential-parity","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_five","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396805: iterated-exponential parity at iterate count 5*. URL: <https://oeis.org/A396805>.

*Commentary.*

Specializing odd_iff_odd at k=5 proves the positive-index parity conjecture for the fifth compositional iterate. The further residue conjectures modulo three and five are not proved here.

**Theorem 1.6 (A396806 parity).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((\operatorname{Odd}\left(\operatorname{aK}\left(6, n\right)\right) \iff \operatorname{Odd}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_six` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396806-iterate-exponential-parity` (proved) by `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_six`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396806-iterate-exponential-parity","declaration_gid":"D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_six","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396806: iterated-exponential parity at iterate count 6*. URL: <https://oeis.org/A396806>.

*Commentary.*

Specializing odd_iff_odd at k=6 proves the positive-index parity conjecture for the sixth compositional iterate. The further residue conjectures modulo three and six are not proved here.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.A_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.fixed_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.odd_iff_odd`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_five`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_six`
- Truth anchor: `D5/S1/Recurrence/Residue/IterateExponentialParity.parity_iterate_three`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFModFour](QuarticEGFModFour.md)

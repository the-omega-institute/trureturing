# Conjugate Reflection and Scaling

## Abstract

Conjugate reflection reverses scaling entries around the critical line.

**Proposition 1.1 (Mirror fixed points lie on the critical line).**

$\forall s\in\mathbb{C},\ \operatorname{mirror}(s)=s \Rightarrow \Re(s)=\frac{1}{2}$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate reflection sends a spectral parameter to one minus its conjugate. Every fixed point therefore has real part one half; no zero-location claim is made.

**Theorem 1.2 (The mirror reverses every scaling entry).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ (\forall a,\operatorname{scalingLedger}(\ell,\operatorname{mirror}(s),a)=-\operatorname{scalingLedger}(\ell,s,a)) \land (s=\operatorname{mirror}(s) \Leftrightarrow \Re(s)=\frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the entry given by displacement from one half times ledger length, mirroring negates every coordinate. The same theorem identifies the full fixed locus.

**Remark 1.3 (A symmetry channel is not a location force).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reflection identifies the critical fixed line and can serve as a channel for spectral comparisons. It is not a force that places zeros on that line; positivity and the open analytic obligations remain separate.

**Remark 1.4 (Symmetry does not force fixed points).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Invariance under the mirror permits two-cycles away from the fixed line. The checked coordinate reversal supplies pairing symmetry but no positivity argument, self-adjoint realization, or zero-location result.

**Remark 1.5 (Fixed line versus orbit collapse).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real part one half is exactly the fixed locus of the mirror. Interpreting the Riemann hypothesis as collapse of every zero orbit to that locus is a classification of the open problem, not a conclusion of the fixed-point theorem.

**Remark 1.6 (Set invariance versus pointwise invariance).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mirror reversal can preserve a collection while exchanging its members. Even and odd combinations may change phase conventions, but they do not turn set-level symmetry into the pointwise fixedness needed for a critical-line conclusion.

**Remark 1.7 (Antilinear reflection produces a line).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Combining conjugation with reflection gives an antiholomorphic involution whose fixed locus is the entire critical line rather than a single real point. The theorem establishes that stage; it does not establish that a zero lies on it.

**Remark 1.8 (An invariant set need not lie in the fixed locus).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mirror-stable pair may have neither member fixed. This elementary distinction is the precise gap between a symmetric zero inventory and the assertion that every zero has real part one half.

**Remark 1.9 (Scaled midline reading).**

Lean statement: `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq`

*Formalization.* `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive rescaling transports the half-density coordinate to a correspondingly scaled midline. This is an interpretive coordinate change: the checked declaration proves only the original mirror fixed locus and makes no claim about quasiperiodic zeta zeros, structural zeros, or denominator safety.

**Remark 1.10 (Three order-two mechanisms have different sources).**

$$
\operatorname{J}\left(s\right) = 1 - \operatorname{conj}\left(s\right)
$$

*Source.* Repository-derived.

*Commentary.*

The source distinguishes three independent appearances of two. Complex conjugation supplies the code-blind pair behind J(s) = 1-conj(s), squared modulus, and the coefficient inner product. The real Galois pair phi <-> psi supplies the code-specific integrality of the deficit. Additive multiplicity two, through the double-occupancy prohibition, supplies the denominator zeta(2*phi^2*s). Replacing Fibonacci by Tribonacci is reported to preserve the half-line while destroying integrality, so the conjugation and Galois mechanisms are independently replaceable. All three are order-two structures, but only the first two are compared through fixed sets: the critical midline is fixed by the complex involution, while the integers are fixed by the real conjugation. The source consequently reads ontological zeros on the midline and integral deficits as parallel fixed-point statements, and places their intersection where the quasiperiodic critical line meets the multiplicity pole, one deficit unit from its carry image.

## References

- Truth anchor: `D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq`
- Truth anchor: `D5/S3/Weil/ReflectionLedger.mirror_reversal_spec`
- Dependency: [D5/S3/Weil/LabeledZeta](LabeledZeta.md)

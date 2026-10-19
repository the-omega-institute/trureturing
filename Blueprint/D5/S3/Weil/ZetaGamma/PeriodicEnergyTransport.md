# Periodic energy transport

## Abstract

Original half-open interval L2 data transport through the actual circle, correlations and noncentral image lattice.

For d,t real put I=(t,t+d], windowMeasure(d,t)=Lebesgue measure restricted to I, zeroExtension=1_I*u, periodicExtension(x)=AddCircle.liftIoc(d,t,u)(x mod d), and windowEnergy=integral_I |u|^2. The two translation energies integrate |z(x)-z(x-s)|^2 over the real line and |u(x)-v(x-s)|^2 over I, respectively. The correlations use conjugate(z(x))*z(x-s) and conjugate(u(x))*v(x-s).

For an arbitrary real weight w, weightedDifferenceCorrelation(x,s) is w(s)*conjugate(u(x))*(v(x-s)-z(x-s)). The image kernel is the sum of w(x-y+m*d) over all nonzero integers m. Its reflection and Fubini helpers, the unique-copy norm and absolute-sum identities, and the L2 difference expansions are consumed by the actual periodic Gamma comparison.

**Theorem 1.1 (periodic minus zero norm le).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_minus_zero_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_minus_zero_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive period d, base point t, complex function u and real z, removing the central zero-extension copy has norm at most the actual periodic-extension value. No measurability or endpoint-value hypothesis is used.

**Theorem 1.2 (copyReflection measurePreserving).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.copyReflection_measurePreserving`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.copyReflection_measurePreserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real d and t and integer m, the involution (x,y) maps to (x,x+m*d-y) and preserves windowMeasure(d,t) times Lebesgue measure. It is the same reflection used for every lattice copy and for the central copy.

**Theorem 1.3 (windowMeasure prod windowMeasure).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.windowMeasure_prod_windowMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.windowMeasure_prod_windowMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d and t, the product of the two window measures equals windowMeasure(d,t) times Lebesgue measure restricted to R times (t,t+d]. This pays the second physical-window restriction exactly.

**Theorem 1.4 (weightedLattice image integrable and identity).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.weightedLattice_image_integrable_and_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.weightedLattice_image_integrable_and_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, arbitrary t, a real weight w and a complex function u, assume the weighted difference correlation is integrable on the physical window times the real shift line. Then the full noncentral image pairing is integrable on the window square and its integral equals that actual weighted difference-correlation integral. The coefficient of this Hermitian image pairing is one. The proof uses the unique half-open copy, absolute Tonelli, the same measure-preserving reflection on each copy, and absolutely summable Fubini. Its weightedImageKernel sums every nonzero integer image; it omits only the zero image.

**Theorem 1.5 (periodic shift memLp).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive period d and arbitrary base point t, interval MemLp(u,2) implies interval MemLp of x mapping to the actual periodic extension at x-s, for every real displacement s. Haar translation is transported by AddCircle.liftIoc; the original representative needs no global measurability.

**Theorem 1.6 (periodic correlation integrable le).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_correlation_integrable_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_correlation_integrable_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and interval MemLp(u,2), the product |u(x)| times |periodicExtension(d,t,u,x-s)| is integrable on the original window and its integral is at most windowEnergy(d,t,u), for every real s. The measure has physical mass d and is not normalized to one.

**Theorem 1.7 (periodic shift joint aestronglyMeasurable).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_joint_aestronglyMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_joint_aestronglyMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and interval MemLp(u,2), the map (x,s) mapping to periodicExtension(d,t,u,x-s) is AE strongly measurable on windowMeasure(d,t) times Lebesgue measure.

**Theorem 1.8 (zero shift joint aestronglyMeasurable).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zero_shift_joint_aestronglyMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zero_shift_joint_aestronglyMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d and t and interval MemLp(u,2), the map (x,s) mapping to zeroExtension(d,t,u,x-s) is AE strongly measurable on windowMeasure(d,t) times Lebesgue measure.

**Theorem 1.9 (l2 complex correlation integrable).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.l2_complex_correlation_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.l2_complex_correlation_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an arbitrary measurable type and measure, two complex MemLp 2 functions f and g have integrable Hermitian product conjugate(f(x))*g(x). The proof uses the L2 norm-product estimate and preserves complex conjugation.

**Theorem 1.10 (zeroCorrelation eq window).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_eq_window`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_eq_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d, t, u and s, the full-line zero-extension correlation equals the original-window integral of conjugate(u(x))*zeroExtension(d,t,u,x-s). This is an exact indicator-integral identity, with no integrability premise.

**Theorem 1.11 (zeroTranslationEnergy expansion).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d and t, interval MemLp(u,2) gives zeroTranslationEnergy(d,t,u,s)=2*windowEnergy(d,t,u)-2*Re zeroCorrelation(d,t,u,s), for every real s. Both copies of the zero extension have exactly the original physical L2 mass.

**Theorem 1.12 (periodicTranslationEnergy expansion).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, arbitrary t and interval MemLp(u,2), periodicTranslationEnergy(d,t,u,s)=2*windowEnergy(d,t,u)-2*Re periodicCorrelation(d,t,u,s), for every real s. The shift is the actual AddCircle translation.

**Theorem 1.13 (zeroCorrelation neg).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d, t, u and s, zeroCorrelation(d,t,u,-s) is the complex conjugate of zeroCorrelation(d,t,u,s). Real correlation is consequently even; complex correlation is not assumed even.

**Theorem 1.14 (periodicCorrelation neg).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicCorrelation_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicCorrelation_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and arbitrary t, u and s, periodicCorrelation(d,t,u,-s) is the complex conjugate of periodicCorrelation(d,t,u,s). The identity follows on the actual circle by Haar translation and conjugation.

**Theorem 1.15 (correlation difference slice).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.correlation_difference_slice`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.correlation_difference_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d and interval MemLp(u,2), the window integral of conjugate(u(x)) times the periodic-minus-zero difference at x-s equals periodicCorrelation minus zeroCorrelation at s. Integrability is proved before applying integral subtraction.

**Theorem 1.16 (zeroTranslationEnergy aestronglyMeasurable).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_aestronglyMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_aestronglyMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d and t and interval MemLp(u,2), the real zero-extension translation energy is AE strongly measurable as a function of the real displacement.

**Theorem 1.17 (periodicTranslationEnergy aestronglyMeasurable).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_aestronglyMeasurable`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_aestronglyMeasurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, arbitrary t and interval MemLp(u,2), the real periodic translation energy is AE strongly measurable as a function of the real displacement.

**Theorem 1.18 (zeroTranslationEnergy nonneg le).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_nonneg_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_nonneg_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary d and t and interval MemLp(u,2), every zero-extension translation energy lies between zero and four times the original window L2 mass.

**Theorem 1.19 (periodicTranslationEnergy nonneg le).**

Lean statement: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_nonneg_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_nonneg_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, arbitrary t and interval MemLp(u,2), every periodic translation energy lies between zero and four times the original window L2 mass.

These are transport, integrability and correlation results. They establish no signed Weil, Schur or Robin positivity and no Riemann hypothesis conclusion.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.copyReflection_measurePreserving`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.correlation_difference_slice`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.l2_complex_correlation_integrable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicCorrelation_neg`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_aestronglyMeasurable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_expansion`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodicTranslationEnergy_nonneg_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_correlation_integrable_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_minus_zero_norm_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_joint_aestronglyMeasurable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.periodic_shift_memLp`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.weightedLattice_image_integrable_and_identity`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.windowMeasure_prod_windowMeasure`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_eq_window`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroCorrelation_neg`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_aestronglyMeasurable`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_expansion`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zeroTranslationEnergy_nonneg_le`
- Truth anchor: `D5/S3/Weil/ZetaGamma/PeriodicEnergyTransport.zero_shift_joint_aestronglyMeasurable`
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition](ArchimedeanJumpDecomposition.md)

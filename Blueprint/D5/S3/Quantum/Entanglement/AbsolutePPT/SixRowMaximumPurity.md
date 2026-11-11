# SixRowMaximumPurity

## Abstract

Six-row actual APPT maximum and least eventual central threshold

**Definition 1.1 (CentralOptimal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.CentralOptimal`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.CentralOptimal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every actual complex matrix rho on Fin 6 times Fin n, PSD, complex trace one and literal all-global-unitary APPT imply real trace-square purity at most the existing SixRowScalarData.theta(n). There also exists an actual rho with all these properties and purity equal to theta(n). Ordered-spectrum uniqueness is not part of this predicate.

**Definition 1.2 (EventualCentralFrom).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.EventualCentralFrom`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.EventualCentralFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, 6<=n and k<=n imply CentralOptimal(n). The threshold concerns universal actual-density maximality together with actual attainment.

**Theorem 1.3 (central optimal).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=23, SixRowLiteralUpper.density_upper supplies the universal bound for arbitrary complex PSD trace-one APPT rho. SixRowAttainment.central_attainment supplies an actual equality witness centralDensity(n): its second conjunction projection drops only the projector-rank clause and retains PSD, trace one, APPT and exact purity.

**Theorem 1.4 (ordered spectrum upper and equality).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.ordered_spectrum_upper_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.ordered_spectrum_upper_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independently, for every n>=23, every product-to-Fin equivalence e and arbitrary original antitone nonnegative unit-mass spectrum l whose actual e-labelled complex diagonal is APPT, the square sum is at most theta(n), and equals theta(n) iff l is exactly SixRowConcentration.centralSpectrum(n). This consumes SixRowLiteralUpper.literal_upper_and_equality. Repeated and zero entries are allowed; no concentrated vector is assumed APPT and no unique-matrix claim is made.

**Theorem 1.5 (central spectrum attainment).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_spectrum_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_spectrum_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n>=23, the named centralSpectrum(n) is antitone, nonnegative, has mass one and square sum theta(n). Its actual diagonal under finProdFinEquiv is PSD, trace one, literal APPT and has purity theta(n). Unfolding only centralSpectrum matches SixRowAttainment.central_spectrum_data and central_density_diagonal; central_attainment supplies the physical properties. The first j=(5*n+1)/2 entries are 7/(30*n+2*j), and all remaining entries are 5/(30*n+2*j).

**Theorem 1.6 (eventual central iff).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_central_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_central_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, EventualCentralFrom(k) iff 23<=k. Sufficiency uses central_optimal for each n>=k. If k<=22, instantiate the purported universal result at n=22 and apply its actual-density upper clause to SixRowAttainment.ray22Density. The physical n22_obstruction supplies PSD, trace one, APPT and strict purity greater than theta(22), contradicting that clause. Its exact values are 35/4489 and theta(22)=3/385, differing by 8/1728265; uniqueness is not used.

**Theorem 1.7 (eventual threshold is least).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_threshold_is_least`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_threshold_is_least` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural number 23 is IsLeast of the set of k with EventualCentralFrom(k), directly from eventual_central_iff.

**Definition 1.8 (n0).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.find of the established nonempty predicate EventualCentralFrom defines the least eventual central-maximum threshold. The existence witness is 23; the definition does not impose ordered-spectrum uniqueness.

**Theorem 1.9 (n0 eq).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defined n0 equals 23. Nat.find_min' gives n0<=23, and Nat.find_spec with eventual_central_iff gives 23<=n0.

**Theorem 1.10 (result).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final theorem combines actual universal maximum and actual attainment for every n>=23, independent arbitrary original ordered-spectrum equality, the existing exact parity formula theta(n)=6/(35*n) for even n and 6*(35*n+2)/(35*n+1)^2 for odd n, IsLeast of the eventual central-maximum thresholds at 23, and n0=23. It adds no target-equivalent assumption and does not determine maxima for 6<=n<=22. Tran, arXiv:2611.01492v1, Theorem A and the final discussion, gives the prior n>=68 range and asks for the least fixed-row threshold.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.CentralOptimal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.EventualCentralFrom`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_optimal`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.central_spectrum_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_central_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.eventual_threshold_is_least`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.n0_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.ordered_spectrum_upper_and_equality`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SixRowMaximumPurity.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAttainment](SchmidtStar/SixRowAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowLiteralUpper](SchmidtStar/SixRowLiteralUpper.md)

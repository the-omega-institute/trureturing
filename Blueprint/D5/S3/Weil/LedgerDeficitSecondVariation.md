# Ledger Deficit as a Second Variation

## Abstract

The squared norm-deficit second variation, its mirror-antisymmetric zero address, and the Dirac measure embedding.

**Definition 1.1 (Squared norm-deficit curve).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.normDeficitCurve`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.normDeficitCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a signed ledger displacement d, the auxiliary curve is (exp(-d u) - 1)^2. It measures squared distance from the unitary norm at u = 0, so the first-order orientation is discarded and the local quantity is a nonnegative energy.

**Definition 1.2 (Chosen second variation).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected candidate is ((N - 1)^2)''(0) for N(u) = exp(-u), evaluated along the ledger displacement rate. This is the squared-distance Hessian of the norm coordinate to the unitary value 1. The logarithmic candidate is flat in this coordinate; the unsquared norm candidates retain a signed first variation and therefore do not give the centered loss geometry. The definition satisfies the machine identity ledgerDeficitSecondVariation d = 2 d^2 and is consequently nonnegative.

**Theorem 1.3 (The defining Hessian identity).**

$$\forall d\in\mathbb{R}, \operatorname{ledgerDeficitSecondVariation}(d)=2d^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the exponential curve twice and applying the product rule gives exactly twice the square of the signed displacement. This is a definition-level algebraic check, not a claim about the zeta zero set or about the open Weil bridge.

**Definition 1.4 (Canonical zero-to-ledger address).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroLedgerAddress`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.zeroLedgerAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A zero rho is assigned the mirror-antisymmetric address rho - mirror(rho). The address is canonical from the already frozen reflection geometry: it vanishes on the critical fixed locus and changes sign under the mirror. No enumeration order or external labeling is introduced.

**Definition 1.5 (Length on complex addresses).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.realPartLedgerLength`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.realPartLedgerLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complex addresses receive the additive ledger length Re. The addressed scaling is therefore the existing scalingLedger evaluated at the displacement address, retaining the ledger's semantic factor (Re(rho) - 1/2) and making the resulting scalar a quadratic displacement.

**Definition 1.6 (Zero-addressed scaling readout).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroAddressedScaling`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.zeroAddressedScaling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero address is fed to the existing scalingLedger with the additive real-part length. This is the scalar ledger displacement used by the selected second variation.

**Theorem 1.7 (Zero-addressed scaling is a squared displacement).**

$$\forall \rho\in\mathbb{C}, \operatorname{zeroAddressedScaling}(\rho)=2(\operatorname{Re}(\rho)-\operatorname{criticalAbscissa})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_scaling_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding the mirror-antisymmetric address and the real-part length gives twice the square of the real displacement from the critical line.

**Theorem 1.8 (Mirror compatibility of addressed variation).**

$$\forall \rho\in\mathbb{C}, \operatorname{ledgerDeficitSecondVariation}(\operatorname{zeroAddressedScaling}(\operatorname{mirror}(\rho)))=\operatorname{ledgerDeficitSecondVariation}(\operatorname{zeroAddressedScaling}(\rho))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_variation_mirror` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mirror reverses both the scaling entry and the antisymmetric address. Their product is therefore unchanged, and the selected even energy assigns equal local deficit to both members of a mirror pair. At a common address, the signed entries still cancel exactly by ZeroGeometry; the energy records the magnitude without mistaking cross-position cancellation for local balance.

**Definition 1.9 (Scalar-to-measure embedding).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.scalarToDeficitMeasure`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.scalarToDeficitMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonnegative scalar weight w at rho is embedded as ENNReal.ofReal(w) times the Dirac measure at rho. This is the canonical atomic inclusion: it changes codomain without changing the spectral address, and the nonnegativity theorem ensures that no signed mass is silently clipped.

**Definition 1.10 (Mirror-pair deficit measure).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.mirrorPairDeficitMeasure`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.mirrorPairDeficitMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mirror pair is embedded by adding the two weighted Dirac atoms, one at each spectral address.

**Theorem 1.11 (Mirror-pair measure compatibility).**

$$\forall \rho\in\mathbb{C}, w\in\mathbb{R}, \operatorname{mirrorPairDeficitMeasure}(\operatorname{mirror}(\rho),w)=\operatorname{mirrorPairDeficitMeasure}(\rho,w)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_deficit_measure_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-point measure obtained by adding the two Dirac atoms is invariant under swapping the mirror pair. This respects the cancellation identity in ZeroGeometry while retaining the nonnegative second-order mass at each address.

**Theorem 1.12 (The selected variation is nonnegative).**

$$\forall d\in\mathbb{R}, 0\leq\operatorname{ledgerDeficitSecondVariation}(d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defining Hessian identity is a nonnegative square, so every ledger displacement has nonnegative deficit energy.

**Theorem 1.13 (The selected variation is even under reversal).**

$$\forall d\in\mathbb{R}, \operatorname{ledgerDeficitSecondVariation}(-d)=\operatorname{ledgerDeficitSecondVariation}(d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversing the signed ledger displacement leaves the squared second-order energy unchanged.

**Theorem 1.14 (Signed cancellation and even energy).**

$$\forall \ell, \rho, a, \operatorname{ledgerDeficitSecondVariation}(\operatorname{scalingLedger}(\ell,\operatorname{mirror}(\rho),a))=\operatorname{ledgerDeficitSecondVariation}(\operatorname{scalingLedger}(\ell,\rho,a)) \land \operatorname{scalingLedger}(\ell,\rho,a)+\operatorname{scalingLedger}(\ell,\operatorname{mirror}(\rho),a)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_zero_readout_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every additive ledger and every common address, the mirror entries sum to zero while their selected second variations agree. This is the required compatibility law: reflection cancels the signed ledger reading, and the centered quadratic loss descends to the mirror orbit.

**Definition 1.15 (Zero-indexed deficit measure).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroDeficitMeasure`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.zeroDeficitMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete readout places the selected deficit weight at the zero's original spectral address.

**Remark 1.16 (Independent semantic justification).**

Lean statement: `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation`

*Formalization.* `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The choice is derived from the intrinsic ledger declarations only. scalingLedger length s a is (s.re - 1/2) times length a, so its signed value is the displacement from the critical line. half_density_reading_norm identifies the corresponding normalized norm as exp(-scalingLedger ...); hence the unitary locus is the norm value 1 at zero displacement. For a signed displacement d, introduce the dimensionless rate curve N_d(u) = exp(-d u). The Euclidean/Riemannian metric in the positive norm coordinate has squared distance (N_d(u) - 1)^2 from that unitary locus. Its Hessian at u = 0 is therefore the centered, nonnegative local energy, and no additional calibration constant is needed.

This geometry selects ((N - 1)^2)''(0) among the listed candidates: log N is affine in u and has zero curvature, while N - 1 and N^2 - 1 are unsquared signed displacements whose values change sign under reversal and so are not centered nonnegative losses. Squaring before differentiating is additive across independent coordinates and even under d to -d, yielding the machine identity ledgerDeficitSecondVariation d = 2 d^2.

The address rho - mirror(rho) is the canonical mirror-antisymmetric zero coordinate. mirror_reversal_spec reverses the addressed ledger entry, while the selected even energy is invariant; ZeroGeometry still supplies exact signed cancellation at a common address. Finally, scalarToDeficitMeasure embeds each nonnegative scalar as ENNReal.ofReal(w) times the Dirac measure at its spectral address, and the zeroDeficitMeasure readout uses the proven nonnegative weight. This argument was fixed before any toy comparison and does not use which candidate matches the W-B1 toy or any toy constants.

## References

- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.ledgerDeficitSecondVariation`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_eq`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_neg`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.ledger_deficit_second_variation_nonneg`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.mirrorPairDeficitMeasure`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_deficit_measure_invariant`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.mirror_pair_zero_readout_compatibility`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.normDeficitCurve`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.realPartLedgerLength`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.scalarToDeficitMeasure`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroAddressedScaling`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroDeficitMeasure`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.zeroLedgerAddress`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_scaling_eq`
- Truth anchor: `D5/S3/Weil/LedgerDeficitSecondVariation.zero_addressed_variation_mirror`
- Dependency: [D5/S3/Weil/CriticalLine](CriticalLine.md)
- Dependency: [D5/S3/Zeros/ZeroGeometry](../Zeros/ZeroGeometry.md)

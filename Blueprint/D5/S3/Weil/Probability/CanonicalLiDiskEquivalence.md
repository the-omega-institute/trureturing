# CanonicalLiDiskEquivalence

## Abstract

The actual canonical Li series has a full-disk convergence criterion equivalent to the standard Riemann hypothesis.

**Theorem 1.1 (Disk points map to the actual right half-plane).**

$$\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \frac{1}{2} < \operatorname{Re}\left(\frac{1}{1 - z}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.disk_mobius_re_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict real-part inequality is derived from the original complex norm and the positive inverse denominator.

**Theorem 1.2 (RH supplies actual disk nonvanishing).**

$$\mathit{RiemannHypothesis} \Rightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_xi_disk_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing xi/nontrivial-zero identity and the standard RiemannHypothesis predicate exclude a zero in the disk image.

**Theorem 1.3 (Definitional adapter to literal xi).**

$$\forall z \in \mathbb{C},\; \operatorname{canonicalXiDisk}\left(z\right) = \operatorname{xiReading}\left(\frac{1}{1 - z}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.canonical_xi_disk_def` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original disk definition is retained in Growth.

**Theorem 1.4 (Half-plane to disk).**

$$\left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right) \Rightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.xi_right_half_plane_zero_free_disk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This direction uses the existing disk_mobius_re_half.

**Theorem 1.5 (Both geometric directions).**

$$\left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right) \Leftrightarrow \left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.xi_disk_zero_free_iff_right_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both domains are open and contain every qualifying complex point.

**Theorem 1.6 (A005 with the original disk definition).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{canonicalXiDisk}\left(z\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_xi_disk_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original RH forward proof is combined with Growth's bare converse.

**Theorem 1.7 (A005 in literal source coordinates).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{xiReading}\left(\frac{1}{1 - z}\right) \ne 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_xi_disk_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No Li summability premise occurs in either direction.

**Theorem 1.8 (A001 through A005, each as a full iff).**

$$\left(\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow \operatorname{Re}\left(\mathit{rho}\right) = \frac{1}{2}\right)\right) \land \left(\left(\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \operatorname{xiReading}\left(\frac{1}{2} + i \cdot z\right) = 0 \Rightarrow \operatorname{Im}\left(z\right) = 0\right)\right) \land \left(\left(\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall s \in \mathbb{C},\; \frac{1}{2} < \operatorname{Re}\left(s\right) \Rightarrow \operatorname{xiReading}\left(s\right) \ne 0\right)\right) \land \left(\left(\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall rho \in \mathbb{C},\; \operatorname{IsNontrivialZero}\left(\mathit{rho}\right) \Rightarrow \left\lVert 1 - \frac{1}{\mathit{rho}} \right\rVert = 1\right)\right) \land \left(\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{xiReading}\left(\frac{1}{1 - z}\right) \ne 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.actual_zero_geometry_disk_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower owner supplies A001-A004. RH retains Mathlib's exceptional-zero and s!=1 quantifiers; xiReading is the actual entire function. This package does not establish RH, the larger E1/P0 atoms, or the remaining atlas.

**Theorem 1.9 (The existing generator is analytic on the disk).**

$$\mathit{RiemannHypothesis} \Rightarrow \operatorname{AnalyticOnNhd}\left(\mathbb{C}, \mathit{liGenerator}, \operatorname{ball}\left(0, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_li_generator_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RH is used only in this forward direction to justify the actual logarithmic derivative everywhere in the disk.

**Theorem 1.10 (Globalize the proved canonical Taylor coefficients).**

$$\mathit{RiemannHypothesis} \Rightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{HasSum}\left((n:\mathbb{N}\mapsto\operatorname{canonicalLiCoefficient}\left(n + 1\right) \cdot z^{n}), \operatorname{liGenerator}\left(z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_canonical_li_global_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The merged all-order coefficient identification is inserted into the standard holomorphic Taylor theorem. No coefficients are redefined.

**Theorem 1.11 (Absolute convergence at every radius below one).**

$$\mathit{RiemannHypothesis} \Rightarrow \left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left|\operatorname{canonicalLiCoefficient}\left(n + 1\right)\right| \cdot r^{n})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_canonical_li_disk_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite-dimensional absolute summability converts the full complex Taylor series into the original weighted absolute coefficient sum.

**Theorem 1.12 (Close both directions of the canonical criterion).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall r \in \mathbb{R}_{\geq0},\; r < 1 \Rightarrow \operatorname{Summable}\left((n:\mathbb{N}\mapsto\left|\operatorname{canonicalLiCoefficient}\left(n + 1\right)\right| \cdot r^{n})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_li_disk_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward proof is combined with the prior analytic-order converse. Neither the arithmetic condition nor RH is asserted unconditionally.

**Theorem 1.13 (The actual full-disk expansion is equivalent to RH).**

$$\mathit{RiemannHypothesis} \Leftrightarrow \left(\forall z \in \mathbb{C},\; \left\lVert z \right\rVert < 1 \Rightarrow \operatorname{HasSum}\left((n:\mathbb{N}\mapsto\operatorname{canonicalLiCoefficient}\left(n + 1\right) \cdot z^{n}), \operatorname{liGenerator}\left(z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_li_global_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conclusion concerns every point of the full disk, not a local germ or a finite coefficient prefix.

## References

- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.actual_zero_geometry_disk_spec`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.canonical_xi_disk_def`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.disk_mobius_re_half`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_canonical_li_disk_summable`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_canonical_li_global_expansion`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_li_disk_summable`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_li_global_expansion`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_canonical_xi_disk_ne_zero`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_iff_xi_disk_ne_zero`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_li_generator_analytic`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.rh_xi_disk_ne_zero`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.xi_disk_zero_free_iff_right_half_plane`
- Truth anchor: `D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.xi_right_half_plane_zero_free_disk`
- Dependency: [D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree](CanonicalLiGrowthZeroFree.md)

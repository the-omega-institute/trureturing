# SixRowOuterScalar

## Abstract

The scalar intervals follow the manuscript closed coverage. The n23 low interval retains the actual mass square, including the quartic and all q and r splits. At n24 the possible r=q=0 and W=4 corner has mass at least 144, above center 140. The imported middle theorem is used without reimplementing its certificate. These are scalar consequences, not a physical APPT extraction or concentration theorem.

The scalar intervals follow the manuscript closed coverage. The n23 low interval retains the actual mass square, including the quartic and all q and r splits. At n24 the possible r=q=0 and W=4 corner has mass at least 144, above center 140. The imported middle theorem is used without reimplementing its certificate. These are scalar consequences, not a physical APPT extraction or concentration theorem.

**Theorem 1.1 (head cap elimination).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.head_cap_elimination`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.head_cap_elimination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem head_cap_elimination (r H D a q d : ℝ) (h : PhysicalScalarHyp r H D a q) (hr : r ≤ 1/5) (hDd : D ≤ d) : Den r*W r H D a q ≤ Den r*(q+r*(6-15*r))+cn r*V r q ∧ Den r*W r H D a q ≤ Den r*(q+r*d)+An r*V r q

**Theorem 1.2 (cap interval strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.cap_interval_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.cap_interval_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem cap_interval_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/12 ≤ r) (hru : r ≤ 1/5) : W r H D a q < T138 r

**Theorem 1.3 (low W le).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.low_W_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.low_W_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem low_W_le (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hr : r ≤ 1/12) : W r H D a q ≤ T144 r ∧ (W r H D a q=T144 r → r=0 ∧ q=0)

**Theorem 1.4 (n24 low strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n24_low_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n24_low_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem n24_low_strict (j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) : 0 < gap 144 j (1/140) r H D a q

**Theorem 1.5 (continuous strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.continuous_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.continuous_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem continuous_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/3 ≤ r) (hru : r ≤ 79/200) : W r H D a q < T138 r

**Theorem 1.6 (variance strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.variance_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.variance_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem variance_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 3/10 ≤ r) (hru : r ≤ 1/3) : W r H D a q < T138 r

**Theorem 1.7 (base strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem base_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/12 ≤ r) (hru : r ≤ 79/200) : W r H D a q < T138 r

**Theorem 1.8 (n23 low strict).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n23_low_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n23_low_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem n23_low_strict (j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) : 0 < gap 138 j th23 r H D a q

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.cap_interval_strict`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.continuous_strict`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.head_cap_elimination`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.low_W_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n23_low_strict`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n24_low_strict`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.variance_strict`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial](SixRowOuterPolynomial.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData](SixRowScalarData.md)

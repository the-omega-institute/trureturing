# SixRowScalarData

## Abstract

The full physical scalar relaxation includes nonnegativity, charge, the actual zero-slot Cauchy denominators fourteen and twenty, the special-edge cap, the finite head-box estimate, the tail cap, same-vector coupling and averaged variance. Extraction from a literal APPT spectrum is a separate obligation. Concentrated mass and energy use the actual plateau index; positive mass and both exact parity propagation formulas are derived here.

The full physical scalar relaxation includes nonnegativity, charge, the actual zero-slot Cauchy denominators fourteen and twenty, the special-edge cap, the finite head-box estimate, the tail cap, same-vector coupling and averaged variance. Extraction from a literal APPT spectrum is a separate obligation. Concentrated mass and energy use the actual plateau index; positive mass and both exact parity propagation formulas are derived here.

**Definition 1.1 (PhysicalScalarHyp).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.PhysicalScalarHyp`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.PhysicalScalarHyp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

structure PhysicalScalarHyp (r H D a q : ℝ) : Prop extends SixRowMiddleScalar.Hyp6 r H D a q

**Definition 1.2 (mass).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def mass (N j r H D : ℝ) : ℝ

**Definition 1.3 (energy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.energy`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def energy (N j r H D a q : ℝ) : ℝ

**Definition 1.4 (thetaEven).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaEven`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaEven` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def thetaEven (N : ℝ) : ℝ

**Definition 1.5 (thetaOdd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaOdd`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaOdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def thetaOdd (N : ℝ) : ℝ

**Definition 1.6 (theta).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.theta`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.theta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def theta (n : ℕ) : ℝ

**Definition 1.7 (centralIndex).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.centralIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.centralIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def centralIndex (n : ℕ) : ℕ

**Definition 1.8 (kappa).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def kappa (r : ℝ) : ℝ

**Definition 1.9 (T).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def T (N th r : ℝ) : ℝ

**Definition 1.10 (gap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.gap`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def gap (N j th r H D a q : ℝ) : ℝ

**Theorem 1.11 (mass pos).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem mass_pos (N j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hN : 138 ≤ N) (hj : 15 ≤ j) : 0 < mass N j r H D

**Theorem 1.12 (square completion).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.square_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.square_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem square_completion (N j th r H D a q : ℝ) (ht : th ≠ 0) : gap N j th r H D a q = th*(mass N j r H D-(2+r)/(2*th))^2+T N th r-W r H D a q

**Theorem 1.13 (endpoint zero).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.endpoint_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.endpoint_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem endpoint_zero (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hr : r=2/5) : H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ slack r H D=0

**Theorem 1.14 (mass energy envelope).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_energy_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_energy_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem mass_energy_envelope (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) : W r H D a q ≤ (6-15*r)*(6-14*r)

**Theorem 1.15 (q le 29 8).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.q_le_29_8`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.q_le_29_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem q_le_29_8 (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) : q ≤ 29/8

**Theorem 1.16 (kappa nonneg).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem kappa_nonneg (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 2/5) : 0 ≤ kappa r

**Theorem 1.17 (T even).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem T_even (N r : ℝ) (hN : 0 < N) : T N (thetaEven N) r = N*kappa r

**Theorem 1.18 (T odd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem T_odd (N r : ℝ) (hN : 0 < N) : T N (thetaOdd N) r = N*kappa r-(2+r)^2/(4*(35*N+12))

**Theorem 1.19 (T138 identity).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T138_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T138_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem T138_identity (r : ℝ) : T138 r = 138*kappa r-(2+r)^2/(4*(35*138+12))

**Theorem 1.20 (T even ge base).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even_ge_base`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even_ge_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem T_even_ge_base (N r : ℝ) (hN : 138 ≤ N) (hr : 0 ≤ r) (hr' : r ≤ 2/5) : T138 r ≤ T N (thetaEven N) r

**Theorem 1.21 (T odd ge base).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd_ge_base`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd_ge_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem T_odd_ge_base (N r : ℝ) (hN : 138 ≤ N) (hr : 0 ≤ r) (hr' : r ≤ 2/5) : T138 r ≤ T N (thetaOdd N) r

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.PhysicalScalarHyp`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T138_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_even_ge_base`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.T_odd_ge_base`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.centralIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.endpoint_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.kappa_nonneg`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_energy_envelope`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.mass_pos`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.q_le_29_8`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.square_completion`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.theta`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaEven`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowScalarData.thetaOdd`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar](../FiveRowP2Scalar.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar](SixRowMiddleScalar.md)

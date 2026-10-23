# FiveRowP2Scalar

## Abstract

A continuous scalar relaxation for five-row spectra. All parameters are real and the interval endpoints are included. The energy estimate retains the nonnegative common loss for dimensions at least one hundred.

A continuous scalar relaxation for five-row spectra. All parameters are real and the interval endpoints are included. The energy estimate retains the nonnegative common loss for dimensions at least one hundred.

**Definition 1.1 (Hyp).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.Hyp`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.Hyp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

structure Hyp (r H D a q s : ℝ) : Prop where r0 : 0 ≤ r r1 : r ≤ 1/2 H0 : 0 ≤ H D0 : 0 ≤ D a0 : 0 ≤ a q0 : 0 ≤ q s0 : 0 ≤ s mass : H+D+s = 5-10*r amin : H^2/9 ≤ a amax : a ≤ H^2 qmin : D^2/14 ≤ q qbox : q ≤ D qmass : q ≤ D^2 qcap : q ≤ 10/3 coupled : a+2*r*H+10*r^2 ≤ (2-q/2)^2 variance : (2/3)*(a-H^2/10)+(q-D^2/15) ≤ 4*s-(2/5)*s^2

**Definition 1.2 (phi).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.phi`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def phi (q : ℝ) : ℝ

**Definition 1.3 (W).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.W`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def W (r H D a q : ℝ) : ℝ

**Definition 1.4 (B).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def B (r : ℝ) : ℝ

**Definition 1.5 (B0).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B0`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def B0 (r : ℝ) : ℝ

For arbitrary real N, j, r, H and D, the scalar mass is N + j*r + H - D. This is the mass used by the energy expression and the concentrated estimates.

**Definition 1.6 (energy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def energy (N j r H D a q : ℝ) : ℝ

**Theorem 1.7 (quadratic upper).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quadratic_upper (A b c lo hi x K : ℝ) (hA : 0 ≤ A) (hx : lo ≤ x) (hx' : x ≤ hi) (hlo : A*lo^2+b*lo+c ≤ K) (hhi : A*hi^2+b*hi+c ≤ K) : A*x^2+b*x+c ≤ K

**Theorem 1.8 (quadratic lower).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quadratic_lower (A b c lo hi x K : ℝ) (hA : A ≤ 0) (hx : lo ≤ x) (hx' : x ≤ hi) (hlo : K ≤ A*lo^2+b*lo+c) (hhi : K ≤ A*hi^2+b*hi+c) : K ≤ A*x^2+b*x+c

**Theorem 1.9 (energy envelopes).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy_envelopes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy_envelopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem energy_envelopes {r H D a q s : ℝ} (h : Hyp r H D a q s) : a+q+2*r*H+10*r^2 ≤ 4-phi q ∧ a+q+2*r*H+10*r^2 ≤ 4

**Theorem 1.10 (pointwise energy cap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.pointwise_energy_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.pointwise_energy_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem pointwise_energy_cap {r H D a q s : ℝ} (h : Hyp r H D a q s) : W r H D a q ≤ B0 r

**Theorem 1.11 (homogeneous energy cap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.homogeneous_energy_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.homogeneous_energy_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem homogeneous_energy_cap (u v H D a q s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hH : 0 ≤ H) (hD : 0 ≤ D) (ha : 0 ≤ a) (hq : 0 ≤ q) (hs : 0 ≤ s) (hm : H+D+s=5*u-10*v) (ha' : a ≤ H^2) (hq' : q ≤ D^2) (hnorm : 0 < u → Hyp (v/u) (H/u) (D/u) (a/u^2) (q/u^2) (s/u)) : a+q+v*(H+D) ≤ (4/5)*(u+3*v)*(5*u-10*v)

**Theorem 1.12 (concentrated ge100).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.concentrated_ge100`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.concentrated_ge100` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_ge100 (N j r H D a q s : ℝ) (hN : 100 ≤ N) (h : Hyp r H D a q s) : energy N j r H D a q + (N-100)*(1+3*r)*(5-10*r)/125 ≤ (25/(24*N))*(mass N j r H D)^2

**Theorem 1.13 (common loss nonnegative).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.common_loss_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.common_loss_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem common_loss_nonnegative (N r : ℝ) (hN : 100 ≤ N) (hr : 0 ≤ r) (hr' : r ≤ 1/2) : 0 ≤ (N-100)*(1+3*r)*(5-10*r)/125

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.B0`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.Hyp`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.W`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.common_loss_nonnegative`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.concentrated_ge100`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.energy_envelopes`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.homogeneous_energy_cap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.phi`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.pointwise_energy_cap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Scalar.quadratic_upper`

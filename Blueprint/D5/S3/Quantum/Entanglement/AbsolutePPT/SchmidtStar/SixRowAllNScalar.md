# SixRowAllNScalar

## Abstract

All dimensions at least twenty-three and every integer plateau index in the actual range remain quantified. Even propagation retains the endpoint square. Odd propagation retains the negative parity correction and separates both neighboring integer half-lattices using the exact corrected G identities and positive shifted polynomials. Equality in the concentrated scalar bound is equivalent to r=2/5, zero moments and the unique ceiling multiplicity. Physical extraction, norm-cone transfer, literal APPT attainment and the threshold obstruction are separate obligations.

All dimensions at least twenty-three and every integer plateau index in the actual range remain quantified. Even propagation retains the endpoint square. Odd propagation retains the negative parity correction and separates both neighboring integer half-lattices using the exact corrected G identities and positive shifted polynomials. Equality in the concentrated scalar bound is equivalent to r=2/5, zero moments and the unique ceiling multiplicity. Physical extraction, norm-cone transfer, literal APPT attainment and the threshold obstruction are separate obligations.

**Theorem 1.1 (low threshold propagation).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.low_threshold_propagation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.low_threshold_propagation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem low_threshold_propagation (N r : ℝ) (hN : 150 ≤ N) (hr0 : 0 ≤ r) (hr : r ≤ 1/12) : T144 r < T N (thetaEven N) r ∧ T144 r < T N (thetaOdd N) r

**Theorem 1.2 (even high gap).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.even_high_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.even_high_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem even_high_gap (N j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hN : 144 ≤ N) (hr : 1/3 ≤ r) : (2-5*r)/3 ≤ gap N j (thetaEven N) r H D a q

**Definition 1.3 (Aplus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aplus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Aplus (N : ℝ) : ℝ

**Definition 1.4 (Bplus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bplus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Bplus (N : ℝ) : ℝ

**Definition 1.5 (Aminus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aminus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aminus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Aminus (N : ℝ) : ℝ

**Definition 1.6 (Bminus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bminus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bminus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Bminus (N : ℝ) : ℝ

**Definition 1.7 (Mminus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mminus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mminus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Mminus (N d : ℝ) : ℝ

**Definition 1.8 (Mplus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mplus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Mplus (N d : ℝ) : ℝ

**Definition 1.9 (centerOdd).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.centerOdd`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.centerOdd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def centerOdd (N d : ℝ) : ℝ

**Definition 1.10 (Gminus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gminus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gminus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Gminus (N d : ℝ) : ℝ

**Definition 1.11 (Gplus).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gplus`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gplus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Gplus (N d : ℝ) : ℝ

**Theorem 1.12 (odd endpoint identities).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_identities`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_endpoint_identities (N d : ℝ) (hN : 138 ≤ N) : Gminus N d = thetaOdd N*(Mminus N d)^2-(2+(2-d)/5)*Mminus N d+ N*(1+(2-d)/5)-(42*d^2+6*d)/5 ∧ Gplus N d = thetaOdd N*(Mplus N d)^2-(2+(2-d)/5)*Mplus N d+ N*(1+(2-d)/5)-(42*d^2+6*d)/5

**Theorem 1.13 (odd coefficients).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_coefficients (N : ℝ) (hN : 138 ≤ N) : 0 < Aplus N ∧ 0 < Aminus N ∧ 0 < 40*Bplus N-Aplus N ∧ 0 < 40*Bminus N-Aminus N

**Theorem 1.14 (odd endpoint signs).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_signs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_endpoint_signs (N d : ℝ) (hN : 138 ≤ N) (hd : 0 ≤ d) (hd' : d ≤ 1/40) : 0 < Gminus N d ∧ 0 ≤ Gplus N d ∧ (Gplus N d=0 → d=0)

**Theorem 1.15 (odd center distances).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_center_distances`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_center_distances` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_center_distances (N d : ℝ) (hN : 138 ≤ N) (hd : 0 ≤ d) (hd' : d ≤ 3/N^2) : Mminus N d+19/100 < centerOdd N d ∧ centerOdd N d+19/100 < Mplus N d

**Theorem 1.16 (odd high continuous).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_high_continuous (N r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hN : 138 ≤ N) (hr : 79/200 ≤ r) (hd : 3/N^2 ≤ 2-5*r) : W r H D a q < T N (thetaOdd N) r

**Theorem 1.17 (odd high integer).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem odd_high_integer (N r H D a q : ℝ) (j k : ℤ) (h : PhysicalScalarHyp r H D a q) (hN : 138 ≤ N) (hr : 79/200 ≤ r) (hd : 2-5*r ≤ 3/N^2) (hk : (k:ℝ)=(5*N-6)/12) : 0 ≤ gap N (j:ℝ) (thetaOdd N) r H D a q ∧ (gap N (j:ℝ) (thetaOdd N) r H D a q=0 → r=2/5 ∧ H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ j=k+1)

**Theorem 1.18 (central gap zero).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.central_gap_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.central_gap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem central_gap_zero (n : ℕ) (hn : 23 ≤ n) : gap (6*(n:ℝ)) (centralIndex n:ℝ) (theta n) (2/5) 0 0 0 0=0

**Theorem 1.19 (concentrated scalar).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.concentrated_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.concentrated_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem concentrated_scalar (n j : ℕ) (hn : 23 ≤ n) (hjl : 15 ≤ j) (hju : j ≤ 6*n-21) (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) : 0 < mass (6*(n:ℝ)) (j:ℝ) r H D ∧ energy (6*(n:ℝ)) (j:ℝ) r H D a q ≤ theta n*(mass (6*(n:ℝ)) (j:ℝ) r H D)^2 ∧ (energy (6*(n:ℝ)) (j:ℝ) r H D a q = theta n*(mass (6*(n:ℝ)) (j:ℝ) r H D)^2 ↔ r=2/5 ∧ H=0 ∧ D=0 ∧ a=0 ∧ q=0 ∧ j=centralIndex n)

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aminus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Aplus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bminus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Bplus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gminus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Gplus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mminus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.Mplus`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.centerOdd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.central_gap_zero`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.concentrated_scalar`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.even_high_gap`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.low_threshold_propagation`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_center_distances`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_coefficients`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_identities`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_endpoint_signs`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_continuous`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowAllNScalar.odd_high_integer`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar](SixRowOuterScalar.md)

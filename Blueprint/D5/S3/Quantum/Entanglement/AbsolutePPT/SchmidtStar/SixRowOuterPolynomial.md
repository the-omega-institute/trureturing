# SixRowOuterPolynomial

## Abstract

These fixed rational short tables certify the quartic and the two head-cap eliminations on complete closed intervals. Integer homogeneous tensors use the existing SixRowHeadPolynomial row and tensor primitives. The low P2 table retains its sole zero corner by a quantitative fourth-power separation. No middle or K6 certificate is regenerated.

These fixed rational short tables certify the quartic and the two head-cap eliminations on complete closed intervals. Integer homogeneous tensors use the existing SixRowHeadPolynomial row and tensor primitives. The low P2 table retains its sole zero corner by a quantitative fourth-power separation. No middle or K6 certificate is regenerated.

**Definition 1.1 (K).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.K`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def K : ℝ

**Definition 1.2 (th23).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.th23`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.th23` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def th23 : ℝ

**Definition 1.3 (C).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.C`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def C (z : ℝ) : ℝ

**Definition 1.4 (F).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.F`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def F (d : ℝ) : ℝ

**Definition 1.5 (Den).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.Den`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.Den` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def Den (r : ℝ) : ℝ

**Definition 1.6 (An).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.An`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.An` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def An (r : ℝ) : ℝ

**Definition 1.7 (V).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.V`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def V (r q : ℝ) : ℝ

**Definition 1.8 (T144).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.T144`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.T144` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def T144 (r : ℝ) : ℝ

**Definition 1.9 (P1).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P1`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def P1 (r q T : ℝ) : ℝ

**Definition 1.10 (P2).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P2`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def P2 (r d T : ℝ) : ℝ

**Theorem 1.11 (quartic 0).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_0`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quartic_0 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((0 : ℝ)+(1 : ℝ)*x)

**Theorem 1.12 (quartic 1).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_1`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quartic_1 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((1 : ℝ)+(1 : ℝ)*x)

**Theorem 1.13 (quartic 2).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_2`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quartic_2 (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (1/25 : ℝ) ≤ F ((2 : ℝ)+(1 : ℝ)*x)

**Theorem 1.14 (p1 mid cut).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p1_mid_cut (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (10797119/4131840000 : ℝ) ≤ P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (3/32) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))

**Theorem 1.15 (p1 mid tail).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p1_mid_tail (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (944503/2017500 : ℝ) ≤ P1 ((1/12 : ℝ)+(7/60 : ℝ)*x) (4-10*((1/12 : ℝ)+(7/60 : ℝ)*x)) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))

**Theorem 1.16 (p1 low cut).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p1_low_cut (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (375/2048 : ℝ) ≤ P1 ((0 : ℝ)+(1/12 : ℝ)*x) (3/32) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))

**Theorem 1.17 (p1 low tail).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p1_low_tail (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) : (158245/663552 : ℝ) ≤ P1 ((0 : ℝ)+(1/12 : ℝ)*x) (29/8) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))

**Theorem 1.18 (p2 mid).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_mid`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_mid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p2_mid (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) : (8181393293863/3228000000000000 : ℝ) ≤ P2 ((1/12 : ℝ)+(7/60 : ℝ)*x) ((137/100 : ℝ)*y) (T138 ((1/12 : ℝ)+(7/60 : ℝ)*x))

**Theorem 1.19 (p2 low).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p2_low (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) : (0 : ℝ) ≤ P2 ((0 : ℝ)+(1/12 : ℝ)*x) ((137/100 : ℝ)*y) (T144 ((0 : ℝ)+(1/12 : ℝ)*x))

**Theorem 1.20 (quartic lower).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem quartic_lower (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 3) : 1/25 ≤ F d

**Theorem 1.21 (p2 low separation).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem p2_low_separation (x y : ℝ) (hx : 0 ≤ x) (hX : x ≤ 1) (hy : 0 ≤ y) (hY : y ≤ 1) : x^4/4+y^4/4 ≤ P2 (x/12) ((137/100)*y) (T144 (x/12))

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.An`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.C`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.Den`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.F`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.K`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.P2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.T144`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.V`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_cut`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_low_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_cut`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p1_mid_tail`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_low_separation`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.p2_mid`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.quartic_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterPolynomial.th23`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddlePolynomial](SixRowMiddlePolynomial.md)

/- GID: D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Uniform product evaluations of the periodic Temperley–Lieb seed recurrences. -/

/-
result
  proof_shape: content (coupled Darboux recurrence invariant and terminal-degree induction)
  escape_witness: IMDAW.terminal_factorization (through seed_terminal)
  admission_basis: open-problem-resolution (#18569; Proved)
  Direct frozen dependencies: NikolovSegal.UnitaryField.prod_zpow_base
    (via prod_zpow_range, product_linear and seed_terminal).
    Declaration statement_id:
    sha256:7521cf7201bdc621ff7161cf5a6c5802afccc0cf6f0b1539361eaa2f47c1dab4.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20099.
The public definitions transcribe Appendix C of arXiv:2312.14837v2.
The parameter order in the private recurrence is a=h/(y*w), b=h*w/y,
c=h*y*w, d=h*y/w, where h=q^(p+1) and Q=q^2.
Vanishing of the terminal A coefficient and repeated Darboux shifts prove the product.
No declaration is a finite certificate, enumeration, checker, or numerical reduction;
utility is none because the statements and recurrence proofs are uniform in all degrees.

IMDAW.shift_off | proof_shape: bind-only | consumers: IMDAW.shift_transform
IMDAW.shift_diag0 | proof_shape: bind-only | consumers: IMDAW.shift_transform
IMDAW.shift_diag | proof_shape: bind-only | consumers: IMDAW.shift_transform
IMDDarboux.transform | proof_shape: content | consumers: IMDAW.shift_transform
IMDAW.regular_shift | proof_shape: bind-only | consumers: IMDAW.terminal_factorization
IMDAW.regular_den | proof_shape: bind-only | consumers: IMDAW.regular_square, IMDAW.shift_transform, IMDAW.source_initial
IMDAW.regular_square | proof_shape: bind-only | consumers: IMDAW.shift_transform, IMDAW.source_step_coefficients
IMDAW.shift_transform | proof_shape: content | consumers: IMDAW.terminal_factorization
IMDAW.a_vanish | proof_shape: bind-only | consumers: IMDAW.terminal_factorization
IMDAW.terminal_factorization | proof_shape: content | consumers: seed_terminal
IMDAW.a_mul_var | proof_shape: bind-only | consumers: IMDAW.diag_symmetric
IMDAW.diag_symmetric | proof_shape: bind-only | consumers: IMDAW.diag_h
IMDAW.parameter_invariants | proof_shape: bind-only | consumers: IMDAW.diag_h, IMDAW.off_h, IMDAW.beta0_h, IMDAW.source_regular, IMDAW.source_initial, IMDAW.source_step_coefficients
IMDAW.diag_h | proof_shape: bind-only | consumers: IMDAW.diag_source
IMDAW.off_h | proof_shape: bind-only | consumers: IMDAW.off_h_source
IMDAW.beta0_h | proof_shape: bind-only | consumers: IMDAW.source_initial
IMDAW.beta_source | proof_shape: bind-only | consumers: IMDAW.diag_source
al_diff | proof_shape: bind-only | consumers: off_source
off_denominator | proof_shape: bind-only | consumers: off_source
off_source | proof_shape: bind-only | consumers: IMDAW.off_h_source
power_sub_inv_ne | proof_shape: bind-only | consumers: IMDAW.source_step_coefficients
qcb_nat | proof_shape: bind-only | consumers: IMDAW.source_initial
symmetric_exponent_sum | proof_shape: bind-only | consumers: product_linear
prod_zpow_range | proof_shape: bind-only | consumers: product_linear
product_factor | proof_shape: bind-only | consumers: product_linear
product_linear | proof_shape: bind-only | consumers: seed_terminal
IMDAW.diag_source | proof_shape: bind-only | consumers: IMDAW.source_step_coefficients
IMDAW.off_h_source | proof_shape: bind-only | consumers: IMDAW.source_step_coefficients
qcb_al | proof_shape: bind-only | consumers: qcb_nat, IMDAW.source_step_coefficients
qpow_double_minus | proof_shape: bind-only | consumers: qbr_pair
qpow_double_plus | proof_shape: bind-only | consumers: qbr_pair
qbr_pair | proof_shape: bind-only | consumers: IMDAW.source_step_coefficients
IMDAW.plus_den | proof_shape: bind-only | consumers: IMDAW.source_initial, IMDAW.source_step_coefficients
IMDAW.source_regular | proof_shape: bind-only | consumers: IMDAW.source_initial, IMDAW.source_step_coefficients, seed_terminal
IMDAW.source_initial | proof_shape: bind-only | consumers: seed_eq_aw
IMDAW.source_step_coefficients | proof_shape: bind-only | consumers: seed_eq_aw
seed_eq_aw | proof_shape: content | consumers: seed_terminal
parameter_power | proof_shape: bind-only | consumers: seed_terminal
terminal_ab | proof_shape: bind-only | consumers: seed_terminal
seed_terminal | proof_shape: content | consumers: result
qcb_square | proof_shape: bind-only | consumers: sigma_coeff
sigma_coeff | proof_shape: bind-only | consumers: sigma_eq_seed
sigma_eq_seed | proof_shape: content | consumers: result
prod_zpow_range, product_linear and seed_terminal have Direct frozen dependencies:
NikolovSegal.UnitaryField.prod_zpow_base; all other listed helpers: none.
IMDDarboux.transform | escape_witness: IMDDarboux.transform
IMDAW.shift_transform | escape_witness: IMDDarboux.transform
IMDAW.terminal_factorization | escape_witness: IMDAW.terminal_factorization
seed_eq_aw | escape_witness: seed_eq_aw
seed_terminal | escape_witness: IMDAW.terminal_factorization
sigma_eq_seed | escape_witness: sigma_eq_seed
All bind-only helpers have escape_witness: none.
-/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalGeometry
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.PeriodicTemperleyLiebSeedProduct


/-- `[k] = (q^k - q^{-k}) / (q - q^{-1})`. -/
noncomputable def qbr (q : ℂ) (k : ℤ) : ℂ := (q ^ k - q ^ (-k)) / (q - q⁻¹)

/-- `{k} = q^k + q^{-k}`. -/
noncomputable def qcb (q : ℂ) (k : ℤ) : ℂ := q ^ k + q ^ (-k)

/-- `α_z = z + z^{-1}`. -/
noncomputable def al (z : ℂ) : ℂ := z + z⁻¹

/-- Proposition C.1, (C.3)–(C.4): `X^{(p)}_{p+n}(ω, x, y)` for `n = 0, 1, 2, …`. -/
noncomputable def seedX (q x y w : ℂ) (p : ℕ) : ℕ → ℂ
  | 0 => 1
  | 1 => al x + al y * al w / qcb q (p + 1)
  | n + 2 =>
    let k : ℤ := p + n + 1
    (al x + al (q ^ p) * al y * al w / (qcb q k * qcb q (k + 1))) * seedX q x y w p (n + 1) +
      (al (q ^ p) ^ 2 - qcb q k ^ 2) * (al y ^ 2 - qcb q k ^ 2) * (al w ^ 2 - qcb q k ^ 2) /
        ((q - q⁻¹) ^ 2 * qbr q (2 * k - 1) * qbr q (2 * k + 1) * qcb q k ^ 2) * seedX q x y w p n

/-- Proposition C.2, (C.24)–(C.25): `σ^{(0)}_{0,n}(w, x, y)`. -/
noncomputable def seedSigma (q x y w : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => al x + al y * al w / qcb q 1
  | n + 2 =>
    let k : ℤ := n + 1
    (al x + 2 * al y * al w / (qcb q k * qcb q (k + 1))) * seedSigma q x y w (n + 1) -
      qbr q k ^ 2 * (al y ^ 2 - qcb q k ^ 2) * (al w ^ 2 - qcb q k ^ 2) /
        (qbr q (2 * k + 1) * qbr q (2 * k - 1) * qcb q k ^ 2) * seedSigma q x y w n

/-- `(ωx)^{p-m} ∏_{r=-(m-p-1)/2}^{(m-p-1)/2} (x q^{2r} + εω)(ε q^{2r} + xω)`, with `2r = -N+1+2j`,
`N = m - p`. -/
noncomputable def seedProduct (q x w ε : ℂ) (N : ℕ) : ℂ :=
  (w * x) ^ (-(N : ℤ)) * ∏ j ∈ Finset.range N,
    (x * q ^ (-(N : ℤ) + 1 + 2 * j) + ε * w) * (ε * q ^ (-(N : ℤ) + 1 + 2 * j) + x * w)

/-- Conjectures C.1 and C.2 (Ikhlef–Morin-Duchesne): for `q, x, ω ∈ ℂˣ` with `q` not a root of
unity and `ε = ±1`, `X^{(p)}_m(ω, x, εq^m) = (ωx)^{p-m} ∏ (x q^{2r} + εω)(ε q^{2r} + xω)` for
`1 ≤ p ≤ m` (C.5), and `σ^{(0)}_{0,m}(w, x, εq^m) = (wx)^{-m} ∏ (x q^{2r} + εw)(ε q^{2r} + xw)`
for `m ≥ 0` (C.26). -/
def claim : Prop :=
  ∀ q x w ε : ℂ, q ≠ 0 → x ≠ 0 → w ≠ 0 → (∀ n : ℕ, 1 ≤ n → q ^ n ≠ 1) → (ε = 1 ∨ ε = -1) →
    (∀ p m : ℕ, 1 ≤ p → p ≤ m → seedX q x (ε * q ^ m) w p (m - p) = seedProduct q x w ε (m - p)) ∧
    (∀ m : ℕ, seedSigma q x (ε * q ^ m) w m = seedProduct q x w ε m)


set_option maxHeartbeats 3000000

namespace IMDAW

private noncomputable def A (Q a b c d v : ℂ) : ℂ :=
  (1-a*b*v)*(1-a*c*v)*(1-a*d*v)*(Q-a*b*c*d*v) /
    (a*(Q-a*b*c*d*v^2)*(1-a*b*c*d*v^2))

private noncomputable def C (Q a b c d v : ℂ) : ℂ :=
  a*(1-Q*v)*(1-b*c*v)*(1-b*d*v)*(1-c*d*v) /
    ((1-a*b*c*d*v^2)*(1-a*b*c*d*Q*v^2))

private noncomputable def P (Q a b c d T : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => T - (a+a⁻¹) + A Q a b c d 1
  | n+2 => (T-(a+a⁻¹)+A Q a b c d (Q^(n+1))+C Q a b c d (Q^n))*P Q a b c d T (n+1)
    - A Q a b c d (Q^n)*C Q a b c d (Q^n)*P Q a b c d T n

private theorem shift_off (Q a b c d v : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (h0 : 1-a*b*c*d*v^2 ≠ 0)
    (h1 : 1-a*b*c*d*Q*v^2 ≠ 0)
    (h2 : 1-a*b*c*d*Q^2*v^2 ≠ 0) :
    A Q (a*Q) b c d v * C Q (a*Q) b c d v =
      A Q a b c d (Q*v) * C Q a b c d v := by
  have hh0 := mul_ne_zero hQ h0
  have hh1 := mul_ne_zero hQ h1
  have hh2 := mul_ne_zero hQ h2
  ring_nf at h0 h1 h2 hh0 hh1 hh2
  unfold A C
  field_simp (disch := first | assumption | (ring_nf; assumption))
  <;> ring

private theorem shift_diag0 (Q a b c d : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (hm : Q-a*b*c*d ≠ 0)
    (h0 : 1-a*b*c*d ≠ 0)
    (h1 : 1-a*b*c*d*Q ≠ 0) :
    -(a*Q+(a*Q)⁻¹)+ A Q (a*Q) b c d 1 =
      -(a+a⁻¹)+A Q a b c d 1 + C Q a b c d 1 := by
  unfold A C
  field_simp (disch := first
    | assumption
    | positivity
    | (convert h0 using 1 <;> (ring_nf; done))
    | (convert h1 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h0 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h1 using 1 <;> (ring_nf; done))
    )
  <;> ring

private theorem shift_diag (Q a b c d v : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (h0 : 1-a*b*c*d*v^2 ≠ 0)
    (h1 : 1-a*b*c*d*Q*v^2 ≠ 0)
    (h2 : 1-a*b*c*d*Q^2*v^2 ≠ 0)
    (h3 : 1-a*b*c*d*Q^3*v^2 ≠ 0) :
    -(a*Q+(a*Q)⁻¹)+A Q (a*Q) b c d (Q*v)+C Q (a*Q) b c d v =
      -(a+a⁻¹)+A Q a b c d (Q*v)+C Q a b c d (Q*v) := by
  unfold A C
  field_simp (disch := first
    | assumption
    | positivity
    | (convert h0 using 1 <;> (ring_nf; done))
    | (convert h1 using 1 <;> (ring_nf; done))
    | (convert h2 using 1 <;> (ring_nf; done))
    | (convert h3 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h0 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h1 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h2 using 1 <;> (ring_nf; done))
    | (convert mul_ne_zero hQ h3 using 1 <;> (ring_nf; done))
    )
  <;> ring

end IMDAW


namespace IMDDarboux

private theorem transform (T z : ℂ) (A C f g : ℕ → ℂ)
    (hf0 : f 0 = 1) (hg0 : g 0 = 1)
    (hf1 : f 1 = T-z+A 0) (hg1 : g 1 = T-z+A 0+C 1)
    (hf : ∀ n, f (n+2) = (T-z+A (n+1)+C (n+1))*f (n+1)-A n*C (n+1)*f n)
    (hg : ∀ n, g (n+2) = (T-z+A (n+1)+C (n+2))*g (n+1)-A (n+1)*C (n+1)*g n) :
    ∀ n, f (n+1) = g (n+1)-C (n+1)*g n ∧
      (T-z)*g n = f (n+1)-A n*f n := by
  intro n
  induction n with
  | zero =>
    constructor <;> simp only [zero_add, hf0, hg0, hf1, hg1] <;> ring
  | succ n ih =>
    constructor
    · linear_combination hf n - hg n + (T-z+A (n+1))*ih.1 - C (n+1)*ih.2
    · linear_combination -hf n - (T-z)*ih.1 + C (n+1)*ih.2

end IMDDarboux

namespace IMDAW

private def Regular (Q a b c d : ℂ) : Prop := ∀ n : ℕ, Q-a*b*c*d*Q^n ≠ 0

private theorem regular_shift (Q a b c d : ℂ) (hr : Regular Q a b c d) :
    Regular Q (a*Q) b c d := by
  intro n
  have he : Q-(a*Q)*b*c*d*Q^n = Q-a*b*c*d*Q^(n+1) := by
    rw [pow_succ]; ring
  rw [he]
  exact hr (n+1)

private theorem regular_den (Q a b c d : ℂ) (hr : Regular Q a b c d) (n : ℕ) :
    1-a*b*c*d*Q^n ≠ 0 := by
  intro he
  apply hr (n+1)
  calc
    Q-a*b*c*d*Q^(n+1) = Q*(1-a*b*c*d*Q^n) := by rw [pow_succ]; ring
    _ = 0 := by rw [he, mul_zero]

private theorem regular_square (Q a b c d : ℂ) (hr : Regular Q a b c d) (n j : ℕ) :
    1-a*b*c*d*Q^j*(Q^n)^2 ≠ 0 := by
  convert regular_den Q a b c d hr (n*2+j) using 1 <;>
    rw [pow_add, pow_mul] <;> ring

private theorem shift_transform (Q a b c d T : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (hr : Regular Q a b c d) (n : ℕ) :
    (T-(a+a⁻¹))*P Q (a*Q) b c d T n =
      P Q a b c d T (n+1) - A Q a b c d (Q^n)*P Q a b c d T n := by
  let aa : ℕ → ℂ := fun n => A Q a b c d (Q^n)
  let cc : ℕ → ℂ | 0 => 0 | n+1 => C Q a b c d (Q^n)
  have h0 := regular_den Q a b c d hr 0
  have h1 := regular_den Q a b c d hr 1
  have hm := hr 0
  simp only [pow_zero, mul_one] at h0 hm
  simp only [pow_one] at h1
  have hd0 := shift_diag0 Q a b c d hQ ha hm h0 h1
  have hg1 : P Q (a*Q) b c d T 1 = T-(a+a⁻¹)+aa 0+cc 1 := by
    simp only [P, aa, cc, pow_zero]
    linear_combination hd0
  have hg : ∀ k, P Q (a*Q) b c d T (k+2) =
      (T-(a+a⁻¹)+aa (k+1)+cc (k+2))*P Q (a*Q) b c d T (k+1) -
        aa (k+1)*cc (k+1)*P Q (a*Q) b c d T k := by
    intro k
    have hh0 := regular_square Q a b c d hr k 0
    have hh1 := regular_square Q a b c d hr k 1
    have hh2 := regular_square Q a b c d hr k 2
    have hh3 := regular_square Q a b c d hr k 3
    simp only [pow_zero, pow_one, mul_one] at hh0 hh1
    have hd := shift_diag Q a b c d (Q^k) hQ ha hh0 hh1 hh2 hh3
    have ho := shift_off Q a b c d (Q^k) hQ ha hh0 hh1 hh2
    simp only [aa, cc, P]
    simp only [pow_succ] at hd ho ⊢
    simp only [mul_comm (Q^k) Q] at hd ho ⊢
    linear_combination P Q (a*Q) b c d T (k+1)*hd -
      P Q (a*Q) b c d T k*ho
  exact (IMDDarboux.transform T (a+a⁻¹) aa cc
    (P Q a b c d T) (P Q (a*Q) b c d T) rfl rfl
    (by simp [P, aa]) hg1 (by intro k; rfl) hg n).2

private theorem a_vanish (Q a b c d : ℂ) (N : ℕ) (hab : a*b*Q^N = 1) :
    A Q a b c d (Q^N) = 0 := by
  unfold A
  rw [hab]
  simp

private theorem terminal_factorization (Q a b c d T : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (hr : Regular Q a b c d) (N : ℕ) (hab : a*b*Q^N = 1) :
    P Q a b c d T (N+1) =
      ∏ j ∈ Finset.range (N+1), (T-(a*Q^j+(a*Q^j)⁻¹)) := by
  induction N generalizing a with
  | zero =>
    have he := a_vanish Q a b c d 0 hab
    simp only [pow_zero] at he
    simp [P, he]
  | succ N ih =>
    have he := shift_transform Q a b c d T hQ ha hr (N+1)
    rw [a_vanish Q a b c d (N+1) hab, zero_mul, sub_zero] at he
    rw [← he]
    have hs : (a*Q)*b*Q^N = 1 := by
      calc
        (a*Q)*b*Q^N = a*b*Q^(N+1) := by rw [pow_succ]; ring
        _ = 1 := hab
    rw [ih (a*Q) (mul_ne_zero ha hQ) (regular_shift Q a b c d hr) hs]
    conv_rhs => rw [Finset.prod_range_succ']
    simp only [pow_zero, mul_one]
    conv_rhs => rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hc : (a*Q)*Q^j = a*Q^(j+1) := by
      simpa only [mul_assoc] using congrArg (fun z : ℂ => a*z) (pow_succ' Q j).symm
    rw [hc]

end IMDAW

namespace IMDAW

private theorem a_mul_var (Q a b c d v : ℂ) (hQ : Q ≠ 0) :
    A Q a b c d (Q*v) =
      (1-a*b*Q*v)*(1-a*c*Q*v)*(1-a*d*Q*v)*(1-a*b*c*d*v) /
        (a*(1-a*b*c*d*Q*v^2)*(1-a*b*c*d*Q^2*v^2)) := by
  unfold A
  calc
    _ = (Q*((1-a*b*Q*v)*(1-a*c*Q*v)*(1-a*d*Q*v)*(1-a*b*c*d*v))) /
        (Q*(a*(1-a*b*c*d*Q*v^2)*(1-a*b*c*d*Q^2*v^2))) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ hQ

private theorem diag_symmetric (Q a b c d v : ℂ) (hQ : Q ≠ 0) (ha : a ≠ 0)
    (h0 : 1-a*b*c*d*v^2 ≠ 0)
    (h1 : 1-a*b*c*d*Q*v^2 ≠ 0)
    (h2 : 1-a*b*c*d*Q^2*v^2 ≠ 0) :
    a+a⁻¹-A Q a b c d (Q*v)-C Q a b c d v =
      v*((a+b+c+d)*(Q+a*b*c*d*Q^2*v^2-a*b*c*d*Q*v-a*b*c*d*v)+
        (a*b*c+a*b*d+a*c*d+b*c*d)*(1+a*b*c*d*Q*v^2-Q*v-Q^2*v)) /
      ((1-a*b*c*d*v^2)*(1-a*b*c*d*Q^2*v^2)) := by
  rw [a_mul_var Q a b c d v hQ]
  unfold C
  let R := a*b*c*d
  let D0 := 1-R*v^2
  let D1 := 1-R*Q*v^2
  let D2 := 1-R*Q^2*v^2
  let NA := (1-a*b*Q*v)*(1-a*c*Q*v)*(1-a*d*Q*v)*(1-R*v)
  let NC := a*(1-Q*v)*(1-b*c*v)*(1-b*d*v)*(1-c*d*v)
  let S := v*((a+b+c+d)*(Q+R*Q^2*v^2-R*Q*v-R*v)+
    (a*b*c+a*b*d+a*c*d+b*c*d)*(1+R*Q*v^2-Q*v-Q^2*v))
  change a+a⁻¹-NA/(a*D1*D2)-NC/(D0*D1) = S/(D0*D2)
  have hd0 : D0 ≠ 0 := h0
  have hd1 : D1 ≠ 0 := h1
  have hd2 : D2 ≠ 0 := h2
  apply (eq_div_iff (mul_ne_zero hd0 hd2)).2
  apply (mul_right_inj' (mul_ne_zero ha hd1)).mp
  have hai : (a+a⁻¹)*a = a^2+1 := by rw [add_mul, inv_mul_cancel₀ ha]; ring
  calc
    _ = ((a+a⁻¹)*a)*D0*D1*D2 -
        (NA/(a*D1*D2))*(a*D1*D2)*D0 - (NC/(D0*D1))*(D0*D1)*(a*D2) := by ring
    _ = (a^2+1)*D0*D1*D2-NA*D0-NC*(a*D2) := by
      rw [div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero ha hd1) hd2),
        div_mul_cancel₀ _ (mul_ne_zero hd0 hd1), hai]
    _ = (a*D1)*S := by dsimp [S, NA, NC, D0, D1, D2, R]; ring

private theorem parameter_invariants (h y w : ℂ) (hy : y ≠ 0) (hw : w ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    a*b*c*d = h^4 ∧ a+b+c+d = h*al y*al w ∧
      a*b*c+a*b*d+a*c*d+b*c*d = h^3*al y*al w := by
  dsimp
  unfold al
  constructor
  · field_simp <;> ring
  constructor <;> field_simp <;> ring

private theorem diag_h (Q h y w v : ℂ) (hQ : Q ≠ 0) (hh : h ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (h0 : 1-h^4*v^2 ≠ 0) (h1 : 1-h^4*Q*v^2 ≠ 0) (h2 : 1-h^4*Q^2*v^2 ≠ 0)
    (hp0 : 1+h^2*v ≠ 0) (hp1 : 1+h^2*Q*v ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    a+a⁻¹-A Q a b c d (Q*v)-C Q a b c d v =
      h*al y*al w*v*(Q+h^2) / ((1+h^2*v)*(1+h^2*Q*v)) := by
  dsimp
  have hi := parameter_invariants h y w hy hw
  have hd := diag_symmetric Q (h/(y*w)) (h*w/y) (h*y*w) (h*y/w) v hQ
    (div_ne_zero hh (mul_ne_zero hy hw))
    (by simpa only [hi.1] using h0) (by simpa only [hi.1] using h1)
    (by simpa only [hi.1] using h2)
  rw [hd, hi.1, hi.2.1, hi.2.2]
  have hm0 : 1-h^2*v ≠ 0 := by
    intro he
    apply h0
    calc
      1-h^4*v^2 = (1-h^2*v)*(1+h^2*v) := by ring
      _ = 0 := by rw [he, zero_mul]
  have hm1 : 1-h^2*Q*v ≠ 0 := by
    intro he
    apply h2
    calc
      1-h^4*Q^2*v^2 = (1-h^2*Q*v)*(1+h^2*Q*v) := by ring
      _ = 0 := by rw [he, zero_mul]
  calc
    _ = (((1-h^2*v)*(1-h^2*Q*v))*(h*al y*al w*v*(Q+h^2))) /
        (((1-h^2*v)*(1-h^2*Q*v))*((1+h^2*v)*(1+h^2*Q*v))) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero hm0 hm1)

private theorem off_h (Q h y w v : ℂ) (hQ : Q ≠ 0) (hh : h ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hm : Q-h^4*v^2 ≠ 0) (h0 : 1-h^4*v^2 ≠ 0) (h1 : 1-h^4*Q*v^2 ≠ 0)
    (hp : 1+h^2*v ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    A Q a b c d v*C Q a b c d v =
      (1-Q*v)*(Q-h^4*v)*(1-h^2*y^2*v)*(1-h^2/y^2*v)*
        (1-h^2*w^2*v)*(1-h^2/w^2*v) /
      ((Q-h^4*v^2)*(1-h^4*Q*v^2)*(1+h^2*v)^2) := by
  dsimp
  unfold A C
  have hi := (parameter_invariants h y w hy hw).1
  simp only [hi]
  field_simp
  <;> ring

end IMDAW
namespace IMDAW

private theorem beta0_h (Q h y w : ℂ) (hQ : Q ≠ 0) (hh : h ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hm : Q-h^4 ≠ 0) (h0 : 1-h^4 ≠ 0) (hp : 1+h^2 ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    a+a⁻¹-A Q a b c d 1 = al y*al w/al h := by
  dsimp
  unfold A
  have hi := (parameter_invariants h y w hy hw).1
  simp only [hi, one_pow, mul_one]
  have hal : al h ≠ 0 := by
    unfold al
    intro he
    apply hp
    have he' := congrArg (fun z : ℂ => z*h) he
    field_simp at he'
    linear_combination he'
  unfold al at *
  field_simp (disch := first | assumption | (intro hz; apply hh; linear_combination hz; done) | (intro hz; apply hy; linear_combination hz; done) | (intro hz; apply hw; linear_combination hz; done) | (intro hz; apply hm; linear_combination hz; done) | (intro hz; apply h0; linear_combination hz; done) | (intro hz; apply hp; linear_combination hz; done) | (intro hz; apply hal; linear_combination hz; done)) <;> ring_nf <;> field_simp (disch := first | assumption | (intro hz; apply hh; linear_combination hz; done) | (intro hz; apply hy; linear_combination hz; done) | (intro hz; apply hw; linear_combination hz; done) | (intro hz; apply hm; linear_combination hz; done) | (intro hz; apply h0; linear_combination hz; done) | (intro hz; apply hp; linear_combination hz; done) | (intro hz; apply hal; linear_combination hz; done))
  <;> ring

private theorem beta_source (q h s : ℂ) (hq : q ≠ 0) (hh : h ≠ 0) (hs : s ≠ 0)
    (h0 : 1+h^2*s^2 ≠ 0) (h1 : 1+h^2*q^2*s^2 ≠ 0) :
    h*s^2*(q^2+h^2)/((1+h^2*s^2)*(1+h^2*q^2*s^2)) =
      al (h/q) / (al (h*s)*al (q*h*s)) := by
  have hA : al (h/q) = (h^2+q^2)/(q*h) := by
    unfold al; field_simp <;> ring
  have hB : al (h*s) = (1+h^2*s^2)/(h*s) := by
    unfold al; field_simp <;> ring
  have hC : al (q*h*s) = (1+h^2*q^2*s^2)/(q*h*s) := by
    unfold al; field_simp <;> ring
  rw [hA, hB, hC]
  field_simp [hq, hh, hs, h0, h1]
  <;> ring
end IMDAW


private theorem al_diff (z t : ℂ) (hz : z ≠ 0) (ht : t ≠ 0) :
    al z^2-al t^2 = -(1-z^2*t^2)*(1-z⁻¹^2*t^2)/t^2 := by
  unfold al
  field_simp
  <;> ring

private theorem off_denominator (q t : ℂ) (hq : q ≠ 0) (ht : t ≠ 0) (hd : q-q⁻¹ ≠ 0) :
    (q-q⁻¹)^2*((t^2/q-(t^2/q)⁻¹)/(q-q⁻¹))*
      ((q*t^2-(q*t^2)⁻¹)/(q-q⁻¹))*al t^2 =
      (1-t^4/q^2)*(1-q^2*t^4)*(1+t^2)^2/t^6 := by
  have hq2 : q^2-1 ≠ 0 := by
    have he : q^2-1 = q*(q-q⁻¹) := by field_simp <;> ring
    rw [he]
    exact mul_ne_zero hq hd
  unfold al
  field_simp (disch := first | assumption | (intro hz; apply hq; linear_combination hz; done) | (intro hz; apply ht; linear_combination hz; done) | (intro hz; apply hd; linear_combination hz; done) | (intro hz; apply hq2; linear_combination hz; done)) <;> ring_nf <;> field_simp (disch := first | assumption | (intro hz; apply hq; linear_combination hz; done) | (intro hz; apply ht; linear_combination hz; done) | (intro hz; apply hd; linear_combination hz; done) | (intro hz; apply hq2; linear_combination hz; done))
  <;> ring

private theorem off_source (q r t y w : ℂ) (hq : q ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0)
    (hy : y ≠ 0) (hw : w ≠ 0) (hd : q-q⁻¹ ≠ 0)
    (hm : 1-t^4/q^2 ≠ 0) (hp : 1-q^2*t^4 ≠ 0) (hc : 1+t^2 ≠ 0) :
    (al r^2-al t^2)*(al y^2-al t^2)*(al w^2-al t^2) /
      ((q-q⁻¹)^2*((t^2/q-(t^2/q)⁻¹)/(q-q⁻¹))*
        ((q*t^2-(q*t^2)⁻¹)/(q-q⁻¹))*al t^2) =
      -((1-r^2*t^2)*(1-r⁻¹^2*t^2)*(1-y^2*t^2)*(1-y⁻¹^2*t^2)*
        (1-w^2*t^2)*(1-w⁻¹^2*t^2) /
      ((1-t^4/q^2)*(1-q^2*t^4)*(1+t^2)^2)) := by
  rw [off_denominator q t hq ht hd, al_diff r t hr ht,
    al_diff y t hy ht, al_diff w t hw ht]
  field_simp
  <;> ring



private theorem power_sub_inv_ne (q : ℂ) (hq : q ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (n : ℕ) (hn : 1 ≤ n) :
    q^n-(q^n)⁻¹ ≠ 0 := by
  intro he
  have he' := congrArg (fun z : ℂ => z*q^n) he
  simp only [sub_mul, zero_mul, inv_mul_cancel₀ (pow_ne_zero n hq)] at he'
  apply hroot (n*2) (by omega)
  simpa only [pow_mul, pow_two] using sub_eq_zero.mp he'

private theorem qcb_al (q : ℂ) (k : ℤ) : qcb q k = al (q^k) := by
  simp only [qcb, al, zpow_neg]

private theorem qcb_nat (q : ℂ) (n : ℕ) : qcb q n = al (q^n) := by
  simpa only [zpow_natCast] using qcb_al q (n : ℤ)

private theorem symmetric_exponent_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, (-(N:ℤ)+1+2*j)) = 0 := by
  cases N with
  | zero => simp
  | succ n =>
    have h := congrArg (fun k : ℕ => (k : ℤ)) (Finset.sum_range_id_mul_two (n+1))
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.add_sub_cancel] at h
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum]
    push_cast at h ⊢
    linear_combination h

private theorem prod_zpow_range (q : ℂ) (hq : q ≠ 0) (f : ℕ → ℤ) (N : ℕ) :
    (∏ j ∈ Finset.range N, q^(f j)) = q^(∑ j ∈ Finset.range N, f j) := by
  simpa using congrArg (fun z : ℂˣ => (z : ℂ))
    (NikolovSegal.UnitaryField.prod_zpow_base (Finset.range N) (Units.mk0 q hq) f)

private theorem product_factor (x w t ε : ℂ) (hx : x ≠ 0) (hw : w ≠ 0) (ht : t ≠ 0)
    (hε : ε = 1 ∨ ε = -1) :
    (x*t+ε*w)*(ε*t+x*w) = (x*w)*t*(al x+al (ε*t/w)) := by
  rcases hε with rfl | rfl <;> unfold al <;> field_simp <;> ring

private theorem product_linear (q x w ε : ℂ) (hq : q ≠ 0) (hx : x ≠ 0) (hw : w ≠ 0)
    (hε : ε = 1 ∨ ε = -1) (N : ℕ) :
    seedProduct q x w ε N =
      ∏ j ∈ Finset.range N, (al x+al (ε*q^(-(N:ℤ)+1+2*j)/w)) := by
  unfold seedProduct
  have hf (j : ℕ) := product_factor x w (q^(-(N:ℤ)+1+2*j)) ε hx hw
    (zpow_ne_zero _ hq) hε
  simp_rw [hf]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [prod_zpow_range q hq, symmetric_exponent_sum, zpow_zero]
  have hi : (w*x)^(-(N:ℤ))*(x*w)^N = 1 := by
    simpa only [mul_comm x w, zpow_natCast] using
      (zpow_neg_mul_zpow_self (N : ℤ) (mul_ne_zero hw hx))
  calc
    _ = ((w*x)^(-(N:ℤ))*(x*w)^N)*
        (∏ j ∈ Finset.range N, (al x+al (ε*q^(-(N:ℤ)+1+2*j)/w))) := by ring
    _ = _ := by rw [hi, one_mul]


namespace IMDAW

private theorem diag_source (q h s y w : ℂ) (hq : q ≠ 0) (hh : h ≠ 0)
    (hs : s ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (h0 : 1-h^4*s^4 ≠ 0) (h1 : 1-h^4*q^2*s^4 ≠ 0)
    (h2 : 1-h^4*q^4*s^4 ≠ 0) (hp0 : 1+h^2*s^2 ≠ 0) (hp1 : 1+h^2*q^2*s^2 ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    a+a⁻¹-A (q^2) a b c d (q^2*s^2)-C (q^2) a b c d (s^2) =
      al (h/q)*al y*al w /
        (al (h*s)*al (q*h*s)) := by
  dsimp
  have hd := diag_h (q^2) h y w (s^2) (pow_ne_zero 2 hq) hh hy hw
    (by convert h0 using 2 <;> ring) (by convert h1 using 2 <;> ring)
    (by convert h2 using 2 <;> ring) hp0 (by convert hp1 using 2 <;> ring)
  rw [hd]
  calc
    _ = (al y*al w)*
        (h*s^2*(q^2+h^2)/((1+h^2*s^2)*(1+h^2*q^2*s^2))) := by ring
    _ = _ := by rw [beta_source q h s hq hh hs hp0 hp1]; ring

private theorem off_h_source (q h s y w : ℂ) (hq : q ≠ 0) (hh : h ≠ 0)
    (hs : s ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0) (hd : q-q⁻¹ ≠ 0)
    (hm : q^2-h^4*s^4 ≠ 0) (h0 : 1-h^4*s^4 ≠ 0)
    (h1 : 1-h^4*q^2*s^4 ≠ 0) (hp : 1+h^2*s^2 ≠ 0) :
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    A (q^2) a b c d (s^2)*C (q^2) a b c d (s^2) =
      -((al (h/q)^2-al (h*s)^2)*
        (al y^2-al (h*s)^2)*(al w^2-al (h*s)^2) /
      ((q-q⁻¹)^2*(((h*s)^2/q-((h*s)^2/q)⁻¹)/(q-q⁻¹))*
        ((q*(h*s)^2-(q*(h*s)^2)⁻¹)/(q-q⁻¹))*al (h*s)^2)) := by
  dsimp
  have hma : 1-(h*s)^4/q^2 ≠ 0 := by
    have he : 1-(h*s)^4/q^2 = (q^2-h^4*s^4)/q^2 := by field_simp <;> ring
    rw [he]
    exact div_ne_zero hm (pow_ne_zero 2 hq)
  have hpa : 1-q^2*(h*s)^4 ≠ 0 := by convert h1 using 2 <;> ring
  have hca : 1+(h*s)^2 ≠ 0 := by convert hp using 2 <;> ring
  rw [off_source q (h/q) (h*s) y w hq (div_ne_zero hh hq)
    (mul_ne_zero hh hs) hy hw hd hma hpa hca]
  rw [off_h (q^2) h y w (s^2) (pow_ne_zero 2 hq) hh hy hw
    (by convert hm using 2 <;> ring) (by convert h0 using 2 <;> ring)
    (by convert h1 using 2 <;> ring) hp]
  ring_nf at hm h1 hp
  field_simp (disch := first | assumption | (ring_nf; assumption))
  <;> ring

end IMDAW


private theorem qpow_double_minus (q : ℂ) (hq : q ≠ 0) (k : ℤ) :
    q^(2*k-1) = (q^k)^2/q := by
  simpa only [zpow_mul', zpow_ofNat, div_eq_mul_inv] using zpow_sub_one₀ hq (2*k)

private theorem qpow_double_plus (q : ℂ) (hq : q ≠ 0) (k : ℤ) :
    q^(2*k+1) = q*(q^k)^2 := by
  calc
    q^(2*k+1) = q^(k+k+1) := by congr 1; ring
    _ = q^k*q^k*q := by rw [zpow_add₀ hq, zpow_add₀ hq, zpow_one]
    _ = _ := by ring

private theorem qbr_pair (q : ℂ) (hq : q ≠ 0) (k : ℤ) :
    qbr q (2*k-1) = ((q^k)^2/q-((q^k)^2/q)⁻¹)/(q-q⁻¹) ∧
    qbr q (2*k+1) = (q*(q^k)^2-(q*(q^k)^2)⁻¹)/(q-q⁻¹) := by
  simp only [qbr, zpow_neg, qpow_double_minus q hq, qpow_double_plus q hq, and_self]


namespace IMDAW

private theorem plus_den (h v : ℂ) (hr : 1-h^4*v^2 ≠ 0) : 1+h^2*v ≠ 0 := by
  intro he
  apply hr
  calc
    1-h^4*v^2 = (1-h^2*v)*(1+h^2*v) := by ring
    _ = 0 := by rw [he, mul_zero]

private theorem source_regular (q y w : ℂ) (hq : q ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (p : ℕ) :
    let h := q^(p+1)
    Regular (q^2) (h/(y*w)) (h*w/y) (h*y*w) (h*y/w) := by
  dsimp only
  intro n
  rw [(parameter_invariants (q^(p+1)) y w hy hw).1]
  have he : q^2-(q^(p+1))^4*(q^2)^n = q^2*(1-q^(4*p+2+2*n)) := by
    simp only [mul_sub, mul_one, ← pow_mul, ← pow_add]
    congr 1
    congr 1
    omega
  rw [he]
  exact mul_ne_zero (pow_ne_zero 2 hq)
    (sub_ne_zero.mpr (Ne.symm (hroot (4*p+2+2*n) (by omega))))

private theorem source_initial (q y w : ℂ) (hq : q ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (p : ℕ) :
    let h := q^(p+1)
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    a+a⁻¹-A (q^2) a b c d 1 = al y*al w/qcb q (p+1) := by
  dsimp only
  have hr := source_regular q y w hq hy hw hroot p
  have hi := (parameter_invariants (q^(p+1)) y w hy hw).1
  have hm := hr 0
  have h0 := regular_den _ _ _ _ _ hr 0
  simp only [hi, pow_zero, mul_one] at hm h0
  have hp := plus_den (q^(p+1)) 1 (by simpa using h0)
  simp only [mul_one] at hp
  have hc := qcb_nat q (p+1)
  simp only [Nat.cast_add, Nat.cast_one] at hc
  rw [hc]
  exact beta0_h (q^2) (q^(p+1)) y w (pow_ne_zero 2 hq)
    (pow_ne_zero (p+1) hq) hy hw hm h0 hp

private theorem source_step_coefficients (q y w : ℂ) (hq : q ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (p n : ℕ) :
    let h := q^(p+1)
    let a := h/(y*w); let b := h*w/y; let c := h*y*w; let d := h*y/w
    let k : ℤ := p+n+1
    (a+a⁻¹-A (q^2) a b c d ((q^2)^(n+1))-C (q^2) a b c d ((q^2)^n) =
      al (q^p)*al y*al w /
        (qcb q k*qcb q (k+1))) ∧
    (A (q^2) a b c d ((q^2)^n)*C (q^2) a b c d ((q^2)^n) =
      -((al (q^p)^2-qcb q k^2)*
        (al y^2-qcb q k^2)*(al w^2-qcb q k^2) /
        ((q-q⁻¹)^2*qbr q (2*k-1)*qbr q (2*k+1)*qcb q k^2))) := by
  dsimp only
  let h := q^(p+1)
  have hh : h ≠ 0 := pow_ne_zero (p+1) hq
  have hs : q^n ≠ 0 := pow_ne_zero n hq
  have hr := source_regular q y w hq hy hw hroot p
  have hi := (parameter_invariants (q^(p+1)) y w hy hw).1
  have hv : (q^2)^n = (q^n)^2 := pow_right_comm q 2 n
  have h0 := regular_square _ _ _ _ _ hr n 0
  have h1 := regular_square _ _ _ _ _ hr n 1
  have h2 := regular_square _ _ _ _ _ hr n 2
  have hm := hr (n*2)
  rw [hi] at h0 h1 h2 hm
  simp only [hv, pow_zero, pow_one, mul_one] at h0 h1 h2
  change 1-h^4*((q^n)^2)^2 ≠ 0 at h0
  change 1-h^4*q^2*((q^n)^2)^2 ≠ 0 at h1
  change 1-h^4*(q^2)^2*((q^n)^2)^2 ≠ 0 at h2
  have h0' : 1-h^4*(q^n)^4 ≠ 0 := by convert h0 using 2 <;> ring
  have h1' : 1-h^4*q^2*(q^n)^4 ≠ 0 := by convert h1 using 2 <;> ring
  have h2' : 1-h^4*q^4*(q^n)^4 ≠ 0 := by convert h2 using 2 <;> ring
  have hm' : q^2-h^4*(q^n)^4 ≠ 0 := by
    simp only [pow_mul, hv] at hm
    change q^2-h^4*((q^n)^2)^2 ≠ 0 at hm
    convert hm using 2 <;> ring
  have hp0 := plus_den h ((q^n)^2) (by convert h0' using 2 <;> ring)
  have hp1 := plus_den h (q^2*(q^n)^2) (by convert h2' using 2 <;> ring)
  have hp1' : 1+h^2*q^2*(q^n)^2 ≠ 0 := by convert hp1 using 2 <;> ring
  have hd := diag_source q h (q^n) y w hq hh hs hy hw h0' h1' h2' hp0 hp1'
  have hdiff := power_sub_inv_ne q hq hroot 1 (Nat.le_refl 1)
  simp only [pow_one] at hdiff
  have ho := off_h_source q h (q^n) y w hq hh hs hy hw hdiff hm' h0' h1' hp0
  have hk : q^((p:ℤ)+(n:ℤ)+1) = h*q^n := by
    dsimp [h]
    simp only [zpow_add₀ hq, zpow_natCast, zpow_one, pow_succ]
    ring
  have hk1 : q^((p:ℤ)+(n:ℤ)+1+1) = q*h*q^n := by
    simpa only [hk, mul_comm, mul_left_comm, mul_assoc] using
      zpow_add_one₀ hq ((p:ℤ)+(n:ℤ)+1)
  have hp : h/q = q^p := div_eq_of_eq_mul hq rfl
  have hv1 : (q^2)^(n+1) = q^2*(q^n)^2 := by rw [pow_succ, hv]; ring
  constructor
  · rw [hv1, hv]
    rw [hd]
    simp only [qcb_al, hk, hk1, hp]
  · rw [hv]
    rw [ho]
    rw [(qbr_pair q hq ((p:ℤ)+(n:ℤ)+1)).1,
      (qbr_pair q hq ((p:ℤ)+(n:ℤ)+1)).2]
    simp only [qcb_al, hk, hp]
end IMDAW



private theorem seed_eq_aw (q x y w : ℂ) (hq : q ≠ 0) (hy : y ≠ 0) (hw : w ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (p n : ℕ) :
    let h := q^(p+1)
    seedX q x y w p n = (-1)^n*IMDAW.P (q^2)
      (h/(y*w)) (h*w/y) (h*y*w) (h*y/w) (-al x) n := by
  dsimp only
  induction n using Nat.twoStepInduction with
  | zero => simp [seedX, IMDAW.P]
  | one =>
    have hd := IMDAW.source_initial q y w hq hy hw hroot p
    dsimp only at hd
    simp only [seedX, IMDAW.P, pow_one]
    linear_combination -hd
  | more n ih ih1 =>
    have hd := (IMDAW.source_step_coefficients q y w hq hy hw hroot p n).1
    have ho := (IMDAW.source_step_coefficients q y w hq hy hw hroot p n).2
    have hdiag : -al x-(q^(p+1)/(y*w)+(q^(p+1)/(y*w))⁻¹)+
        IMDAW.A (q^2) (q^(p+1)/(y*w)) (q^(p+1)*w/y) (q^(p+1)*y*w) (q^(p+1)*y/w) ((q^2)^(n+1))+
        IMDAW.C (q^2) (q^(p+1)/(y*w)) (q^(p+1)*w/y) (q^(p+1)*y*w) (q^(p+1)*y/w) ((q^2)^n) =
        -(al x+al (q^p)*al y*al w/(qcb q ((p:ℤ)+n+1)*qcb q ((p:ℤ)+n+1+1))) := by
      linear_combination -hd
    simp only [seedX, IMDAW.P, ih, ih1]
    rw [hdiag, ho]
    simp only [pow_succ]
    ring

private theorem parameter_power (q w ε : ℂ) (hq : q ≠ 0) (hw : w ≠ 0)
    (hε : ε = 1 ∨ ε = -1) (p N j : ℕ) :
    q^(p+1)/(ε*q^(p+N)*w)*(q^2)^j = ε*q^(-(N:ℤ)+1+2*j)/w := by
  have hi : ε⁻¹ = ε := by
    exact inv_eq_self₀.mpr
      (hε.elim (fun h => Or.inr (Or.inr h)) (fun h => Or.inl h))
  have hr : q^(p+1)/q^(p+N) = q^(-(N:ℤ)+1) := by
    convert (zpow_natCast_sub_natCast₀ hq (p+1) (p+N)).symm using 1
    congr 1
    push_cast
    ring
  calc
    _ = (ε/w)*(q^(p+1)/q^(p+N))*(q^2)^j := by
      simp only [div_eq_mul_inv, mul_inv_rev, hi]
      ring
    _ = (ε/w)*q^(-(N:ℤ)+1)*q^((2*j:ℕ):ℤ) := by rw [hr]; simp only [zpow_natCast, pow_mul]
    _ = _ := by
      rw [mul_assoc, ← zpow_add₀ hq]
      have he : -(N:ℤ)+1+((2*j:ℕ):ℤ) = -(N:ℤ)+1+2*j := by
        exact (Int.add_left_inj ↑(2 * j)).mpr rfl
      rw [he]
      ring

private theorem terminal_ab (q y w ε : ℂ) (hq : q ≠ 0) (hw : w ≠ 0)
    (hε : ε = 1 ∨ ε = -1) (p N : ℕ) (hy : y = ε*q^(p+(N+1))) :
    (q^(p+1)/(y*w))*(q^(p+1)*w/y)*(q^2)^N = 1 := by
  subst y
  have he : ε^2 = 1 := sq_eq_one_iff.mpr hε
  have he0 : ε ≠ 0 := right_ne_zero_of_mul_eq_one he
  have hnp : q^(p+(N+1)) = q^(p+1)*q^N := by
    simpa only [Nat.add_right_comm p 1 N, Nat.add_assoc] using pow_add q (p+1) N
  rw [hnp]
  have hv : (q^2)^N = (q^N)^2 := pow_right_comm q 2 N
  rw [hv]
  field_simp [he0, pow_ne_zero (p+1) hq, pow_ne_zero N hq, hw] <;> rw [he] <;> ring

private theorem seed_terminal (q x w ε : ℂ) (hq : q ≠ 0) (hx : x ≠ 0) (hw : w ≠ 0)
    (hroot : ∀ n : ℕ, 1 ≤ n → q^n ≠ 1) (hε : ε = 1 ∨ ε = -1) (p N : ℕ) :
    seedX q x (ε*q^(p+N)) w p N = seedProduct q x w ε N := by
  cases N with
  | zero => simp [seedX, seedProduct]
  | succ N =>
    have he0 : ε ≠ 0 := by
      exact right_ne_zero_of_mul_eq_one (sq_eq_one_iff.mpr hε)
    let y := ε*q^(p+(N+1))
    let h := q^(p+1)
    let a := h/(y*w)
    let b := h*w/y
    let c := h*y*w
    let d := h*y/w
    have hy : y ≠ 0 := mul_ne_zero he0 (pow_ne_zero _ hq)
    have ha : a ≠ 0 := div_ne_zero (pow_ne_zero _ hq) (mul_ne_zero hy hw)
    have hr := IMDAW.source_regular q y w hq hy hw hroot p
    have hab : a*b*(q^2)^N = 1 := terminal_ab q y w ε hq hw hε p N rfl
    have hseed := seed_eq_aw q x y w hq hy hw hroot p (N+1)
    change seedX q x y w p (N+1) = (-1)^(N+1)*IMDAW.P (q^2) a b c d (-al x) (N+1) at hseed
    change seedX q x y w p (N+1) = seedProduct q x w ε (N+1)
    rw [hseed, IMDAW.terminal_factorization (q^2) a b c d (-al x) (pow_ne_zero 2 hq) ha hr N hab,
      product_linear q x w ε hq hx hw hε (N+1)]
    have hp : (∏ j ∈ Finset.range (N+1), (-al x-(a*(q^2)^j+(a*(q^2)^j)⁻¹))) =
        (-1)^(N+1)*(∏ j ∈ Finset.range (N+1), (al x+al (a*(q^2)^j))) := by
      have hf (j : ℕ) : -al x-(a*(q^2)^j+(a*(q^2)^j)⁻¹) = -(al x+al (a*(q^2)^j)) := by
        exact Eq.symm (neg_add' (al x) (al (a * (q ^ 2) ^ j)))
      simp_rw [hf]
      rw [Finset.prod_neg]
      simp
    rw [hp]
    have hsign : (-1:ℂ)^(N+1)*(-1)^(N+1) = 1 := by
      exact pow_mul_pow_eq_one (N+1) ((neg_mul_neg (1 : ℂ) 1).trans (one_mul 1))
    rw [← mul_assoc, hsign, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    rw [show a*(q^2)^j = ε*q^(-((N+1:ℕ):ℤ)+1+2*j)/w from parameter_power q w ε hq hw hε p (N+1) j]




private theorem qcb_square (q : ℂ) (hq : q ≠ 0) (k : ℤ) :
    4 - qcb q k ^ 2 = -(q^k - q^(-k))^2 := by
  unfold qcb
  have h : q^k * q^(-k) = 1 := by
    simpa only [neg_neg] using (zpow_neg_mul_zpow_self (-k) hq)
  linear_combination -4*h

private theorem sigma_coeff (q y w : ℂ) (hq : q ≠ 0) (k : ℤ) :
    (4-qcb q k^2)*(al y^2-qcb q k^2)*(al w^2-qcb q k^2) /
      ((q-q⁻¹)^2*qbr q (2*k-1)*qbr q (2*k+1)*qcb q k^2) =
    -(qbr q k^2*(al y^2-qcb q k^2)*(al w^2-qcb q k^2) /
      (qbr q (2*k+1)*qbr q (2*k-1)*qcb q k^2)) := by
  rw [qcb_square q hq k]
  simp only [qbr, div_eq_mul_inv, mul_inv_rev, ← inv_pow, inv_inv]
  ring

private theorem sigma_eq_seed (q x y w : ℂ) (hq : q ≠ 0) (n : ℕ) :
    seedSigma q x y w n = seedX q x y w 0 n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [seedSigma, seedX]
  | more n ih ih1 =>
    simp only [seedSigma, seedX, ih, ih1]
    have ha : al (q^0) = 2 := by norm_num [al]
    simp only [Nat.cast_zero, zero_add, ha]
    norm_num only [show (2:ℂ)^2=4 by norm_num]
    rw [sigma_coeff q y w hq]
    ring



theorem result : claim := by
  intro q x w ε hq hx hw hroot hε
  constructor
  · intro p m hp hpm
    have he := seed_terminal q x w ε hq hx hw hroot hε p (m-p)
    have hpm' : p+(m-p) = m := Nat.add_sub_of_le hpm
    simpa only [hpm'] using he
  · intro m
    rw [sigma_eq_seed q x (ε*q^m) w hq m]
    simpa only [Nat.zero_add] using seed_terminal q x w ε hq hx hw hroot hε 0 m


end D5.S3.Quantum.Algebra.PeriodicTemperleyLiebSeedProduct

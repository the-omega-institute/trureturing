/- GID: D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.claim; result=D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.result; claim=D5/S3/Quantum/Dynamics/PairTunnelingAnsatzGroundStateRefutation.claim
   digest: Eight-boson obstruction to Volkoff's pair-tunnelling ground-state ansatz. -/

/-
proof_shape: result: bind-only
escape_witness: none; finite polynomial expansion, a diagonal coefficient bridge,
  and exact eigenvalue comparison.
admission_basis: open-problem-resolution (#11667; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.PairTunnelingAnsatzGroundStateRefutation

open scoped BigOperators
open MvPolynomial

/-- The quadratic factors; `false` denotes the factor with `+2icxy`. -/
noncomputable def ansatzFactor (c : ℝ) (sign : Bool) : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ 2 + C (if sign then (-2 * Complex.I * (c : ℂ)) else (2 * Complex.I * (c : ℂ))) *
    X 0 * X 1 - X 1 ^ 2

/-- The source polynomial, with `false` for the sum and `true` for the difference. -/
noncomputable def ansatzPolynomial (N : ℕ) (sign : Bool) (c : ℝ) : MvPolynomial (Fin 2) ℂ :=
  ansatzFactor c false ^ (N / 2) +
    if sign then -ansatzFactor c true ^ (N / 2) else ansatzFactor c true ^ (N / 2)

/-- Fock amplitudes in the basis `|N-k,k⟩`, without the scalar normalization. -/
noncomputable def omega (N : ℕ) (sign : Bool) (c : ℝ) : Fin (N + 1) → ℂ := fun k =>
  (Real.sqrt ((N - k.val).factorial * k.val.factorial : ℕ) : ℂ) *
    coeff (Finsupp.single 0 (N - k.val) + Finsupp.single 1 k.val) (ansatzPolynomial N sign c)

/-- Matrix of `a₀†²a₁² + a₁†²a₀²` on the `N`-boson sector. -/
noncomputable def pairTunnel (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := fun i j =>
  if i.val + 2 = j.val then
    (Real.sqrt (((N - i.val - 1) * (N - i.val) * (i.val + 1) * (i.val + 2) : ℕ) : ℝ) : ℂ)
  else if j.val + 2 = i.val then
    (Real.sqrt (((N - j.val - 1) * (N - j.val) * (j.val + 1) * (j.val + 2) : ℕ) : ℝ) : ℂ)
  else 0

/-- A nonzero eigenvector with a real eigenvalue least among all real eigenvalues. -/
def IsGroundState {N : ℕ} (H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (v : Fin (N + 1) → ℂ) : Prop :=
  v ≠ 0 ∧ ∃ eigen : ℝ, H.mulVec v = (eigen : ℂ) • v ∧
    ∀ (μ : ℝ) (w : Fin (N + 1) → ℂ), w ≠ 0 → H.mulVec w = (μ : ℂ) • w → eigen ≤ μ

/-- Volkoff's conjecture, restricted to the even sectors specified in Section V.A. -/
def claim : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → ∃ (c : ℝ) (sign : Bool),
    omega N sign c ≠ 0 ∧ IsGroundState (pairTunnel N) (omega N sign c)

set_option maxHeartbeats 1000000 in
-- The fourth-power expansion and nine coefficient rows share one proof.
theorem result : ¬ claim := by
  classical
  intro h
  obtain ⟨c, sign, _, hne, eigen, heig, hmin⟩ := h 8 ⟨4, rfl⟩ (by norm_num)
  let weight : Fin 9 → ℝ := fun k => Real.sqrt ((8 - k.val).factorial * k.val.factorial : ℕ)
  have hweight (k : Fin 9) : (weight k : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hmono (a b : ℕ) (z : ℂ) :
      monomial (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) z = C z * X 0 ^ a * X 1 ^ b := by
    simp only [X_pow_eq_monomial, C_apply, monomial_mul, zero_add, mul_one]
  have hpoly (d : ℝ) : ansatzFactor d false ^ 4 =
      ∑ k : Fin 9, monomial (Finsupp.single (0 : Fin 2) (8 - k.val) + Finsupp.single 1 k.val)
      (![1, 8*Complex.I*d, -24*(d:ℂ)^2-4, -32*Complex.I*(d:ℂ)^3-24*Complex.I*d,
        16*(d:ℂ)^4+48*(d:ℂ)^2+6, 32*Complex.I*(d:ℂ)^3+24*Complex.I*d,
        -24*(d:ℂ)^2-4, -8*Complex.I*d, 1] k) := by
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceSub,
      Matrix.cons_val_zero, Matrix.cons_val_succ, hmono]
    norm_num [ansatzFactor]
    simp only [map_ofNat]
    have hi : (C Complex.I : MvPolynomial (Fin 2) ℂ)^2 = -1 := by
      rw [← map_pow, Complex.I_sq, map_neg, map_one]
    have hi3 : (C Complex.I : MvPolynomial (Fin 2) ℂ)^3 = -C Complex.I := by
      rw [show 3 = 2+1 from rfl, pow_succ, hi]; ring
    have hi4 : (C Complex.I : MvPolynomial (Fin 2) ℂ)^4 = 1 := by
      rw [show 4 = 2*2 from rfl, pow_mul, hi]; ring
    ring_nf
    simp only [hi, hi3, hi4]
    ring
  have hcoeff (d : ℝ) :
      (fun k : Fin 9 => coeff (Finsupp.single (0 : Fin 2) (8-k.val) + Finsupp.single 1 k.val)
        (ansatzFactor d false ^ 4)) =
      ![1, 8*Complex.I*d, -24*(d:ℂ)^2-4, -32*Complex.I*(d:ℂ)^3-24*Complex.I*d,
        16*(d:ℂ)^4+48*(d:ℂ)^2+6, 32*Complex.I*(d:ℂ)^3+24*Complex.I*d,
        -24*(d:ℂ)^2-4, -8*Complex.I*d, 1] := by
    funext k
    rw [hpoly]
    fin_cases k <;> simp [coeff_sum, coeff_monomial, coeff_sub, coeff_neg, Fin.sum_univ_succ,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply]
  have hfactor (d : ℝ) : ansatzFactor d true = ansatzFactor (-d) false := by
    simp only [ansatzFactor, Bool.false_eq_true, ↓reduceIte, Complex.ofReal_neg]
    congr 3; ring
  let evenQ : Fin 9 → ℂ :=
    ![2, 0, -48*(c:ℂ)^2-8, 0, 32*(c:ℂ)^4+96*(c:ℂ)^2+12,
      0, -48*(c:ℂ)^2-8, 0, 2]
  let oddQ : Fin 9 → ℂ :=
    ![0, 16*Complex.I*c, 0, -64*Complex.I*(c:ℂ)^3-48*Complex.I*c, 0,
      64*Complex.I*(c:ℂ)^3+48*Complex.I*c, 0, -16*Complex.I*c, 0]
  have homega (s : Bool) : omega 8 s c = fun k => (weight k : ℂ) * (if s then oddQ else evenQ) k := by
    funext k
    cases s
    · simp only [omega, ansatzPolynomial, hfactor, Nat.reduceDiv, Bool.false_eq_true,
        ↓reduceIte, coeff_add]
      change (weight k : ℂ) * (((fun k : Fin 9 => coeff
        (Finsupp.single 0 (8-k.val) + Finsupp.single 1 k.val) (ansatzFactor c false ^ 4)) k) +
        ((fun k : Fin 9 => coeff (Finsupp.single 0 (8-k.val) + Finsupp.single 1 k.val)
          (ansatzFactor (-c) false ^ 4)) k)) = _
      rw [hcoeff, hcoeff]
      fin_cases k <;> dsimp [evenQ] <;> push_cast <;> ring
    · simp only [omega, ansatzPolynomial, hfactor, Nat.reduceDiv, ↓reduceIte, coeff_add, coeff_neg]
      change (weight k : ℂ) * (((fun k : Fin 9 => coeff
        (Finsupp.single 0 (8-k.val) + Finsupp.single 1 k.val) (ansatzFactor c false ^ 4)) k) -
        ((fun k : Fin 9 => coeff (Finsupp.single 0 (8-k.val) + Finsupp.single 1 k.val)
          (ansatzFactor (-c) false ^ 4)) k)) = _
      rw [hcoeff, hcoeff]
      fin_cases k <;> dsimp [oddQ] <;> push_cast <;> ring
  have scale (a b d e : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hab : a*b = d^2*e) :
      (Real.sqrt a : ℂ) * (Real.sqrt b : ℂ) = (d : ℂ) * (Real.sqrt e : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul ha, hab, Real.sqrt_mul (sq_nonneg d),
      Real.sqrt_sq hd, Complex.ofReal_mul]
  have s1 := scale 112 1440 2 40320 (by norm_num) (by norm_num) (by norm_num)
  have s2 := scale 112 40320 56 1440 (by norm_num) (by norm_num) (by norm_num)
  have s3 := scale 252 720 6 5040 (by norm_num) (by norm_num) (by norm_num)
  have s4 := scale 252 5040 42 720 (by norm_num) (by norm_num) (by norm_num)
  have s5 := scale 360 576 12 1440 (by norm_num) (by norm_num) (by norm_num)
  have s6 := scale 360 1440 30 576 (by norm_num) (by norm_num) (by norm_num)
  have s7 := scale 400 720 20 720 (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_ofNat] at s1 s2 s3 s4 s5 s6 s7
  let diff : (Fin 9 → ℂ) → (Fin 9 → ℂ) := fun q =>
    ![2*q 2, 6*q 3, 56*q 0+12*q 4, 42*q 1+20*q 5, 30*q 2+30*q 6,
      20*q 3+42*q 7, 12*q 4+56*q 8, 6*q 5, 2*q 6]
  have bridge (q : Fin 9 → ℂ) :
      (pairTunnel 8).mulVec (fun k => (weight k : ℂ)*q k) =
        fun k => (weight k : ℂ)*diff q k := by
    funext k
    fin_cases k <;>
      norm_num only [pairTunnel, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, weight, diff,
        Nat.factorial, Nat.reduceSucc, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        mul_zero, zero_mul, add_zero, zero_add, ite_true, ite_false, Fin.sum_univ_zero,
        Matrix.cons_val_zero', Matrix.cons_val_succ',
        Nat.cast_ofNat, Complex.ofReal_ofNat] <;>
      dsimp only <;>
      norm_num only [Nat.cast_ofNat, Nat.reduceSucc] <;>
      simp only [← mul_assoc] <;>
      (repeat' first | rw [s1] | rw [s2] | rw [s3] | rw [s4] | rw [s5] | rw [s6] | rw [s7]) <;>
      dsimp [Fin.succ] <;> first | rfl | ring
  have groundLower (μ : ℝ) (w : Fin 9 → ℂ) (hw : w ≠ 0)
      (heq : (pairTunnel 8).mulVec w = (μ : ℂ) • w) : -8*Real.sqrt 13 ≤ μ := by
    let u : Fin 9 → ℂ := fun k => w k / (weight k : ℂ)
    have hu : w = fun k => (weight k : ℂ)*u k := by
      funext k
      dsimp [u]
      exact (mul_div_cancel₀ (w k) (hweight k)).symm
    have hueq : diff u = (μ : ℂ) • u := by
      rw [hu, bridge] at heq
      funext k
      apply mul_left_cancel₀ (hweight k)
      have hk := congrFun heq k
      simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
      change (weight k : ℂ)*diff u k = (weight k : ℂ)*((μ : ℂ)*u k)
      calc
        _ = (μ : ℂ)*((weight k : ℂ)*u k) := hk
        _ = _ := by ring
    have h0 := congrFun hueq 0
    have h1 := congrFun hueq 1
    have h2 := congrFun hueq 2
    have h3 := congrFun hueq 3
    have h4 := congrFun hueq 4
    have h5 := congrFun hueq 5
    have h6 := congrFun hueq 6
    have h7 := congrFun hueq 7
    have h8 := congrFun hueq 8
    change 2*u 2 = (μ : ℂ)*u 0 at h0
    change 6*u 3 = (μ : ℂ)*u 1 at h1
    change 56*u 0+12*u 4 = (μ : ℂ)*u 2 at h2
    change 42*u 1+20*u 5 = (μ : ℂ)*u 3 at h3
    change 30*u 2+30*u 6 = (μ : ℂ)*u 4 at h4
    change 20*u 3+42*u 7 = (μ : ℂ)*u 5 at h5
    change 12*u 4+56*u 8 = (μ : ℂ)*u 6 at h6
    change 6*u 5 = (μ : ℂ)*u 7 at h7
    change 2*u 6 = (μ : ℂ)*u 8 at h8
    -- Eliminating each three-term chain gives its characteristic polynomial.
    have hpe : ((μ : ℂ)*((μ : ℂ)^2-832)*((μ : ℂ)^2-112))*u 0 = 0 := by
      linear_combination
        -((μ : ℂ)^4-832*(μ : ℂ)^2+40320)*h0 -
        (2*(μ : ℂ)^3-944*(μ : ℂ))*h2 -
        (24*(μ : ℂ)^2-2688)*h4 - 720*(μ : ℂ)*h6 - 40320*h8
    have hpo : ((μ : ℂ)^4-904*(μ : ℂ)^2+63504)*u 1 = 0 := by
      linear_combination -((μ : ℂ)^3-652*(μ : ℂ))*h1 -
        (6*(μ : ℂ)^2-1512)*h3 - 120*(μ : ℂ)*h5 - 5040*h7
    by_contra hn
    have hm : μ < -8*Real.sqrt 13 := lt_of_not_ge hn
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
    have hsn := Real.sqrt_nonneg (13 : ℝ)
    have hmneg : μ < 0 := by nlinarith
    have hm2 : 832 < μ^2 := by
      have ht : 0 < (-μ-8*Real.sqrt 13)*(-μ+8*Real.sqrt 13) :=
        mul_pos (by linarith) (by nlinarith)
      nlinarith [ht]
    have heven : μ*(μ^2-832)*(μ^2-112) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (ne_of_lt hmneg) (ne_of_gt (by linarith)))
        (ne_of_gt (by linarith))
    have hodd : μ^4-904*μ^2+63504 ≠ 0 := by
      apply ne_of_gt
      nlinarith [sq_nonneg (μ^2-832)]
    have hu0 : u 0 = 0 := by
      have hp : (((μ*(μ^2-832)*(μ^2-112) : ℝ) : ℂ))*u 0 = 0 := by
        push_cast
        exact hpe
      exact (mul_eq_zero.mp hp).resolve_left (Complex.ofReal_ne_zero.mpr heven)
    have hu1 : u 1 = 0 := by
      have hp : (((μ^4-904*μ^2+63504 : ℝ) : ℂ))*u 1 = 0 := by
        push_cast
        exact hpo
      exact (mul_eq_zero.mp hp).resolve_left (Complex.ofReal_ne_zero.mpr hodd)
    have hu2 : u 2 = 0 := by linear_combination h0/2 + (μ : ℂ)*hu0/2
    have hu3 : u 3 = 0 := by linear_combination h1/6 + (μ : ℂ)*hu1/6
    have hu4 : u 4 = 0 := by
      linear_combination h2/12 + (μ : ℂ)*hu2/12 - 56*hu0/12
    have hu5 : u 5 = 0 := by
      linear_combination h3/20 + (μ : ℂ)*hu3/20 - 42*hu1/20
    have hu6 : u 6 = 0 := by
      linear_combination h4/30 + (μ : ℂ)*hu4/30 - hu2
    have hu7 : u 7 = 0 := by
      linear_combination h5/42 + (μ : ℂ)*hu5/42 - 20*hu3/42
    have hu8 : u 8 = 0 := by
      linear_combination h6/56 + (μ : ℂ)*hu6/56 - 12*hu4/56
    apply hw
    rw [hu]
    funext k
    fin_cases k <;> simp [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8]
  let z : Fin 9 → ℂ := ![1, 0, -4*(Real.sqrt 13 : ℂ), 0, 30, 0, -4*(Real.sqrt 13 : ℂ), 0, 1]
  have hr : (Real.sqrt 13 : ℂ)^2 = 13 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
    norm_num
  have hz : (fun k => (weight k : ℂ)*z k) ≠ 0 := by
    intro hz
    have := congrFun hz 0
    simp only [z, Matrix.cons_val_zero, mul_one, Pi.zero_apply] at this
    exact hweight 0 this
  have hzeig : (pairTunnel 8).mulVec (fun k => (weight k : ℂ)*z k) =
      ((-8*Real.sqrt 13 : ℝ) : ℂ) • (fun k => (weight k : ℂ)*z k) := by
    rw [bridge]
    funext k
    fin_cases k <;> simp [diff, z, Pi.smul_apply, smul_eq_mul] <;>
      ring_nf <;> simp only [hr] <;> ring
  have hground : IsGroundState (pairTunnel 8) (fun k => (weight k : ℂ)*z k) :=
    ⟨hz, -8*Real.sqrt 13, hzeig, groundLower⟩
  have groundEnergy : eigen = -8*Real.sqrt 13 := by
    obtain ⟨_, g, hgeig, hgmin⟩ := hground
    have hg : g = -8*Real.sqrt 13 := le_antisymm
      (hgmin _ _ hz hzeig) (groundLower _ _ hz hgeig)
    apply le_antisymm
    · exact hmin _ _ hz hzeig
    · rw [← hg]
      exact hgmin _ _ hne heig
  let q : Fin 9 → ℂ := if sign then oddQ else evenQ
  have eqcoeff : diff q = (eigen : ℂ) • q := by
    rw [homega sign, bridge] at heig
    funext k
    apply mul_left_cancel₀ (hweight k)
    have hk := congrFun heig k
    simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
    change (weight k : ℂ) * diff q k = (weight k : ℂ) * ((eigen : ℂ) * q k)
    calc
      _ = (eigen : ℂ) * ((weight k : ℂ) * q k) := hk
      _ = _ := by ring
  cases sign with
  | false =>
    have h0 := congrArg Complex.re (congrFun eqcoeff 0)
    have h2 := congrArg Complex.re (congrFun eqcoeff 2)
    have h4 := congrArg Complex.re (congrFun eqcoeff 4)
    dsimp [q, diff, evenQ] at h0 h2 h4
    norm_num [Complex.mul_re, ← Complex.ofReal_pow] at h0 h2 h4
    have he : eigen = -48*c^2-8 := by nlinarith [h0]
    rw [he] at h2 h4
    have ha : 10*c^4-2*c^2-1 = 0 := by nlinarith [h2]
    have hb : 12*c^6+38*c^4-12*c^2-3 = 0 := by nlinarith [h4]
    have hat : (10*c^4-2*c^2-1)*c^2 = 0 := by rw [ha]; ring
    have hc : 68*c^2-26 = 0 := by nlinarith [ha, hb, hat]
    nlinarith [ha, hc, sq_nonneg (c^2-13/34)]
  | true =>
    have hc0 : c ≠ 0 := by
      intro hz
      apply hne
      rw [homega true]
      funext k
      fin_cases k <;> simp [oddQ, hz]
    have h1 := congrArg Complex.im (congrFun eqcoeff 1)
    have h3 := congrArg Complex.im (congrFun eqcoeff 3)
    dsimp [q, diff, oddQ] at h1 h3
    norm_num [Complex.mul_im, Complex.mul_re, ← Complex.ofReal_pow] at h1 h3
    have hf : c*(24*c^2+eigen+18) = 0 := by nlinarith [h1]
    have he : eigen = -24*c^2-18 := by
      have := (mul_eq_zero.mp hf).resolve_left hc0
      nlinarith
    rw [he] at h3
    have hg : c*(6*c^4+4*c^2-3) = 0 := by nlinarith [h3]
    have ha : 6*c^4+4*c^2-3 = 0 := (mul_eq_zero.mp hg).resolve_left hc0
    have ht : c^2 < 9/20 := by
      by_contra hn
      have hl : 9/20 ≤ c^2 := le_of_not_gt hn
      nlinarith [sq_nonneg (c^2-9/20)]
    have helower : -(144/5 : ℝ) < eigen := by rw [he]; linarith
    rw [groundEnergy] at helower
    have hrreal := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
    have hrnonneg := Real.sqrt_nonneg (13 : ℝ)
    nlinarith
end D5.S3.Quantum.Dynamics.PairTunnelingAnsatzGroundStateRefutation

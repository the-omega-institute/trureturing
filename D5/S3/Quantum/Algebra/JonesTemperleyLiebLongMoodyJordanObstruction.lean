/- GID: D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Long-Moody braid operators of Jones-Temperley-Lieb endpoint-sector seeds have a nontrivial Jordan block. -/

/-
proof_shape: result: content.
escape_witness: loop_path (an endpoint sector of dimension at least two contains a path whose
  vertex 2 is the first vertex, i.e. a path beginning 1, 2, 1), used on the proof path of result
  through local_vectors and sector_jordan. The content private theorems are loop_path,
  local_vectors, sector_jordan and no_fixed_seed. Every other private theorem is bind-only and is
  used on the proof path of result: μ_pos, perron_frobenius, δ_pos, E_square, α_data, E_triple,
  ρ_inverse, seed_zero_polynomial, first_projection, block_action.
admission_basis: open-problem-resolution (#13581; Proved)
Direct frozen dependency: D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb (LegalPath,
  pathProjection, weighted_legal_path_temperley_lieb).
-/

import D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open scoped BigOperators
open Matrix D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

namespace D5.S3.Quantum.Algebra.JonesTemperleyLiebLongMoodyJordanObstruction

def adj (ℓ : ℕ) (a b : Fin (ℓ - 1)) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

instance (ℓ : ℕ) : DecidableRel (adj ℓ) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def mu (ℓ : ℕ) (a : Fin (ℓ - 1)) : ℝ :=
  Real.sin (((a.val : ℝ) + 1) * Real.pi / ℓ)

def delta (ℓ : ℕ) : ℝ := 2 * Real.cos (Real.pi / ℓ)

/-- The first vertex is paper vertex 1. -/
def v1 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : Fin (ℓ - 1) := ⟨0, by omega⟩

abbrev Sector (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) :=
  LegalPath (adj ℓ) (n + 1) (v1 ℓ hℓ) t

instance (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) : Fintype (Sector ℓ n hℓ t) :=
  inferInstanceAs (Fintype (LegalPath (adj ℓ) (n + 1) (v1 ℓ hℓ) t))

instance (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) : DecidableEq (Sector ℓ n hℓ t) :=
  Classical.decEq _

/-- Generator `j` acts at path vertex `j + 1`; out-of-range indices are zero. -/
def E (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) (j : ℕ) :
    Matrix (Sector ℓ n hℓ t) (Sector ℓ n hℓ t) ℂ :=
  if hj : j < n then
    (delta ℓ : ℂ) • pathProjection (adj ℓ) (mu ℓ) (delta ℓ) (n + 1) (v1 ℓ hℓ) t
      (j + 1) ⟨by omega, by omega⟩
  else 0

def alpha (ℓ : ℕ) : ℂ :=
  Complex.I * Complex.exp (-((Real.pi : ℂ) * Complex.I) / (2 * (ℓ : ℂ)))

def rho (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) (j : ℕ) :
    Matrix (Sector ℓ n hℓ t) (Sector ℓ n hℓ t) ℂ :=
  alpha ℓ • 1 + (alpha ℓ)⁻¹ • E ℓ n hℓ t j

def s (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) (i : ℕ) := rho ℓ n hℓ t i

/-- Zero-based seed: `seed j` is the paper's `g (j + 1)`. -/
def seed (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) : ℕ →
    Matrix (Sector ℓ n hℓ t) (Sector ℓ n hℓ t) ℂ
  | 0 => rho ℓ n hℓ t 0 * rho ℓ n hℓ t 0
  | j + 1 => s ℓ n hℓ t (j + 1) * seed ℓ n hℓ t j * (s ℓ n hℓ t (j + 1))⁻¹

def g (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) (j : Fin n) :=
  seed ℓ n hℓ t j.val

private def lmBlock {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (U G H : Matrix X X ℂ) : Matrix (Fin n × X) (Fin n × X) ℂ :=
  fun x y =>
    if x.1.val = 0 ∧ y.1.val = 1 then (U * G) x.2 y.2
    else if x.1.val = 1 ∧ y.1.val = 0 then U x.2 y.2
    else if x.1.val = 1 ∧ y.1.val = 1 then (U * (1 - H)) x.2 y.2
    else if 2 ≤ x.1.val ∧ x.1 = y.1 then U x.2 y.2 else 0

/-- Equation (braid-matrices) at `i = 1`, using zero-based slot indices. -/
def S1 (ℓ n : ℕ) (hℓ : 2 ≤ ℓ) (t : Fin (ℓ - 1)) :
    Matrix (Fin n × Sector ℓ n hℓ t) (Fin n × Sector ℓ n hℓ t) ℂ := by
  classical
  let U := s ℓ n hℓ t 1
  let G := seed ℓ n hℓ t 0
  let H := seed ℓ n hℓ t 1
  exact lmBlock n U G H

def b (ℓ : ℕ) : ℂ := -(alpha ℓ)⁻¹ ^ 3

def claim : Prop :=
  ∀ (ℓ n : ℕ) (t : Fin (ℓ - 1)) (hℓ : 4 ≤ ℓ), 3 ≤ n →
    let h₂ : 2 ≤ ℓ := Nat.le_trans (by decide : 2 ≤ 4) hℓ
    2 ≤ Fintype.card (Sector ℓ n h₂ t) →
    (∀ (j : Fin n) (v : Sector ℓ n h₂ t → ℂ),
      g ℓ n h₂ t j *ᵥ v = v → v = 0) ∧
    ∃ w : Fin n × Sector ℓ n h₂ t → ℂ,
      (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ ((S1 ℓ n h₂ t - b ℓ • 1) *ᵥ w) = 0 ∧
      (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ w ≠ 0

private theorem μ_pos (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (a : Fin (ℓ - 1)) : 0 < mu ℓ a := by
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have ha : (a.val : ℝ) + 1 < ℓ := by
    exact_mod_cast (show a.val + 1 < ℓ by omega)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos (by positivity) Real.pi_pos) hl
  · exact (div_lt_iff₀ hl).2 (by nlinarith [Real.pi_pos])

private theorem perron_frobenius (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (a : Fin (ℓ - 1)) :
    (∑ b : Fin (ℓ - 1) with adj ℓ a b, mu ℓ b) = delta ℓ * mu ℓ a := by
  have hl : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
  have hup : (∑ b : Fin (ℓ - 1), if a.val + 1 = b.val then mu ℓ b else 0) =
      Real.sin (((a.val : ℝ) + 2) * Real.pi / ℓ) := by
    by_cases ha : a.val + 1 < ℓ - 1
    · let c : Fin (ℓ - 1) := ⟨a.val + 1, ha⟩
      rw [Finset.sum_eq_single c]
      · norm_num [c, mu, Nat.cast_add, add_assoc]
      · intro b _ hbc
        have hb : a.val + 1 ≠ b.val := by
          intro hb
          apply hbc
          exact Fin.ext hb.symm
        simp [hb]
      · simp
    · have he : a.val + 2 = ℓ := by omega
      have hz : Real.sin (((a.val : ℝ) + 2) * Real.pi / ℓ) = 0 := by
        have he' : (a.val : ℝ) + 2 = ℓ := by exact_mod_cast he
        rw [he', mul_div_cancel_left₀ _ hl, Real.sin_pi]
      rw [hz]
      apply Finset.sum_eq_zero
      intro b _
      have hb : a.val + 1 ≠ b.val := by omega
      simp [hb]
  have hdown : (∑ b : Fin (ℓ - 1), if b.val + 1 = a.val then mu ℓ b else 0) =
      Real.sin ((a.val : ℝ) * Real.pi / ℓ) := by
    by_cases ha : 0 < a.val
    · let c : Fin (ℓ - 1) := ⟨a.val - 1, by omega⟩
      rw [Finset.sum_eq_single c]
      · have he : c.val + 1 = a.val := by dsimp [c]; omega
        simp only [he, if_true, mu]
        have he' : (c.val : ℝ) + 1 = a.val := by exact_mod_cast he
        rw [he']
      · intro b _ hbc
        have hb : b.val + 1 ≠ a.val := by
          intro hb
          apply hbc
          apply Fin.ext
          dsimp [c]
          omega
        simp [hb]
      · simp
    · have he : a.val = 0 := by omega
      simp only [he, Nat.cast_zero, zero_mul, zero_div, Real.sin_zero]
      apply Finset.sum_eq_zero
      intro b _
      simp
  have hsplit : (∑ b : Fin (ℓ - 1) with adj ℓ a b, mu ℓ b) =
      (∑ b : Fin (ℓ - 1), if a.val + 1 = b.val then mu ℓ b else 0) +
      (∑ b : Fin (ℓ - 1), if b.val + 1 = a.val then mu ℓ b else 0) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold adj
    by_cases h1 : a.val + 1 = b.val <;> by_cases h2 : b.val + 1 = a.val
    · omega
    all_goals simp [h1, h2]
  rw [hsplit, hup, hdown, Real.sin_add_sin]
  have hc : ((((a.val : ℝ) + 2) * Real.pi / ℓ +
      (a.val : ℝ) * Real.pi / ℓ) / 2) = ((a.val : ℝ) + 1) * Real.pi / ℓ := by ring
  have hd : ((((a.val : ℝ) + 2) * Real.pi / ℓ -
      (a.val : ℝ) * Real.pi / ℓ) / 2) = Real.pi / ℓ := by ring
  rw [hc, hd]
  unfold delta mu
  ring

private theorem δ_pos (ℓ : ℕ) (hℓ : 4 ≤ ℓ) : 0 < delta ℓ := by
  have hl : (4 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hp := Real.pi_pos
  have ht : Real.pi / (ℓ : ℝ) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hp.le (by norm_num) hl
  unfold delta
  apply mul_pos (by norm_num)
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < Real.pi / (ℓ : ℝ) := div_pos hp (by linarith)
    linarith
  · linarith

private theorem E_square (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (t : Fin (ℓ - 1)) (j : ℕ) :
    E ℓ n h₂ t j * E ℓ n h₂ t j = (delta ℓ : ℂ) • E ℓ n h₂ t j := by
  unfold E
  split_ifs with hj
  · have hsymm : Std.Symm (adj ℓ) := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
    have hp := (weighted_legal_path_temperley_lieb (adj ℓ) hsymm (mu ℓ)
      (μ_pos ℓ h₂) (delta ℓ) (δ_pos ℓ hℓ) (perron_frobenius ℓ h₂)
      (n + 1) (v1 ℓ h₂) t).1 (j + 1) ⟨by omega, by omega⟩
    rw [Matrix.smul_mul, Matrix.mul_smul, hp.2]
  · simp

private theorem α_data (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    alpha ℓ ≠ 0 ∧ (delta ℓ : ℂ) = -(alpha ℓ ^ 2 + (alpha ℓ)⁻¹ ^ 2) ∧
      alpha ℓ ^ 2 ≠ 1 ∧ alpha ℓ ^ 6 ≠ 1 := by
  have hs : alpha ℓ ^ 2 = -Complex.exp (-((Real.pi / ℓ : ℝ) : ℂ) * Complex.I) := by
    unfold alpha
    rw [mul_pow, Complex.I_sq, ← Complex.exp_nat_mul]
    push_cast
    field_simp
  have hi : (alpha ℓ)⁻¹ ^ 2 = -Complex.exp (((Real.pi / ℓ : ℝ) : ℂ) * Complex.I) := by
    rw [inv_pow, hs, inv_neg, ← Complex.exp_neg]
    congr 2
    ring
  have hd : (delta ℓ : ℂ) = -(alpha ℓ ^ 2 + (alpha ℓ)⁻¹ ^ 2) := by
    rw [hs, hi, Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, delta, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have h6 : alpha ℓ ^ 6 = -Complex.exp (-(((3 * (Real.pi / ℓ)) : ℝ) : ℂ) * Complex.I) := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul, hs, neg_pow]
    norm_num
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hl : (4 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have ht : Real.pi / (ℓ : ℝ) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hl
  have hsin (x : ℝ) (hx : 0 < x) (hxp : x < Real.pi) :
      -Complex.exp (-(x : ℂ) * Complex.I) ≠ 1 := by
    intro he
    have hm := congrArg Complex.im he
    rw [Complex.exp_mul_I] at hm
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_im, mul_zero, add_zero, zero_add, mul_one, neg_neg] at hm
    exact (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx hxp)) hm
  refine ⟨mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _), hd, ?_, ?_⟩
  · rw [hs]
    exact hsin _ (by positivity) (by linarith [Real.pi_pos])
  · rw [h6]
    exact hsin _ (by positivity) (by linarith [Real.pi_pos])

private theorem E_triple (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (hn : 3 ≤ n) (t : Fin (ℓ - 1)) :
    E ℓ n h₂ t 0 * E ℓ n h₂ t 1 * E ℓ n h₂ t 0 = E ℓ n h₂ t 0 := by
  have hsymm : Std.Symm (adj ℓ) := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  have hp := (weighted_legal_path_temperley_lieb (adj ℓ) hsymm (mu ℓ)
    (μ_pos ℓ h₂) (delta ℓ) (δ_pos ℓ hℓ) (perron_frobenius ℓ h₂)
    (n + 1) (v1 ℓ h₂) t).2.1 1 ⟨by omega, by omega⟩
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  simp only [E, dif_pos h0, dif_pos h1]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [hp]
  simp only [smul_smul]
  congr 1
  have hd : (delta ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (δ_pos ℓ hℓ))
  field_simp

private theorem ρ_inverse (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (t : Fin (ℓ - 1)) (j : ℕ) :
    (rho ℓ n h₂ t j)⁻¹ = (alpha ℓ)⁻¹ • 1 + alpha ℓ • E ℓ n h₂ t j ∧
      rho ℓ n h₂ t j * (rho ℓ n h₂ t j)⁻¹ = 1 ∧
      (rho ℓ n h₂ t j)⁻¹ * rho ℓ n h₂ t j = 1 := by
  have ha := (α_data ℓ hℓ).1
  have hd := (α_data ℓ hℓ).2.1
  have hx : rho ℓ n h₂ t j * ((alpha ℓ)⁻¹ • 1 + alpha ℓ • E ℓ n h₂ t j) = 1 := by
    unfold rho
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      E_square ℓ n h₂ hℓ t j, smul_smul]
    rw [hd]
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hu := Matrix.isUnit_det_of_right_inverse hx
  exact ⟨Matrix.inv_eq_right_inv hx, Matrix.mul_nonsing_inv _ hu,
    Matrix.nonsing_inv_mul _ hu⟩

private theorem seed_zero_polynomial (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (t : Fin (ℓ - 1)) :
    (seed ℓ n h₂ t 0 - alpha ℓ ^ 2 • 1) *
      (seed ℓ n h₂ t 0 - (alpha ℓ)⁻¹ ^ 6 • 1) = 0 := by
  have ha := (α_data ℓ hℓ).1
  have hd := (α_data ℓ hℓ).2.1
  simp only [seed, rho, sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, E_square ℓ n h₂ hℓ t 0, smul_smul]
  rw [hd]
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
    smul_eq_mul]
  field_simp
  ring

private theorem no_fixed_seed (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (t : Fin (ℓ - 1)) (j : ℕ) (v : Sector ℓ n h₂ t → ℂ)
    (hv : seed ℓ n h₂ t j *ᵥ v = v) : v = 0 := by
  have ha2 := (α_data ℓ hℓ).2.2.1
  have ha6 := (α_data ℓ hℓ).2.2.2
  have hai6 : (alpha ℓ)⁻¹ ^ 6 ≠ 1 := by
    rw [inv_pow]
    intro h
    apply ha6
    simpa using congrArg (fun z : ℂ => z⁻¹) h
  induction j generalizing v with
  | zero =>
    have h := congrArg (fun M : Matrix (Sector ℓ n h₂ t) (Sector ℓ n h₂ t) ℂ => M *ᵥ v)
      (seed_zero_polynomial ℓ n h₂ hℓ t)
    rw [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hv, Matrix.zero_mulVec] at h
    have he : ((1 - alpha ℓ ^ 2) * (1 - (alpha ℓ)⁻¹ ^ 6)) • v = 0 := by
      calc
        _ = v - alpha ℓ ^ 2 • v - (alpha ℓ)⁻¹ ^ 6 • (v - alpha ℓ ^ 2 • v) := by module
        _ = 0 := h
    exact (smul_eq_zero.mp he).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha2)) (sub_ne_zero.mpr (Ne.symm hai6)))
  | succ j ih =>
    have hu := ρ_inverse ℓ n h₂ hℓ t (j + 1)
    have h := congrArg (fun z => (rho ℓ n h₂ t (j + 1))⁻¹ *ᵥ z) hv
    simp only [seed, s, Matrix.mulVec_mulVec, ← mul_assoc, hu.2.2, one_mul] at h
    rw [← Matrix.mulVec_mulVec] at h
    have hz := ih _ h
    calc
      v = (rho ℓ n h₂ t (j + 1) * (rho ℓ n h₂ t (j + 1))⁻¹) *ᵥ v := by
        rw [hu.2.1, Matrix.one_mulVec]
      _ = rho ℓ n h₂ t (j + 1) *ᵥ ((rho ℓ n h₂ t (j + 1))⁻¹ *ᵥ v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hz, Matrix.mulVec_zero]

private theorem loop_path (ℓ n : ℕ) (h₂ : 2 ≤ ℓ)
    (hn : 3 ≤ n) (t : Fin (ℓ - 1)) (hdim : 2 ≤ Fintype.card (Sector ℓ n h₂ t)) :
    ∃ p : Sector ℓ n h₂ t, (p.1 ⟨2, by omega⟩).val = 0 := by
  classical
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have ascend (z : Sector ℓ (N + 3) h₂ t)
      (hz : ∀ k : Fin (N + 4), (z.1 k.castSucc).val + 1 = (z.1 k.succ).val) :
      ∀ k : Fin (N + 5), (z.1 k).val = k.val := by
    intro k
    induction k using Fin.induction with
    | zero => simpa [v1] using congrArg Fin.val z.2.1
    | succ k hk =>
      have he := hz k
      simp only [Fin.val_succ]
      simp only [Fin.val_castSucc] at hk
      omega
  have bad : ∃ z : Sector ℓ (N + 3) h₂ t, ∃ k : Fin (N + 4),
      (z.1 k.succ).val + 1 = (z.1 k.castSucc).val := by
    by_contra hb
    push Not at hb
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp (show 1 <
      Fintype.card (Sector ℓ (N + 3) h₂ t) by omega)
    have hz (z : Sector ℓ (N + 3) h₂ t) (k : Fin (N + 4)) :
        (z.1 k.castSucc).val + 1 = (z.1 k.succ).val :=
      (z.2.2.2 k).resolve_right (hb z k)
    apply hxy
    apply Subtype.ext
    funext k
    apply Fin.ext
    rw [ascend x (hz x), ascend y (hz y)]
  obtain ⟨x, k, hk⟩ := bad
  let P : ℕ → Prop := fun i => ∃ hi : i < N + 4,
    (x.1 ⟨i + 1, by omega⟩).val + 1 = (x.1 ⟨i, by omega⟩).val
  have hex : ∃ i, P i := ⟨k.val, k.isLt, hk⟩
  let i := Nat.find hex
  obtain ⟨hi, hdown⟩ : P i := Nat.find_spec hex
  have hpre : ∀ j (hj : j ≤ i), (x.1 ⟨j, by omega⟩).val = j := by
    intro j
    induction j with
    | zero => intro hj; simpa [v1] using congrArg Fin.val x.2.1
    | succ j ih =>
      intro hj
      have hji : j < i := by omega
      have hnot : ¬P j := Nat.find_min hex hji
      have he := x.2.2.2 ⟨j, by omega⟩
      have hup : (x.1 ⟨j, by omega⟩).val + 1 = (x.1 ⟨j + 1, by omega⟩).val := by
        rcases he with he | he
        · exact he
        · exact False.elim (hnot ⟨by omega, he⟩)
      have hjv := ih (by omega)
      omega
  have hiv := hpre i le_rfl
  have hpos : 0 < i := by omega
  have hflank : x.1 ⟨i - 1, by omega⟩ = x.1 ⟨i + 1, by omega⟩ := by
    apply Fin.ext
    have hprev := hpre (i - 1) (by omega)
    omega
  let y : Fin (N + 3) → Fin (ℓ - 1) := fun j =>
    if hj : j.val < i then x.1 ⟨j.val, by omega⟩ else x.1 ⟨j.val + 2, by omega⟩
  have hy0 : y 0 = v1 ℓ h₂ := by
    simpa [y, hpos] using x.2.1
  have hyend : y (Fin.last (N + 2)) = t := by
    dsimp only [y, Fin.val_last]
    split_ifs with he
    · have hie : i = N + 3 := by omega
      have heq : x.1 ⟨N + 2, by omega⟩ = x.1 (Fin.last (N + 4)) := by
        have e0 : (⟨N + 2, by omega⟩ : Fin (N + 5)) = ⟨i - 1, by omega⟩ :=
          Fin.ext (by change N + 2 = i - 1; omega)
        have e1 : Fin.last (N + 4) = (⟨i + 1, by omega⟩ : Fin (N + 5)) :=
          Fin.ext (by change N + 4 = i + 1; omega)
        exact (congrArg x.1 e0).trans (hflank.trans (congrArg x.1 e1).symm)
      exact heq.trans x.2.2.1
    · exact x.2.2.1
  have hyedge (j : Fin (N + 2)) : adj ℓ (y j.castSucc) (y j.succ) := by
    dsimp only [y, Fin.val_castSucc, Fin.val_succ]
    split_ifs with hj hj'
    · exact x.2.2.2 ⟨j.val, by omega⟩
    · have heq : x.1 ⟨j.val, by omega⟩ = x.1 ⟨j.val + 2, by omega⟩ := by
        have e0 : (⟨j.val, by omega⟩ : Fin (N + 5)) = ⟨i - 1, by omega⟩ :=
          Fin.ext (by change j.val = i - 1; omega)
        have e1 : (⟨j.val + 2, by omega⟩ : Fin (N + 5)) = ⟨i + 1, by omega⟩ :=
          Fin.ext (by change j.val + 2 = i + 1; omega)
        exact (congrArg x.1 e0).trans (hflank.trans (congrArg x.1 e1).symm)
      rw [heq]
      exact x.2.2.2 ⟨j.val + 2, by omega⟩
    · omega
    · exact x.2.2.2 ⟨j.val + 2, by omega⟩
  let z : Fin (N + 5) → Fin (ℓ - 1) := fun j =>
    if hj : j.val < 2 then ⟨j.val, by omega⟩ else y ⟨j.val - 2, by omega⟩
  have hz0 : z 0 = v1 ℓ h₂ := by simp [z, v1]
  have hzend : z (Fin.last (N + 4)) = t := by
    have hne : ¬N + 4 < 2 := by omega
    simpa [z, hne, Fin.last] using hyend
  have hzedge (j : Fin (N + 4)) : adj ℓ (z j.castSucc) (z j.succ) := by
    by_cases h0 : j.val = 0
    · simp [z, h0, adj]
    · by_cases h1 : j.val = 1
      · simp [z, h1, hy0, adj, v1]
      · have hj : ¬j.val < 2 := by omega
        have hj' : ¬j.val + 1 < 2 := by omega
        simp only [z, Fin.val_castSucc, Fin.val_succ, dif_neg hj, dif_neg hj']
        have e : (⟨j.val + 1 - 2, by omega⟩ : Fin (N + 3)) =
            (⟨j.val - 2, by omega⟩ : Fin (N + 2)).succ :=
          Fin.ext (by change j.val + 1 - 2 = j.val - 2 + 1; omega)
        rw [e]
        exact hyedge ⟨j.val - 2, by omega⟩
  refine ⟨⟨z, hz0, hzend, hzedge⟩, ?_⟩
  change (z ⟨2, by omega⟩).val = 0
  simpa [z, v1] using congrArg Fin.val hy0

private theorem first_projection (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (hn : 3 ≤ n) (t : Fin (ℓ - 1)) (p : Sector ℓ n h₂ t)
    (hp : (p.1 ⟨2, by omega⟩).val = 0) :
    E ℓ n h₂ t 0 *ᵥ Pi.single p 1 = (delta ℓ : ℂ) • Pi.single p 1 := by
  have first (x : Sector ℓ n h₂ t) : (x.1 ⟨1, by omega⟩).val = 1 := by
    have he := x.2.2.2 (0 : Fin (n + 1))
    change adj ℓ (x.1 0) (x.1 ⟨1, by omega⟩) at he
    have hx0 : (x.1 0).val = 0 := by simpa [v1] using congrArg Fin.val x.2.1
    change (x.1 0).val + 1 = (x.1 ⟨1, by omega⟩).val ∨
      (x.1 ⟨1, by omega⟩).val + 1 = (x.1 0).val at he
    omega
  have hp0 : p.1 ⟨0, by omega⟩ = v1 ℓ h₂ := p.2.1
  have hflank : p.1 ⟨0, by omega⟩ = p.1 ⟨2, by omega⟩ := by
    apply Fin.ext
    simpa only [hp0, v1] using hp.symm
  have hm : mu ℓ (p.1 ⟨1, by omega⟩) = delta ℓ * mu ℓ (v1 ℓ h₂) := by
    simp only [mu, delta, first p, v1, Fin.val_mk, Nat.cast_one, Nat.cast_zero,
      zero_add, one_mul]
    rw [show ((1 : ℝ) + 1) * Real.pi / ℓ = 2 * (Real.pi / ℓ) by ring,
      Real.sin_two_mul]
    ring
  have h0 : (0 : ℕ) < n := by omega
  rw [Matrix.mulVec_single_one]
  ext x
  change E ℓ n h₂ t 0 x p = (delta ℓ : ℂ) * (Pi.single p 1 : Sector ℓ n h₂ t → ℂ) x
  by_cases hxp : x = p
  · subst x
    simp only [E, dif_pos h0, Matrix.smul_apply, smul_eq_mul, pathProjection,
      Pi.single_eq_same]
    rw [if_pos ⟨fun _ _ => True.intro, hflank⟩]
    rw [Real.sqrt_mul_self (μ_pos ℓ h₂ _).le, hp0, hm]
    rw [div_self (mul_ne_zero (ne_of_gt (δ_pos ℓ hℓ)) (ne_of_gt (μ_pos ℓ h₂ _)))]
    simp
  · have haway : ¬(∀ k : Fin (n + 2), k.val ≠ 1 → x.1 k = p.1 k) := by
      intro he
      apply hxp
      apply Subtype.ext
      funext k
      by_cases hk : k.val = 1
      · have hk' : k = (⟨1, by omega⟩ : Fin (n + 2)) := Fin.ext hk
        exact (congrArg x.1 hk').trans
          ((Fin.ext ((first x).trans (first p).symm)).trans (congrArg p.1 hk').symm)
      · exact he k hk
    simp only [E, dif_pos h0, Matrix.smul_apply, smul_eq_mul, pathProjection]
    rw [if_neg (fun he => haway he.1)]
    simp [hxp]

private def pairVec {X : Type*} (n : ℕ) (x y : X → ℂ) (i : Fin n × X) : ℂ :=
  if i.1.val = 0 then x i.2 else if i.1.val = 1 then y i.2 else 0

private theorem block_action {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (hn : 2 ≤ n) (U G H : Matrix X X ℂ) (x y : X → ℂ) :
    lmBlock n U G H *ᵥ pairVec n x y =
      pairVec n ((U * G) *ᵥ y) (U *ᵥ x + (U * (1 - H)) *ᵥ y) := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by change 0 ≠ 1; decide)
  ext ⟨i, p⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  let f : Fin n → ℂ := fun j => ∑ q : X,
    lmBlock n U G H (i, p) (j, q) * pairVec n x y (j, q)
  have hs : (∑ j : Fin n, f j) = f i0 + f i1 := by
    have hz (j : Fin n) (_ : j ∈ Finset.univ)
        (hj : j ∉ ({i0, i1} : Finset (Fin n))) : f j = 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have h0 : j.val ≠ 0 := fun he => hj.1 (Fin.ext he)
      have h1 : j.val ≠ 1 := fun he => hj.2 (Fin.ext he)
      simp [f, pairVec, h0, h1]
    have h := Finset.sum_subset (Finset.subset_univ {i0, i1}) hz
    simpa [h01] using h.symm
  change (∑ j : Fin n, f j) = _
  rw [hs]
  by_cases hi0 : i.val = 0
  · simp [f, lmBlock, pairVec, i0, i1, hi0, Matrix.mulVec, dotProduct]
  · by_cases hi1 : i.val = 1
    · simp [f, lmBlock, pairVec, i0, i1, hi1, Matrix.mulVec, dotProduct]
    · simp [f, lmBlock, pairVec, i0, i1, hi0, hi1, Fin.ext_iff]

private theorem local_vectors (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (hn : 3 ≤ n) (t : Fin (ℓ - 1)) (hdim : 2 ≤ Fintype.card (Sector ℓ n h₂ t)) :
    ∃ f0 f1 : Sector ℓ n h₂ t → ℂ, f1 ≠ 0 ∧
      rho ℓ n h₂ t 0 *ᵥ f0 = b ℓ • f0 ∧
      rho ℓ n h₂ t 0 *ᵥ f1 = alpha ℓ • f0 + alpha ℓ • f1 ∧
      rho ℓ n h₂ t 1 *ᵥ f0 = alpha ℓ • f0 + (alpha ℓ)⁻¹ ^ 3 • f1 ∧
      rho ℓ n h₂ t 1 *ᵥ f1 = b ℓ • f1 ∧
      (rho ℓ n h₂ t 1)⁻¹ *ᵥ f0 = (alpha ℓ)⁻¹ • f0 + (alpha ℓ)⁻¹ • f1 ∧
      (rho ℓ n h₂ t 1)⁻¹ *ᵥ f1 = (-alpha ℓ ^ 3) • f1 := by
  obtain ⟨p, hp⟩ := loop_path ℓ n h₂ hn t hdim
  let f0 : Sector ℓ n h₂ t → ℂ := Pi.single p 1
  let f1 := alpha ℓ ^ 2 • (E ℓ n h₂ t 1 *ᵥ f0)
  have ha := (α_data ℓ hℓ).1
  have hd := (α_data ℓ hℓ).2.1
  have hδ : (delta ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (δ_pos ℓ hℓ))
  have he0 : E ℓ n h₂ t 0 *ᵥ f0 = (delta ℓ : ℂ) • f0 :=
    first_projection ℓ n h₂ hℓ hn t p hp
  have he10 : E ℓ n h₂ t 0 *ᵥ (E ℓ n h₂ t 1 *ᵥ f0) = f0 := by
    have h := congrArg (fun M : Matrix (Sector ℓ n h₂ t) (Sector ℓ n h₂ t) ℂ => M *ᵥ f0)
      (E_triple ℓ n h₂ hℓ hn t)
    simp only [← Matrix.mulVec_mulVec, he0, Matrix.mulVec_smul] at h
    have h' := congrArg (fun v => (delta ℓ : ℂ)⁻¹ • v) h
    simpa only [smul_smul, inv_mul_cancel₀ hδ, one_smul] using h'
  have he01 : E ℓ n h₂ t 0 *ᵥ f1 = alpha ℓ ^ 2 • f0 := by
    dsimp only [f1]
    rw [Matrix.mulVec_smul, he10]
  have he11 : E ℓ n h₂ t 1 *ᵥ f1 = (delta ℓ : ℂ) • f1 := by
    dsimp only [f1]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, E_square ℓ n h₂ hℓ t 1,
      Matrix.smul_mulVec]
    simp only [smul_smul]
    congr 1
    ring
  have hf0 : f0 ≠ 0 := by
    intro h
    have h' := congrFun h p
    simp [f0] at h'
  have hf1 : f1 ≠ 0 := by
    intro h
    change alpha ℓ ^ 2 • (E ℓ n h₂ t 1 *ᵥ f0) = 0 at h
    have hz := (smul_eq_zero.mp h).resolve_left (pow_ne_zero 2 ha)
    rw [hz, Matrix.mulVec_zero] at he10
    exact hf0 he10.symm
  have hdiag : alpha ℓ + (alpha ℓ)⁻¹ * (delta ℓ : ℂ) = b ℓ := by
    rw [hd]
    unfold b
    field_simp
    ring
  have hid : (alpha ℓ)⁻¹ + alpha ℓ * (delta ℓ : ℂ) = -alpha ℓ ^ 3 := by
    rw [hd]
    field_simp
    ring
  refine ⟨f0, f1, hf1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rho, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he0,
      smul_smul, ← add_smul, hdiag]
  · simp only [rho, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he01,
      smul_smul]
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [rho, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, f1,
      smul_smul]
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  · simp only [rho, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he11,
      smul_smul, ← add_smul, hdiag]
  · rw [(ρ_inverse ℓ n h₂ hℓ t 1).1]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, f1,
      smul_smul]
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  · rw [(ρ_inverse ℓ n h₂ hℓ t 1).1]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he11,
      smul_smul, ← add_smul, hid]

private theorem sector_jordan (ℓ n : ℕ) (h₂ : 2 ≤ ℓ) (hℓ : 4 ≤ ℓ)
    (hn : 3 ≤ n) (t : Fin (ℓ - 1)) (hdim : 2 ≤ Fintype.card (Sector ℓ n h₂ t)) :
    ∃ w : Fin n × Sector ℓ n h₂ t → ℂ,
      (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ ((S1 ℓ n h₂ t - b ℓ • 1) *ᵥ w) = 0 ∧
      (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ w ≠ 0 := by
  obtain ⟨f0, f1, hf1, h00, h01, h10, h11, hi0, hi1⟩ :=
    local_vectors ℓ n h₂ hℓ hn t hdim
  let a := alpha ℓ
  have ha : a ≠ 0 := (α_data ℓ hℓ).1
  have hα : alpha ℓ ≠ 0 := ha
  let W := pairVec n
    ((-a ^ 5 * (a ^ 2 + 1) * (a ^ 8 - a ^ 6 - a ^ 4 - a ^ 2 + 1)) • f0 +
      (a * (2 * a ^ 6 + a ^ 4 - 1)) • f1)
    ((-a ^ 11 * (a ^ 2 + 1)) • f0)
  let V := pairVec n
    ((-a ^ 2 * (a ^ 4 - 1) * (a ^ 6 - 1)) • f0 +
      (a⁻¹ ^ 2 * (a ^ 6 - 1)) • f1)
    ((a ^ 6 - 1) • f1)
  have hW : (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ W = V := by
    dsimp only [S1, seed, s, W, V]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      block_action n (by omega)]
    simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      h00, h01, h10, h11, hi0]
    ext ⟨i, p⟩
    simp only [pairVec, Pi.sub_apply, Pi.smul_apply]
    split_ifs
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, b]
      dsimp only [a]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b]
      dsimp only [a]
      ring_nf
      field_simp [hα]
      ring
    · simp
  have hV : (S1 ℓ n h₂ t - b ℓ • 1) *ᵥ V = 0 := by
    dsimp only [S1, seed, s, V]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      block_action n (by omega)]
    simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
      h00, h01, h10, h11, hi1]
    ext ⟨i, p⟩
    simp only [pairVec, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
    split_ifs
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, b]
      dsimp only [a]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b]
      dsimp only [a]
      field_simp
      ring
    · simp
  have hne : V ≠ 0 := by
    intro he
    have hz : (a ^ 6 - 1) • f1 = 0 := by
      funext p
      have h := congrFun he (⟨1, by omega⟩, p)
      simpa [V, pairVec] using h
    have hc : a ^ 6 - 1 ≠ 0 := sub_ne_zero.mpr (α_data ℓ hℓ).2.2.2
    exact hf1 ((smul_eq_zero.mp hz).resolve_left hc)
  exact ⟨W, by rw [hW, hV], by rw [hW]; exact hne⟩

theorem result : claim := by
  intro ℓ n t hℓ hn h₂ hdim
  refine ⟨?_, sector_jordan ℓ n h₂ hℓ hn t hdim⟩
  intro j v hv
  exact no_fixed_seed ℓ n h₂ hℓ t j.val v hv

#print axioms result

end D5.S3.Quantum.Algebra.JonesTemperleyLiebLongMoodyJordanObstruction

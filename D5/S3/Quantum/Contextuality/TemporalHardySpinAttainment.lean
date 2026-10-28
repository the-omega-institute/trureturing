/- GID: D5/S3/Quantum/Contextuality/TemporalHardySpinAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/TemporalHardySpinAttainment
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Temporal Hardy success probability one quarter is attained by every positive spin. -/

import D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound
import D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

/-! Spin coherent vectors and temporal Hardy attainment. -/

noncomputable section
open scoped BigOperators Matrix
open Matrix
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz spinRad)
open D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

namespace D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment

/-- The spin component u·S. -/
def spinComponent (n : ℕ) (u : Fin 3 → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (u 0 : ℂ) • Jx n + (u 1 : ℂ) • Jy n + (u 2 : ℂ) • Jz n

/-- Π is the Lüders spectral projector of M for the outcome a. -/
def IsSpectralProjector {n : ℕ}
    (M P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : ℝ) : Prop :=
  P * P = P ∧ Pᴴ = P ∧ ∀ v, P *ᵥ v = v ↔ M *ᵥ v = (a : ℂ) • v

/-- prob(X, x; Y, y) = ⟨ψ|Π_X Π_Y Π_X|ψ⟩. -/
def seqProb {n : ℕ} (ψ : Fin (n + 1) → ℂ)
    (PX PY : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℂ :=
  star ψ ⬝ᵥ ((PX * PY * PX) *ᵥ ψ)

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ (uA₁ uA₂ uB₁ uB₂ : Fin 3 → ℝ) (a₁ a₂ b₁ b₂ : ℝ)
      (PA₁ PA₂ PB₁ PB₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ψ : Fin (n + 1) → ℂ),
      (∑ i, uA₁ i ^ 2 = 1) ∧ (∑ i, uA₂ i ^ 2 = 1) ∧
      (∑ i, uB₁ i ^ 2 = 1) ∧ (∑ i, uB₂ i ^ 2 = 1) ∧
      IsSpectralProjector (spinComponent n uA₁) PA₁ a₁ ∧
      IsSpectralProjector (spinComponent n uA₂) PA₂ a₂ ∧
      IsSpectralProjector (spinComponent n uB₁) PB₁ b₁ ∧
      IsSpectralProjector (spinComponent n uB₂) PB₂ b₂ ∧
      star ψ ⬝ᵥ ψ = 1 ∧
      seqProb ψ PA₁ PB₁ = 0 ∧ seqProb ψ (1 - PA₁) PB₂ = 0 ∧
      seqProb ψ PA₂ (1 - PB₁) = 0 ∧ seqProb ψ PA₂ PB₂ = 1 / 4

private def coeff (n : ℕ) (r : ℝ) (k : Fin (n + 1)) : ℝ :=
  spinRad n k * r ^ k.val

private def tilt (n : ℕ) (r : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (((1 - r ^ 2) / (1 + r ^ 2) : ℝ) : ℂ) • Jz n +
    (((2 * r) / (1 + r ^ 2) : ℝ) : ℂ) • Jx n

private lemma radius_spec (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℝ, 0 < r ∧ (1 + r ^ 2) ^ n = 2 := by
  let t : ℝ := (2 : ℝ) ^ ((n : ℝ)⁻¹)
  have ht : 1 < t := Real.one_lt_rpow (by norm_num) (by positivity)
  refine ⟨Real.sqrt (t - 1), Real.sqrt_pos.mpr (by linarith), ?_⟩
  rw [Real.sq_sqrt (by linarith : 0 ≤ t - 1)]
  rw [show 1 + (t - 1) = t by ring]
  exact Real.rpow_inv_natCast_pow (by norm_num) (by omega)

private lemma coeff_zero (n : ℕ) (r : ℝ) : coeff n r 0 = 1 := by
  simp only [coeff, spinRad, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one,
    Real.sqrt_one, pow_zero, mul_one]

private lemma coeff_sq_sum (n : ℕ) (r : ℝ) :
    ∑ k : Fin (n + 1), (coeff n r k) ^ 2 = (1 + r ^ 2) ^ n := by
  rw [add_comm (1 : ℝ), add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff, spinRad, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_pow, mul_one]
  rw [← pow_mul, ← pow_mul]
  ring

private lemma ladder_pair (n k : ℕ) (hk : k < n) :
    Real.sqrt ((k + 1 : ℝ) * (n - k : ℝ)) * Real.sqrt (n.choose (k + 1) : ℝ) =
      (n - k : ℝ) * Real.sqrt (n.choose k : ℝ) ∧
    Real.sqrt ((k + 1 : ℝ) * (n - k : ℝ)) * Real.sqrt (n.choose k : ℝ) =
      (k + 1 : ℝ) * Real.sqrt (n.choose (k + 1) : ℝ) := by
  have hkn : k ≤ n := le_of_lt hk
  have hd : 0 ≤ (n : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkn)
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n k)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hkn] at h
  constructor
  · rw [← Real.sqrt_mul (mul_nonneg (by positivity) hd)]
    have he : ((k + 1 : ℝ) * (n - k : ℝ)) * (n.choose (k + 1) : ℝ) =
        (n - k : ℝ) ^ 2 * (n.choose k : ℝ) := by nlinarith [h]
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hd]
  · rw [← Real.sqrt_mul (mul_nonneg (by positivity) hd)]
    have he : ((k + 1 : ℝ) * (n - k : ℝ)) * (n.choose k : ℝ) =
        (k + 1 : ℝ) ^ 2 * (n.choose (k + 1) : ℝ) := by nlinarith [h]
    rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

private def binomVector (n : ℕ) (r : ℝ) : Fin (n + 1) → ℂ :=
  fun k => (coeff n r k : ℂ)

private lemma raising_entry (n : ℕ) (i j : Fin (n + 1)) :
    Jplus n i j = if i.val + 1 = j.val then
      (Real.sqrt ((j.val : ℝ) * ((n : ℝ) + 1 - j.val)) : ℂ) else 0 := by
  unfold Jplus
  congr 2
  ring

private lemma upper_ladder (n : ℕ) (r : ℝ) (i j : Fin (n + 1))
    (h : i.val + 1 = j.val) :
    Jplus n i j * binomVector n r j =
      ((n : ℂ) - i.val) * (r : ℂ) * binomVector n r i := by
  have hi : i.val < n := by have := j.isLt; omega
  have hv : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast h.symm
  have he := (ladder_pair n i.val hi).1
  have hs : (j.val : ℝ) * ((n : ℝ) + 1 - j.val) = (i.val + 1 : ℝ) * (n - i.val : ℝ) := by
    rw [hv]; ring
  rw [raising_entry, if_pos h]
  unfold binomVector coeff spinRad
  have hh : Real.sqrt ((j.val : ℝ) * ((n : ℝ) + 1 - j.val)) *
      (Real.sqrt (n.choose j.val : ℝ) * r ^ j.val) =
      ((n : ℝ) - i.val) * r * (Real.sqrt (n.choose i.val : ℝ) * r ^ i.val) := by
    rw [hs, ← h, pow_succ]
    calc _ = (Real.sqrt ((i.val + 1 : ℝ) * (n - i.val : ℝ)) *
        Real.sqrt (n.choose (i.val + 1) : ℝ)) * r ^ i.val * r := by ring
      _ = _ := by rw [he]; ring
  exact_mod_cast hh

private lemma lower_ladder (n : ℕ) (r : ℝ) (i j : Fin (n + 1))
    (h : j.val + 1 = i.val) :
    (Jplus n)ᴴ i j * binomVector n r j * (r : ℂ) =
      (i.val : ℂ) * binomVector n r i := by
  have hj : j.val < n := by have := i.isLt; omega
  have hv : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast h.symm
  have he := (ladder_pair n j.val hj).2
  have hs : (i.val : ℝ) * ((n : ℝ) + 1 - i.val) = (j.val + 1 : ℝ) * (n - j.val : ℝ) := by
    rw [hv]; ring
  rw [conjTranspose_apply, raising_entry, if_pos h]
  rw [Complex.star_def, Complex.conj_ofReal]
  unfold binomVector coeff spinRad
  have hh : Real.sqrt ((i.val : ℝ) * ((n : ℝ) + 1 - i.val)) *
      (Real.sqrt (n.choose j.val : ℝ) * r ^ j.val) * r =
      (i.val : ℝ) * (Real.sqrt (n.choose i.val : ℝ) * r ^ i.val) := by
    rw [hs, ← h, pow_succ]
    calc _ = (Real.sqrt ((j.val + 1 : ℝ) * (n - j.val : ℝ)) *
        Real.sqrt (n.choose j.val : ℝ)) * r ^ j.val * r := by ring
      _ = _ := by rw [he]; push_cast; ring
  exact_mod_cast hh

private lemma raising_action (n : ℕ) (r : ℝ) (i : Fin (n + 1)) :
    (Jplus n *ᵥ binomVector n r) i =
      ((n : ℂ) - i.val) * (r : ℂ) * binomVector n r i := by
  change ∑ j, Jplus n i j * binomVector n r j = _
  by_cases hi : i.val < n
  · let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    rw [Finset.sum_eq_single j]
    · exact upper_ladder n r i j rfl
    · intro k hk hkj
      have hne : ¬i.val + 1 = k.val := by
        intro h; apply hkj; apply Fin.ext; exact h.symm
      rw [raising_entry, if_neg hne, zero_mul]
    · intro h; exact (h (Finset.mem_univ j)).elim
  · have hin : i.val = n := by have := i.isLt; omega
    rw [hin, sub_self, zero_mul, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [raising_entry, if_neg (by have := j.isLt; omega), zero_mul]

private lemma lowering_action (n : ℕ) (r : ℝ) (i : Fin (n + 1)) :
    ((Jplus n)ᴴ *ᵥ binomVector n r) i * (r : ℂ) =
      (i.val : ℂ) * binomVector n r i := by
  change (∑ j, (Jplus n)ᴴ i j * binomVector n r j) * (r : ℂ) = _
  rw [Finset.sum_mul]
  by_cases hi : 0 < i.val
  · let j : Fin (n + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
    rw [Finset.sum_eq_single j]
    · exact lower_ladder n r i j (by dsimp [j]; omega)
    · intro k hk hkj
      have hne : ¬k.val + 1 = i.val := by
        intro h; apply hkj; apply Fin.ext; dsimp [j]; omega
      rw [conjTranspose_apply, raising_entry, if_neg hne, star_zero, zero_mul, zero_mul]
    · intro h; exact (h (Finset.mem_univ j)).elim
  · have hiz : i.val = 0 := by omega
    rw [hiz, Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [conjTranspose_apply, raising_entry, if_neg (by omega), star_zero,
      zero_mul, zero_mul]

private lemma tilt_eigenvector (n : ℕ) (r : ℝ) :
    tilt n r *ᵥ binomVector n r = ((n : ℂ) / 2) • binomVector n r := by
  ext i
  have hu := raising_action n r i
  have hl := lowering_action n r i
  have hd : (1 : ℂ) + (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ)<1 + r ^ 2))
  simp only [tilt, Matrix.add_mulVec, Matrix.smul_mulVec, Jx,
    Matrix.add_mulVec, Matrix.smul_mulVec, Jz, Matrix.mulVec_diagonal,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [hu]
  field_simp
  linear_combination (2 : ℂ) * hl

private lemma tilt_off_band (n : ℕ) (r : ℝ) (i j : Fin (n + 1))
    (hd : i ≠ j) (hu : i.val + 1 ≠ j.val) (hl : j.val + 1 ≠ i.val) :
    tilt n r i j = 0 := by
  simp only [tilt, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Jz,
    Matrix.diagonal_apply_ne _ hd, mul_zero, zero_add, Jx,
    Matrix.smul_apply, Matrix.add_apply, raising_entry, if_neg hu,
    conjTranspose_apply, if_neg hl, star_zero, add_zero, mul_zero]

private lemma tilt_upper_nonzero (n : ℕ) (r : ℝ) (hr : 0 < r)
    (i j : Fin (n + 1)) (h : i.val + 1 = j.val) : tilt n r i j ≠ 0 := by
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hji : ¬j.val + 1 = i.val := by omega
  have hj : (0 : ℝ)<j.val := by exact_mod_cast (show 0<j.val by omega)
  have hjn : (0 : ℝ)<(n : ℝ) + 1 - j.val := by
    have he : (j.val : ℝ) < (n : ℝ) + 1 := by exact_mod_cast j.isLt
    linarith
  have hs : (Real.sqrt ((j.val : ℝ) * ((n : ℝ) + 1 - j.val)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hj hjn)).ne'
  have hc : (((2 * r) / (1 + r ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (div_pos (by positivity) (by positivity) :
      (0 : ℝ)<2 * r / (1 + r ^ 2)))
  simp only [tilt, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Jz,
    Matrix.diagonal_apply_ne _ hij, mul_zero, zero_add, Jx,
    Matrix.smul_apply, Matrix.add_apply, raising_entry, if_pos h,
    conjTranspose_apply, if_neg hji, star_zero, add_zero]
  exact mul_ne_zero hc (mul_ne_zero (by norm_num) hs)

private lemma tilt_first_zero (n : ℕ) (r : ℝ) (hr : 0 < r)
    (v : Fin (n + 1) → ℂ) (eigen : ℂ)
    (hv : tilt n r *ᵥ v = eigen • v) (h0 : v 0 = 0) : v = 0 := by
  apply boundary_zero_observability (by omega) v h0
  intro i hi hprev
  by_cases hin : i.val < n
  · let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have hnext : i.succ.succ = j.castSucc.succ := by apply Fin.ext; rfl
    rw [hnext, extend_interior]
    have hrow := congrFun hv i
    have hsum : (tilt n r *ᵥ v) i = tilt n r i j * v j := by
      change ∑ l, tilt n r i l * v l = _
      apply Finset.sum_eq_single j
      · intro l hl hlj
        by_cases hli : l = i
        · subst l; rw [hi, mul_zero]
        · by_cases hlp : l.val + 1 = i.val
          · have he : i.castSucc.castSucc = l.castSucc.succ := Fin.ext hlp.symm
            rw [he, extend_interior] at hprev
            rw [hprev, mul_zero]
          · rw [tilt_off_band n r i l (Ne.symm hli)
              (by intro h; apply hlj; apply Fin.ext; exact h.symm) hlp, zero_mul]
      · intro h; exact (h (Finset.mem_univ j)).elim
    rw [hsum] at hrow
    change tilt n r i j * v j = eigen * v i at hrow
    rw [hi, mul_zero] at hrow
    exact (mul_eq_zero.mp hrow).resolve_left (tilt_upper_nonzero n r hr i j rfl)
  · have he : i.succ.succ = Fin.last (n + 2) := by
      apply Fin.ext
      dsimp
      have := i.isLt
      omega
    rw [he, extend_last]

private lemma tilt_eigenspace (n : ℕ) (r : ℝ) (hr : 0 < r)
    (v : Fin (n + 1) → ℂ) :
    tilt n r *ᵥ v = ((n : ℂ) / 2) • v ↔ ∃ z : ℂ, v = z • binomVector n r := by
  constructor
  · intro hv
    have hz : (v - v 0 • binomVector n r) 0 = 0 := by
      change v 0 - v 0 * (coeff n r 0 : ℂ) = 0
      rw [coeff_zero, Complex.ofReal_one, mul_one, sub_self]
    have he : tilt n r *ᵥ (v - v 0 • binomVector n r) =
        ((n : ℂ) / 2) • (v - v 0 • binomVector n r) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hv, tilt_eigenvector,
        smul_sub, smul_comm (v 0)]
    have hh := tilt_first_zero n r hr _ _ he hz
    exact ⟨v 0, sub_eq_zero.mp hh⟩
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_smul, tilt_eigenvector, smul_comm z]

private def north (n : ℕ) : Fin (n + 1) → ℂ := Pi.single 0 1

private lemma north_norm (n : ℕ) : star (north n) ⬝ᵥ north n = 1 := by
  rw [north, dotProduct_single]
  simp only [Pi.star_apply, Pi.single_eq_same, star_one, mul_one]

private lemma z_eigenspace (n : ℕ) (v : Fin (n + 1) → ℂ) :
    Jz n *ᵥ v = ((n : ℂ) / 2) • v ↔ ∃ z : ℂ, v = z • north n := by
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    by_cases hi : i = 0
    · subst i; simp only [north, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
    · have hn : (i.val : ℂ) ≠ 0 := by
        exact_mod_cast (show i.val ≠ 0 by intro h; apply hi; exact Fin.ext h)
      have h := congrFun hv i
      simp only [Jz, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
      push_cast at h
      have hz : (i.val : ℂ) * v i = 0 := by linear_combination -h
      rw [(mul_eq_zero.mp hz).resolve_left hn]
      simp only [north, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi, mul_zero]
  · rintro ⟨z, rfl⟩
    ext i
    simp only [Jz, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, north]
    by_cases hi : i = 0
    · subst i; simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Pi.single_eq_same,
        Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
    · rw [Pi.single_eq_of_ne hi]; ring

def ray (n : ℕ) (w : Fin (n + 1) → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (d : ℂ)⁻¹ • vecMulVec w (star w)

private lemma ray_action (n : ℕ) (w v : Fin (n + 1) → ℂ) (d : ℝ) :
    ray n w d *ᵥ v = ((d : ℂ)⁻¹ * (star w ⬝ᵥ v)) • w := by
  rw [ray, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  change (d : ℂ)⁻¹ * (w i * (star w ⬝ᵥ v)) =
    ((d : ℂ)⁻¹ * (star w ⬝ᵥ v)) * w i
  ring

private lemma ray_spectral (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (w : Fin (n + 1) → ℂ) (a d : ℝ) (hd : d ≠ 0)
    (hnorm : star w ⬝ᵥ w = (d : ℂ))
    (he : ∀ v, M *ᵥ v = (a : ℂ) • v ↔ ∃ z : ℂ, v = z • w) :
    IsSpectralProjector M (ray n w d) a := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  refine ⟨?_, ?_, ?_⟩
  · unfold ray
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
      hnorm, Matrix.vecMulVec_smul, smul_smul]
    congr 1
    field_simp [hdC]
  · rw [ray, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  · intro v
    rw [he]
    constructor
    · intro h
      exact ⟨(d : ℂ)⁻¹ * (star w ⬝ᵥ v), h.symm.trans (ray_action n w v d)⟩
    · rintro ⟨z, rfl⟩
      rw [ray_action, dotProduct_smul, hnorm]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hdC]

theorem result : claim := by
  intro n hn
  obtain ⟨r, hr, hpow⟩ := radius_spec n hn
  let b := binomVector n r
  let φ := north n
  let ψ := b - φ
  let P := ray n φ 1
  let Q := ray n b 2
  let u₀ : Fin 3 → ℝ := ![0, 0, 1]
  let u : Fin 3 → ℝ := ![2 * r / (1 + r ^ 2), 0, (1 - r ^ 2) / (1 + r ^ 2)]
  have hb : star b ⬝ᵥ b = 2 := by
    change (∑ i : Fin (n + 1), star (coeff n r i : ℂ) * (coeff n r i : ℂ)) = 2
    simp only [Complex.star_def, Complex.conj_ofReal, ← pow_two]
    exact_mod_cast (coeff_sq_sum n r).trans hpow
  have hφ : star φ ⬝ᵥ φ = 1 := north_norm n
  have hφb : star φ ⬝ᵥ b = 1 := by
    change star (north n) ⬝ᵥ binomVector n r = 1
    rw [north, ← Pi.single_star, single_dotProduct]
    simp only [star_one, one_mul, binomVector, coeff_zero, Complex.ofReal_one]
  have hbφ : star b ⬝ᵥ φ = 1 := by
    change star (binomVector n r) ⬝ᵥ north n = 1
    rw [north, dotProduct_single]
    change star (coeff n r 0 : ℂ) * 1 = 1
    rw [coeff_zero, Complex.ofReal_one, star_one, mul_one]
  have hψ : star ψ ⬝ᵥ ψ = 1 := by
    change star (b - φ) ⬝ᵥ (b - φ) = 1
    rw [star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hb, hbφ, hφb, hφ]
    norm_num
  have hψb : star ψ ⬝ᵥ b = 1 := by
    change star (b - φ) ⬝ᵥ b = 1
    rw [star_sub, sub_dotProduct, hb, hφb]
    norm_num
  have hvalue : (((n : ℝ) / 2 : ℝ) : ℂ) = (n : ℂ) / 2 := by push_cast; rfl
  have hP : IsSpectralProjector (Jz n) P ((n : ℝ) / 2) := by
    apply ray_spectral n (Jz n) φ ((n : ℝ) / 2) 1 (by norm_num) hφ
    intro v
    rw [hvalue]
    exact z_eigenspace n v
  have hQ : IsSpectralProjector (tilt n r) Q ((n : ℝ) / 2) := by
    apply ray_spectral n (tilt n r) b ((n : ℝ) / 2) 2 (by norm_num) hb
    intro v
    rw [hvalue]
    exact tilt_eigenspace n r hr v
  have hPψ : P *ᵥ ψ = 0 := by
    change ray n φ 1 *ᵥ (b - φ) = 0
    rw [ray_action, dotProduct_sub, hφb, hφ, sub_self, mul_zero, zero_smul]
  have hQψ : Q *ᵥ ψ = (1 / 2 : ℂ) • b := by
    change ray n b 2 *ᵥ (b - φ) = (1 / 2 : ℂ) • b
    rw [ray_action, dotProduct_sub, hb, hbφ]
    norm_num
  have hPb : P *ᵥ b = φ := by
    change ray n φ 1 *ᵥ b = φ
    rw [ray_action, hφb]
    norm_num
  have hQφ : Q *ᵥ φ = (1 / 2 : ℂ) • b := by
    change ray n b 2 *ᵥ φ = (1 / 2 : ℂ) • b
    rw [ray_action, hbφ]
    norm_num
  have hu₀ : ∑ i, u₀ i ^ 2 = 1 := by norm_num [u₀, Fin.sum_univ_succ]
  have hu : ∑ i, u i ^ 2 = 1 := by
    norm_num [u, Fin.sum_univ_succ]
    field_simp
    ring
  have hM₀ : spinComponent n u₀ = Jz n := by
    norm_num [spinComponent, u₀]
  have hM : spinComponent n u = tilt n r := by
    ext i j
    dsimp [spinComponent, u, tilt]
    ring
  have hCPψ : (1 - P) *ᵥ ψ = ψ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPψ, sub_zero]
  have hCQQψ : (1 - Q) *ᵥ (Q *ᵥ ψ) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hQ.1, sub_self]
  refine ⟨u₀, u, u, u₀, (n : ℝ) / 2, (n : ℝ) / 2, (n : ℝ) / 2, (n : ℝ) / 2,
    P, Q, Q, P, ψ, hu₀, hu, hu, hu₀, ?_, ?_, ?_, ?_, hψ, ?_, ?_, ?_, ?_⟩
  · rw [hM₀]; exact hP
  · rw [hM]; exact hQ
  · rw [hM]; exact hQ
  · rw [hM₀]; exact hP
  · unfold seqProb
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPψ,
      Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero]
  · unfold seqProb
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCPψ, hPψ,
      Matrix.mulVec_zero, dotProduct_zero]
  · unfold seqProb
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hCQQψ,
      Matrix.mulVec_zero, dotProduct_zero]
  · unfold seqProb
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQψ,
      Matrix.mulVec_smul, hPb, Matrix.mulVec_smul, hQφ,
      dotProduct_smul, dotProduct_smul, hψb]
    norm_num

end D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment

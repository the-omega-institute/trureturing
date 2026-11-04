/- GID: D5/S1/Dynamics/Shadowing/QuadraticRotationHitting
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/QuadraticRotationHitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative short-return meshes for scaled quadratic-irrational rotations. -/

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

/-! Integer norm separation and signed finite meshes give uniform rotation
hitting estimates. All integer lifts are retained in the proofs. -/

namespace D5.S1.Dynamics.Shadowing

/-- A scaled square root has an explicit badly-approximable lower bound. -/
theorem sqrt_two_scaled_round_lower (M k : ℕ) (hM : 0 < M) (hk : 0 < k) :
    1 / ((M : ℝ) * (M + 3) * k) ≤
      |(k : ℝ) * (Real.sqrt 2 / M) - round ((k : ℝ) * (Real.sqrt 2 / M))| := by
  let m : ℤ := round ((k : ℝ) * (Real.sqrt 2 / M))
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hm0 : 0 ≤ m := by
    dsimp [m]
    rw [round_eq]
    apply Int.floor_nonneg.mpr
    positivity
  have hmr : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have hsum : 0 < (k : ℝ) * Real.sqrt 2 + M * m := by positivity
  have hN : (2 * (k : ℤ)^2 - (M : ℤ)^2 * m^2) ≠ 0 := by
    intro he
    have he' : (2 : ℝ) * (k : ℝ)^2 - (M : ℝ)^2 * (m : ℝ)^2 = 0 := by
      exact_mod_cast he
    have hfac : ((k : ℝ) * Real.sqrt 2 - M * m) *
        ((k : ℝ) * Real.sqrt 2 + M * m) = 0 := by
      calc
        _ = (k : ℝ)^2 * (Real.sqrt 2)^2 - (M : ℝ)^2 * (m : ℝ)^2 := by ring
        _ = 0 := by rw [hs]; nlinarith [he']
    have heq := (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hsum)
    exact (irrational_sqrt_two.natCast_mul hk.ne').ne_int ((M : ℤ) * m)
      (by push_cast; linarith)
  have hN1 : (1 : ℝ) ≤ |(2 : ℝ) * (k : ℝ)^2 - (M : ℝ)^2 * (m : ℝ)^2| := by
    exact_mod_cast Int.one_le_abs hN
  have hid : (2 : ℝ) * (k : ℝ)^2 - (M : ℝ)^2 * (m : ℝ)^2 =
      M * ((k : ℝ) * (Real.sqrt 2 / M) - m) *
        ((k : ℝ) * Real.sqrt 2 + M * m) := by
    calc
      _ = ((k : ℝ) * Real.sqrt 2 - M * m) *
          ((k : ℝ) * Real.sqrt 2 + M * m) := by
        nlinarith [show ((k : ℝ) * Real.sqrt 2)^2 = (k : ℝ)^2 * 2 by rw [mul_pow, hs]]
      _ = _ := by field_simp
  rw [hid, abs_mul, abs_mul, abs_of_pos hMr, abs_of_pos hsum] at hN1
  have hmupper := round_le_add_half ((k : ℝ) * (Real.sqrt 2 / M))
  change (m : ℝ) ≤ _ at hmupper
  have hmupper' := (mul_le_mul_of_nonneg_left hmupper hMr.le)
  have hcancel : (M : ℝ) * ((k : ℝ) * (Real.sqrt 2 / M) + 1 / 2) =
      (k : ℝ) * Real.sqrt 2 + M / 2 := by field_simp
  rw [hcancel] at hmupper'
  have hs3 : 2 * Real.sqrt 2 ≤ 3 := by nlinarith
  have hs3k := mul_le_mul_of_nonneg_right hs3 hkr.le
  have hMk := mul_le_mul_of_nonneg_left hk1 hMr.le
  have hden : (k : ℝ) * Real.sqrt 2 + M * m ≤ (M + 3) * k := by nlinarith
  have hbound := mul_le_mul_of_nonneg_left hden
    (mul_nonneg hMr.le (abs_nonneg ((k : ℝ) * (Real.sqrt 2 / M) - m)))
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < M * (M + 3) * k)).2
  nlinarith [hN1.trans hbound]

/-- A signed mesh approximates any phase, with its last index bounded by the
reciprocal step. The integer lift records circle wrap-around explicitly. -/
theorem signed_rotation_mesh (θ τ e : ℝ) (he : e ≠ 0) :
    ∃ j : ℕ, (j : ℝ) * |e| < 1 ∧
      ∃ m : ℤ, |θ + j * e - τ - m| ≤ |e| := by
  have hb : 0 < |e| := abs_pos.mpr he
  have positive_mesh (t : ℝ) : ∃ j : ℕ, (j : ℝ) * |e| < 1 ∧
      0 ≤ Int.fract t - j * |e| ∧ Int.fract t - j * |e| < |e| := by
    let j := ⌊Int.fract t / |e|⌋₊
    have hj := Nat.floor_le (div_nonneg (Int.fract_nonneg t) hb.le)
    have hj' := Nat.lt_floor_add_one (Int.fract t / |e|)
    change (j : ℝ) ≤ _ at hj
    change _ < (j : ℝ) + 1 at hj'
    have hl := (le_div_iff₀ hb).mp hj
    have hu := (div_lt_iff₀ hb).mp hj'
    exact ⟨j, hl.trans_lt (Int.fract_lt_one t), by linarith, by nlinarith⟩
  rcases lt_or_gt_of_ne he with hneg | hpos
  · obtain ⟨j, hj, hl, hu⟩ := positive_mesh (θ - τ)
    refine ⟨j, hj, ⌊θ - τ⌋, ?_⟩
    rw [abs_of_neg hneg] at hl hu ⊢
    rw [abs_le]
    have ht := Int.fract_add_floor (θ - τ)
    constructor <;> linarith
  · obtain ⟨j, hj, hl, hu⟩ := positive_mesh (τ - θ)
    refine ⟨j, hj, -⌊τ - θ⌋, ?_⟩
    rw [abs_of_pos hpos] at hl hu ⊢
    rw [Int.cast_neg, abs_le]
    have ht := Int.fract_add_floor (τ - θ)
    constructor <;> linarith

/-- A badly-approximable rotation hits every quarter interval in O(p) steps,
uniformly over the starting phase. No qualitative density theorem is used. -/
theorem badly_approximable_quarter_hitting (α κ : ℝ) (hκ : 0 < κ)
    (hlower : ∀ k : ℕ, 0 < k → κ / k ≤ |(k : ℝ) * α - round ((k : ℝ) * α)|)
    (p : ℕ) (hp : 0 < p) (θ a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 3 / 4) :
    ∃ j : ℕ, (j : ℝ) ≤ 256 * p / κ ∧
      Int.fract (θ + (j : ℝ) * p * α) ∈ Set.Icc a (a + 1 / 4) := by
  obtain ⟨q, hq, hq16, hshort⟩ :=
    Real.exists_nat_abs_mul_sub_round_le ((p : ℝ) * α) (n := 16) (by norm_num)
  let r : ℤ := round ((q : ℝ) * ((p : ℝ) * α))
  let e : ℝ := (q : ℝ) * ((p : ℝ) * α) - r
  have hl := hlower (q * p) (Nat.mul_pos hq hp)
  have hmul : ((q * p : ℕ) : ℝ) * α = (q : ℝ) * ((p : ℝ) * α) := by push_cast; ring
  rw [hmul] at hl
  change κ / ((q * p : ℕ) : ℝ) ≤ |e| at hl
  have hβ : 0 < |e| := (div_pos hκ (by positivity)).trans_le hl
  have hshort' : |e| ≤ 1 / 17 := by
    dsimp [e, r]
    convert hshort using 1 <;> norm_num
  obtain ⟨t, ht, m, hm⟩ := signed_rotation_mesh θ (a + 1 / 8) e (abs_pos.mp hβ)
  let j := t * q
  let z : ℤ := (t : ℤ) * r + m
  let w : ℝ := θ + (j : ℝ) * p * α
  have herr : |w - (a + 1 / 8) - z| ≤ |e| := by
    convert hm using 1
    congr 1
    dsimp [w, j, z, e]
    push_cast
    ring
  have helo := (abs_le.mp herr).1
  have hehi := (abs_le.mp herr).2
  have hfract : Int.fract w = w - z := Int.fract_eq_iff.mpr
    ⟨by linarith, by linarith, z, by ring⟩
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hq16r : (q : ℝ) ≤ 16 := by exact_mod_cast hq16
  have hrecip : 1 / |e| ≤ (q : ℝ) * p / κ := by
    apply (div_le_div_iff₀ hβ hκ).2
    have hh := (div_le_iff₀ (mul_pos hqr hpr)).mp
      (show κ / ((q : ℝ) * p) ≤ |e| by simpa using hl)
    nlinarith
  have htbound : (t : ℝ) ≤ (q : ℝ) * p / κ :=
    ((le_div_iff₀ hβ).2 ht.le).trans hrecip
  refine ⟨j, ?_, ?_⟩
  · have hqbound : (q : ℝ) * q ≤ 256 := by nlinarith
    have htq := mul_le_mul_of_nonneg_right htbound hqr.le
    have hqp := mul_le_mul_of_nonneg_right hqbound hpr.le
    dsimp [j]
    rw [Nat.cast_mul]
    apply htq.trans
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hκ).2
    nlinarith
  · change Int.fract w ∈ _
    rw [hfract]
    exact ⟨by linarith, by linarith⟩

/-- The integral bound used by the progression construction. -/
theorem sqrt_two_scaled_quarter_hitting (M p : ℕ) (hM : 0 < M) (hp : 0 < p)
    (θ a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 3 / 4) :
    ∃ j ≤ (256 * M * (M + 3)) * p,
      Int.fract (θ + (j : ℝ) * p * (Real.sqrt 2 / M)) ∈ Set.Icc a (a + 1 / 4) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨j, hj, hit⟩ := badly_approximable_quarter_hitting (Real.sqrt 2 / M)
    (1 / ((M : ℝ) * (M + 3))) (by positivity)
    (fun k hk => by simpa only [div_div] using sqrt_two_scaled_round_lower M k hM hk)
    p hp θ a ha ha'
  refine ⟨j, ?_, hit⟩
  have heq : (256 : ℝ) * p / (1 / ((M : ℝ) * (M + 3))) =
      ((256 * M * (M + 3)) * p : ℕ) := by push_cast; field_simp <;> ring
  rw [heq] at hj
  exact_mod_cast hj

end D5.S1.Dynamics.Shadowing

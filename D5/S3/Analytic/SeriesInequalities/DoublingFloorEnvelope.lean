/- GID: D5/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/DoublingFloorEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Doubling floors have uniform two-sided near-critical profiles. -/

/- Every declaration concerns arbitrary infinite sequences or real functions,
   with noncomputable real powers, infinite sums or suprema. No bounded
   enumeration, checker, numeric reduction or certified finite instance is
   supplied. The computational-content kind is none; the other utility
   fields are not applicable. -/

import D5.S3.Analytic.SeriesInequalities.PrescribedRatioFloorSmoothing
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.Compact

open Filter Finset Set
open scoped Topology ENNReal

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope

open PrescribedRatioFloorSmoothing

/-- The numerical profile on a fixed geometric grid. -/
def profile (η : ℕ → ℝ) (N b a u : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal ((N * b ^ k) ^ (-u) * η k ^ (-a + u))

private lemma cross_scale {g : ℝ → ℝ} {D t x : ℝ}
    (hg : ∀ y : ℝ, 2 ≤ y → 1 ≤ g y) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ y : ℝ, 2 ≤ y → g (2 * y) ≤ D * g y)
    (ht : 2 ≤ t) (htx : t ≤ x) :
    g x ≤ D * (x / t) ^ (Real.log D / Real.log 2) * g t := by
  have htpos : 0 < t := by linarith
  have hxpos : 0 < x := htpos.trans_le htx
  have hyone : 1 ≤ x / t := (le_div_iff₀ htpos).2 (by simpa using htx)
  have hypos := zero_lt_one.trans_le hyone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hDpos := zero_lt_one.trans_le hD
  let j := ⌈Real.log (x / t) / Real.log 2⌉₊
  have hnlo : Real.log (x / t) / Real.log 2 ≤ (j : ℝ) := Nat.le_ceil _
  have hnhi : (j : ℝ) ≤ Real.log (x / t) / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hyone) hlog2.le)).le
  have hcover : x / t ≤ (2 : ℝ) ^ j := by
    rw [← Real.exp_log hypos, show (2 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 2) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hlog2).mp hnlo)
  have hxt : x ≤ (2 : ℝ) ^ j * t := (div_le_iff₀ htpos).mp hcover
  have harg : 2 ≤ (2 : ℝ) ^ j * t := (ht.trans htx).trans hxt
  have hpowD : D ^ j ≤ D * (x / t) ^ (Real.log D / Real.log 2) := by
    rw [show D ^ j = Real.exp ((j : ℝ) * Real.log D) by
      rw [Real.exp_nat_mul, Real.exp_log hDpos]]
    rw [Real.rpow_def_of_pos hypos, ← Real.exp_log hDpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Real.log_exp]
    exact (mul_le_mul_of_nonneg_right hnhi hlogD).trans_eq (by ring)
  exact ((hmono (ht.trans htx) harg hxt).trans (doubling_iterate hD hdouble j t ht)).trans
    (mul_le_mul_of_nonneg_right hpowD (zero_le_one.trans (hg t ht)))

private lemma damped_power_bound {s h : ℝ} (hh : 0 < h) :
    ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, 1 ≤ y → y ^ s * Real.exp (-h * y) ≤ B := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s h hh
  obtain ⟨M, hM⟩ := (eventually_atTop.1 ((tendsto_order.1 hlim).2 1 zero_lt_one))
  let T := max 1 M
  have hcont : ContinuousOn (fun y : ℝ => y ^ s * Real.exp (-h * y)) (Icc 1 T) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.rpow_const (fun y hy => Or.inl (by change y ≠ 0; linarith [hy.1]))
    · fun_prop
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun y hy => ?_⟩
  by_cases hyt : y ≤ T
  · exact (hA (mem_image_of_mem _ ⟨hy, hyt⟩)).trans (le_max_left _ _)
  · exact (hM y (le_of_lt ((le_max_right 1 M).trans_lt (lt_of_not_ge hyt)))).le.trans
      (le_max_right _ _)

private lemma log_floor {g : ℝ → ℝ} {a c : ℝ} (hc : 0 < c)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (k : ℕ) :
    Real.log (c * doublingFloor g a k) =
      Real.log c - Real.log ((k : ℝ) + 2) - (1 / a) * Real.log (g ((k : ℝ) + 2)) := by
  have hx : 0 < (k : ℝ) + 2 := by positivity
  have hx2 : 2 ≤ (k : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hgp := zero_lt_one.trans_le (hg _ hx2)
  rw [doublingFloor, Real.log_mul hc.ne' (by positivity),
    Real.log_div (by norm_num) (by positivity),
    Real.log_one, Real.log_mul hx.ne' (Real.rpow_pos_of_pos hgp _).ne', Real.log_rpow hgp]
  ring

private lemma term_factor {g : ℝ → ℝ} {a c N b u : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hN : 0 < N) (hb : 0 < b)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (k : ℕ) :
    (N * b ^ k) ^ (-u) * (c * doublingFloor g a k) ^ (-a + u) =
      Real.exp (-u * (Real.log N + (k : ℝ) * Real.log b)) *
        (c ^ (-a) * (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2))) *
          Real.exp (u * Real.log (c * doublingFloor g a k)) := by
  have hx : 0 < (k : ℝ) + 2 := by positivity
  have hx2 : 2 ≤ (k : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hgp := zero_lt_one.trans_le (hg _ hx2)
  have hη : 0 < c * doublingFloor g a k := by unfold doublingFloor; positivity
  rw [Real.rpow_def_of_pos (mul_pos hN (pow_pos hb k)), Real.rpow_def_of_pos hη,
    Real.log_mul hN.ne' (pow_pos hb k).ne', Real.log_pow,
    Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hx, ← Real.exp_log hgp]
  rw [log_floor hc hg]
  simp only [← Real.exp_add]
  congr 1
  field_simp [ha.ne']
  ring

private lemma raw_term_upper {g : ℝ → ℝ} {a c N b D : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hcone : c ≤ 1) (hN : 1 ≤ N) (hb : 1 < b)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ k : ℕ,
      (N * b ^ k) ^ (-(1 / T)) * (c * doublingFloor g a k) ^ (-a + 1 / T) ≤
        C * (T ^ a * g T) := by
  let d := Real.log D / Real.log 2
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg hD) (Real.log_pos (by norm_num)).le
  have hlogb : 0 < Real.log b := Real.log_pos hb
  obtain ⟨B, hB, hBbound⟩ := damped_power_bound (s := a + d) hlogb
  let C := Real.exp (2 * Real.log b) * c ^ (-a) * max 1 (D * B)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun T hT k => ?_⟩
  have hTp : 0 < T := by linarith
  have hx : 0 < (k : ℝ) + 2 := by positivity
  have hx2 : 2 ≤ (k : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hgT : 0 < g T := zero_lt_one.trans_le (hg T hT)
  have hgx : 0 < g ((k : ℝ) + 2) := zero_lt_one.trans_le (hg _ hx2)
  have hηpos : 0 < c * doublingFloor g a k := by unfold doublingFloor; positivity
  have hηone : c * doublingFloor g a k ≤ 1 := by
    have hgpow := Real.one_le_rpow (hg _ hx2) (one_div_pos.mpr ha).le
    have hden : 1 ≤ ((k : ℝ) + 2) * g ((k : ℝ) + 2) ^ (1 / a) := by nlinarith
    have hfloor : doublingFloor g a k ≤ 1 := (div_le_one (by positivity)).mpr hden
    exact (mul_le_mul_of_nonneg_left hfloor hc.le).trans (by simpa using hcone)
  have hηexp : Real.exp ((1 / T) * Real.log (c * doublingFloor g a k)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos
      (one_div_pos.mpr hTp).le (Real.log_nonpos hηpos.le hηone))
  have hgrid : Real.exp (-(1 / T) * (Real.log N + (k : ℝ) * Real.log b)) ≤
      Real.exp (2 * Real.log b) * Real.exp (-Real.log b * (((k : ℝ) + 2) / T)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
    have hi : 1 / T ≤ 1 := (div_le_one hTp).mpr (by linarith)
    have := mul_nonneg (one_div_pos.mpr hTp).le hlogN
    have := mul_le_mul_of_nonneg_right hi hlogb.le
    field_simp
    nlinarith
  have hscale : Real.exp (-Real.log b * (((k : ℝ) + 2) / T)) *
      (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2)) ≤
        max 1 (D * B) * (T ^ a * g T) := by
    by_cases hxT : (k : ℝ) + 2 ≤ T
    · have hpow := Real.rpow_le_rpow hx.le hxT ha.le
      have hgmono := hmono hx2 hT hxT
      have hexp : Real.exp (-Real.log b * (((k : ℝ) + 2) / T)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr hlogb.le) (div_nonneg hx.le hTp.le))
      calc
        _ ≤ ((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2) :=
          mul_le_of_le_one_left (mul_pos (Real.rpow_pos_of_pos hx _) hgx).le hexp
        _ ≤ T ^ a * g T := mul_le_mul hpow hgmono hgx.le (Real.rpow_nonneg hTp.le _)
        _ ≤ max 1 (D * B) * (T ^ a * g T) :=
          le_mul_of_one_le_left (mul_pos (Real.rpow_pos_of_pos hTp a) hgT).le (le_max_left _ _)
    · have hTx := (not_le.mp hxT).le
      have hyone : 1 ≤ ((k : ℝ) + 2) / T := (le_div_iff₀ hTp).2 (by simpa using hTx)
      have hgrowth := cross_scale hg hmono hD hdouble hT hTx
      have hpowe : ((k : ℝ) + 2) ^ a =
          (((k : ℝ) + 2) / T) ^ a * T ^ a := by
        rw [← Real.mul_rpow (div_nonneg hx.le hTp.le) hTp.le, div_mul_cancel₀ _ hTp.ne']
      have hbnd := hBbound (((k : ℝ) + 2) / T) hyone
      have hmix : (((k : ℝ) + 2) / T) ^ a * (((k : ℝ) + 2) / T) ^ d =
          (((k : ℝ) + 2) / T) ^ (a + d) := (Real.rpow_add (div_pos hx hTp) _ _).symm
      calc
        _ ≤ Real.exp (-Real.log b * (((k : ℝ) + 2) / T)) *
            (((k : ℝ) + 2) ^ a * (D * (((k : ℝ) + 2) / T) ^ d * g T)) := by
          gcongr
        _ = (D * (T ^ a * g T)) *
            ((((k : ℝ) + 2) / T) ^ (a + d) *
              Real.exp (-Real.log b * (((k : ℝ) + 2) / T))) := by rw [hpowe, ← hmix]; ring
        _ ≤ (D * (T ^ a * g T)) * B := by gcongr
        _ ≤ max 1 (D * B) * (T ^ a * g T) := by
          have := mul_le_mul_of_nonneg_right (le_max_right 1 (D * B))
            (mul_pos (Real.rpow_pos_of_pos hTp a) hgT).le
          simpa only [mul_assoc, mul_comm, mul_left_comm] using this
  rw [term_factor ha hc (zero_lt_one.trans_le hN) (zero_lt_one.trans hb) hg]
  have hmain : 0 ≤ c ^ (-a) * (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2)) := by positivity
  calc
    _ ≤ Real.exp (-(1 / T) * (Real.log N + (k : ℝ) * Real.log b)) *
        (c ^ (-a) * (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2))) :=
      mul_le_of_le_one_right (mul_nonneg (Real.exp_pos _).le hmain) hηexp
    _ ≤ (Real.exp (2 * Real.log b) * c ^ (-a)) *
        (Real.exp (-Real.log b * (((k : ℝ) + 2) / T)) *
          (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2))) := by
      have := mul_le_mul_of_nonneg_right hgrid hmain
      nlinarith
    _ ≤ (Real.exp (2 * Real.log b) * c ^ (-a)) *
        (max 1 (D * B) * (T ^ a * g T)) := by gcongr
    _ = C * (T ^ a * g T) := by dsimp [C]; ring

private lemma raw_term_lower {g : ℝ → ℝ} {a c N b D : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hcone : c ≤ 1) (hN : 1 ≤ N) (hb : 1 < b)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      C * (T ^ a * g T) ≤
        (N * b ^ ⌊T⌋₊) ^ (-(1 / T)) *
          (c * doublingFloor g a ⌊T⌋₊) ^ (-a + 1 / T) := by
  obtain ⟨Cg, hCg, hpoly⟩ := doubling_polynomial hg hmono hD hdouble
  let d := Real.log D / Real.log 2
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg hD) (Real.log_pos (by norm_num)).le
  let A := Real.log c - (1 / a) * Real.log Cg - 2 * (1 + d / a)
  let C := Real.exp (-(Real.log N + Real.log b)) * c ^ (-a) * Real.exp A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun T hT => ?_⟩
  have hTp : 0 < T := by linarith
  let k := ⌊T⌋₊
  have hklo : (k : ℝ) ≤ T := Nat.floor_le hTp.le
  have hkhi : T < (k : ℝ) + 1 := Nat.lt_floor_add_one T
  have hx : 0 < (k : ℝ) + 2 := by positivity
  have hTx : T ≤ (k : ℝ) + 2 := by linarith
  have hxT : (k : ℝ) + 2 ≤ 2 * T := by linarith
  have hx2 : 2 ≤ (k : ℝ) + 2 := hT.trans hTx
  have hgx : 0 < g ((k : ℝ) + 2) := zero_lt_one.trans_le (hg _ hx2)
  have hgT : 0 < g T := zero_lt_one.trans_le (hg _ hT)
  have hCgpos := zero_lt_one.trans_le hCg
  have hloggx : Real.log (g ((k : ℝ) + 2)) ≤
      Real.log Cg + d * Real.log ((k : ℝ) + 2) := by
    have := Real.log_le_log hgx (hpoly _ hx2)
    rwa [Real.log_mul hCgpos.ne' (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx] at this
  have hlogx : Real.log ((k : ℝ) + 2) ≤ (k : ℝ) + 2 :=
    (Real.log_le_sub_one_of_pos hx).trans (by linarith)
  have hi : 0 < 1 / T := one_div_pos.mpr hTp
  have hione : 1 / T ≤ 1 := (div_le_one hTp).mpr (by linarith)
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hcone
  have hlCg : 0 ≤ Real.log Cg := Real.log_nonneg hCg
  have hscale : (1 / T) * ((k : ℝ) + 2) ≤ 2 := by
    have := (div_le_iff₀ hTp).2 hxT
    simpa [div_eq_mul_inv, mul_comm] using this
  have hexplog : A ≤ (1 / T) * Real.log (c * doublingFloor g a k) := by
    rw [log_floor hc hg]
    have hp : 0 < 1 / a := one_div_pos.mpr ha
    have h₁ := mul_le_mul_of_nonneg_left hloggx (mul_nonneg hi.le hp.le)
    have h₂ := mul_le_mul_of_nonneg_left hlogx (mul_nonneg hi.le (show 0 ≤ 1 + d / a by positivity))
    have h₃ := mul_le_mul_of_nonneg_right hione (mul_nonneg hp.le hlCg)
    have h₄ := mul_le_mul_of_nonpos_right hione hlc
    have h₅ := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 1 + d / a by positivity)
    dsimp [A]
    ring_nf at h₁ h₂ h₃ h₄ h₅ ⊢
    linarith only [h₁, h₂, h₃, h₄, h₅]
  have hgridlog : -(Real.log N + Real.log b) ≤
      -(1 / T) * (Real.log N + (k : ℝ) * Real.log b) := by
    have hlogN := Real.log_nonneg hN
    have hlogb := (Real.log_pos hb).le
    have h₁ := mul_le_mul_of_nonneg_right hione hlogN
    have hkT : (1 / T) * (k : ℝ) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hTp]; exact hklo
    have h₂ := mul_le_mul_of_nonneg_right hkT hlogb
    nlinarith
  have hFx : T ^ a * g T ≤ ((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2) :=
    mul_le_mul (Real.rpow_le_rpow hTp.le hTx ha.le) (hmono hT hx2 hTx)
      hgT.le (Real.rpow_nonneg hx.le _)
  rw [term_factor ha hc (zero_lt_one.trans_le hN) (zero_lt_one.trans hb) hg]
  dsimp [C]
  have hgrid := Real.exp_le_exp.mpr hgridlog
  have hηexp := Real.exp_le_exp.mpr hexplog
  calc
    _ ≤ Real.exp (-(1 / T) * (Real.log N + (k : ℝ) * Real.log b)) *
        (c ^ (-a) * (((k : ℝ) + 2) ^ a * g ((k : ℝ) + 2))) * Real.exp A := by
      have := mul_le_mul hgrid (mul_le_mul_of_nonneg_left hFx
        (Real.rpow_pos_of_pos hc (-a)).le) (by positivity) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_right this (Real.exp_pos A).le
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    _ ≤ _ := mul_le_mul_of_nonneg_left hηexp (by positivity)

/-- The complete numerical supremum for a fixed scaled doubling floor has
matching bounds, independent of the small positive exponent correction.
No summability assumption on the floor is needed. -/
theorem raw_profile_two_sided {g : ℝ → ℝ} {a c N b D : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hcone : c ≤ 1) (hN : 1 ≤ N) (hb : 1 < b)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤
        profile (fun k => c * doublingFloor g a k) N b a u ∧
      profile (fun k => c * doublingFloor g a k) N b a u ≤
        ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u))) := by
  obtain ⟨C₁, hC₁, hupper⟩ := raw_term_upper ha hc hcone hN hb hg hmono hD hdouble
  obtain ⟨c₁, hc₁, hlower⟩ := raw_term_lower ha hc hcone hN hb hg hmono hD hdouble
  refine ⟨c₁, C₁, hc₁, hC₁, fun u hu hule => ?_⟩
  have hT : 2 ≤ 1 / u := (le_div_iff₀ hu).2 (by linarith)
  have hinv : 1 / (1 / u) = u := by field_simp
  have hpow : (1 / u) ^ a = u ^ (-a) := by rw [one_div, Real.inv_rpow hu.le, Real.rpow_neg hu.le]
  constructor
  · have hl := hlower (1 / u) hT
    rw [hinv, hpow] at hl
    exact (ENNReal.ofReal_le_ofReal hl).trans
      (le_iSup (fun k => ENNReal.ofReal ((N * b ^ k) ^ (-u) *
        (c * doublingFloor g a k) ^ (-a + u))) ⌊1 / u⌋₊)
  · apply iSup_le
    intro k
    have hh := hupper (1 / u) hT k
    rw [hinv, hpow] at hh
    exact ENNReal.ofReal_le_ofReal hh

/-- A pointwise comparison of floors transfers the entire profile with constants
uniform over a positive exponent interval. -/
private lemma profile_comparison {η ω : ℕ → ℝ} {B N b a u : ℝ}
    (hω : ∀ k, 0 < ω k) (hη : ∀ k, 0 < η k) (hB : 1 ≤ B)
    (hlo : ∀ k, ω k ≤ η k) (hhi : ∀ k, η k ≤ B * ω k)
    (hN : 0 < N) (hb : 0 < b) (hu : 0 ≤ u) (hua : u ≤ a) :
    ENNReal.ofReal (B ^ (-a)) * profile ω N b a u ≤ profile η N b a u ∧
      profile η N b a u ≤ profile ω N b a u := by
  have hBp := zero_lt_one.trans_le hB
  constructor
  · rw [profile, ENNReal.mul_iSup]
    apply iSup_le
    intro k
    have hpow : B ^ (-a) * ω k ^ (-a + u) ≤ η k ^ (-a + u) := by
      calc
        _ ≤ B ^ (-a + u) * ω k ^ (-a + u) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
            (Real.rpow_nonneg (hω k).le _)
        _ = (B * ω k) ^ (-a + u) := (Real.mul_rpow hBp.le (hω k).le).symm
        _ ≤ η k ^ (-a + u) := Real.rpow_le_rpow_of_nonpos (hη k) (hhi k) (by linarith)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBp.le _)]
    have hweight : 0 ≤ (N * b ^ k) ^ (-u) := by positivity
    have := mul_le_mul_of_nonneg_left hpow hweight
    have ht : B ^ (-a) * ((N * b ^ k) ^ (-u) * ω k ^ (-a + u)) ≤
        (N * b ^ k) ^ (-u) * η k ^ (-a + u) := by nlinarith
    exact (ENNReal.ofReal_le_ofReal ht).trans (le_iSup
      (fun j => ENNReal.ofReal ((N * b ^ j) ^ (-u) * η j ^ (-a + u))) k)
  · apply iSup_le
    intro k
    have hpow := Real.rpow_le_rpow_of_nonpos (hω k) (hlo k) (show -a + u ≤ 0 by linarith)
    have ht := mul_le_mul_of_nonneg_left hpow
      (Real.rpow_nonneg (mul_pos hN (pow_pos hb k)).le (-u))
    exact (ENNReal.ofReal_le_ofReal ht).trans (le_iSup
      (fun j => ENNReal.ofReal ((N * b ^ j) ^ (-u) * ω j ^ (-a + u))) k)

/-- For every prescribed adjacent ratio and total mass, one fixed floor
matches the doubling target throughout a whole interval of small positive `u`.
The profile is numerical and carries no claim about a sampling execution. -/
theorem prescribed_ratio_matching_profile {g : ℝ → ℝ} {a D N b R K : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hR : 1 < R) (hK : 0 < K)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hs : Summable (doublingFloor g a)) :
    ∃ η : ℕ → ℝ, (∀ k, 0 < η k ∧ η k ≤ 1) ∧ Antitone η ∧ Summable η ∧
      (∑' k, η k) ≤ K ∧ (∀ k, η k ≤ R * η (k + 1)) ∧
      ∃ c₁ C₁ ε : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
        ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤ profile η N b a u ∧
        profile η N b a u ≤ ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u))) := by
  obtain ⟨q, _, _, _, hq⟩ := prescribed_ratio_floor hR
  obtain ⟨c, hc, hcone, hpos, hanti, hsum, hmass, hratio, B, hB, hbounds⟩ :=
    hq g a D K ha hK hg hmono hD hdouble hs
  let η := fun k => (c : ℝ) * smooth (q : ℝ) (doublingFloor g a) k
  obtain ⟨c₁, C₁, hc₁, hC₁, hraw⟩ := raw_profile_two_sided ha hc hcone hN hb hg hmono hD hdouble
  refine ⟨η, hpos, hanti, hsum, hmass, hratio,
    B ^ (-a) * c₁, C₁, min (1 / 2) a, ?_, hC₁, by positivity, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB) _) hc₁
  · intro u hu hue
    have huhalf := hue.trans (min_le_left _ _)
    have hua := hue.trans (min_le_right _ _)
    have hω (k : ℕ) : 0 < (c : ℝ) * doublingFloor g a k := by
      have hx2 : 2 ≤ (k : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
      have := zero_lt_one.trans_le (hg _ hx2)
      unfold doublingFloor
      positivity
    have hcompare := profile_comparison hω (fun k => (hpos k).1) hB
      (fun k => (hbounds k).1) (fun k => (hbounds k).2)
      (zero_lt_one.trans_le hN) (zero_lt_one.trans hb) hu.le hua
    obtain ⟨hl, hh⟩ := hraw u hu huhalf
    refine ⟨?_, hcompare.2.trans hh⟩
    have := mul_le_mul_of_nonneg_left hl (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (B ^ (-a)) from zero_le)
    have hp : 0 ≤ B ^ (-a) := Real.rpow_nonneg (zero_le_one.trans hB) _
    calc
      _ = ENNReal.ofReal (B ^ (-a)) * ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) := by
        rw [← ENNReal.ofReal_mul hp]; congr 1; ring
      _ ≤ ENNReal.ofReal (B ^ (-a)) *
          profile (fun k => (c : ℝ) * doublingFloor g a k) N b a u := this
      _ ≤ profile η N b a u := hcompare.1

private lemma necessary_floor_domination {g : ℝ → ℝ} {η : ℕ → ℝ} {a D N b C ε : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hC : 0 < C) (hε : 0 < ε)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hη : ∀ k, 0 < η k)
    (hbound : ∀ u : ℝ, 0 < u → u ≤ ε →
      profile η N b a u ≤ ENNReal.ofReal (C * (u ^ (-a) * g (1 / u)))) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ k : ℕ, L ≤ k → c * doublingFloor g a k ≤ η k := by
  obtain ⟨Cg, hCg, hpoly⟩ := doubling_polynomial hg hmono hD hdouble
  let d := Real.log D / Real.log 2
  have hd : 0 ≤ d := div_nonneg (Real.log_nonneg hD) (Real.log_pos (by norm_num)).le
  let H := max 1 (C * Real.exp (Real.log N + Real.log b))
  have hH : 1 ≤ H := le_max_left _ _
  have hHp : 0 < H := zero_lt_one.trans_le hH
  let A := Real.log H + Real.log Cg + a + d
  have hA : 0 < A := by
    have := Real.log_nonneg hH
    have := Real.log_nonneg hCg
    dsimp [A]; linarith
  let Q := 2 * A / a
  let c := Real.exp (-(Real.log H + Q) / a)
  have hc : 0 < c := Real.exp_pos _
  let L := ⌈max 2 (max (2 / a) (1 / ε))⌉₊
  refine ⟨c, hc, L, fun k hk => ?_⟩
  let t : ℝ := (k : ℝ) + 2
  have hLt : max 2 (max (2 / a) (1 / ε)) ≤ t := by
    have hlo := Nat.le_ceil (max 2 (max (2 / a) (1 / ε)))
    have hkl : (L : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp [t]
    linarith
  have ht : 2 ≤ t := (le_max_left _ _).trans hLt
  have hta : 2 / a ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans hLt)
  have htε : 1 / ε ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans hLt)
  have htp : 0 < t := by linarith
  have hu : 0 < 1 / t := one_div_pos.mpr htp
  have huε : 1 / t ≤ ε := by
    have := (div_le_iff₀ hε).mp htε
    apply (div_le_iff₀ htp).2
    nlinarith
  have hsu : a / 2 ≤ a - 1 / t := by
    have := (div_le_iff₀ ha).mp hta
    have hi : 1 / t ≤ a / 2 := by rw [div_le_iff₀ htp]; nlinarith
    linarith
  have hgt : 0 < g t := zero_lt_one.trans_le (hg _ ht)
  have hpow : (1 / t) ^ (-a) = t ^ a := by
    rw [one_div, Real.inv_rpow htp.le, Real.rpow_neg htp.le, inv_inv]
  have hinv : 1 / (1 / t) = t := by field_simp
  have hterm : (N * b ^ k) ^ (-(1 / t)) * η k ^ (-a + 1 / t) ≤ C * (t ^ a * g t) := by
    have htarg : 0 ≤ C * ((1 / t) ^ (-a) * g (1 / (1 / t))) := by rw [hinv]; positivity
    have := (le_iSup (fun j => ENNReal.ofReal
      ((N * b ^ j) ^ (-(1 / t)) * η j ^ (-a + 1 / t))) k).trans (hbound _ hu huε)
    have := (ENNReal.ofReal_le_ofReal_iff htarg).mp this
    rwa [hpow, hinv] at this
  have hgridlog : -(Real.log N + Real.log b) ≤
      -(1 / t) * (Real.log N + (k : ℝ) * Real.log b) := by
    have hlogN := Real.log_nonneg hN
    have hlogb := (Real.log_pos hb).le
    have hi : 1 / t ≤ 1 := (div_le_one htp).mpr (by linarith)
    have hkT : (1 / t) * (k : ℝ) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one htp]; dsimp [t]; linarith
    have h₁ := mul_le_mul_of_nonneg_right hi hlogN
    have h₂ := mul_le_mul_of_nonneg_right hkT hlogb
    nlinarith
  have hgrid : Real.exp (-(Real.log N + Real.log b)) ≤ (N * b ^ k) ^ (-(1 / t)) := by
    rw [Real.rpow_def_of_pos (mul_pos (zero_lt_one.trans_le hN) (pow_pos (zero_lt_one.trans hb) k)),
      Real.log_mul (zero_lt_one.trans_le hN).ne'
        (pow_pos (zero_lt_one.trans hb) k).ne', Real.log_pow]
    simpa only [mul_comm] using Real.exp_le_exp.mpr hgridlog
  have hηpow : η k ^ (-a + 1 / t) ≤ H * (t ^ a * g t) := by
    have h₁ := (mul_le_mul_of_nonneg_right hgrid (Real.rpow_pos_of_pos (hη k) _).le).trans hterm
    have h₂ := mul_le_mul_of_nonneg_left h₁ (Real.exp_pos (Real.log N + Real.log b)).le
    have he : Real.exp (Real.log N + Real.log b) * Real.exp (-(Real.log N + Real.log b)) = 1 := by
      rw [← Real.exp_add]; simp
    have h₃ : η k ^ (-a + 1 / t) ≤
        (C * Real.exp (Real.log N + Real.log b)) * (t ^ a * g t) := by
      rw [← mul_assoc, he, one_mul] at h₂
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h₂
    exact h₃.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (mul_pos (Real.rpow_pos_of_pos htp a) hgt).le)
  let F := Real.log H + a * Real.log t + Real.log (g t)
  have hlogbound : (a - 1 / t) * (-Real.log (η k)) ≤ F := by
    have := Real.log_le_log (Real.rpow_pos_of_pos (hη k) _) hηpow
    rw [Real.log_rpow (hη k), Real.log_mul hHp.ne' (by positivity),
      Real.log_mul (Real.rpow_pos_of_pos htp a).ne' hgt.ne', Real.log_rpow htp] at this
    dsimp [F]
    nlinarith only [this]
  have hF : F ≤ A * t := by
    have hloggt : Real.log (g t) ≤ Real.log Cg + d * Real.log t := by
      have := Real.log_le_log hgt (hpoly t ht)
      rwa [Real.log_mul (zero_lt_one.trans_le hCg).ne' (Real.rpow_pos_of_pos htp _).ne',
        Real.log_rpow htp] at this
    have hlogt : Real.log t ≤ t := (Real.log_le_sub_one_of_pos htp).trans (by linarith)
    have hlogH := Real.log_nonneg hH
    have hlogCg := Real.log_nonneg hCg
    have h₁ := mul_le_mul_of_nonneg_right (show 1 ≤ t by linarith) (add_nonneg hlogH hlogCg)
    have h₂ := mul_le_mul_of_nonneg_left hlogt (show 0 ≤ a + d by linarith)
    dsimp [F, A]
    nlinarith only [hloggt, h₁, h₂]
  have hcorrect : -Real.log (η k) / t ≤ Q := by
    by_cases hlog : 0 ≤ -Real.log (η k)
    · have h₁ := mul_le_mul_of_nonneg_right hsu hlog
      have h₂ : a / 2 * (-Real.log (η k)) ≤ A * t := h₁.trans (hlogbound.trans hF)
      rw [div_le_iff₀ htp]
      dsimp [Q]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ha).2
      nlinarith only [h₂]
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hlog) htp.le).trans
        (by dsimp [Q]; positivity)
  have hlogη : -(Real.log H + Q) / a - Real.log t - (1 / a) * Real.log (g t) ≤ Real.log (η k) := by
    have hL : a * (-Real.log (η k)) ≤ F + Q := by
      have he : (a - 1 / t) * (-Real.log (η k)) =
          a * (-Real.log (η k)) - (-Real.log (η k)) / t := by ring
      rw [he] at hlogbound
      linarith only [hlogbound, hcorrect]
    have hLb : -Real.log (η k) ≤ (F + Q) / a :=
      (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hL)
    have : (F + Q) / a = (Real.log H + Q) / a + Real.log t + (1 / a) * Real.log (g t) := by
      dsimp [F]; field_simp [ha.ne']; ring
    calc
      _ = -((F + Q) / a) := by rw [this]; ring
      _ ≤ Real.log (η k) := by linarith only [hLb]
  have hx2 : 2 ≤ (k : ℝ) + 2 := ht
  have hfloorpos : 0 < c * doublingFloor g a k := by unfold doublingFloor; positivity
  apply (Real.log_le_log_iff hfloorpos (hη k)).mp
  rw [log_floor hc hg]
  dsimp [c]
  rw [Real.log_exp]
  exact hlogη

/-- A summable positive floor meeting a doubling growth bound forces the
integral-test sequence to be summable. No doubling condition on that floor
is assumed, and its moving exponent is retained in the estimate. -/
theorem summable_floor_of_profile_bound {g : ℝ → ℝ} {η : ℕ → ℝ} {a D N b C ε : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hC : 0 < C) (hε : 0 < ε)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t)
    (hη : ∀ k, 0 < η k) (hsη : Summable η)
    (hbound : ∀ u : ℝ, 0 < u → u ≤ ε →
      profile η N b a u ≤ ENNReal.ofReal (C * (u ^ (-a) * g (1 / u)))) :
    Summable (doublingFloor g a) := by
  obtain ⟨c, hc, L, hL⟩ := necessary_floor_domination ha hN hb hC hε hg hmono hD hdouble hη hbound
  have htail : Summable (fun k => c * doublingFloor g a (k + L)) := by
    apply Summable.of_nonneg_of_le _ (fun k => hL (k + L) (by omega))
      ((summable_nat_add_iff L).2 hsη)
    intro k
    have hx2 : 2 ≤ ((k + L : ℕ) : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) (k + L); linarith
    have := zero_lt_one.trans_le (hg _ hx2)
    unfold doublingFloor
    positivity
  exact (summable_nat_add_iff L).1 ((summable_mul_left_iff hc.ne').1 htail)

/-- The fixed-class floor constraints, with a prescribed adjacent ratio and mass. -/
def AdmissibleFloor (R K : ℝ) (η : ℕ → ℝ) : Prop :=
  (∀ k, 0 < η k ∧ η k ≤ 1) ∧ Antitone η ∧ Summable η ∧
    (∑' k, η k) ≤ K ∧ ∀ k, η k ≤ R * η (k + 1)

/-- The tail series starts at index two; the first two terms are zero. -/
def integralTestTerm (g : ℝ → ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  if 2 ≤ k then 1 / ((k : ℝ) * g (k : ℝ) ^ (1 / a)) else 0

private lemma integral_test_shift (g : ℝ → ℝ) (a : ℝ) :
    Summable (integralTestTerm g a) ↔ Summable (doublingFloor g a) := by
  rw [← summable_nat_add_iff 2]
  have he : (fun k => integralTestTerm g a (k + 2)) = doublingFloor g a := by
    funext k
    simp [integralTestTerm, doublingFloor, Nat.cast_add]
  rw [he]

/-- The numerical integral criterion for one fixed admissible floor.
It quantifies all sufficiently small positive exponent corrections and
keeps the prescribed ratio and mass unchanged. -/
theorem fixed_floor_growth_criterion {g : ℝ → ℝ} {a D N b R K : ℝ}
    (ha : 0 < a) (hN : 1 ≤ N) (hb : 1 < b) (hR : 1 < R) (hK : 0 < K)
    (hg : ∀ t : ℝ, 2 ≤ t → 1 ≤ g t) (hmono : MonotoneOn g (Ici 2))
    (hD : 1 ≤ D) (hdouble : ∀ t : ℝ, 2 ≤ t → g (2 * t) ≤ D * g t) :
    (Summable (integralTestTerm g a) ↔
      ∃ η : ℕ → ℝ, AdmissibleFloor R K η ∧
        ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
          profile η N b a u ≤ ENNReal.ofReal (C * (u ^ (-a) * g (1 / u)))) ∧
      (Summable (integralTestTerm g a) →
        ∃ η : ℕ → ℝ, AdmissibleFloor R K η ∧
          ∃ c₁ C₁ ε : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
            ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤ profile η N b a u ∧
              profile η N b a u ≤ ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u)))) := by
  have hmatch (hs : Summable (integralTestTerm g a)) :
      ∃ η : ℕ → ℝ, AdmissibleFloor R K η ∧
        ∃ c₁ C₁ ε : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε ∧ ∀ u : ℝ, 0 < u → u ≤ ε →
          ENNReal.ofReal (c₁ * (u ^ (-a) * g (1 / u))) ≤ profile η N b a u ∧
            profile η N b a u ≤ ENNReal.ofReal (C₁ * (u ^ (-a) * g (1 / u))) := by
    obtain ⟨η, hp, hanti, hsum, hmass, hratio, hbounds⟩ :=
      prescribed_ratio_matching_profile ha hN hb hR hK hg hmono hD hdouble
        ((integral_test_shift g a).1 hs)
    exact ⟨η, ⟨hp, hanti, hsum, hmass, hratio⟩, hbounds⟩
  refine ⟨⟨?_, ?_⟩, hmatch⟩
  · intro hs
    obtain ⟨η, hadm, c₁, C₁, ε, _, hC₁, hε, hbounds⟩ := hmatch hs
    exact ⟨η, hadm, C₁, ε, hC₁, hε, fun u hu hue => (hbounds u hu hue).2⟩
  · rintro ⟨η, hadm, C, ε, hC, hε, hbounds⟩
    exact (integral_test_shift g a).2 (summable_floor_of_profile_bound ha hN hb hC hε
      hg hmono hD hdouble (fun k => (hadm.1 k).1) hadm.2.2.1 hbounds)

end D5.S3.Analytic.SeriesInequalities.DoublingFloorEnvelope

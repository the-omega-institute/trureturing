/- GID: D5/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumCriticalMissingWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A shifted critical cutoff gives strict missing windows with a small square tail. -/

import D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
import D5.S3.Fourier.Concentration.FiniteSineMissingWindow

/-! The critical-scale missing-window bound for weighted sine polynomials. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators NNReal

attribute [local instance] Classical.propDecidable

namespace D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow

open OrdinateCounting (Spectrum)
open SpectrumPhaseCutoff (mass sine)
open D5.S3.Fourier.Concentration.FiniteSineMissingWindow
  (exists_arbitrarily_late_missing_window sineScore)

private theorem mem_cut {S : Spectrum} {X : ℝ} {j : S.index} :
    j ∈ S.cut X ↔ S.gamma j ≤ X :=
  (S.finite_le X).mem_toFinset

/-- The mass has a positive squared-logarithmic coefficient, with error at most linear
in the logarithm. -/
def HasLogSquaredMass (S : Spectrum) (w : S.index → ℝ) : Prop :=
  ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ᶠ Y : ℝ in atTop,
    |mass S w Y - a * Real.log Y ^ 2| ≤ C * (1 + Real.log Y)

/-- A uniform little-o square-weight bound over every finite upper cutoff. -/
def HasSmallSquareTail (S : Spectrum) (w : S.index → ℝ) : Prop := by
  classical
  exact ∀ η : ℝ, 0 < η → ∀ᶠ X : ℝ in atTop, ∀ T : ℝ, X ≤ T →
    ∑ j ∈ S.cut T \ S.cut X, w j ^ 2 ≤ η * Real.log X ^ 2 / X

/-- A uniform square-weight bound of order `log X / X` over every finite upper cutoff. -/
def HasLogarithmicSquareTail (S : Spectrum) (w : S.index → ℝ) : Prop := by
  classical
  exact ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ T : ℝ, X ≤ T →
    ∑ j ∈ S.cut T \ S.cut X, w j ^ 2 ≤ C * Real.log X / X

private theorem log_shifted_cutoff {T : ℝ} (hT : 0 < T) (K β : ℝ) :
    Real.log (Real.exp (-K) * T ^ β) = β * Real.log T - K := by
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hT _).ne',
    Real.log_exp, Real.log_rpow hT]
  ring

private theorem shifted_cutoff_le {K T β : ℝ} (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hβ : β ≤ 1) : Real.exp (-K) * T ^ β ≤ T := calc
  _ ≤ T ^ β := mul_le_of_le_one_left (by positivity)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK))
  _ ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hβ

private theorem eventual_mass_margin {S : Spectrum} {w : S.index → ℝ}
    {a C β : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hβ : 0 < β)
    (hmass : ∀ᶠ Y : ℝ in atTop,
      |mass S w Y - a * Real.log Y ^ 2| ≤ C * (1 + Real.log Y)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop,
      mass S w (Real.exp (-K) * T ^ β) + 3 * Real.log T < β ^ 2 * mass S w T := by
  let K := (C * (β + β ^ 2) + 4) / (2 * a * β)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKexact : 2 * a * β * K = C * (β + β ^ 2) + 4 := by
    dsimp [K]
    field_simp
  refine ⟨K, hK, ?_⟩
  have hX := (tendsto_rpow_atTop hβ).const_mul_atTop (Real.exp_pos (-K))
  filter_upwards [hmass, hX.eventually hmass, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (a * K ^ 2 + C * (1 + β ^ 2))]
    with T hTmass hXmass hT hlog
  have hlogX := log_shifted_cutoff hT K β
  have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hTmass).1 (sq_nonneg β)
  have hupp := (abs_le.mp hXmass).2
  rw [hlogX] at hupp
  nlinarith only [hlow, hupp, hlog, mul_nonneg hC hK.le,
    congrArg (fun x : ℝ => x * Real.log T) hKexact]

private theorem eventual_mesh_cost {S : Spectrum} {w : S.index → ℝ}
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hmass : ∀ᶠ Y : ℝ in atTop,
      |mass S w Y - a * Real.log Y ^ 2| ≤ C * (1 + Real.log Y)) :
    ∀ᶠ T : ℝ in atTop, mass S w T / T < Real.log T := by
  let D := a + 2 * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall := (isLittleO_log_rpow_atTop (r := 1) one_pos).bound
    (show 0 < 1 / D by positivity)
  filter_upwards [hmass, hsmall, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with T hm hs hT hL
  have hLpos : 0 < Real.log T := zero_lt_one.trans_le hL
  have hL2 : 1 + Real.log T ≤ 2 * Real.log T ^ 2 := by
    nlinarith only [hL, mul_nonneg (sub_nonneg.mpr hL) hLpos.le]
  have hW : mass S w T < D * Real.log T ^ 2 := by
    nlinarith only [(abs_le.mp hm).2, mul_le_mul_of_nonneg_left hL2 hC,
      sq_pos_of_pos hLpos, show D = a + 2 * C + 1 from rfl]
  have hs' : Real.log T ≤ 1 / D * T := by
    simpa only [Real.norm_eq_abs, Real.rpow_one, abs_of_pos hT, abs_of_pos hLpos] using hs
  have hDT : D * Real.log T ≤ T := by
    exact (le_inv_mul_iff₀ hD).mp (by simpa only [one_div] using hs')
  apply (div_lt_iff₀ hT).mpr
  exact hW.trans_le (by simpa only [pow_two, mul_comm (Real.log T) T, mul_assoc]
    using mul_le_mul_of_nonneg_right hDT hLpos.le)

private theorem grid_count_le {H T r : ℝ} (hH : 1 ≤ H) (hr : 0 < r) :
    (⌊(H / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 ≤ H * (T ^ 2 / r + 1) := by
  have hfloor : (⌊(H / r) / (1 / T ^ 2)⌋₊ : ℝ) ≤ (H / r) / (1 / T ^ 2) :=
    Nat.floor_le (div_nonneg (div_nonneg (zero_le_one.trans hH) hr.le) (by positivity))
  calc
    _ ≤ (H / r) / (1 / T ^ 2) + 1 := add_le_add_left hfloor 1
    _ = H * (T ^ 2 / r) + 1 := by rw [div_div_eq_mul_div, div_one]; ring
    _ ≤ _ := by rw [mul_add, mul_one]; exact add_le_add_right hH _

private theorem eventual_grid_bound {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) :
    ∀ᶠ T : ℝ in atTop,
      (⌊(Real.exp (T ^ β) / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 ≤ Real.exp (2 * T ^ β) := by
  have hpow := tendsto_rpow_atTop hβ
  have hratio := ((tendsto_exp_div_rpow_atTop (2 / β)).comp hpow).eventually_ge_atTop
    (2 / r)
  filter_upwards [hratio, (Real.tendsto_exp_atTop.comp hpow).eventually_ge_atTop 2,
    eventually_gt_atTop (0 : ℝ)] with T hratioT hexpT hT
  change 2 ≤ Real.exp (T ^ β) at hexpT
  have heq : (T ^ β) ^ (2 / β) = T ^ 2 := by
    rw [← Real.rpow_mul hT.le, show β * (2 / β) = (2 : ℝ) by field_simp]
    norm_cast
  change 2 / r ≤ Real.exp (T ^ β) / (T ^ β) ^ (2 / β) at hratioT
  rw [heq] at hratioT
  have hratio' := (le_div_iff₀ (sq_pos_of_pos hT)).mp hratioT
  have hgrid : T ^ 2 / r + 1 ≤ Real.exp (T ^ β) := by
    rw [show 2 / r * T ^ 2 = 2 * (T ^ 2 / r) by ring] at hratio'
    linarith only [hratio', hexpT]
  calc
    _ ≤ Real.exp (T ^ β) * (T ^ 2 / r + 1) := grid_count_le (by linarith) hr
    _ ≤ Real.exp (T ^ β) * Real.exp (T ^ β) :=
      mul_le_mul_of_nonneg_left hgrid (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, two_mul]

private theorem cutoff_sums {S : Spectrum} {X T : ℝ} (hXT : X ≤ T) (f : S.index → ℝ) :
    let head := (Finset.univ : Finset (S.cut T)).filter (fun j => S.gamma j.val ≤ X)
    (∑ j ∈ head, f j.val) = ∑ j ∈ S.cut X, f j := by
  classical
  dsimp only
  symm
  refine Finset.sum_bij (fun j hj => ⟨j, mem_cut.mpr ((mem_cut.mp hj).trans hXT)⟩) ?_ ?_ ?_ ?_
  · intro j hj
    simp [mem_cut.mp hj]
  · intro i _ j _ h
    exact congrArg Subtype.val h
  · intro j hj
    exact ⟨j.val, mem_cut.mpr (Finset.mem_filter.mp hj).2, Subtype.eta _ _⟩
  · intros
    rfl

private theorem tail_sums {S : Spectrum} {X T : ℝ} (f : S.index → ℝ) :
    let head := (Finset.univ : Finset (S.cut T)).filter (fun j => S.gamma j.val ≤ X)
    (∑ j ∈ headᶜ, f j.val) = ∑ j ∈ S.cut T \ S.cut X, f j := by
  classical
  dsimp only
  symm
  refine Finset.sum_bij
    (fun j hj => ⟨j, (Finset.mem_sdiff.mp hj).1⟩) ?_ ?_ ?_ ?_
  · intro j hj
    simpa using (fun hx => (Finset.mem_sdiff.mp hj).2 (mem_cut.mpr hx))
  · intro i _ j _ h
    exact congrArg Subtype.val h
  · intro j hj
    have hx : ¬ S.gamma j.val ≤ X := by simpa using hj
    exact ⟨j.val, Finset.mem_sdiff.mpr ⟨j.property, fun hm => hx (mem_cut.mp hm)⟩,
      Subtype.eta _ _⟩
  · intros
    rfl

private theorem missing_window_of_cutoff {S : Spectrum} {w : S.index → ℝ}
    {X T r β H : ℝ} (hw : ∀ j, 0 ≤ w j) (hli : LinearIndependent ℚ S.gamma)
    (hT : 1 < T) (hr : 0 < r) (hXT : X ≤ T)
    (hmarginT : mass S w X + 3 * Real.log T < β ^ 2 * mass S w T)
    (hmeshT : mass S w T / T < Real.log T) :
    let V := ∑ j ∈ S.cut T \ S.cut X, w j ^ 2
    (V = 0 ∨ ((⌊(H / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1) *
        Real.exp (-Real.log T ^ 2 / (2 * V)) < 1) →
    0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + H),
        sine S w T (u / r) < β ^ 2 * mass S w T - Real.log T := by
  intro V hbudget
  have hL := Real.log_pos hT
  have hmassX : 0 ≤ mass S w X := Finset.sum_nonneg fun j _ => hw j
  have hWT : 0 < mass S w T := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) hn))
      ((by linarith only [hmassX, hL] : 0 ≤ mass S w X + 3 * Real.log T).trans_lt hmarginT)
  let J := S.cut T
  let head : Finset J := Finset.univ.filter (fun j => S.gamma j.val ≤ X)
  let f (j : J) := S.gamma j.val
  let p (j : J) : ℝ≥0 := ⟨w j.val, hw j.val⟩
  have htail : (∑ j ∈ headᶜ, (p j : ℝ) ^ 2) = V := tail_sums (fun j => w j ^ 2)
  rw [← htail] at hbudget
  have hslope : ∑ j ∈ headᶜ, (p j : ℝ) * |f j| ≤ T * mass S w T := by
    calc
      _ ≤ ∑ j : J, (p j : ℝ) * |f j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => by positivity)
      _ ≤ ∑ j : J, T * w j.val := by
        apply Finset.sum_le_sum
        intro j _
        rw [mul_comm T, show (p j : ℝ) = w j.val from rfl,
          show f j = S.gamma j.val from rfl, abs_of_pos (S.gamma_pos _)]
        exact mul_le_mul_of_nonneg_left (mem_cut.mp j.property) (hw _)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_coe_sort]; rfl
  have hcost : (1 / T ^ 2) * ∑ j ∈ headᶜ, (p j : ℝ) * |f j| < Real.log T := calc
    _ ≤ (1 / T ^ 2) * (T * mass S w T) := mul_le_mul_of_nonneg_left hslope (by positivity)
    _ = mass S w T / T := by field_simp
    _ < _ := hmeshT
  have hfiniteMargin : (∑ j ∈ head, (p j : ℝ)) + Real.log T +
      (1 / T ^ 2) * ∑ j ∈ headᶜ, (p j : ℝ) * |f j| < β ^ 2 * mass S w T - Real.log T := by
    have hhead : (∑ j ∈ head, (p j : ℝ)) = mass S w X := cutoff_sums hXT w
    linarith only [hcost, hhead, hmarginT, hL]
  refine ⟨hWT, fun A => ?_⟩
  obtain ⟨b, hb, hbound⟩ := exists_arbitrarily_late_missing_window head f p
    (hli.comp Subtype.val Subtype.val_injective) (by positivity) hL hbudget hfiniteMargin (A / r)
  refine ⟨b * r, (div_lt_iff₀ hr).mp hb, fun u hu => ?_⟩
  have hu' : u / r ∈ Icc b (b + H / r) := by
    refine ⟨(le_div_iff₀ hr).mpr hu.1, (div_le_iff₀ hr).mpr ?_⟩
    rw [add_mul, div_mul_cancel₀ _ hr.ne']
    exact hu.2
  have h := hbound (u / r) hu'
  simp only [sineScore, Pi.zero_apply, zero_add] at h
  change (∑ j : S.cut T, w j.val * Real.sin (S.gamma j.val * (u / r))) < _ at h
  rwa [Finset.sum_coe_sort (S.cut T) (fun j => w j * Real.sin (S.gamma j * (u / r)))] at h

/-- At the critical mass fraction, there are arbitrarily late closed windows of length
`exp (T ^ β)` on which the sine score stays strictly below `β ^ 2 * mass S w T - Real.log T`. -/
theorem eventual_critical_missing_window (S : Spectrum) (w : S.index → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hli : LinearIndependent ℚ S.gamma)
    (hmass : HasLogSquaredMass S w) (htail : HasSmallSquareTail S w)
    {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) (hβ₁ : β < 1) :
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + Real.exp (T ^ β)),
        sine S w T (u / r) < β ^ 2 * mass S w T - Real.log T := by
  classical
  obtain ⟨a, C, ha, hC, hmass⟩ := hmass
  obtain ⟨K, hK, hmargin⟩ := eventual_mass_margin ha hC hβ hmass
  let X (T : ℝ) := Real.exp (-K) * T ^ β
  let η := Real.exp (-K) / (8 * β ^ 2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hX := (tendsto_rpow_atTop hβ).const_mul_atTop (Real.exp_pos (-K))
  filter_upwards [hmargin, eventual_mesh_cost ha hC hmass, eventual_grid_bound hr hβ,
    hX.eventually (htail η hη), hX.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with T hmarginT hmeshT hgridT htailT hX₁ hT
  have hTpos := zero_lt_one.trans hT
  have hXT : X T ≤ T := shifted_cutoff_le hK.le hT.le hβ₁.le
  have hlogX : Real.log (X T) = β * Real.log T - K := log_shifted_cutoff hTpos K β
  let V := ∑ j ∈ S.cut T \ S.cut (X T), w j ^ 2
  have hV : V ≤ Real.log T ^ 2 / (8 * T ^ β) := by
    calc
      V ≤ η * Real.log (X T) ^ 2 / X T := htailT T hXT
      _ ≤ η * (β * Real.log T) ^ 2 / X T := by
        gcongr
        · exact Real.log_nonneg hX₁
        · linarith only [hlogX, hK]
      _ = _ := by
        dsimp only [η, X]
        field_simp [(Real.exp_pos (-K)).ne', hβ.ne', (Real.rpow_pos_of_pos hTpos β).ne']
  have hbudget : V = 0 ∨
      ((⌊(Real.exp (T ^ β) / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1) *
        Real.exp (-Real.log T ^ 2 / (2 * V)) < 1 := by
    by_cases hz : V = 0
    · exact Or.inl hz
    · right
      have hVpos : 0 < V :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (w j)) (Ne.symm hz)
      have hpowpos := Real.rpow_pos_of_pos hTpos β
      have hrate : 4 * T ^ β ≤ Real.log T ^ 2 / (2 * V) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * V)).mpr
        have hb := (le_div_iff₀ (by positivity : 0 < 8 * T ^ β)).mp hV
        simpa only [mul_assoc, mul_left_comm, mul_comm, show (4 : ℝ) * 2 = 8 by norm_num]
          using (show (4 * 2) * (T ^ β * V) ≤ Real.log T ^ 2 by
            rwa [show (4 * 2) * (T ^ β * V) = V * (8 * T ^ β) by ring])
      calc
        _ ≤ Real.exp (2 * T ^ β) * Real.exp (-(4 * T ^ β)) := by
          apply mul_le_mul hgridT _ (by positivity) (by positivity)
          apply Real.exp_le_exp.mpr
          linarith only [hrate, show -Real.log T ^ 2 / (2 * V) =
            -(Real.log T ^ 2 / (2 * V)) by ring]
        _ < 1 := by
          rw [← Real.exp_add, Real.exp_lt_one_iff]
          linarith only [hpowpos]
  exact missing_window_of_cutoff hw hli hT hr hXT hmarginT hmeshT hbudget

private theorem eventual_logarithmic_grid_bound {r β c : ℝ}
    (hr : 0 < r) (hβ : 0 < β) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop,
      let E := c * T ^ β * Real.log T
      (⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 < Real.exp (2 * E) := by
  let B := 1 / r + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hgrow := ((tendsto_rpow_atTop hβ).const_mul_atTop hc).eventually_gt_atTop
    (2 + Real.log B)
  filter_upwards [hgrow, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (1 : ℝ)] with T hg hlog hT
  let E := c * T ^ β * Real.log T
  change (⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1 < _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoly : T ^ 2 / r + 1 ≤ B * T ^ 2 := by
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT.le
    dsimp [B]
    linarith only [hT2, show (1 / r + 1) * T ^ 2 = T ^ 2 / r + T ^ 2 by ring]
  have hlogBudget : 2 * Real.log T + Real.log B < E := by
    change 2 + Real.log B < c * T ^ β at hg
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by dsimp [B]; linarith [div_pos one_pos hr])
    have hcost := mul_le_mul_of_nonneg_left hlog hlogB
    have hstrict := mul_lt_mul_of_pos_right hg (zero_lt_one.trans_le hlog)
    dsimp [E]
    nlinarith only [hcost, hstrict]
  have hpolyExp : B * T ^ 2 = Real.exp (2 * Real.log T + Real.log B) := by
    rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hB,
      Real.exp_log (zero_lt_one.trans hT)]
    ring
  calc
    _ ≤ Real.exp E * (T ^ 2 / r + 1) := grid_count_le (Real.one_le_exp_iff.mpr hE) hr
    _ ≤ Real.exp E * (B * T ^ 2) := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ < Real.exp E * Real.exp E := by
      rw [hpolyExp]
      exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hlogBudget) (Real.exp_pos _)
    _ = Real.exp (2 * E) := by rw [← Real.exp_add, two_mul]

/-- A logarithmic square-tail bound gives a strictly positive logarithmic gain in the
waiting exponent at the same critical mass fraction and signed logarithmic margin. -/
theorem eventual_logarithmic_missing_window (S : Spectrum) (w : S.index → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hli : LinearIndependent ℚ S.gamma)
    (hmass : HasLogSquaredMass S w) (htail : HasLogarithmicSquareTail S w)
    {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) (hβ₁ : β < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ A : ℝ, ∃ a > A, ∀ u ∈ Icc a (a + Real.exp (c * T ^ β * Real.log T)),
        sine S w T (u / r) < β ^ 2 * mass S w T - Real.log T := by
  classical
  obtain ⟨a, Cmass, ha, hCmass, hmass⟩ := hmass
  obtain ⟨C, hC, htail⟩ := htail
  obtain ⟨K, hK, hmargin⟩ := eventual_mass_margin ha hCmass hβ hmass
  let D := C * β * Real.exp K
  have hD : 0 < D := by dsimp [D]; positivity
  let c := 1 / (4 * D)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  let X (T : ℝ) := Real.exp (-K) * T ^ β
  have hX := (tendsto_rpow_atTop hβ).const_mul_atTop (Real.exp_pos (-K))
  filter_upwards [hmargin, eventual_mesh_cost ha hCmass hmass,
    eventual_logarithmic_grid_bound hr hβ hc, hX.eventually htail,
    eventually_gt_atTop (1 : ℝ)] with T hmarginT hmeshT hgridT htailT hT
  have hTpos := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hpowpos := Real.rpow_pos_of_pos hTpos β
  have hXT : X T ≤ T := shifted_cutoff_le hK.le hT.le hβ₁.le
  have hlogX : Real.log (X T) = β * Real.log T - K := log_shifted_cutoff hTpos K β
  let E := c * T ^ β * Real.log T
  let V := ∑ j ∈ S.cut T \ S.cut (X T), w j ^ 2
  have hV : V ≤ D * Real.log T / T ^ β := by
    calc
      V ≤ C * Real.log (X T) / X T := htailT T hXT
      _ ≤ C * (β * Real.log T) / X T := by
        gcongr
        linarith only [hlogX, hK]
      _ = _ := by
        dsimp only [X, D]
        rw [Real.exp_neg, div_mul_eq_div_div, div_inv_eq_mul]
        ring
  have hbudget : V = 0 ∨
      ((⌊(Real.exp E / r) / (1 / T ^ 2)⌋₊ : ℝ) + 1) *
        Real.exp (-Real.log T ^ 2 / (2 * V)) < 1 := by
    by_cases hz : V = 0
    · exact Or.inl hz
    · right
      have hVpos : 0 < V :=
        lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (w j)) (Ne.symm hz)
      have hVmul := (le_div_iff₀ hpowpos).mp hV
      have hrate : T ^ β * Real.log T / (2 * D) ≤ Real.log T ^ 2 / (2 * V) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * D)
          (by positivity : 0 < 2 * V)).mpr
        convert mul_le_mul_of_nonneg_right hVmul (by positivity : 0 ≤ 2 * Real.log T)
          using 1 <;> ring
      have hTwoE : 2 * E = T ^ β * Real.log T / (2 * D) := by
        dsimp only [E, c]
        ring
      calc
        _ < Real.exp (2 * E) * Real.exp (-Real.log T ^ 2 / (2 * V)) :=
          mul_lt_mul_of_pos_right hgridT (Real.exp_pos _)
        _ ≤ Real.exp (2 * E) * Real.exp (-(2 * E)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply Real.exp_le_exp.mpr
          rw [hTwoE, neg_div]
          exact neg_le_neg hrate
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact missing_window_of_cutoff hw hli hT hr hXT hmarginT hmeshT hbudget

#print axioms eventual_critical_missing_window
#print axioms eventual_logarithmic_missing_window

end D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow

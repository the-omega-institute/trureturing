/- GID: D5/S3/Arith/CharacterSums/PascadiPrimeCubeCount
   generality: G
   mirror-B: none(waiver:original-prime-cube-count)
   mirror-E: none(waiver:original-prime-cube-count)
   anchors: []
   utility: none
   digest: The original six-return count in the prime-cube area range, over every scalar center. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalUnitMiddleCount
import D5.S3.Arith.CharacterSums.PascadiOriginalRowReduction
import D5.S3.Arith.CharacterSums.PascadiSeventhHeightRange
import D5.S3.Arith.CharacterSums.PascadiOriginalRangeEstimates
import D5.S3.Arith.CharacterSums.PascadiScalarCenters
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! Assemble the actual prime-cube six-return estimate in the original variables. -/

namespace D5.S3.Arith.CharacterSums.Original

open scoped BigOperators

noncomputable section

private theorem prime_cube_centers_card (p : ℕ) (hp : p.Prime) [NeZero (p ^ 3)] :
    ((Finset.univ : Finset (ZMod (p ^ 3))).filter fun γ => γ*γ=1).card ≤ 4 := by
  classical
  let S := {γ : ZMod (p ^ 3) // γ*γ=1}
  let f : S → rootsOfUnity 2 (ZMod (p ^ 3)) := fun γ =>
    rootsOfUnity.mkOfPowEq γ.1 (by simpa only [pow_two] using γ.2)
  have hf : Function.Injective f := by
    intro γ δ h
    apply Subtype.ext
    exact congrArg (fun ζ : rootsOfUnity 2 (ZMod (p ^ 3)) => (ζ.1 : ZMod (p ^ 3))) h
  have hcard := Fintype.card_le_of_injective f hf
  have hroot : Fintype.card (rootsOfUnity 2 (ZMod (p ^ 3))) ≤ 4 := by
    by_cases hp2 : p=2
    · subst p
      have h := Fintype.card_le_of_injective
        (fun ζ : rootsOfUnity 2 (ZMod (2^3)) => ζ.1) Subtype.val_injective
      norm_num [ZMod.card_units_eq_totient] at h ⊢
      exact h
    · haveI := ZMod.isCyclic_units_of_prime_pow p hp hp2 3
      have h : Fintype.card (rootsOfUnity 2 (ZMod (p ^ 3))) ≤ 2 := by
        rw [← Nat.card_eq_fintype_card, rootsOfUnity_eq_ker,
          IsCyclic.card_powMonoidHom_ker]
        exact Nat.gcd_le_right _ (by decide : 0 < 2)
      omega
  have h := hcard.trans hroot
  simpa only [S, Fintype.card_subtype] using h

private theorem prime_cube_unit_of_not_dvd {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ZMod (p ^ 3)) := by
  have hn : ¬ p ∣ z.natAbs := by simpa only [← Int.natCast_dvd] using hz
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 3)).mpr hn
  rw [Nat.cast_natAbs] at hu
  by_cases hpos : 0 ≤ z
  · simpa only [abs_of_nonneg hpos] using hu
  · have hneg : IsUnit (-(z : ZMod (p ^ 3))) := by
      simpa only [abs_of_neg (lt_of_not_ge hpos), Int.cast_neg] using hu
    simpa only [neg_neg] using hneg.neg

private theorem scalar_count_crude {c : ℕ} [NeZero c] (X Y : ℝ)
    (hX : 0 ≤ X) (hY : 1 ≤ Y) (hXY : X ≤ Y) (a₁ a₂ γ : ZMod c) :
    ((scalarSolutionsReal c X Y a₁ a₂ γ).card : ℝ) ≤ 729*Y^6 := by
  classical
  have hY0 : 0 ≤ Y := by linarith
  have hcard := Finset.card_filter_le
    (s := literalRowBox ⌊X⌋₊ ⌊Y⌋₊)
    (p := fun h => sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn γ)
  have hint (n : ℕ) : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  have hb : (literalRowBox ⌊X⌋₊ ⌊Y⌋₊).card =
      (2*⌊X⌋₊+1)^3*(2*⌊Y⌋₊+1)^3 := by
    simp only [literalRowBox, Finset.product_eq_sprod, Finset.card_product,
      Fintype.card_piFinset_const, hint]
  have hx : 0 ≤ (2*(⌊X⌋₊ : ℝ)+1) := by positivity
  have hy : 0 ≤ (2*(⌊Y⌋₊ : ℝ)+1) := by positivity
  have hxY : 2*(⌊X⌋₊ : ℝ)+1 ≤ 3*Y := by
    linarith only [Nat.floor_le hX, hXY, hY]
  have hyY : 2*(⌊Y⌋₊ : ℝ)+1 ≤ 3*Y := by
    linarith only [Nat.floor_le hY0, hY]
  calc
    ((scalarSolutionsReal c X Y a₁ a₂ γ).card : ℝ) ≤
        ((literalRowBox ⌊X⌋₊ ⌊Y⌋₊).card : ℝ) := by exact_mod_cast hcard
    _ = (2*(⌊X⌋₊ : ℝ)+1)^3*(2*(⌊Y⌋₊ : ℝ)+1)^3 := by
      rw [hb]
      push_cast
      rfl
    _ ≤ (3*Y)^3*(3*Y)^3 := mul_le_mul
      (pow_le_pow_left₀ hx hxY 3) (pow_le_pow_left₀ hy hyY 3)
      (by positivity) (by positivity)
    _ = _ := by ring

private theorem large_minus_count (ε C α : ℝ)
    (hε : 0 < ε) (hC : 1 ≤ C) (hα : α < 26 / 7) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧ ∀ (p : ℕ) (_hp : p.Prime) [NeZero (p ^ 3)]
      (X Y : ℝ) (a₁ a₂ : ZMod (p ^ 3)),
      1 ≤ X → X ≤ Y → 3*Y < (p : ℝ)^2 →
      (p : ℝ)^3 ≤ X*Y → X*Y ≤ C*(p : ℝ)^α →
      P < (p : ℝ) →
      IsUnit a₁ → IsUnit a₂ →
      ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ (-1)).card : ℝ) ≤
        K*Y^2*(p : ℝ)^ε := by
  classical
  obtain ⟨K₀, hK₀, hcount⟩ := actual_unit_middle_tuple_count_seventh (ε/2) (by linarith)
  obtain ⟨D, hD, habsorb⟩ := range_error_absorption_of_exponent ε C K₀ α hε hC hK₀
    (by linarith only [hα])
  obtain ⟨P, hP, hcut⟩ := seventh_area_height_cutoff α C hα hC
  refine ⟨P, 3*D+72, hP, by positivity, ?_⟩
  intro p hp inst X Y a₁ a₂ hX hXY hsmall hlower harea hlarge ha₁ ha₂
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hY1 : 1 ≤ Y := hX.trans hXY
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hA : 0 < X*Y := mul_pos hX0 hY0
  have hgap := hcut (p : ℝ) (X*Y) hlarge hA.le harea
  have hupper : X*Y < (p : ℝ)^4 := by
    have hYp : Y < (p : ℝ)^2 := by linarith only [hsmall, hY0]
    have hsq := pow_lt_pow_left₀ hYp hY0.le (by decide : 2 ≠ 0)
    have hXYsq : X*Y ≤ Y^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hXY) hY0.le]
    nlinarith only [hsq, hXYsq]
  let T := (minusSolutions (p ^ 3) ⌊X⌋₊ ⌊Y⌋₊ a₁ a₂).filter
    fun h => ¬ (p : ℤ) ∣ h.2 2*h.1 2
  have hmem (h : ReturnRows) (hh : h ∈ T) :
      (∀ i, |(h.1 i : ℝ)| ≤ X) ∧ (∀ i, |(h.2 i : ℝ)| ≤ Y) ∧
      sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1) :=
    (mem_scalarSolutionsReal X Y hX0.le hY0.le a₁ a₂ (-1) h).mp
      (Finset.mem_filter.mp hh).1
  have hunit (h : ReturnRows) (hh : h ∈ T) :
      IsUnit (h.1 2 : ZMod (p ^ 3)) ∧ IsUnit (h.2 2 : ZMod (p ^ 3)) := by
    have hn := (Finset.mem_filter.mp hh).2
    exact ⟨prime_cube_unit_of_not_dvd hp (fun hd => hn (dvd_mul_of_dvd_right hd _)),
      prime_cube_unit_of_not_dvd hp (fun hd => hn (dvd_mul_of_dvd_left hd _))⟩
  have ht := hcount p hp X Y (Real.sqrt (X*Y)) a₁ a₂ T hX hXY hsmall
    hlower hupper.le (Real.sqrt_pos.mpr hA) (Real.sq_sqrt hA.le) ha₁ ha₂
    (fun h hh i => ⟨(hmem h hh).1 i, (hmem h hh).2.1 i⟩)
    (fun h hh => (hmem h hh).2.2) hunit hgap
  have hT : (T.card : ℝ) ≤ D*(X*Y)*(p : ℝ)^ε :=
    ht.trans (habsorb p (X*Y) hp2 hA.le harea)
  have hfloor : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  have hwidth : 3*⌊Y⌋₊ < p^2 := by
    have : (3 : ℝ)*(⌊Y⌋₊ : ℝ) < (p : ℝ)^2 := by
      linarith only [Nat.floor_le hY0.le, hsmall]
    exact_mod_cast this
  have hr := Nminus_le_three_Uminus_of_three_width hp hfloor hwidth a₁ a₂ ha₁ ha₂
  change (scalarSolutionsReal (p ^ 3) X Y a₁ a₂ (-1)).card ≤
    3*T.card+8*(2*⌊Y⌋₊+1)^2 at hr
  have hrR : ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ (-1)).card : ℝ) ≤
      3*(T.card : ℝ)+8*(2*(⌊Y⌋₊ : ℝ)+1)^2 := by
    exact_mod_cast hr
  have hsquare : (2*(⌊Y⌋₊ : ℝ)+1)^2 ≤ 9*Y^2 := by
    have : 2*(⌊Y⌋₊ : ℝ)+1 ≤ 3*Y := by
      linarith only [Nat.floor_le hY0.le, hY1]
    calc
      _ ≤ (3*Y)^2 := pow_le_pow_left₀ (by positivity) this 2
      _ = _ := by ring
  have hpε : 1 ≤ (p : ℝ)^ε := Real.one_le_rpow (by linarith only [hp2]) hε.le
  have hXYsquare : X*Y ≤ Y^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hXY hY0.le
  calc
    _ ≤ 3*(D*(X*Y)*(p : ℝ)^ε)+8*(9*Y^2) := by
      nlinarith only [hrR, hT, hsquare]
    _ ≤ (3*D+72)*Y^2*(p : ℝ)^ε := by
      have hh := mul_le_mul_of_nonneg_right hXYsquare
        (by positivity : 0 ≤ 3*D*(p : ℝ)^ε)
      have hq := mul_le_mul_of_nonneg_left hpε (by positivity : 0 ≤ 72*Y^2)
      nlinarith only [hh, hq]

/-- The original prime-cube area range bounds the total literal six-letter
count, summed over every scalar center whose square is one. There is no
excluded prime or supplied lattice, chart, endpoint family or counting bound. -/
theorem prime_cube_scalar_return_count_of_exponent (ε C₀ α : ℝ)
    (hε : 0 < ε) (hC₀ : 1 ≤ C₀) (hα : α < 26 / 7) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (_hp : p.Prime) [NeZero (p ^ 3)]
      (X Y : ℝ) (a₁ a₂ : ZMod (p ^ 3)),
      (p : ℝ)^((3 : ℝ)/2) ≤ X → X ≤ Y →
      X*Y ≤ C₀*(p : ℝ)^α → 6*Y < (p : ℝ)^2 →
      IsUnit a₁ → IsUnit a₂ →
      (∑ γ ∈ (Finset.univ : Finset (ZMod (p ^ 3))).filter (fun γ => γ*γ=1),
        ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ γ).card : ℝ)) ≤
        K*Y^2*(p : ℝ)^ε := by
  classical
  have hC : 1 ≤ 4*C₀ := by linarith only [hC₀]
  obtain ⟨P, K₁, hP, hK₁, hlarge_count⟩ := large_minus_count ε (4*C₀) α hε hC hα
  let D := 256*K₁+729*P^8
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨4*D, by positivity, ?_⟩
  intro p hp inst X Y a₁ a₂ hmin hXY harea hwidth ha₁ ha₂
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hpε : 1 ≤ (p : ℝ)^ε := Real.one_le_rpow hp1 hε.le
  have hbase : 1 ≤ (p : ℝ)^((3 : ℝ)/2) :=
    Real.one_le_rpow hp1 (by norm_num)
  have hX1 : 1 ≤ X := hbase.trans hmin
  have hY1 : 1 ≤ Y := hX1.trans hXY
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hAsq : ((p : ℝ)^((3 : ℝ)/2))^2 = (p : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hpR.le]
    norm_num
  have hlower : (p : ℝ)^3 ≤ X*Y := by
    rw [← hAsq, pow_two]
    exact mul_le_mul hmin (hmin.trans hXY) (by positivity) hX0.le
  let S := (Finset.univ : Finset (ZMod (p ^ 3))).filter fun γ => γ*γ=1
  have hcenter : (S.card : ℝ) ≤ 4 := by
    exact_mod_cast prime_cube_centers_card p hp
  have hone (γ : ZMod (p ^ 3)) (hγ : γ ∈ S) :
      ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ γ).card : ℝ) ≤
        D*Y^2*(p : ℝ)^ε := by
    have hγ2 : γ*γ=1 := (Finset.mem_filter.mp hγ).2
    by_cases hlarge : P < (p : ℝ)
    · have hdouble := hlarge_count p hp (2*X) (2*Y) a₁ a₂
        (by linarith only [hX1]) (by linarith only [hXY])
        (by linarith only [hwidth])
        (by nlinarith only [hlower, mul_pos hX0 hY0]) (by nlinarith only [harea])
        hlarge ha₁ ha₂
      have hc := scalarSolutionsReal_card_le_minus_doubled a₁ a₂ γ hγ2 X Y
        hX0.le hY0.le
      change (scalarSolutionsReal (p ^ 3) X Y a₁ a₂ γ).card ≤
        64*(scalarSolutionsReal (p ^ 3) (2*X) (2*Y) a₁ a₂ (-1)).card at hc
      have hcR : ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ γ).card : ℝ) ≤
          64*((scalarSolutionsReal (p ^ 3) (2*X) (2*Y) a₁ a₂ (-1)).card : ℝ) := by
        exact_mod_cast hc
      calc
        _ ≤ 64*(K₁*(2*Y)^2*(p : ℝ)^ε) :=
          hcR.trans (mul_le_mul_of_nonneg_left hdouble (by norm_num))
        _ = (256*K₁)*Y^2*(p : ℝ)^ε := by ring
        _ ≤ D*Y^2*(p : ℝ)^ε := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg Y)
          dsimp only [D]
          exact le_add_of_nonneg_right (by positivity)
    · have hpP : (p : ℝ) ≤ P := le_of_not_gt hlarge
      have hpsq : (p : ℝ)^2 ≤ P^2 := pow_le_pow_left₀ hpR.le hpP 2
      have hy6 : Y ≤ 6*Y := by linarith only [hY0]
      have hYP : Y ≤ P^2 := hy6.trans (hwidth.le.trans hpsq)
      have hY4 : Y^4 ≤ P^8 := by
        calc
          _ ≤ (P^2)^4 := pow_le_pow_left₀ hY0.le hYP 4
          _ = _ := (pow_mul P 2 4).symm
      calc
        _ ≤ 729*Y^6 := scalar_count_crude X Y hX0.le hY1 hXY a₁ a₂ γ
        _ = 729*Y^4*Y^2 := by ring
        _ ≤ 729*P^8*Y^2 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hY4 (by norm_num)) (sq_nonneg Y)
        _ ≤ 729*P^8*Y^2*(p : ℝ)^ε :=
          le_mul_of_one_le_right (by positivity) hpε
        _ ≤ D*Y^2*(p : ℝ)^ε := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg Y)
          dsimp only [D]
          exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ ∑ _γ ∈ S, D*Y^2*(p : ℝ)^ε := Finset.sum_le_sum hone
    _ = (S.card : ℝ)*(D*Y^2*(p : ℝ)^ε) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4*(D*Y^2*(p : ℝ)^ε) := mul_le_mul_of_nonneg_right hcenter (by positivity)
    _ = (4*D)*Y^2*(p : ℝ)^ε := by simp only [mul_assoc]

/-- Preserve the original eighteen-fifths prime-cube count. -/
theorem prime_cube_scalar_return_count (ε C₀ : ℝ) (hε : 0 < ε) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (p : ℕ) (_hp : p.Prime) [NeZero (p ^ 3)]
      (X Y : ℝ) (a₁ a₂ : ZMod (p ^ 3)),
      (p : ℝ)^((3 : ℝ)/2) ≤ X → X ≤ Y →
      X*Y ≤ C₀*(p : ℝ)^((18 : ℝ)/5) → 6*Y < (p : ℝ)^2 →
      IsUnit a₁ → IsUnit a₂ →
      (∑ γ ∈ (Finset.univ : Finset (ZMod (p ^ 3))).filter (fun γ => γ*γ=1),
        ((scalarSolutionsReal (p ^ 3) X Y a₁ a₂ γ).card : ℝ)) ≤
        K*Y^2*(p : ℝ)^ε := by
  exact prime_cube_scalar_return_count_of_exponent ε C₀ ((18 : ℝ)/5) hε hC₀ (by norm_num)

end
end D5.S3.Arith.CharacterSums.Original

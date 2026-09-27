/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainLift
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: The capped-gain lift on individual full labels. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainLift.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainLattice

/-!
# The capped-gain lift on individual full labels

The analytic input is expressed as the family `F₀ + r G`. Only increasingness
of `G` is required: supermodularity of `G` is deliberately not a hypothesis.
-/

namespace Erdos7.CappedGain

variable {ι : Type*} [DecidableEq ι]

def rho (q t L : ℚ) : ℚ := 1 / (q - min t L)

def charge (q t L : ℚ) : ℚ := max (L - t) 0 / (q - t)

def lift (q t : ℚ) (F₀ G : Finset ι → ℚ) (L : ℚ) (S : Finset ι) : ℚ :=
  charge q t L + max (F₀ S + rho q t L * G S)
    (F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L))

theorem rho_pos {q t : ℚ} (hqt : t < q) (L : ℚ) : 0 < rho q t L := by
  unfold rho
  exact div_pos (by norm_num) (by linarith [min_le_left t L])

theorem rho_le {q t : ℚ} (hqt : t < q) (L : ℚ) : rho q t L ≤ 1 / (q - t) := by
  unfold rho
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
  linarith [min_le_left t L]

theorem rho_monotone {q t : ℚ} (hqt : t < q) : Monotone (rho q t) := by
  intro x y hxy
  unfold rho
  apply div_le_div_of_nonneg_left (by norm_num)
    (by linarith [min_le_left t y])
  linarith [min_le_min_left t hxy]

theorem charge_nonneg {q t : ℚ} (hqt : t < q) (L : ℚ) : 0 ≤ charge q t L := by
  exact div_nonneg (le_max_right _ _) (by linarith)

theorem lift_majorizes (q t : ℚ) (F₀ G : Finset ι → ℚ) (L : ℚ) (S : Finset ι) :
    charge q t L + F₀ S + rho q t L * G S ≤ lift q t F₀ G L S := by
  unfold lift
  linarith [le_max_left (F₀ S + rho q t L * G S)
    (F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L))]

theorem lift_eq_subtract {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) (L : ℚ) (S : Finset ι) :
    lift q t F₀ G L S = charge q t L + F₀ S + G S / (q - t) -
      (1 / (q - t) - rho q t L) * min (G S) (q - t) := by
  have hc : q - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt hqt)
  have hr : 0 ≤ 1 / (q - t) - rho q t L := sub_nonneg.mpr (rho_le hqt L)
  have hid : (F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L)) -
      (F₀ S + rho q t L * G S) =
      (1 / (q - t) - rho q t L) * (G S - (q - t)) := by
    field_simp
    <;> ring
  unfold lift
  by_cases hG : G S ≤ q - t
  · have hm := mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hG)
    have hb : F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L) ≤
        F₀ S + rho q t L * G S := by linarith
    rw [max_eq_left hb, min_eq_left hG]
    ring
  · have hG' : q - t ≤ G S := le_of_not_ge hG
    have hm := mul_nonneg hr (sub_nonneg.mpr hG')
    have hb : F₀ S + rho q t L * G S ≤
        F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L) := by linarith
    rw [max_eq_right hb, min_eq_right hG']
    field_simp
    <;> ring

theorem lift_eq_loadPart {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) (L : ℚ) (S : Finset ι) :
    lift q t F₀ G L S = F₀ S + G S / (q - t) - min (G S) (q - t) / (q - t) +
      loadPart q t (min (G S) (q - t)) L := by
  rw [lift_eq_subtract hqt]
  by_cases hL : L ≤ t
  · simp only [charge, rho, loadPart, hL, if_true, min_eq_right hL,
      max_eq_right (sub_nonpos.mpr hL), zero_div]
    ring
  · have htL : t ≤ L := le_of_not_ge hL
    simp only [charge, rho, loadPart, hL, if_false, min_eq_left htL,
      max_eq_left (sub_nonneg.mpr htL)]
    ring

theorem lift_load_monotone {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) {S : Finset ι} (hG : 0 ≤ G S) :
    Monotone (fun L ↦ lift q t F₀ G L S) := by
  intro x y hxy
  change lift q t F₀ G x S ≤ lift q t F₀ G y S
  rw [lift_eq_loadPart hqt, lift_eq_loadPart hqt]
  have h := loadPart_monotone hqt (le_min hG (by linarith)) (min_le_right _ _) hxy
  linarith

theorem lift_load_increment {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) {S : Finset ι} (hG : 0 ≤ G S)
    {x y d : ℚ} (hxy : x ≤ y) (hd : 0 ≤ d) :
    lift q t F₀ G (x + d) S - lift q t F₀ G x S ≤
      lift q t F₀ G (y + d) S - lift q t F₀ G y S := by
  simp only [lift_eq_loadPart hqt]
  have h := loadPart_increment_mono hqt (le_min hG (by linarith))
    (min_le_right (G S) (q - t)) hxy hd
  linarith

theorem lift_mixed_increment {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) (hG : Increasing G)
    {x y : ℚ} (hxy : x ≤ y) {S T : Finset ι} (hST : S ⊆ T) :
    lift q t F₀ G y S - lift q t F₀ G x S ≤
      lift q t F₀ G y T - lift q t F₀ G x T := by
  simp only [lift_eq_subtract hqt]
  have hm := min_le_min_right (q - t) (hG hST)
  have hr := sub_nonneg.mpr (rho_monotone hqt hxy)
  have h := mul_le_mul_of_nonneg_left hm hr
  nlinarith

theorem lift_future_supermodular {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ) (hG : Increasing G)
    (hPhi : ∀ r : ℚ, 0 ≤ r → r ≤ 1 / (q - t) →
      Supermodular (fun S ↦ F₀ S + r * G S)) (L : ℚ) :
    Supermodular (lift q t F₀ G L) := by
  have hc0 : (0 : ℚ) ≤ 1 / (q - t) := by positivity
  have h1 := hPhi (rho q t L) (rho_pos hqt L).le (rho_le hqt L)
  have h2 : Supermodular (fun S ↦ F₀ S + G S / (q - t) -
      (1 - (q - t) * rho q t L)) := by
    intro A B
    have h := hPhi (1 / (q - t)) hc0 (le_refl _) A B
    dsimp at h ⊢
    linear_combination h
  have hdiff : Increasing (fun S ↦
      (F₀ S + G S / (q - t) - (1 - (q - t) * rho q t L)) -
        (F₀ S + rho q t L * G S)) := by
    intro A B hAB
    have h := mul_le_mul_of_nonneg_left (hG hAB)
      (sub_nonneg.mpr (rho_le hqt L))
    dsimp
    linear_combination h
  have hm := supermodular_max_of_increasing_difference h1 h2 hdiff
  intro A B
  have h := hm A B
  unfold lift
  linarith

theorem lift_future_increasing {q t : ℚ} (hqt : t < q)
    (F₀ G : Finset ι → ℚ)
    (hPhi : ∀ r : ℚ, 0 ≤ r → r ≤ 1 / (q - t) →
      Increasing (fun S ↦ F₀ S + r * G S)) (L : ℚ) :
    Increasing (lift q t F₀ G L) := by
  intro A B hAB
  have h1 := hPhi (rho q t L) (rho_pos hqt L).le (rho_le hqt L) hAB
  have h2 := hPhi (1 / (q - t)) (by positivity) (le_refl _) hAB
  have h2' : F₀ A + G A / (q - t) - (1 - (q - t) * rho q t L) ≤
      F₀ B + G B / (q - t) - (1 - (q - t) * rho q t L) := by
    dsimp at h2
    linear_combination h2
  have h := max_le_max h1 h2'
  unfold lift
  linarith

/-- The main full-label supermodularity theorem for the capped-gain operator. -/
theorem lift_supermodular {q t : ℚ} (hqt : t < q)
    (P : ι → Prop) [DecidablePred P] (w : ι → ℚ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ x, P x → w x = 0)
    (F₀ G : Finset ι → ℚ) (hG0 : ∀ S, 0 ≤ G S) (hG : Increasing G)
    (hPhi : ∀ r : ℚ, 0 ≤ r → r ≤ 1 / (q - t) →
      Supermodular (fun S ↦ F₀ S + r * G S)) :
    Supermodular (fun A ↦ lift q t F₀ G (modularLoad w A) (A.filter P)) := by
  apply supermodular_load_filter P w hw hzero (lift q t F₀ G)
  · intro l _
    exact lift_future_supermodular hqt F₀ G hG hPhi l
  · intro S x y d _ hxy hd
    exact lift_load_increment hqt F₀ G (hG0 S) hxy hd
  · intro l m _ hlm S T hST
    exact lift_mixed_increment hqt F₀ G hG hlm hST

theorem lift_increasing {q t : ℚ} (hqt : t < q)
    (P : ι → Prop) [DecidablePred P] (w : ι → ℚ) (hw : ∀ x, 0 ≤ w x)
    (F₀ G : Finset ι → ℚ) (hG0 : ∀ S, 0 ≤ G S)
    (hPhi : ∀ r : ℚ, 0 ≤ r → r ≤ 1 / (q - t) →
      Increasing (fun S ↦ F₀ S + r * G S)) :
    Increasing (fun A ↦ lift q t F₀ G (modularLoad w A) (A.filter P)) := by
  apply increasing_load_filter P w hw (lift q t F₀ G)
  · intro l _
    exact lift_future_increasing hqt F₀ G hPhi l
  · intro S l m _ hlm
    exact lift_load_monotone hqt F₀ G (hG0 S) hlm

theorem lift_zero {q t : ℚ} (hqt : t < q) (ht : 0 ≤ t)
    (F₀ G : Finset ι → ℚ) (hF : F₀ ∅ = 0) (hG : G ∅ = 0) :
    lift q t F₀ G 0 ∅ = 0 := by
  have hc : 0 < q - t := by linarith
  have hr : (q - t) * rho q t 0 ≤ 1 := by
    have h := (le_div_iff₀ hc).mp (rho_le hqt 0)
    simpa [mul_comm] using h
  simp only [lift, charge, hF, hG, mul_zero, zero_add, zero_div, zero_sub]
  rw [max_eq_right (by linarith : -t ≤ 0), zero_div,
    max_eq_left (by linarith : -(1 - (q - t) * rho q t 0) ≤ 0)]
  ring

end Erdos7.CappedGain

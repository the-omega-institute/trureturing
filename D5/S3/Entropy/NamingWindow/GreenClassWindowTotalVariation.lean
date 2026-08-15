/- GID: D5/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/GreenClassWindowTotalVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sandwich window total variation between one coordinate and the coordinate sum. -/

/- Repository and library-search audit trail (2026-08-15):
   * Local pinned-mathlib grep terms: `totalVariation.*prod`, `product.*totalVariation`,
     `total variation.*product`, `variationDist.*prod`, `L1.*prod`, and `prod.*L1`.
   * No finite real-valued total-variation product or window theorem was found. Mathlib's total
     variations are measure-valued, while its product and `L1` results do not state this finite
     half-`L1` sandwich. The proof below uses the repository's finite definition directly.
   * `ProductSubadditive.total_variation_product_subadditive` supplies the binary hybrid proof
     shape, but not the finite dependent-function window statement proved here.
   * `GreenClassWindowEntropy.sum_prod_update` and
     `GreenClassWindowEntropy.coordLaw_sum_eq_one` already prove the needed facts internally.
   * Those local facts are private and not reusable public theorems. Unfreezing the kernel-verified
     module merely to change their visibility is unlawful under SL-008.
   * This file intentionally re-proves the same finite sum-product and coordinate-normalization
     facts against the imported repository definitions.
-/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.TotalVariation.Metric
import D5.S3.TotalVariation.DataProcessing

namespace D5.S3.Entropy.NamingWindow.GreenClassWindowTotalVariation

open MeasureTheory Finset
open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.DataProcessing
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy

noncomputable section

private theorem sum_prod_update {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p : ι → O → ℝ) (i : ι) (g : O → ℝ) :
    (∑ u : ι → O, (∏ j ∈ Finset.univ.erase i, p j (u j)) * g (u i)) =
      (∏ j ∈ Finset.univ.erase i, ∑ a, p j a) * ∑ a, g a := by
  classical
  have hupd : ∀ u : ι → O,
      (∏ j ∈ Finset.univ.erase i, p j (u j)) * g (u i) =
        ∏ j, (Function.update p i g) j (u j) := by
    intro u
    rw [← Finset.mul_prod_erase _ (fun j => (Function.update p i g) j (u j))
      (Finset.mem_univ i), Function.update_self]
    refine (mul_comm _ _).trans ?_
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [Finset.sum_congr rfl fun u _ => hupd u,
    ← Fintype.prod_sum (fun j => (Function.update p i g) j),
    ← Finset.mul_prod_erase _ (fun j => ∑ a, (Function.update p i g) j a)
      (Finset.mem_univ i), Function.update_self]
  refine (mul_comm _ _).trans ?_
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

private theorem coordLaw_sum_eq_one {O : Type*} [Fintype O] [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ℕ) : ∑ a, coordLaw μ i a = 1 := by
  simp only [coordLaw]
  rw [show (∑ a, (μ i {a}).toReal) = (∑ a, μ i {a}).toReal from
    (ENNReal.toReal_sum fun a _ => measure_ne_top _ _).symm]
  rw [MeasureTheory.sum_measure_singleton]
  simp

private noncomputable def hybrid {ι O : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → O → ℝ) (s : Finset ι) (u : ι → O) : ℝ :=
  ∏ i, if i ∈ s then p i (u i) else q i (u i)

/-- **Window total variation is bounded by the sum of coordinate total variations.** -/
theorem totalVariation_windowLaw_le_sum
    {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p q : ι → O → ℝ)
    (hp : ∀ i, (∀ a, 0 ≤ p i a) ∧ ∑ a, p i a = 1)
    (hq : ∀ i, (∀ a, 0 ≤ q i a) ∧ ∑ a, q i a = 1) :
    totalVariation (windowLaw p) (windowLaw q) ≤
      ∑ i, totalVariation (p i) (q i) := by
  classical
  have hstep (s : Finset ι) (a : ι) (ha : a ∉ s) :
      totalVariation (hybrid p q (insert a s)) (hybrid p q s) =
        totalVariation (p a) (q a) := by
    let m : ι → O → ℝ := fun j b => if j ∈ s then p j b else q j b
    have hm_nonneg (j : ι) (b : O) : 0 ≤ m j b := by
      dsimp [m]
      split_ifs with hj
      · exact (hp j).1 b
      · exact (hq j).1 b
    have hm_sum (j : ι) : ∑ b, m j b = 1 := by
      dsimp [m]
      split_ifs with hj
      · exact (hp j).2
      · exact (hq j).2
    have hpoint (u : ι → O) :
        |hybrid p q (insert a s) u - hybrid p q s u| =
          (∏ j ∈ Finset.univ.erase a, m j (u j)) * |p a (u a) - q a (u a)| := by
      have hinsert :
          (∏ j ∈ Finset.univ.erase a,
              if j ∈ insert a s then p j (u j) else q j (u j)) =
            ∏ j ∈ Finset.univ.erase a, m j (u j) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        have hja : j ≠ a := (Finset.mem_erase.mp hj).1
        dsimp [m]
        simp [hja]
      have hs :
          (∏ j ∈ Finset.univ.erase a, if j ∈ s then p j (u j) else q j (u j)) =
            ∏ j ∈ Finset.univ.erase a, m j (u j) := by
        exact Finset.prod_congr rfl fun _ _ => rfl
      rw [hybrid, hybrid,
        ← Finset.mul_prod_erase _
          (fun j => if j ∈ insert a s then p j (u j) else q j (u j))
          (Finset.mem_univ a),
        ← Finset.mul_prod_erase _
          (fun j => if j ∈ s then p j (u j) else q j (u j))
          (Finset.mem_univ a),
        if_pos (Finset.mem_insert_self a s), if_neg ha, hinsert, hs, ← sub_mul,
        abs_mul, abs_of_nonneg (Finset.prod_nonneg fun j _ => hm_nonneg j (u j)), mul_comm]
    have hsum :
        (∑ u : ι → O, |hybrid p q (insert a s) u - hybrid p q s u|) =
          2 * totalVariation (p a) (q a) := by
      calc
        (∑ u : ι → O, |hybrid p q (insert a s) u - hybrid p q s u|) =
            ∑ u : ι → O,
              (∏ j ∈ Finset.univ.erase a, m j (u j)) * |p a (u a) - q a (u a)| :=
          Finset.sum_congr rfl fun u _ => hpoint u
        _ = (∏ j ∈ Finset.univ.erase a, ∑ b, m j b) *
              ∑ b, |p a b - q a b| :=
          sum_prod_update m a (fun b => |p a b - q a b|)
        _ = ∑ b, |p a b - q a b| := by
          rw [Finset.prod_congr rfl fun j _ => hm_sum j, Finset.prod_const_one, one_mul]
        _ = 2 * totalVariation (p a) (q a) := by
          rw [totalVariation]
          ring
    calc
      totalVariation (hybrid p q (insert a s)) (hybrid p q s) =
          (1 / 2 : ℝ) *
            ∑ u : ι → O, |hybrid p q (insert a s) u - hybrid p q s u| := rfl
      _ = (1 / 2 : ℝ) * (2 * totalVariation (p a) (q a)) := by rw [hsum]
      _ = totalVariation (p a) (q a) := by ring
  have htel (s : Finset ι) :
      totalVariation (hybrid p q s) (hybrid p q ∅) ≤
        ∑ i ∈ s, totalVariation (p i) (q i) := by
    induction s using Finset.induction_on with
    | empty => simp [hybrid, totalVariation]
    | @insert a s ha ih =>
        calc
          totalVariation (hybrid p q (insert a s)) (hybrid p q ∅) ≤
              totalVariation (hybrid p q (insert a s)) (hybrid p q s) +
                totalVariation (hybrid p q s) (hybrid p q ∅) :=
            total_variation_triangle _ _ _
          _ = totalVariation (p a) (q a) +
                totalVariation (hybrid p q s) (hybrid p q ∅) := by
            rw [hstep s a ha]
          _ ≤ totalVariation (p a) (q a) +
                ∑ i ∈ s, totalVariation (p i) (q i) :=
            add_le_add (le_refl _) ih
          _ = ∑ i ∈ insert a s, totalVariation (p i) (q i) := by
            rw [Finset.sum_insert ha]
  have huniv : hybrid p q Finset.univ = windowLaw p := by
    funext u
    simp [hybrid, windowLaw]
  have hempty : hybrid p q ∅ = windowLaw q := by
    funext u
    simp [hybrid, windowLaw]
  have hfinal := htel Finset.univ
  rw [huniv, hempty] at hfinal
  simpa using hfinal

/-- **Each coordinate total variation is bounded by the window total variation.** -/
theorem totalVariation_le_totalVariation_windowLaw
    {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] [DecidableEq O]
    (p q : ι → O → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (hq : ∀ i, ∑ a, q i a = 1) (i : ι) :
    totalVariation (p i) (q i) ≤ totalVariation (windowLaw p) (windowLaw q) := by
  let W : (ι → O) → O → ℝ := fun u b => if u i = b then 1 else 0
  have hW : (∀ u b, 0 ≤ W u b) ∧ ∀ u, ∑ b, W u b = 1 := by
    constructor
    · intro u b
      dsimp [W]
      split_ifs <;> norm_num
    · intro u
      simp [W]
  have houtput (r : ι → O → ℝ) (hr : ∀ j, ∑ a, r j a = 1) :
      channelOutput W (windowLaw r) = r i := by
    funext b
    calc
      channelOutput W (windowLaw r) b =
          ∑ u : ι → O, (∏ j ∈ Finset.univ.erase i, r j (u j)) *
            (r i (u i) * if u i = b then 1 else 0) := by
        rw [channelOutput]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [windowLaw,
          ← Finset.mul_prod_erase _ (fun j => r j (u j)) (Finset.mem_univ i)]
        dsimp [W]
        ring
      _ = (∏ j ∈ Finset.univ.erase i, ∑ a, r j a) *
            ∑ a, r i a * if a = b then 1 else 0 :=
        sum_prod_update r i (fun a => r i a * if a = b then 1 else 0)
      _ = r i b := by
        rw [Finset.prod_congr rfl fun j _ => hr j, Finset.prod_const_one, one_mul]
        simp
  have hcontract :=
    total_variation_channel_le (windowLaw p) (windowLaw q) W hW
  rw [houtput p hp, houtput q hq] at hcontract
  exact hcontract

/-- **Green-class window total variation is bounded by the coordinate sum.** -/
theorem totalVariation_greenClass_window_le_sum
    {O : Type*} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O]
    (μ ν : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (S : Finset ℕ) :
    totalVariation (windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1))
        (windowLaw (fun i : (S : Finset ℕ) => coordLaw ν i.1)) ≤
      ∑ i ∈ S, totalVariation (coordLaw μ i) (coordLaw ν i) := by
  classical
  calc
    totalVariation (windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1))
        (windowLaw (fun i : (S : Finset ℕ) => coordLaw ν i.1)) ≤
      ∑ i : (S : Finset ℕ), totalVariation (coordLaw μ i.1) (coordLaw ν i.1) :=
        totalVariation_windowLaw_le_sum
          (fun i : (S : Finset ℕ) => coordLaw μ i.1)
          (fun i : (S : Finset ℕ) => coordLaw ν i.1)
          (fun i => ⟨fun _ => ENNReal.toReal_nonneg, coordLaw_sum_eq_one μ i.1⟩)
          (fun i => ⟨fun _ => ENNReal.toReal_nonneg, coordLaw_sum_eq_one ν i.1⟩)
    _ = ∑ i ∈ S, totalVariation (coordLaw μ i) (coordLaw ν i) :=
      Finset.sum_coe_sort S (fun i => totalVariation (coordLaw μ i) (coordLaw ν i))

end

end D5.S3.Entropy.NamingWindow.GreenClassWindowTotalVariation

/- GID: D5/S3/Entropy/NamingWindow/GreenClassWindowDivergence
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/GreenClassWindowDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Window KL is additive, equals the uniform entropy defect, and detects agreement. -/

/- Repository audit trail (2026-08-15):
   * `GreenClassWindowEntropy.sum_prod_update` and
     `GreenClassWindowEntropy.coordLaw_sum_eq_one` already prove the needed facts internally.
   * Those local facts are private and not reusable public theorems. Unfreezing the kernel-verified
     module merely to change their visibility is unlawful under SL-008.
   * This file intentionally re-proves the same finite sum-product and coordinate-normalization
     facts against the imported repository definitions.
-/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Divergence.StrictGibbs
import D5.S3.Entropy.EntropyDivergenceIdentity

namespace D5.S3.Entropy.NamingWindow.GreenClassWindowDivergence

open MeasureTheory Finset
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GrandmotherTheorem
open D5.S3.Divergence.GibbsEquality
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.EntropyDivergenceIdentity
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

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

/-- **Window divergence additivity.** -/
theorem klDivergence_windowLaw {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p q : ι → O → ℝ) (hp : ∀ i, ∑ a, p i a = 1)
    (hppos : ∀ i a, 0 < p i a) (hqpos : ∀ i a, 0 < q i a) :
    klDivergence (windowLaw p) (windowLaw q) = ∑ i, klDivergence (p i) (q i) := by
  classical
  rw [klDivergence]
  calc
    (∑ u : ι → O, windowLaw p u * Real.log (windowLaw p u / windowLaw q u)) =
        ∑ u : ι → O, ∑ i, (∏ j ∈ Finset.univ.erase i, p j (u j)) *
          (p i (u i) * Real.log (p i (u i) / q i (u i))) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have hsplit : Real.log (windowLaw p u / windowLaw q u) =
          ∑ i, Real.log (p i (u i) / q i (u i)) := by
        rw [windowLaw, windowLaw, ← Finset.prod_div_distrib,
          Real.log_prod (fun i _ => ne_of_gt (div_pos (hppos i (u i)) (hqpos i (u i))))]
      rw [hsplit, windowLaw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_prod_erase _ (fun j => p j (u j)) (Finset.mem_univ i)]
      ring
    _ = ∑ i, ∑ u : ι → O, (∏ j ∈ Finset.univ.erase i, p j (u j)) *
          (p i (u i) * Real.log (p i (u i) / q i (u i))) := Finset.sum_comm
    _ = ∑ i, (∏ j ∈ Finset.univ.erase i, ∑ a, p j a) *
          ∑ a, p i a * Real.log (p i a / q i a) :=
      Finset.sum_congr rfl fun i _ =>
        sum_prod_update p i (fun a => p i a * Real.log (p i a / q i a))
    _ = ∑ i, klDivergence (p i) (q i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_congr rfl fun j _ => hp j, Finset.prod_const_one, one_mul, klDivergence]

/-- The window law of uniform coordinates is the uniform law on window assignments. -/
theorem windowLaw_uniform_eq {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O] :
    windowLaw (fun (_ : ι) (_ : O) => (Fintype.card O : ℝ)⁻¹) =
      fun _ : ι → O => (Fintype.card (ι → O) : ℝ)⁻¹ := by
  funext u
  rw [windowLaw, Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  push_cast
  rw [← inv_pow]

/-- **The naming-window entropy defect is a divergence.** -/
theorem klDivergence_windowLaw_uniform_eq {ι O : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype O] [Nonempty O] (p : ι → O → ℝ)
    (hnn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1) :
    klDivergence (windowLaw p) (windowLaw (fun (_ : ι) (_ : O) => (Fintype.card O : ℝ)⁻¹)) =
      Fintype.card ι * (namingDim O * Real.log 2) - shannonEntropy (windowLaw p) := by
  classical
  have hwnn : ∀ u : ι → O, 0 ≤ windowLaw p u := fun u =>
    Finset.prod_nonneg fun i _ => hnn i (u i)
  have hlog : Real.log (Fintype.card O) = namingDim O * Real.log 2 := by
    rw [namingDim, Real.logb, div_mul_cancel₀]
    exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [windowLaw_uniform_eq,
    kl_divergence_uniform_eq (windowLaw p) ⟨hwnn, windowLaw_sum_eq_one p hp⟩,
    Fintype.card_fun, ← hlog]
  congr 1
  rw [Nat.cast_pow, Real.log_pow]

/-- **Window Gibbs uniqueness.** -/
theorem klDivergence_windowLaw_eq_zero_iff {ι O : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype O] (p q : ι → O → ℝ)
    (hpnn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1)
    (hqnn : ∀ i a, 0 ≤ q i a) (hq : ∀ i, ∑ a, q i a = 1)
    (hppos : ∀ i a, 0 < p i a) (hqpos : ∀ i a, 0 < q i a) :
    klDivergence (windowLaw p) (windowLaw q) = 0 ↔ ∀ i, p i = q i := by
  classical
  have hac (i : ι) : ∀ a, q i a = 0 → p i a = 0 := fun a h =>
    absurd h (ne_of_gt (hqpos i a))
  have hterm (i : ι) : 0 ≤ klDivergence (p i) (q i) :=
    kl_divergence_nonneg (p i) (q i) ⟨hpnn i, hp i⟩ ⟨hqnn i, hq i⟩ (hac i)
  rw [klDivergence_windowLaw p q hp hppos hqpos]
  constructor
  · intro hzero i
    exact (kl_divergence_eq_zero_iff (p i) (q i) ⟨hpnn i, hp i⟩ ⟨hqnn i, hq i⟩ (hac i)).mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hzero i (Finset.mem_univ i))
  · intro heq
    exact Finset.sum_eq_zero fun i _ =>
      (kl_divergence_eq_zero_iff (p i) (q i) ⟨hpnn i, hp i⟩ ⟨hqnn i, hq i⟩
        (hac i)).mpr (heq i)

/-- **Green-class window divergence.** -/
theorem klDivergence_greenClass_window {O : Type*} [Fintype O] [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ ν : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] (S : Finset ℕ)
    (hμpos : ∀ i a, 0 < coordLaw μ i a) (hνpos : ∀ i a, 0 < coordLaw ν i a) :
    klDivergence (windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1))
        (windowLaw (fun i : (S : Finset ℕ) => coordLaw ν i.1)) =
      ∑ i ∈ S, klDivergence (coordLaw μ i) (coordLaw ν i) := by
  classical
  rw [klDivergence_windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1)
      (fun i : (S : Finset ℕ) => coordLaw ν i.1)
      (fun i => coordLaw_sum_eq_one μ i.1) (fun i a => hμpos i.1 a) (fun i a => hνpos i.1 a),
    ← Finset.sum_coe_sort S (fun i => klDivergence (coordLaw μ i) (coordLaw ν i))]

end

end D5.S3.Entropy.NamingWindow.GreenClassWindowDivergence

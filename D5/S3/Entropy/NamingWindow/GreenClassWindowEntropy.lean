/- GID: D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/NamingWindow/GreenClassWindowEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove window entropy; uniform attains the bound, while Gibbs uniqueness is excluded. -/

import D5.S3.Entropy.MaxEntropy
import D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure

namespace D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy

open MeasureTheory Measure Finset
open scoped ENNReal
open D5.S3.Entropy.MaxEntropy
open D5.S0.Naming.GreenClassMeasure
open D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

noncomputable section

/-- The window law of a coordinate family: the product mass function on window assignments. -/
noncomputable def windowLaw {ι O : Type*} [Fintype ι]
    (p : ι → O → ℝ) (u : ι → O) : ℝ :=
  ∏ i, p i (u i)

/-- The per-coordinate real mass function read off a family of alphabet measures. -/
noncomputable def coordLaw {O : Type*} [MeasurableSpace O] (μ : ℕ → Measure O)
    (i : ℕ) (a : O) : ℝ :=
  (μ i {a}).toReal

private theorem negMulLog_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    Real.negMulLog (∏ i, x i) =
      ∑ i, (∏ j ∈ Finset.univ.erase i, x j) * Real.negMulLog (x i) := by
  classical
  by_cases hz : ∃ k, x k = 0
  · obtain ⟨k, hk⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hk, Real.negMulLog_zero]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    by_cases hik : i = k
    · subst hik; rw [hk, Real.negMulLog_zero, mul_zero]
    · rw [Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨fun h => hik h.symm, Finset.mem_univ k⟩) hk, zero_mul]
  · replace hz : ∀ k, x k ≠ 0 := not_exists.mp hz
    simp only [Real.negMulLog]
    rw [Real.log_prod (fun i _ => hz i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_prod_erase _ x (Finset.mem_univ i)]
    ring

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

/-- Normalisation: a window law of normalised coordinate laws is normalised. -/
theorem windowLaw_sum_eq_one {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p : ι → O → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ u : ι → O, windowLaw p u = 1 := by
  classical
  rw [show (∑ u : ι → O, windowLaw p u) = ∑ u : ι → O, ∏ i, p i (u i) from rfl,
    ← Fintype.prod_sum p]
  exact Finset.prod_eq_one fun i _ => hp i

/-- **Window entropy additivity.** -/
theorem shannonEntropy_windowLaw {ι O : Type*} [Fintype ι] [DecidableEq ι] [Fintype O]
    (p : ι → O → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    shannonEntropy (windowLaw p) = ∑ i, shannonEntropy (p i) := by
  classical
  rw [shannonEntropy]
  calc
    (∑ u : ι → O, Real.negMulLog (windowLaw p u)) =
        ∑ u : ι → O, ∑ i, (∏ j ∈ Finset.univ.erase i, p j (u j)) *
          Real.negMulLog (p i (u i)) :=
      Finset.sum_congr rfl fun u _ => negMulLog_prod (fun i => p i (u i))
    _ = ∑ i, ∑ u : ι → O, (∏ j ∈ Finset.univ.erase i, p j (u j)) *
          Real.negMulLog (p i (u i)) := Finset.sum_comm
    _ = ∑ i, (∏ j ∈ Finset.univ.erase i, ∑ a, p j a) *
          ∑ a, Real.negMulLog (p i a) :=
      Finset.sum_congr rfl fun i _ => sum_prod_update p i (fun a => Real.negMulLog (p i a))
    _ = ∑ i, shannonEntropy (p i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_congr rfl fun j _ => hp j, Finset.prod_const_one, one_mul, shannonEntropy]

/-- **Green-class mass is the window law of the pinned content.** -/
theorem greenClass_toReal_eq_windowLaw {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ℕ) (t : ℕ → O) :
    ((Measure.infinitePi μ) (greenClass S t)).toReal =
      windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1) (fun i => t i.1) := by
  rw [D5.S0.Asymptotics.MetricGeometry.VaryingMarginalGreenClassMeasure.varying_greenClass_measure,
    ENNReal.toReal_prod, windowLaw]
  exact (Finset.prod_coe_sort S (fun i => coordLaw μ i (t i))).symm

/-- Each coordinate law of a probability family is normalised. -/
private theorem coordLaw_sum_eq_one {O : Type*} [Fintype O] [MeasurableSpace O]
    [MeasurableSingletonClass O] (μ : ℕ → Measure O) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ℕ) : ∑ a, coordLaw μ i a = 1 := by
  simp only [coordLaw]
  rw [show (∑ a, (μ i {a}).toReal) = (∑ a, μ i {a}).toReal from
    (ENNReal.toReal_sum fun a _ => measure_ne_top _ _).symm]
  rw [MeasureTheory.sum_measure_singleton]
  simp

/-- Natural logarithm of the alphabet size in terms of the naming dimension. -/
private theorem log_card_eq_namingDim {O : Type*} [Fintype O] :
    Real.log (Fintype.card O) = namingDim O * Real.log 2 := by
  rw [namingDim, Real.logb, div_mul_cancel₀]
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

/-- **Naming dimension bounds green-class window entropy.** -/
theorem shannonEntropy_windowLaw_le_namingDim {O : Type*} [Fintype O] [Nonempty O]
    [MeasurableSpace O] [MeasurableSingletonClass O] (μ : ℕ → Measure O)
    [∀ i, IsProbabilityMeasure (μ i)] (S : Finset ℕ) :
    shannonEntropy (windowLaw (fun i : (S : Finset ℕ) => coordLaw μ i.1)) ≤
      S.card * (namingDim O * Real.log 2) := by
  classical
  rw [shannonEntropy_windowLaw (fun i : (S : Finset ℕ) => coordLaw μ ↑i)
      (fun i => coordLaw_sum_eq_one μ ↑i), ← log_card_eq_namingDim]
  calc
    (∑ i : (S : Finset ℕ), shannonEntropy (coordLaw μ i.1)) ≤
        ∑ _i : (S : Finset ℕ), Real.log (Fintype.card O) :=
      Finset.sum_le_sum fun i _ =>
        entropy_le_log_card _ ⟨fun a => ENNReal.toReal_nonneg, coordLaw_sum_eq_one μ i.1⟩
    _ = S.card * Real.log (Fintype.card O) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- The uniform family attains the naming-dimension bound. -/
theorem shannonEntropy_uniform_windowLaw {O : Type*} [Fintype O] [Nonempty O]
    [MeasurableSpace O] [MeasurableSingletonClass O] (S : Finset ℕ) :
    shannonEntropy
        (windowLaw (fun _i : (S : Finset ℕ) => coordLaw (fun _ => uniformAlphabet O) 0)) =
      S.card * (namingDim O * Real.log 2) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card O := by exact_mod_cast Fintype.card_pos
  have hcoord : coordLaw (fun _ : ℕ => uniformAlphabet O) 0 =
      fun _ => (Fintype.card O : ℝ)⁻¹ := by
    funext a
    rw [coordLaw, uniformAlphabet_singleton]
    simp
  have hone : ∀ _i : (S : Finset ℕ),
      ∑ a, coordLaw (fun _ : ℕ => uniformAlphabet O) 0 a = 1 := by
    intro _i
    exact coordLaw_sum_eq_one (fun _ => uniformAlphabet O) 0
  rw [shannonEntropy_windowLaw
      (fun _i : (S : Finset ℕ) => coordLaw (fun _ : ℕ => uniformAlphabet O) 0) hone,
    ← log_card_eq_namingDim]
  have hent : shannonEntropy (coordLaw (fun _ : ℕ => uniformAlphabet O) 0) =
      Real.log (Fintype.card O) := by
    rw [hcoord, shannonEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Real.negMulLog, Real.log_inv]
    field_simp
  rw [Finset.sum_congr rfl fun _i _ => hent, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]

end

end D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy

/- GID: D5/S3/ContinuousObservables/C0Multipliers
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/C0Multipliers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.Multiplier, mathlib/module/Mathlib.Topology.ContinuousMap.ZeroAtInfty, mathlib/module/Mathlib.Topology.UrysohnsLemma]
   utility: none
   digest: Double centralizers of continuous fields vanishing at infinity are bounded continuous fields with their pointwise left and right actions. -/

import Mathlib.Analysis.CStarAlgebra.Multiplier
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FunProp

/-! # Multipliers of fields vanishing at infinity

Local unit sections recover a matrix field from the two centralizer actions.
The recovered field is continuous, bounded, and has exactly the multiplier norm.
-/

noncomputable section

open Filter Set
open scoped Topology ZeroAtInfty BoundedContinuousFunction

namespace D5.S3.ContinuousObservables.C0Multipliers

variable {X B : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [CStarAlgebra B] [Nontrivial B]

private theorem local_unit (K : Set X) (hK : IsCompact K) :
    ∃ e : C₀(X, B), ‖e‖ ≤ 1 ∧ ∀ x ∈ K, e x = 1 := by
  obtain ⟨c, hcK, _, hcs, hc⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let e : C₀(X, B) :=
    { toFun := fun x => (c x : ℂ) • (1 : B)
      continuous_toFun := by fun_prop
      zero_at_infty' := by
        have hs : HasCompactSupport (fun x => (c x : ℂ)) :=
          hcs.comp_left (by simp)
        exact (hs.smul_right (f' := fun _ => (1 : B))).is_zero_at_infty }
  refine ⟨e, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).2
    intro x
    change ‖(c x : ℂ) • (1 : B)‖ ≤ 1
    simpa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc x).1]
      using (hc x).2
  · intro x hx
    change (c x : ℂ) • (1 : B) = 1
    rw [show c x = 1 from hcK hx]
    simp

private def pointUnit (x : X) : C₀(X, B) :=
  (local_unit (B := B) {x} isCompact_singleton).choose

private theorem pointUnit_spec (x : X) :
    ‖pointUnit (B := B) x‖ ≤ 1 ∧ pointUnit (B := B) x x = 1 := by
  have h := (local_unit (B := B) {x} isCompact_singleton).choose_spec
  exact ⟨h.1, h.2 x (mem_singleton x)⟩

private def field (m : DoubleCentralizer ℂ C₀(X, B)) (x : X) : B :=
  m.fst (pointUnit x) x

private theorem actions (m : DoubleCentralizer ℂ C₀(X, B)) (f : C₀(X, B)) (x : X) :
    m.fst f x = field m x * f x ∧ m.snd f x = f x * field m x := by
  have he := (pointUnit_spec (B := B) x).2
  have heq := congrArg (fun g : C₀(X, B) => g x) (m.central (pointUnit x) (pointUnit x))
  change m.snd (pointUnit x) x * pointUnit x x =
    pointUnit x x * m.fst (pointUnit x) x at heq
  rw [he, mul_one, one_mul] at heq
  constructor
  · have h := congrArg (fun g : C₀(X, B) => g x) (m.central (pointUnit x) f)
    change m.snd (pointUnit x) x * f x = pointUnit x x * m.fst f x at h
    simpa [he, heq, field] using h.symm
  · have h := congrArg (fun g : C₀(X, B) => g x) (m.central f (pointUnit x))
    change m.snd f x * pointUnit x x = f x * m.fst (pointUnit x) x at h
    simpa [he, field] using h

private theorem field_continuous (m : DoubleCentralizer ℂ C₀(X, B)) :
    Continuous (field m) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨e, _, he⟩ := local_unit (B := B) K hK
  apply (map_continuous (m.fst e)).continuousAt.congr
  filter_upwards [hKx] with y hy
  simpa [he y hy] using (actions m e y).1.symm

private theorem field_bound (m : DoubleCentralizer ℂ C₀(X, B)) (x : X) :
    ‖field m x‖ ≤ ‖m‖ := by
  calc
    ‖field m x‖ ≤ ‖m.fst (pointUnit x)‖ :=
      (m.fst (pointUnit x)).toBCF.norm_coe_le_norm x
    _ ≤ ‖m.fst‖ * ‖pointUnit (B := B) x‖ := m.fst.le_opNorm _
    _ ≤ ‖m‖ * 1 := by
      rw [DoubleCentralizer.norm_fst]
      exact mul_le_mul_of_nonneg_left (pointUnit_spec x).1 (norm_nonneg _)
    _ = ‖m‖ := mul_one _

private def boundedField (m : DoubleCentralizer ℂ C₀(X, B)) : X →ᵇ B :=
  BoundedContinuousFunction.mkOfBound ⟨field m, field_continuous m⟩ (2 * ‖m‖)
    (fun x y => (dist_le_norm_add_norm _ _).trans <| by
      linarith [field_bound m x, field_bound m y])

private def leftProduct (h : X →ᵇ B) (f : C₀(X, B)) : C₀(X, B) where
  toFun x := h x * f x
  continuous_toFun := h.continuous.mul (map_continuous f)
  zero_at_infty' := Filter.isBoundedUnder_le_mul_tendsto_zero
    ⟨‖h‖, Filter.Eventually.of_forall h.norm_coe_le_norm⟩ (zero_at_infty f)

private def rightProduct (h : X →ᵇ B) (f : C₀(X, B)) : C₀(X, B) where
  toFun x := f x * h x
  continuous_toFun := (map_continuous f).mul h.continuous
  zero_at_infty' := (zero_at_infty f).zero_mul_isBoundedUnder_le
    ⟨‖h‖, Filter.Eventually.of_forall h.norm_coe_le_norm⟩

private def leftOperator (h : X →ᵇ B) : C₀(X, B) →L[ℂ] C₀(X, B) :=
  LinearMap.mkContinuous
    { toFun := leftProduct h
      map_add' := fun f g => ZeroAtInftyContinuousMap.ext fun x => mul_add _ _ _
      map_smul' := fun c f => ZeroAtInftyContinuousMap.ext fun x => mul_smul_comm _ _ _ }
    ‖h‖ (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      exact (norm_mul_le _ _).trans (mul_le_mul (h.norm_coe_le_norm x)
        (f.toBCF.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

private def rightOperator (h : X →ᵇ B) : C₀(X, B) →L[ℂ] C₀(X, B) :=
  LinearMap.mkContinuous
    { toFun := rightProduct h
      map_add' := fun f g => ZeroAtInftyContinuousMap.ext fun x => add_mul _ _ _
      map_smul' := fun c f => ZeroAtInftyContinuousMap.ext fun x => smul_mul_assoc _ _ _ }
    ‖h‖ (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      exact (norm_mul_le _ _).trans ((mul_le_mul (f.toBCF.norm_coe_le_norm x)
        (h.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)))

/-- A bounded continuous field acts on every element vanishing at infinity. -/
def multiplier (h : X →ᵇ B) : DoubleCentralizer ℂ C₀(X, B) where
  fst := leftOperator h
  snd := rightOperator h
  central f g := ZeroAtInftyContinuousMap.ext fun x => mul_assoc _ _ _

/-- Every double centralizer is represented by a unique bounded continuous field,
with both actions on the whole complex algebra and the exact uniform norm. -/
theorem representation (m : DoubleCentralizer ℂ C₀(X, B)) :
    ∃! h : X →ᵇ B, (∀ (f : C₀(X, B)) (x : X),
      m.fst f x = h x * f x ∧ m.snd f x = f x * h x) ∧ ‖h‖ = ‖m‖ := by
  refine ⟨boundedField m, ⟨fun f x => actions m f x, ?_⟩, ?_⟩
  · apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 (field_bound m)
    · rw [← DoubleCentralizer.norm_fst]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro f
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
      intro x
      rw [(actions m f x).1]
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((boundedField m).norm_coe_le_norm x) (f.toBCF.norm_coe_le_norm x)
        (norm_nonneg _) (norm_nonneg _))
  · intro h hh
    apply BoundedContinuousFunction.ext
    intro x
    have hv := (hh.1 (pointUnit x) x).1
    simpa [field, boundedField, (pointUnit_spec (B := B) x).2] using hv.symm

end D5.S3.ContinuousObservables.C0Multipliers

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-readout registration for the actual supported inverse-square-root estimate. -/

noncomputable section
universe u v
open Matrix MeasureTheory
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

/-- Observe the actual inequality, retaining both real operands. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (m : ℝ) (_hm : 0 < m),
    let M := supported_relative_modular_model Φ ρ σ support
    m • 1 ≤ M.data.A → m • 1 ≤ M.data.B →
    let d := cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.A *ᵥ M.data.ξ -
      M.data.V *ᵥ (cfc (fun x : ℝ => 1 / Real.sqrt x) M.data.B *ᵥ M.data.η)
    R.readout () () (Real.sqrt (star d ⬝ᵥ d).re)
      (4 / (Real.pi * Real.sqrt m) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) ^ (1 / 4 : ℝ))

theorem positive_floor {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ r : ℝ, 0 < r ∧ r • (1 : Matrix n n ℂ) ≤ A := by
  classical
  by_cases hn : Nonempty n
  · letI := hn
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff A hA.1.isSelfAdjoint).2 (by
      intro x hx
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hA.eigenvalues_pos i)
    exact ⟨r, hr, by simpa only [Algebra.algebraMap_eq_smul_one] using hle⟩
  · letI : IsEmpty n := not_nonempty_iff.mp hn
    exact ⟨1, zero_lt_one, le_of_eq (Subsingleton.elim _ _)⟩

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let ρ : DensityState a := ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag, CStarMatrix.one_apply_eq]⟩
  let Φ : QuantumChannel a b := {
    toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b))
    trace_preserving := by
      intro X
      change Matrix.trace (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b) X) = Matrix.trace X
      simp [Matrix.trace, Matrix.diag, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
        Matrix.submatrix_apply]
      change X ((Equiv.ofUnique a b).symm default) ((Equiv.ofUnique a b).symm default) =
        X default default
      simp only [Subsingleton.elim ((Equiv.ofUnique a b).symm default) (default : a)] }
  let M := supported_relative_modular_model Φ ρ ρ (supportContained_refl ρ)
  obtain ⟨r, hr, hAr⟩ := positive_floor M.data.A M.hA
  obtain ⟨s, hs, hBs⟩ := positive_floor M.data.B M.hB
  have hmin : 0 < min r s := lt_min hr hs
  have hAf : min r s • (1 : Matrix (M.data.J × M.data.I) _ ℂ) ≤ M.data.A :=
    (smul_le_smul_of_nonneg_right (min_le_left r s) zero_le_one).trans hAr
  have hBf : min r s • (1 : Matrix (M.data.L × M.data.K) _ ℂ) ≤ M.data.B :=
    (smul_le_smul_of_nonneg_right (min_le_right r s) zero_le_one).trans hBs
  exact @h a b inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance Φ ρ ρ (supportContained_refl ρ) (min r s) hmin hAf hBf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v}
    (type_of% @entropy_defect_inverse_sqrt_stability.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_defect_inverse_sqrt_stability, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_defect_inverse_sqrt_stability.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.entropy_defect_inverse_sqrt_stability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.NormSq

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] (x : n → ℂ),
    R.readout () () (‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2) (star x ⬝ᵥ x).re

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance (fun _ => 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u} (type_of% @l2_norm_sq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@l2_norm_sq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@l2_norm_sq.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.l2_norm_sq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.NormSq.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.NormSq

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.Contraction

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {k : Type v} [Fintype n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℂ) (_hV : Vᴴ * V ≤ 1) (x : k → ℂ),
    R.readout () () (‖(WithLp.toLp 2 (V *ᵥ x) : EuclideanSpace ℂ n)‖)
      (‖(WithLp.toLp 2 x : EuclideanSpace ℂ k)‖)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance inferInstance
    0 (by simp) (fun _ => 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @l2_contraction.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@l2_contraction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@l2_contraction.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.l2_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.Contraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.Contraction

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.ResolventBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (_hA : A.PosDef) (m : ℝ) (_hm : 0 < m)
    (_hfloor : m • (1 : Matrix n n ℂ) ≤ A) (x : n → ℂ) (t : ℝ) (_ht : 0 < t),
    R.readout () () (‖(WithLp.toLp 2 ((A + t • 1)⁻¹ *ᵥ x) : EuclideanSpace ℂ n)‖)
      (‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ / m)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 1 Matrix.PosDef.one 1 zero_lt_one
    (by simp) (fun _ => 0) 1 zero_lt_one

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [actual, realize] at h

def family : Registration arena.{u} (type_of% @l2_resolvent_bound.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@l2_resolvent_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@l2_resolvent_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.l2_resolvent_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.ResolventBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.ResolventBound

namespace Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.PowerIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ p q => p ∧ q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {k : Type v} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (alpha : ℝ) (_halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (A : Matrix n n ℂ) (B : Matrix k k ℂ) (_hA : A.PosDef) (_hB : B.PosDef)
    (V : Matrix n k ℂ) (ξ : n → ℂ) (η : k → ℂ),
    let w : ℝ → EuclideanSpace ℂ n := fun t => WithLp.toLp 2
      ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η))
    R.readout () () (MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-alpha) • w t) (Set.Ioi 0))
      ((Real.sin (Real.pi * alpha) / Real.pi) •
        (∫ t in Set.Ioi (0 : ℝ), t ^ (-alpha) • w t) =
        WithLp.toLp 2 (cfc (fun x : ℝ => x ^ (-alpha)) A *ᵥ ξ -
          V *ᵥ (cfc (fun x : ℝ => x ^ (-alpha)) B *ᵥ η)))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance inferInstance
    inferInstance (1 / 2) (by norm_num) 1 1 Matrix.PosDef.one Matrix.PosDef.one
      0 (fun _ => 0) (fun _ => 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), True, False, ?_⟩
  intro he
  have h := congrFun he True
  simp [actual, realize] at h

def family : Registration arena.{u,v} (type_of% @l2_inverse_power_integral.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@l2_inverse_power_integral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@l2_inverse_power_integral.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.l2_inverse_power_integral.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.PowerIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p q => p ∧ q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability.PowerIntegral

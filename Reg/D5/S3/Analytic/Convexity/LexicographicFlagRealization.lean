import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.LexicographicFlagRealization
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

open _root_.D5.S3.Analytic.Convexity.LexicographicFlagRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module Set Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization
universe u v

@[reducible] def signature : Signature where
  Params := Σ V : Type u, Σ r : ℕ, Fin r → V
  State p := Fin p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p k => p.2.2 k) (fun e => nomatch e)

def rejected : Realization signature.{u} := by
  classical
  exact realize signature (fun _ p k =>
    if h : p.1 = EuclideanSpace ℝ (ULift.{u} (Fin 2)) then
      cast h.symm (EuclideanSpace.single (ULift.up 1) (1 : ℝ))
    else p.2.2 k) (fun e => nomatch e)

@[reducible] def coreArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {I : Type v} [FiniteDimensional ℝ V] (a : I → V), FiniteFeasible a →
    ∃ (r : ℕ) (w : Fin r → V), r ≤ finrank ℝ (Submodule.span ℝ (Set.range a)) ∧
      Orthonormal ℝ w ∧
      (∀ k, R.readout () ⟨V, r, w⟩ k ∈ Submodule.span ℝ (Set.range a)) ∧ LexWitness a w

private theorem core_actual : coreArena.{u,v}.Law actual := orthonormal_realization

private theorem core_rejected : ¬ coreArena.{u,v}.Law rejected := by
  classical
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 2))
  let e₀ : E := EuclideanSpace.single (ULift.up 0) 1
  let e₁ : E := EuclideanSpace.single (ULift.up 1) 1
  let a : ULift.{v} Unit → E := fun _ => e₀
  have ha : FiniteFeasible a := by
    intro F
    refine ⟨e₀, ?_⟩
    intro i _
    simp [E, a, e₀, EuclideanSpace.single, PiLp.norm_single]
  obtain ⟨r, w, _, _, hW, hlex⟩ := h a ha
  obtain ⟨k, _, _⟩ := hlex (ULift.up ())
  have hmem : e₁ ∈ Submodule.span ℝ ({e₀} : Set E) := by
    simpa [rejected, realize, E, a, e₁] using hW k
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have heq := congrArg (fun x : E => x (ULift.up 1)) hc
  simp [E, e₀, e₁, EuclideanSpace.single, PiLp.smul_apply] at heq

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _i
  let E := EuclideanSpace ℝ (ULift.{u} (Fin 2))
  let e₀ : E := EuclideanSpace.single (ULift.up 0) 1
  let e₁ : E := EuclideanSpace.single (ULift.up 1) 1
  refine ⟨⟨E, 2, ![e₀, e₁]⟩, 0, 1, ?_⟩
  intro h
  change e₀ = e₁ at h
  have heq := congrArg (fun x : E => x (ULift.up 0)) h
  simp [E, e₀, e₁, EuclideanSpace.single] at heq

def coreRegistration : Registration coreArena.{u,v} (coreArena.{u,v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨core_actual, rejected, core_rejected⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, core_rejected⟩,
    fun i => nomatch i⟩
  dependence := actual_dependence

@[reducible] def fullArena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {I : Type v} [FiniteDimensional ℝ V] (ℓ : I → V →ₗ[ℝ] ℝ),
    let a := fun i => (InnerProductSpace.toDual ℝ V).symm (ℓ i).toContinuousLinearMap
    (∀ i x, ⟪a i, x⟫_ℝ = ℓ i x) ∧
    ((∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ℓ i x) ↔
      ∃ (r : ℕ) (v : Fin r → V),
        ∀ i, ∃ k, 0 < ℓ i (v k) ∧ ∀ j < k, ℓ i (v j) = 0) ∧
    ((∃ (r : ℕ) (v : Fin r → V),
        ∀ i, ∃ k, 0 < ℓ i (v k) ∧ ∀ j < k, ℓ i (v j) = 0) ↔
      ∃ (q : ℕ) (v : Fin q → V), ∀ i, ∃ ε : ℝ, 0 < ε ∧
        ∀ t, 0 < t → t < ε → 0 < ℓ i (curve v t)) ∧
    ((∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ℓ i x) →
      ∃ (r : ℕ) (v : Fin r → V),
        r ≤ finrank ℝ (Submodule.span ℝ (Set.range a)) ∧
        finrank ℝ (Submodule.span ℝ (Set.range a)) ≤ finrank ℝ V ∧
        Orthonormal ℝ v ∧ (∀ k, R.readout () ⟨V, r, v⟩ k ∈ Submodule.span ℝ (Set.range a)) ∧
        (∀ i, ∃ k, 0 < ℓ i (v k) ∧ ∀ j < k, ℓ i (v j) = 0) ∧
        (∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε → 0 < ℓ i (curve v t)) ∧
        Tendsto (curve v) (𝓝 0) (𝓝 0) ∧ (Nonempty I → 1 ≤ r)) ∧
    ((∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ℓ i x) →
      ∃ d : ℕ,
        IsLeast {r | ∃ v : Fin r → V,
          ∀ i, ∃ k, 0 < ℓ i (v k) ∧ ∀ j < k, ℓ i (v j) = 0} d ∧
        IsLeast {q | ∃ p : PolynomialModule ℝ V, polynomialDegree p = q ∧
          p.coeff 0 = 0 ∧ ∀ i, ∃ ε : ℝ, 0 < ε ∧
            ∀ t, 0 < t → t < ε → 0 < ℓ i (PolynomialModule.eval t p)} d) ∧
    (IsEmpty I → finrank ℝ (Submodule.span ℝ (Set.range a)) = 0 ∧
      FiniteFeasible a ∧ LexWitness a (Fin.elim0 : Fin 0 → V) ∧
      (∀ t, curve (Fin.elim0 : Fin 0 → V) t = 0) ∧
      PolynomialFeasible a 0 ∧ polynomialDegree (0 : PolynomialModule ℝ V) = 0)

private theorem full_actual : fullArena.{u,v}.Law actual := linear_form_realization

private theorem full_rejected : ¬ fullArena.{u,v}.Law rejected := by
  intro h
  apply core_rejected
  intro V _ _ I _ a ha
  let ℓ : I → V →ₗ[ℝ] ℝ := fun i => (InnerProductSpace.toDual ℝ V (a i)).toLinearMap
  have hℓ (i : I) : (ℓ i).toContinuousLinearMap = InnerProductSpace.toDual ℝ V (a i) := by
    ext x
    rfl
  have hrep : (fun i => (InnerProductSpace.toDual ℝ V).symm (ℓ i).toContinuousLinearMap) = a := by
    funext i
    rw [hℓ, LinearIsometryEquiv.symm_apply_apply]
  have hf : ∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ℓ i x := ha
  obtain ⟨r, w, hr, _, hw, hW, hlex, _⟩ := (h ℓ).2.2.2.1 hf
  exact ⟨r, w, hrep ▸ hr, hw, hrep ▸ hW, hlex⟩

def fullRegistration : Registration fullArena.{u,v} (fullArena.{u,v}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_actual, rejected, full_rejected⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, full_rejected⟩,
    fun i => nomatch i⟩
  dependence := actual_dependence

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Analytic.Convexity.LexicographicFlagRealization.orthonormal_realization.{u,v})
      (type_of% (realize signature.{u} (fun _ p k => p.2.2 k) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization.core_membership_unit
  realizationName := `Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization.coreRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨coreArena.{u,v}⟩
  objectArena := .source ⟨coreArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coreArena.{u,v} ⟨coreRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p k => p.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.LexicographicFlagRealization
    definition := none
    coordinates := #[0, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "arg", "body", "arg", "arg", "fn", "arg", "body",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def registration_2 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Analytic.Convexity.LexicographicFlagRealization.linear_form_realization.{u,v})
      (type_of% (realize signature.{u} (fun _ p k => p.2.2 k) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization.full_membership_unit
  realizationName := `Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization.fullRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨fullArena.{u,v}⟩
  objectArena := .source ⟨fullArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullArena.{u,v} ⟨fullRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p k => p.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.LexicographicFlagRealization
    definition := none
    coordinates := #[0, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "arg", "fn", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Analytic.Convexity.LexicographicFlagRealization

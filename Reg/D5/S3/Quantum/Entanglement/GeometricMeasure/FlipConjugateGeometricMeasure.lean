import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
import Reg.Support.DependentFamily

/-! Source-bound audit of the flip-conjugate subspaces' geometric measure. -/

namespace Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure

open _root_.D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the geometric measure on the full state space at each dimension. -/
abbrev signature : Signature where
  Params := ℕ
  State d := State d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => G ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve both subspaces, unit normalization, and the complete sharp equality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ), 2 ≤ d → ∀ ψ : State d,
    UnitVector ψ → ψ ∈ H_I d ∨ ψ ∈ H_Ibar d →
      r.readout () d ψ = 1 - sharpValue d

private theorem basis_nonzero : WithLp.toLp 2 (φ 2 0) ≠ 0 := by
  intro h
  have hc := congrArg (fun v : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) =>
    v (0, 0, 0)) h
  have hz : conj (z 2) + z 2 = 1 := by
    norm_num [z, map_div₀, map_add, map_mul, map_ofNat]
    ring
  have hentry : φ 2 0 (0, 0, 0) = 1 / (Real.sqrt 3 : ℂ) := by
    norm_num [φ, hz]
  change φ 2 0 (0, 0, 0) = 0 at hc
  rw [hentry] at hc
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  exact (div_ne_zero one_ne_zero hs) hc

private def witness : State 2 :=
  (‖WithLp.toLp 2 (φ 2 0)‖⁻¹ : ℂ) • φ 2 0

private theorem witness_unit : UnitVector witness := by
  unfold UnitVector witness
  rw [WithLp.toLp_smul]
  exact norm_smul_inv_norm (𝕜 := ℂ) basis_nonzero

private theorem witness_mem : witness ∈ H_I 2 := by
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

private theorem zero_measure : G (0 : State 2) = 1 := by
  have he : UnitVector (fun i : Fin 2 => (EuclideanSpace.single 0 (1 : ℂ)) i) := by
    change ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1
    simp
  have hset : overlapSet (0 : State 2) = {0} := by
    ext t
    constructor
    · rintro ⟨a, b, c, _, _, _, ht⟩
      simpa [overlap] using ht
    · intro ht
      have ht0 : t = 0 := Set.mem_singleton_iff.mp ht
      subst t
      exact ⟨_, _, _, he, he, he, by simp [overlap]⟩
  simp [G, hset]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by decide) witness witness_unit (Or.inl witness_mem)
  change (0 : ℝ) = 1 - sharpValue 2 at hbad
  norm_num [sharpValue] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, witness, ?_⟩
  change G (0 : State 2) ≠ G witness
  rw [zero_measure, result 2 (by decide) witness witness_unit (Or.inl witness_mem)]
  norm_num [sharpValue]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ψ => G ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure
      name := `D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.GeometricMeasure.FlipConjugateGeometricMeasure

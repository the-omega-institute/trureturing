import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.EffectProbabilityExtension
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Foundation.EffectProbabilityExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Foundation.EffectProbabilityExtension
universe u

abbrev signature : Signature where
  Params := Type u
  State d := (CStarMatrix d d ℂ → ℝ) × CStarMatrix d d ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (p : CStarMatrix d d ℂ → ℝ)
    (hpos : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E)
    (hadd : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E + F) = p E + p F)
    (hnorm : p 1 = 1),
    ∃! ρ : Matrix d d ℂ, ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
      ∀ E : CStarMatrix d d ℂ, 0 ≤ E → E ≤ 1 →
        Matrix.trace (ρ * CStarMatrix.ofMatrix.symm E) = (r.readout () d (p,E) : ℂ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let q : d := ⟨0⟩
  let p (E : CStarMatrix d d ℂ) : ℝ := (E q q).re
  have hp : ∀ E, 0 ≤ E → E ≤ 1 → 0 ≤ p E := by
    intro E hE _
    have hs : (CStarMatrix.ofMatrix.symm E).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hE)
    exact (Complex.nonneg_iff.mp (hs.diag_nonneg (i := q))).1
  have ha : ∀ E F, 0 ≤ E → 0 ≤ F → E + F ≤ 1 → p (E+F) = p E + p F := by
    intro E F _ _ _
    change (E q q + F q q).re = _
    simp [p]
  have hn : p 1 = 1 := by simp [p]
  obtain ⟨ρ, ⟨_, ht, he⟩, _⟩ := h p hp ha hn
  have hz := he 1 zero_le_one le_rfl
  change Matrix.trace (ρ * 1) = (0 : ℂ) at hz
  simpa [ht] using hz

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let d := ULift.{u} (Fin 1)
  let q : d := ⟨0⟩
  let p (E : CStarMatrix d d ℂ) : ℝ := (E q q).re
  refine ⟨d, (p, 0), (p, 1), ?_⟩
  change p 0 ≠ p 1
  simp [p]

def registration : Registration arena.{u} (type_of% @effect_density_representation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨effect_density_representation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Foundation.EffectProbabilityExtension.effect_density_representation.{u})
    (type_of% (realize signature.{u} (fun _ _ x => x.1 x.2) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Foundation.EffectProbabilityExtension.effect_density_representation.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Foundation.EffectProbabilityExtension.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ _ x => x.1 x.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.EffectProbabilityExtension,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "body", "body", "arg", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
#print axioms registration_1
end Reg.D5.S3.Quantum.Foundation.EffectProbabilityExtension

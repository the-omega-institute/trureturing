import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

/-! The equivalence compares prescribed masses with the same masses in orbit coordinates. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

open _root_.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

universe g t i

noncomputable section

abbrev signature : Signature.{i + 1, i, 0, i, 0} where
  Params := Type i
  State I := I → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := I → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{i} :=
  realize signature (fun _ _ m => m) (fun e => nomatch e)

def rejected : Realization signature.{i} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

local instance {G : Type g} {T : Type t} [Group G] [MulAction G T] [Fintype T] :
    Fintype (MulAction.orbitRel.Quotient G T) := Fintype.ofFinite _

abbrev arena : Arena where
  signature := signature.{i}
  Law R :=
    ∀ {G : Type g} {T : Type t} {I : Type i} [Group G] [MulAction G T] [Fintype T]
      (event : I → Finset T) (mass : I → ℝ),
      (∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
        (∀ (g : G) t, p (g • t) = p t) ∧ ∀ j, (∑ t ∈ event j, p t) = mass j) ↔
      (∃ z : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
        ∀ j, (∑ o, z o * orbitFrequency (event j) o) = R.readout () I mass j)

private theorem rejected_law : ¬ arena.{g,t,i}.Law rejected := by
  classical
  intro altered
  let G := PUnit.{g+1}
  let T := PUnit.{t+1}
  let I := PUnit.{i+1}
  let event (_ : I) : Finset T := univ
  let mass (_ : I) : ℝ := 1
  obtain ⟨z, _, total, prescribed⟩ := (altered (G := G) event mass).mp
    ⟨fun _ => 1, fun _ => zero_le_one, by simp, fun _ _ => rfl, fun _ => by simp [event, mass]⟩
  have full (o : MulAction.orbitRel.Quotient G T) :
      orbitFrequency (G := G) (univ : Finset T) o = 1 := by
    unfold orbitFrequency
    simp
    exact Subsingleton.elim _ _
  have zero := prescribed (PUnit.unit : I)
  change (∑ o, z o * orbitFrequency (G := G) (univ : Finset T) o) = 0 at zero
  simp only [full, mul_one, total] at zero
  exact one_ne_zero zero

def family : Registration arena.{g,t,i} (type_of% (@invariant_event_masses_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@invariant_event_masses_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨PUnit.{i+1}, fun _ => 0, fun _ => 1, ?_⟩
    intro equal
    exact zero_ne_one (congrFun equal PUnit.unit)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@invariant_event_masses_iff) (Realization signature.{i}) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.eventMasses
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{g,t,i}⟩
  objectArena := .source ⟨arena.{g,t,i}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{g,t,i} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.TableOrbitWeights
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

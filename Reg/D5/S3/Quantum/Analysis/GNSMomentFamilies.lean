import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Analysis.GNSMomentFamilies

/-! The source family keeps the full arbitrary-algebra GNS telescope and both
moments. The observed equality is evaluated at every complex function and
every algebra element, with continuous-dual extensionality as the bridge. -/

noncomputable section
open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.GNSMomentFamilies
open _root_.D5.S3.Quantum.Analysis.NormalMomentFamily

universe u
namespace Reg.D5.S3.Quantum.Analysis.GNSMomentFamilies

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ρ σ : StrongDual ℂ A}
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (F : Family ρ σ),
    let ψ := pairFunctional ρ σ hρ hσ
    ∃ Z : C(Interval, ℂ) →ₚ[ℂ] commutant ψ,
      Z 1 = 1 ∧ (∀ g a, R.readout () () (coefficientMap ψ (Z g) a) (linearMap F g a)) ∧
      Z posterior = pairCoordinate ρ σ hρ hσ

private theorem actual_law : arena.{u}.Law actual := by
  intro A _ _ _ ρ σ hρ hσ F
  obtain ⟨Z, hu, he, hc⟩ := exists_lift hρ hσ F
  exact ⟨Z, hu, fun g a => congrArg (fun η : StrongDual ℂ A => η a) (he g), hc⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := PUnit.{u+1} →L[ℂ] PUnit.{u+1}
  let F : Family (0 : StrongDual ℂ A) 0 := ofLinearMap 0
    (by intros; simp) (by simp) (by simp)
  obtain ⟨Z, _, he, _⟩ := h (A := A) (by intros; simp) (by intros; simp) F
  exact he 0 0

def sourceProposition : Prop := type_of% (@exists_lift.{u})

set_option maxHeartbeats 800000 in
-- The bridge retains the actual dependent GNS carriers and continuous duals.
def family : Registration arena.{u} sourceProposition.{u} where
  actual := actual
  bridge := by
    constructor
    · intro h A _ _ _ ρ σ hρ hσ F
      obtain ⟨Z, hu, he, hc⟩ := h hρ hσ F
      exact ⟨Z, hu, fun g a => congrArg (fun η : StrongDual ℂ A => η a) (he g), hc⟩
    · intro h A _ _ _ ρ σ hρ hσ F
      obtain ⟨Z, hu, he, hc⟩ := h hρ hσ F
      refine ⟨Z, hu, ?_, hc⟩
      intro g
      ext a
      exact he g a
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    intro h
    have hf : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
    norm_num at hf

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (P := sourceProposition.{u}) (@exists_lift.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.GNSMomentFamilies.liftUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.GNSMomentFamilies.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Analysis.GNSMomentFamilies

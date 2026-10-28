import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GainRayCompleteCritical
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Linear.GainRayCompleteCritical
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev Answer (d : ℕ) := ∀ w : List Bool, History w → Mat × Polynomial ℝ × ℝ

abbrev signature : Signature where
  Params := (d : ℕ) × Answer d × World d × List Bool
  State p := History p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat × Polynomial ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => p.2.1 p.2.2.2 h) (fun e => nomatch e)

/-- An intervention may expose the actual world, unlike a literal-history answer. -/
def rejected : Realization signature :=
  realize signature (fun _ p _ =>
    (p.2.2.1.source, gain p.1 p.2.2.1.coeff, p.2.2.1.drift)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d) (P : Protocol d) (answer : Answer d),
    ¬ (∀ W : World d, ∃ w C, Terminates P W w C ∧ w.length+1 ≤ 2*d+3 ∧
      Succeeds W w C.1 ∧
      R.readout () ⟨d,answer,W,w⟩ (readings W w) =
        (W.source,gain d W.coeff,W.drift))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 1 (by omega) (upperProtocol 1) (fun _ _ => (0,0,0))
  intro W
  obtain ⟨w,C,ht,hn,hs⟩ := adaptive_upper 1 W
  exact ⟨w,C,ht,hn,hs,rfl⟩

def registration : Registration arena
    (∀ (d : ℕ) (_hd : 1 ≤ d) (P : Protocol d) (answer : Answer d),
      ¬ CompleteCorrect P answer (2*d+3)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨critical_complete_exclusion,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let β : Coeff 1 := Pi.single 0 1
    have hβ : β ≠ 0 := by
      intro hz
      have hh := congrFun hz 0
      simpa [β] using hh
    let W := chartWorld 1 1 1 zero_lt_one zero_lt_one β hβ 0
    let answer : Answer 1 := fun w h =>
      (0,0,h ⟨0,Nat.zero_lt_succ _⟩)
    refine ⟨⟨1,answer,W,[]⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro he
    have hh := congrArg (fun z : Mat × Polynomial ℝ × ℝ => z.2.2) he
    exact zero_ne_one hh

def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@critical_complete_exclusion)
    (type_of% (realize signature (fun _ p h => p.2.1 p.2.2.2 h)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayCompleteCritical.completeUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayCompleteCritical.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p h => p.2.1 p.2.2.2 h)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayCompleteCritical,
    definition := some {
      owner := `D5.S3.Observer.Linear.GainRayCompleteCritical,
      name := `D5.S3.Observer.Linear.GainRay.CompleteCorrect,
      path := #[] },
    coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end
end Reg.D5.S3.Observer.Linear.GainRayCompleteCritical

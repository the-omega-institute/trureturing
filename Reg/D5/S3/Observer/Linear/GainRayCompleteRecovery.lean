import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GainRayCompleteRecovery
import Reg.Support.DependentFamily

/-! Typed history-family and whole-world identification audit evidence. -/

namespace Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private def fixture (δ : ℝ) : World 1 :=
  chartWorld 1 1 1 zero_lt_one zero_lt_one (Pi.single 0 1)
    (by intro h; have hh := congrFun h 0; simp at hh) δ

private theorem answer_word (d : ℕ) (hd : 1 ≤ d) (W : World d) :
    recoveryAnswer d (recoveryWord d) (readings W (recoveryWord d)) =
      (W.source, gain d W.coeff, W.drift) := by
  obtain ⟨w,C,ht,_,_,ha⟩ := (complete_recovery d hd).1 W
  have hw := ((complete_recovery d hd).2 W w C ht).1
  subst w
  exact ha

abbrev signature : Signature where
  Params := ℕ × List Bool
  State p := History p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat × Polynomial ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => recoveryAnswer p.1 p.2 h) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,0,0)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (_hd : 1 ≤ d),
    CompleteCorrect (recoveryProtocol d) (fun w h => R.readout () ⟨d,w⟩ h) (4*d+5) ∧
    ∀ (W : World d) (w : List Bool)
      (C : {C : Readout d w // C ∈ (recoveryProtocol d).palette w}),
      Terminates (recoveryProtocol d) W w C →
        w = recoveryWord d ∧ w.length+1 = 4*d+5 ∧
        C.1.mulVec (readings W w) = W.coeff ∧
        R.readout () ⟨d,w⟩ (readings W w) = (W.source,gain d W.coeff,W.drift)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w,C,_,_,_,ha⟩ := (h 1 le_rfl).1 (fixture 0)
  have hs : (0 : Mat) = (fixture 0).source := congrArg Prod.fst ha
  have hp := (fixture 0).legal.1 0 0
  rw [← hs] at hp
  norm_num at hp

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_recovery,rejected,rejected_law⟩
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
    refine ⟨⟨1,recoveryWord 1⟩, readings (fixture 0) (recoveryWord 1),
      readings (fixture 1) (recoveryWord 1), ?_⟩
    change recoveryAnswer 1 _ _ ≠ recoveryAnswer 1 _ _
    rw [answer_word 1 le_rfl, answer_word 1 le_rfl]
    intro h
    have hh := congrArg (fun z : Mat × Polynomial ℝ × ℝ => z.2.2) h
    exact zero_ne_one hh

def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@complete_recovery)
    (type_of% (realize signature (fun _ p h => recoveryAnswer p.1 p.2 h)
      (fun e => nomatch e))) ((w : List Bool) → Type) Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery.completeUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p h => recoveryAnswer p.1 p.2 h)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some History,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayCompleteRecovery,
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

abbrev identificationSignature : Signature where
  Params := ℕ
  State d := World d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := History (recoveryWord d)
  Anchor := Empty
  finiteAnchor := inferInstance

def identificationActual : Realization identificationSignature :=
  realize identificationSignature (fun _ d W => readings W (recoveryWord d))
    (fun e => nomatch e)

def identificationRejected : Realization identificationSignature :=
  realize identificationSignature (fun _ _ _ => 0) (fun e => nomatch e)

def identificationArena : Arena where
  signature := identificationSignature
  Law R := ∀ (d : ℕ) (W V : World d),
    R.readout () d W = R.readout () d V →
      W.source = V.source ∧ W.coeff = V.coeff ∧ W.drift = V.drift

private theorem identification_rejected_law : ¬ identificationArena.Law identificationRejected := by
  intro h
  have hh := (h 1 (fixture 0) (fixture 1) rfl).2.2
  exact zero_ne_one hh

def identificationRegistration : Registration identificationArena
    (identificationArena.Law identificationActual) where
  actual := identificationActual
  bridge := Iff.rfl
  variation := ⟨recovery_identifies,identificationRejected,identification_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨identificationRejected, ?_, rfl, identification_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (d : ℕ) (W V : World d),
      readings W (recoveryWord d) ≠ readings V (recoveryWord d)
    refine ⟨1,fixture 0,fixture 1,?_⟩
    intro h
    exact zero_ne_one ((recovery_identifies 1 (fixture 0) (fixture 1) h).2.2)

def identificationEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@recovery_identifies)
    (type_of% (realize identificationSignature
      (fun _ d W => readings W (recoveryWord d)) (fun e => nomatch e))) (ℕ → Type) Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery.identificationUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery.identificationRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨identificationArena⟩,
  objectArena := .source ⟨identificationArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source identificationArena ⟨identificationRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize identificationSignature
    (fun _ d W => readings W (recoveryWord d)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some World,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayCompleteRecovery,
    definition := none, coordinates := #[1,2], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms identificationRegistration
end
end Reg.D5.S3.Observer.Linear.GainRayCompleteRecovery

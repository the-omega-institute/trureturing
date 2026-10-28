import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.JJFiveFailure
import Reg.Support.SingleDependentReadout

/-! The source-bound complete world assignment on the full labelled theorem. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CompleteFailure
open _root_.D5.S3.Observer.CubicGain.JJFiveFailure

open scoped Classical
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.JJFiveFailure
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => List Bool × Bool) (fun _ => World 3)
def actual : Realization signature := realize signature
  (fun _ _ l => world l.1 l.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => world (List.replicate 5 false) false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (labels.card = 64 ∧ (suffixes 5).card = 32 ∧
      (labels.filter (fun l => l.1.getD 0 false = true)).card = 32 ∧
      (labels.filter (fun l => l.1.getD 0 false = false ∧ l.1.getD 1 false = false)).card = 16 ∧
      (labels.filter (fun l => l.1.getD 0 false = false ∧ l.1.getD 1 false = true)).card = 16) ∧
    family = labels.image (fun l => R.readout () () l) ∧
    (∀ (P : Mat) (p : Polynomial ℝ) (δ : ℝ),
      (∃ W : World 3, W.source = P ∧ gain 3 W.coeff = p ∧ W.drift = δ) ↔
        (∀ i j, 0 < P i j) ∧ P.det = 0 ∧ Matrix.trace P = 1 ∧
          p ≠ 0 ∧ p.natDegree ≤ 3) ∧
    (∀ u : List Bool, u.length = 5 → R.readout () () (u, false) ≠ R.readout () () (u, true) ∧
      (∀ e : Bool, (gain 3 (R.readout () () (u, e)).coeff).natDegree = 3) ∧
      ∀ (e : Bool) (i : Fin 8),
        readAt (R.readout () () (u, e)) (terminalWord u) i.val =
          fullResponse ((terminalWord u).take i.val)) ∧
    (family : Set (World 3)) ⊆ wholeSet [true, true] jjHistory ∧
    MixedTripleExclusion.Losing 5 family [true, true] ∧
    Loses 5 (wholeSet [true, true] jjHistory : Set (World 3)) [true, true]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := ((h.2.2.2.1 (List.replicate 5 false) (by simp)).1)
  exact hh rfl

def family : Registration arena (type_of% @jj_five_failure) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨jj_five_failure, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (List.replicate 5 false, false), (List.replicate 5 false, true), ?_⟩
    exact (jj_five_failure.2.2.2.1 (List.replicate 5 false) (by simp)).1

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@jj_five_failure) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.JJFiveFailure.jj_five_failure.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.JJFiveFailure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ l => world l.1 l.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.JJFiveFailure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","fn","arg","fn","arg","arg","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Observer.CubicGain.JJFiveFailure

import D5.S1.Words.MBonacciFactorWindow
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciFactorWindow
open _root_.D5.S1.Words.MBonacciSentinelDesubstitution (word)
open _root_.D5.S1.Words.MBonacciMinimumGreedy (U)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciFactorWindow.factor_window

abbrev signature : Signature where
  Params := Σ _m : ℕ, Σ _n : ℕ, ℕ
  State p := ℕ → Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => factor x p.2.2 p.2.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (k n : ℕ) (_hn : 1 ≤ n) (_hsize : n ≤ U hm k) (q : ℕ),
    ∃ p : ℕ, p ≤ U hm (k + m) ∧ R.readout () ⟨m, n, q⟩ (word hm) = factor (word hm) p n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, _, hp⟩ := h (by decide : 2 ≤ 2) 0 1 (by decide) (by decide) 0
  have he := congrArg List.length hp
  simp [rejected, realize, factor] at he

def family : Registration arena
    (type_of% (@_root_.D5.S1.Words.MBonacciFactorWindow.factor_window)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.MBonacciFactorWindow.factor_window,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, 1, 0⟩, (fun _ => (0 : Fin 2)), (fun _ => (1 : Fin 2)), ?_⟩
    change factor (fun _ => (0 : Fin 2)) 0 1 ≠ factor (fun _ => (1 : Fin 2)) 0 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciFactorWindow.factor_window)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.MBonacciFactorWindow.factor_window.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciFactorWindow.factor_window.family,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.MBonacciFactorWindow, definition := none,
    coordinates := #[0, 3, 6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S1.Words.MBonacciFactorWindow.factor_window

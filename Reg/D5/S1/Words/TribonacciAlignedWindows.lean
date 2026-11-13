import D5.S1.Words.TribonacciAlignedWindows
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The two literal word readings are audited in their exact existential scopes. -/

open _root_.D5.S1.Words.TribonacciAlignedWindows
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.TribonacciAlignedWindows

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => W n) (fun e => nomatch e)

def rejected (role : Bool) : Realization signature :=
  realize signature (fun r _ n => if r = role then 2 else W n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ K : ℕ, 0 < K ∧ ∃ J : ℕ, 1 ≤ J ∧
    ∀ j : ℕ, J ≤ j → ∃ m s : ℕ,
      3 ≤ m ∧ Odd m ∧ Even s ∧ N j ≤ K*m ∧ s+2*m ≤ N j ∧
      ∀ i : ℕ, i < m-1 → R.readout false () (s+i+m) = R.readout true () (s+i)

private theorem no_cc (n : ℕ) : ¬ (W n = 2 ∧ W (n+1) = 2) := by
  rintro ⟨h0,h1⟩
  have hn : W n ≠ _root_.D5.S1.Words.MBonacciSentinelDesubstitution.zero
      (by omega : 2 ≤ 3) := by
    rw [h0]
    change (2 : Fin 3) ≠ 0
    decide
  have hh := (_root_.D5.S1.Words.MBonacciSentinelDesubstitution.actual_word_laws
    (by omega : 2 ≤ 3)).2.2.2.2.2.1 n hn
  have he := h1.symm.trans hh
  exact (by decide : (2 : Fin 3) ≠ 0) he

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  rintro ⟨K,hK,J,hJ,h⟩
  obtain ⟨m,s,hm,ho,he,hb,hf,hr⟩ := h J le_rfl
  have h0 := hr 0 (by omega)
  have h1 := hr 1 (by omega)
  cases role
  · change (if false = false then (2 : Fin 3) else W (s+0+m)) =
      (if true = false then (2 : Fin 3) else W (s+0)) at h0
    change (if false = false then (2 : Fin 3) else W (s+1+m)) =
      (if true = false then (2 : Fin 3) else W (s+1)) at h1
    simp at h0 h1
    exact no_cc s ⟨h0.symm,h1.symm⟩
  · change (if false = true then (2 : Fin 3) else W (s+0+m)) =
      (if true = true then (2 : Fin 3) else W (s+0)) at h0
    change (if false = true then (2 : Fin 3) else W (s+1+m)) =
      (if true = true then (2 : Fin 3) else W (s+1)) at h1
    simp at h0 h1
    exact no_cc (s+m) ⟨h0, by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1⟩

def family : Registration arena (type_of% (@_root_.D5.S1.Words.TribonacciAlignedWindows.aligned_windows)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.TribonacciAlignedWindows.aligned_windows,
    rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro r hr
      funext p n
      simp [actual,rejected,realize,hr]
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    change W 0 ≠ W 1
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.TribonacciAlignedWindows.aligned_windows)
    (type_of% actual) Unit Unit := {
  unitName := `D5.S1.Words.TribonacciAlignedWindows.aligned_windows.__information_unit,
  realizationName := `Reg.D5.S1.Words.TribonacciAlignedWindows.family,
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
    owner := `D5.S1.Words.TribonacciAlignedWindows, definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg","body","arg","arg","body","arg","body","body",
        "arg","body","arg","body","arg","arg","arg","arg","arg",
        "body","body","fn","arg","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }, {
      path := #["arg","body","arg","arg","body","arg","body","body",
        "arg","body","arg","body","arg","arg","arg","arg","arg",
        "body","body","arg","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms family
#print axioms audit

end Reg.D5.S1.Words.TribonacciAlignedWindows

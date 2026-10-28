import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Reg.Support.DependentFamily
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basis

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

abbrev joinSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ p : Nat, Σ U : CountMat n m, CountMat m p
  State p := Edge (p.2.2.2.1 * p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge (p.2.2.2.1 * p.2.2.2.2)
  Anchor := Empty
  finiteAnchor := inferInstance

def reverseEdge {n m : Nat} {M : CountMat n m} (a : Edge M) : Edge M :=
  ⟨a.source, a.target, Fin.rev a.number⟩

def joinActual : Realization joinSignature :=
  realize joinSignature (fun _ _ a => a) (fun e => nomatch e)

def joinRejected : Realization joinSignature :=
  realize joinSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def joinArena : Arena where
  signature := joinSignature
  Law r := ∀ {n m p : Nat} (U : CountMat n m) (V : CountMat m p)
    (a : Edge (U * V)),
    join U V (split U V a).1 (split U V a).2 (by rfl) =
      r.readout () ⟨n, m, p, U, V⟩ a

theorem join_rejected_law : ¬ joinArena.Law joinRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hUV : (U * V) 0 0 = 2 := by
    change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
    simp
  let a : Edge (U * V) :=
    ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
  have hh := h U V a
  rw [join_split] at hh
  have hn := congrArg (fun e : Edge (U * V) => e.number.val) hh
  simp [joinRejected, realize, reverseEdge, U, V, a] at hn

def joinRegistration : Registration joinArena (joinArena.Law joinActual) where
  actual := joinActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m p U V a
    simpa [joinActual, realize] using join_split U V a,
    joinRejected, join_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨joinRejected, ?_, rfl, join_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    let V : CountMat 1 1 := fun _ _ => 1
    have hUV : (U * V) 0 0 = 2 := by
      change (∑ _ : Fin 1, (2 : Nat) * 1) = 2
      simp
    let a : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (0 : Fin 2)⟩
    let b : Edge (U * V) :=
      ⟨0, 0, hUV.symm ▸ (1 : Fin 2)⟩
    change ∃ p : joinSignature.Params, ∃ x y : joinSignature.State p, x ≠ y
    exact ⟨⟨1, 1, 1, U, V⟩, a, b, by simp [a, b]⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.join_split) (type_of% (realize.{0, 0, 0, 0, 0} joinSignature (fun _ _ a => a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedMatrixOverlap") "join_split") "Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap/Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.joinRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(joinArena)⟩,
  objectArena := .source ⟨(joinArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (joinArena) ⟨(joinRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} joinSignature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


abbrev splitSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, CountMat n m
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def splitActual : Realization splitSignature :=
  realize splitSignature (fun _ _ a => a) (fun e => nomatch e)

def splitRejected : Realization splitSignature :=
  realize splitSignature (fun _ _ a => reverseEdge a) (fun e => nomatch e)

def splitArena : Arena where
  signature := splitSignature
  Law r := ∀ {n m p : Nat} (U : CountMat n m) (V : CountMat m p)
    (a : Edge U) (b : Edge V) (h : a.target = b.source),
    split U V (join U V a b h) =
      (r.readout () ⟨n, m, U⟩ a, b)

theorem split_rejected_law : ¬ splitArena.Law splitRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 2
  let V : CountMat 1 1 := fun _ _ => 1
  have hU : U 0 0 = 2 := by rfl
  let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
  let b : Edge V := ⟨0, 0, 0⟩
  have hh := h U V a b rfl
  rw [split_join] at hh
  have hfirst := congrArg (fun p : Edge U × Edge V => p.1) hh
  have hn := congrArg (fun e : Edge U => e.number.val) hfirst
  simp [splitRejected, realize, reverseEdge, U, V, a, b] at hn

def splitRegistration : Registration splitArena (splitArena.Law splitActual) where
  actual := splitActual
  bridge := Iff.rfl
  variation := ⟨by
    intro n m p U V a b h
    simpa [splitActual, realize] using split_join U V a b h,
    splitRejected, split_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨splitRejected, ?_, rfl, split_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 2
    have hU : U 0 0 = 2 := by rfl
    let a : Edge U := ⟨0, 0, hU.symm ▸ (0 : Fin 2)⟩
    let b : Edge U := ⟨0, 0, hU.symm ▸ (1 : Fin 2)⟩
    change ∃ p : splitSignature.Params, ∃ x y : splitSignature.State p, x ≠ y
    refine ⟨⟨1, 1, U⟩, a, b, ?_⟩
    intro h
    have hn := congrArg (fun e : Edge U => e.number.val) h
    exact Nat.zero_ne_one hn

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_join) (type_of% (realize.{0, 0, 0, 0, 0} splitSignature (fun _ _ a => a) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CountedMatrixOverlap") "split_join") "Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap/Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.splitRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(splitArena)⟩,
  objectArena := .source ⟨(splitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (splitArena) ⟨(splitRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} splitSignature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms joinRegistration
#print axioms splitRegistration


abbrev sourceSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ p : Nat, Σ U : CountMat n m, CountMat m p
  State p := Edge (p.2.2.2.1 * p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def sourceActual : Realization sourceSignature :=
  realize sourceSignature (fun _ _ a => a.source) (fun e => nomatch e)

def sourceRejected : Realization sourceSignature :=
  realize sourceSignature (fun _ _ a => Fin.rev a.source) (fun e => nomatch e)

def sourceArena : Arena where
  signature := sourceSignature
  Law r := ∀ {n m p : ℕ} (U : CountMat n m) (V : CountMat m p) (a : Edge (U * V)),
    (split U V a).1.source = r.readout () ⟨n, m, p, U, V⟩ a

theorem source_actual_law : sourceArena.Law sourceActual := by
  intro n m p U V a
  exact split_source U V a

theorem source_rejected_law : ¬ sourceArena.Law sourceRejected := by
  intro h
  let U : CountMat 2 1 := fun _ _ => 1
  let V : CountMat 1 1 := fun _ _ => 1
  let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
  have hh := h U V a
  rw [split_source] at hh
  change a.source = Fin.rev a.source at hh
  have hn := congrArg Fin.val hh
  norm_num [a, join, Fin.rev] at hn

def sourceRegistration : Registration sourceArena (sourceArena.Law sourceActual) where
  actual := sourceActual
  bridge := Iff.rfl
  variation := ⟨source_actual_law, sourceRejected, source_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sourceRejected, ?_, rfl, source_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 2 1 := fun _ _ => 1
    let V : CountMat 1 1 := fun _ _ => 1
    let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
    let b : Edge (U * V) := join U V ⟨1, 0, 0⟩ ⟨0, 0, 0⟩ rfl
    refine ⟨⟨2, 1, 1, U, V⟩, a, b, ?_⟩
    change a.source ≠ b.source
    change (0 : Fin 2) ≠ 1
    decide

noncomputable def registration_source : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_source)
    (type_of% (realize sourceSignature (fun _ _ a => a.source) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.source
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sourceSignature (fun _ _ a => a.source) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev targetSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ p : Nat, Σ U : CountMat n m, CountMat m p
  State p := Edge (p.2.2.2.1 * p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def targetActual : Realization targetSignature :=
  realize targetSignature (fun _ _ a => a.target) (fun e => nomatch e)

def targetRejected : Realization targetSignature :=
  realize targetSignature (fun _ _ a => Fin.rev a.target) (fun e => nomatch e)

def targetArena : Arena where
  signature := targetSignature
  Law r := ∀ {n m p : ℕ} (U : CountMat n m) (V : CountMat m p) (a : Edge (U * V)),
    (split U V a).2.target = r.readout () ⟨n, m, p, U, V⟩ a

theorem target_actual_law : targetArena.Law targetActual := by
  intro n m p U V a
  exact split_target U V a

theorem target_rejected_law : ¬ targetArena.Law targetRejected := by
  intro h
  let U : CountMat 1 1 := fun _ _ => 1
  let V : CountMat 1 2 := fun _ _ => 1
  let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
  have hh := h U V a
  rw [split_target] at hh
  change a.target = Fin.rev a.target at hh
  have hn := congrArg Fin.val hh
  norm_num [a, join, Fin.rev] at hn

def targetRegistration : Registration targetArena (targetArena.Law targetActual) where
  actual := targetActual
  bridge := Iff.rfl
  variation := ⟨target_actual_law, targetRejected, target_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨targetRejected, ?_, rfl, target_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 1 := fun _ _ => 1
    let V : CountMat 1 2 := fun _ _ => 1
    let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
    let b : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 1, 0⟩ rfl
    refine ⟨⟨1, 1, 2, U, V⟩, a, b, ?_⟩
    change a.target ≠ b.target
    change (0 : Fin 2) ≠ 1
    decide

noncomputable def registration_target : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_target)
    (type_of% (realize targetSignature (fun _ _ a => a.target) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.target
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.targetRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨targetArena⟩
  objectArena := .source ⟨targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source targetArena ⟨targetRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize targetSignature (fun _ _ a => a.target) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev middleSignature : Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ p : Nat, Σ U : CountMat n m, CountMat m p
  State p := Edge (p.2.2.2.1 * p.2.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def middleActual : Realization middleSignature :=
  realize middleSignature (fun _ p a => (split p.2.2.2.1 p.2.2.2.2 a).2.source)
    (fun e => nomatch e)

noncomputable def middleRejected : Realization middleSignature :=
  realize middleSignature (fun _ p a => Fin.rev (split p.2.2.2.1 p.2.2.2.2 a).2.source)
    (fun e => nomatch e)

def middleArena : Arena where
  signature := middleSignature
  Law r := ∀ {n m p : ℕ} (U : CountMat n m) (V : CountMat m p) (a : Edge (U * V)),
    (split U V a).1.target = r.readout () ⟨n, m, p, U, V⟩ a

theorem middle_actual_law : middleArena.Law middleActual := by
  intro n m p U V a
  exact split_middle U V a

theorem middle_rejected_law : ¬ middleArena.Law middleRejected := by
  intro h
  let U : CountMat 1 2 := fun _ _ => 1
  let V : CountMat 2 1 := fun _ _ => 1
  let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
  have hh := h U V a
  change (split U V a).1.target = Fin.rev (split U V a).2.source at hh
  dsimp only [a] at hh
  rw [split_join] at hh
  have hn := congrArg Fin.val hh
  norm_num [Fin.rev] at hn

noncomputable def middleRegistration : Registration middleArena (middleArena.Law middleActual) where
  actual := middleActual
  bridge := Iff.rfl
  variation := ⟨middle_actual_law, middleRejected, middle_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨middleRejected, ?_, rfl, middle_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let U : CountMat 1 2 := fun _ _ => 1
    let V : CountMat 2 1 := fun _ _ => 1
    let a : Edge (U * V) := join U V ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
    let b : Edge (U * V) := join U V ⟨0, 1, 0⟩ ⟨1, 0, 0⟩ rfl
    refine ⟨⟨1, 2, 1, U, V⟩, a, b, ?_⟩
    change (split U V a).2.source ≠ (split U V b).2.source
    dsimp only [a, b]
    rw [split_join, split_join]
    change (0 : Fin 2) ≠ 1
    decide

noncomputable def registration_middle : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.split_middle)
    (type_of% (realize middleSignature (fun _ p a =>
      (split p.2.2.2.1 p.2.2.2.2 a).2.source) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.middle
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.middleRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨middleArena⟩
  objectArena := .source ⟨middleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source middleArena ⟨middleRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize middleSignature (fun _ p a =>
    (split p.2.2.2.1 p.2.2.2.2 a).2.source) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap, definition := none, coordinates := #[0, 1, 2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

import D5.S0.Computability.NatPresburgerSolver
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.NatPresburgerSolver
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.NatPresburger _root_.PresburgerArithmetic
open FirstOrder Language


namespace Audit_test_correct
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, Σ _φ : presburger.BoundedFormula (Fin m) n, Fin m → Nat
  State a := Fin a.2.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => test a.2.2.1 a.2.2.2 xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) (xs : Fin n → Nat), F.readout () ⟨m,n,φ,v⟩ xs = true ↔ φ.Realize v xs

theorem bridge : (type_of% (@_root_.NatPresburger.test_correct)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.test_correct)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (m := 0) (n := 0) (.equal 0 0) Fin.elim0 Fin.elim0).mpr (by change (0 : Nat) = 0; rfl)
  cases hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.test_correct)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 0) 1 := .equal (.var (.inr 0)) 0
    refine ⟨⟨0,1,φ,Fin.elim0⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change test φ Fin.elim0 (fun _ => 0) ≠ test φ Fin.elim0 (fun _ => 1)
    have hz : test φ Fin.elim0 (fun _ => 0) = true := (test_correct _ _ _).mpr (by change (0 : Nat) = 0; rfl)
    have ho : test φ Fin.elim0 (fun _ => 1) = false := Bool.eq_false_of_not_eq_true (fun ht => by
      have bad := (test_correct _ _ _).mp ht
      change (1 : Nat) = 0 at bad
      omega)
    rw [hz,ho]
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.test_correct)
      (type_of% (realize signature (fun _ a xs => test a.2.2.1 a.2.2.2 xs) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_test_correct.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_test_correct.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => test a.2.2.1 a.2.2.2 xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_test_correct

namespace Audit_solve_bounded_sound
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, presburger.BoundedFormula (Fin m) n
  State a := Fin a.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin a.2.1 → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => some (fun _ => 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) (xs : Fin n → Nat), F.readout () ⟨m,n,φ⟩ v = some xs → φ.Realize v xs

theorem bridge : (type_of% (@_root_.NatPresburger.solve_bounded_sound)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_bounded_sound)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m := 0) (n := 0) .falsum Fin.elim0 (fun _ => 0) rfl
  exact hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_bounded_sound)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 1) 0 := .equal (.var (.inl 0)) 0
    have hz : ∃ xs, solveBounded φ (fun _ => 0) = some xs :=
      (solve_bounded_exists_some_iff _ _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveBounded φ (fun _ => 1) = none :=
      (solve_bounded_none_iff _ _).mpr (by
        rintro ⟨xs,hxs⟩
        change (1 : Nat) = 0 at hxs
        omega)
    refine ⟨⟨1,0,φ⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change solveBounded φ (fun _ => 0) ≠ solveBounded φ (fun _ => 1)
    obtain ⟨xs,hxs⟩ := hz
    rw [hxs,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_bounded_sound)
      (type_of% (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_sound.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_sound.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "domain", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_bounded_sound

namespace Audit_solve_bounded_exists_some_iff
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, presburger.BoundedFormula (Fin m) n
  State a := Fin a.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin a.2.1 → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat), (∃ xs, F.readout () ⟨m,n,φ⟩ v = some xs) ↔ ∃ xs : Fin n → Nat, φ.Realize v xs

theorem bridge : (type_of% (@_root_.NatPresburger.solve_bounded_exists_some_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_bounded_exists_some_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨xs,hh⟩ := (h (m := 0) (n := 0) (.equal 0 0) Fin.elim0).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
  cases hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_bounded_exists_some_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 1) 0 := .equal (.var (.inl 0)) 0
    have hz : ∃ xs, solveBounded φ (fun _ => 0) = some xs :=
      (solve_bounded_exists_some_iff _ _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveBounded φ (fun _ => 1) = none :=
      (solve_bounded_none_iff _ _).mpr (by
        rintro ⟨xs,hxs⟩
        change (1 : Nat) = 0 at hxs
        omega)
    refine ⟨⟨1,0,φ⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change solveBounded φ (fun _ => 0) ≠ solveBounded φ (fun _ => 1)
    obtain ⟨xs,hxs⟩ := hz
    rw [hxs,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_bounded_exists_some_iff)
      (type_of% (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_exists_some_iff.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_exists_some_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_bounded_exists_some_iff

namespace Audit_solve_bounded_none_iff
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, presburger.BoundedFormula (Fin m) n
  State a := Fin a.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin a.2.1 → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat), F.readout () ⟨m,n,φ⟩ v = none ↔ ¬∃ xs : Fin n → Nat, φ.Realize v xs

theorem bridge : (type_of% (@_root_.NatPresburger.solve_bounded_none_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_bounded_none_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (m := 0) (n := 0) (.equal 0 0) Fin.elim0).mp rfl
  exact hh ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_bounded_none_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 1) 0 := .equal (.var (.inl 0)) 0
    have hz : ∃ xs, solveBounded φ (fun _ => 0) = some xs :=
      (solve_bounded_exists_some_iff _ _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveBounded φ (fun _ => 1) = none :=
      (solve_bounded_none_iff _ _).mpr (by
        rintro ⟨xs,hxs⟩
        change (1 : Nat) = 0 at hxs
        omega)
    refine ⟨⟨1,0,φ⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change solveBounded φ (fun _ => 0) ≠ solveBounded φ (fun _ => 1)
    obtain ⟨xs,hxs⟩ := hz
    rw [hxs,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_bounded_none_iff)
      (type_of% (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_none_iff.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_bounded_none_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a v => solveBounded a.2.2 v) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_bounded_none_iff

namespace Audit_solve_all_sound
abbrev signature : Signature where
  Params := Σ m : Nat, Nat
  State a := presburger.BoundedFormula (Fin a.1) a.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin (a.1+a.2) → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ φ => solveAll φ) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => some (fun _ => 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (w : Fin (m+n) → Nat), F.readout () ⟨m,n⟩ φ = some w → φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m)

theorem bridge : (type_of% (@_root_.NatPresburger.solve_all_sound)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_all_sound)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m := 0) (n := 0) .falsum (fun _ => 0) rfl
  exact hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_all_sound)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 0) 0 := .equal 0 0
    have hz : ∃ w, solveAll φ = some w :=
      (solve_all_exists_some_iff _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0) = none :=
      (solve_all_none_iff _).mpr (by rintro ⟨w,hw⟩; exact hw)
    refine ⟨⟨0,0⟩,φ,.falsum,?_⟩
    change solveAll φ ≠ solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0)
    obtain ⟨w,hw⟩ := hz
    rw [hw,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_all_sound)
      (type_of% (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)))
      (type_of% (presburger.BoundedFormula (Fin 0) 0)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_sound.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_sound.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_all_sound

namespace Audit_solve_all_exists_some_iff
abbrev signature : Signature where
  Params := Σ m : Nat, Nat
  State a := presburger.BoundedFormula (Fin a.1) a.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin (a.1+a.2) → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ φ => solveAll φ) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n), (∃ w, F.readout () ⟨m,n⟩ φ = some w) ↔ ∃ w : Fin (m+n) → Nat, φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m)

theorem bridge : (type_of% (@_root_.NatPresburger.solve_all_exists_some_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_all_exists_some_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨w,hw⟩ := (h (m := 0) (n := 0) (.equal 0 0)).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
  cases hw

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_all_exists_some_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 0) 0 := .equal 0 0
    have hz : ∃ w, solveAll φ = some w :=
      (solve_all_exists_some_iff _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0) = none :=
      (solve_all_none_iff _).mpr (by rintro ⟨w,hw⟩; exact hw)
    refine ⟨⟨0,0⟩,φ,.falsum,?_⟩
    change solveAll φ ≠ solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0)
    obtain ⟨w,hw⟩ := hz
    rw [hw,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_all_exists_some_iff)
      (type_of% (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)))
      (type_of% (presburger.BoundedFormula (Fin 0) 0)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_exists_some_iff.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_exists_some_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_all_exists_some_iff

namespace Audit_solve_all_none_iff
abbrev signature : Signature where
  Params := Σ m : Nat, Nat
  State a := presburger.BoundedFormula (Fin a.1) a.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Option (Fin (a.1+a.2) → Nat)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ φ => solveAll φ) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n), F.readout () ⟨m,n⟩ φ = none ↔ ¬∃ w : Fin (m+n) → Nat, φ.Realize (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m)

theorem bridge : (type_of% (@_root_.NatPresburger.solve_all_none_iff)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.solve_all_none_iff)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := (h (m := 0) (n := 0) (.equal 0 0)).mp rfl
  exact hh ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩

def evidence : Registration arena (type_of% (@_root_.NatPresburger.solve_all_none_iff)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, bad_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i; cases i
    let φ : presburger.BoundedFormula (Fin 0) 0 := .equal 0 0
    have hz : ∃ w, solveAll φ = some w :=
      (solve_all_exists_some_iff _).mpr ⟨Fin.elim0, by change (0 : Nat) = 0; rfl⟩
    have ho : solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0) = none :=
      (solve_all_none_iff _).mpr (by rintro ⟨w,hw⟩; exact hw)
    refine ⟨⟨0,0⟩,φ,.falsum,?_⟩
    change solveAll φ ≠ solveAll (.falsum : presburger.BoundedFormula (Fin 0) 0)
    obtain ⟨w,hw⟩ := hz
    rw [hw,ho]
    simp


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.solve_all_none_iff)
      (type_of% (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)))
      (type_of% (presburger.BoundedFormula (Fin 0) 0)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_none_iff.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerSolver.Audit_solve_all_none_iff.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ _ φ => solveAll φ) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerSolver,
    definition := none, coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 2,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_solve_all_none_iff

end Reg.D5.S0.Computability.NatPresburgerSolver

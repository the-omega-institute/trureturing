import D5.S0.Computability.NatPresburgerCompiler
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.NatPresburgerCompiler
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.NatPresburger _root_.PresburgerArithmetic
open FirstOrder Language


namespace Audit_compile_term_correct
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, Fin m → Nat
  State a := Fin a.2.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := List Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (t : presburger.Term (Fin m ⊕ Fin n)) (v : Fin m → Nat) (xs : Fin n → Nat), (compileTerm t).eval (F.readout () ⟨m,n,v⟩ xs) = Int.ofNat (t.realize (Sum.elim v xs))

theorem bridge : (type_of% (@_root_.NatPresburger.compile_term_correct)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.compile_term_correct)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m := 0) (n := 1) (.var (.inr 0)) Fin.elim0 (fun _ => 1)
  change (0 : Int) = 1 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.compile_term_correct)) where
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
    refine ⟨⟨0,1,Fin.elim0⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change environment Fin.elim0 (fun _ : Fin 1 => 0) ≠
      environment Fin.elim0 (fun _ : Fin 1 => 1)
    simp [environment]


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.compile_term_correct)
      (type_of% (realize signature (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerCompiler.Audit_compile_term_correct.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerCompiler.Audit_compile_term_correct.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerCompiler,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_compile_term_correct

namespace Audit_compile_correct
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, Fin m → Nat
  State a := Fin a.2.1 → Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := List Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (φ : presburger.BoundedFormula (Fin m) n) (v : Fin m → Nat) (xs : Fin n → Nat), (compile φ).holds (F.readout () ⟨m,n,v⟩ xs) ↔ φ.Realize v xs

theorem bridge : (type_of% (@_root_.NatPresburger.compile_correct)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.compile_correct)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  let φ : presburger.BoundedFormula (Fin 0) 1 :=
    BoundedFormula.equal (.var (.inr 0)) 1
  have hh := (h φ Fin.elim0 (fun _ => 1)).mpr (by change (1 : Nat) = 1; rfl)
  change (false = true) at hh
  cases hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.compile_correct)) where
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
    refine ⟨⟨0,1,Fin.elim0⟩,(fun _ => 0),(fun _ => 1),?_⟩
    change environment Fin.elim0 (fun _ : Fin 1 => 0) ≠
      environment Fin.elim0 (fun _ : Fin 1 => 1)
    simp [environment]


noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.compile_correct)
      (type_of% (realize signature (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)))
      (type_of% (Fin 1 → Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerCompiler.Audit_compile_correct.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerCompiler.Audit_compile_correct.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a xs => environment a.2.2 xs) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerCompiler,
    definition := none, coordinates := #[0, 1, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_compile_correct

end Reg.D5.S0.Computability.NatPresburgerCompiler

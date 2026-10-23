import D5.S0.Computability.NatPresburgerEnvironment
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.NatPresburgerEnvironment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.NatPresburger _root_.PresburgerArithmetic


namespace Audit_eval_basis
abbrev signature : Signature where
  Params := Nat
  State a := List Int
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ k env => (basis k).eval env) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ (k : Nat) (env : List Int), F.readout () k env = (env[k]?).getD 0

theorem bridge : (type_of% (@_root_.NatPresburger.eval_basis)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.eval_basis)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 0 []
  change (1 : Int) = 0 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.eval_basis)) where
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
    refine ⟨0, [], [1], ?_⟩
    change (basis 0).eval [] ≠ (basis 0).eval [1]
    simp [eval_basis]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.eval_basis)
      (type_of% (realize signature (fun _ k env => (basis k).eval env) (fun e => nomatch e)))
      (type_of% (List Int)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_eval_basis.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_eval_basis.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ k env => (basis k).eval env) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerEnvironment,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_eval_basis

namespace Audit_environment_lookup
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, Σ _v : Fin m → Nat, Fin n → Nat
  State a := Fin a.1 ⊕ Fin a.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a i => ((environment a.2.2.1 a.2.2.2)[position i]?).getD 0) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (v : Fin m → Nat) (xs : Fin n → Nat) (i : Fin m ⊕ Fin n), F.readout () ⟨m,n,v,xs⟩ i = Int.ofNat (Sum.elim v xs i)

theorem bridge : (type_of% (@_root_.NatPresburger.environment_lookup)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.environment_lookup)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m := 1) (n := 0) (fun _ => 0) Fin.elim0 (.inl 0)
  change (-1 : Int) = 0 at hh
  norm_num at hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.environment_lookup)) where
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
    refine ⟨⟨2,0,![0,1],Fin.elim0⟩, .inl 0, .inl 1, ?_⟩
    dsimp only [actual, realize]
    rw [environment_lookup, environment_lookup]
    norm_num

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.environment_lookup)
      (type_of% (realize signature (fun _ a i => ((environment a.2.2.1 a.2.2.2)[position i]?).getD 0) (fun e => nomatch e)))
      (type_of% (Fin 1 ⊕ Fin 0)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_environment_lookup.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_environment_lookup.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a i => ((environment a.2.2.1 a.2.2.2)[position i]?).getD 0) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerEnvironment,
    definition := none, coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_environment_lookup

namespace Audit_environment_snoc
abbrev signature : Signature where
  Params := Σ m : Nat, Σ n : Nat, Σ _v : Fin m → Nat, Fin n → Nat
  State a := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := List Int
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ a x => environment a.2.2.1 (Fin.snoc a.2.2.2 x)) (fun e => nomatch e)
def bad : Realization signature := realize signature
  (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {m n : Nat} (v : Fin m → Nat) (xs : Fin n → Nat) (x : Nat), F.readout () ⟨m,n,v,xs⟩ x = (x : Int) :: environment v xs

theorem bridge : (type_of% (@_root_.NatPresburger.environment_snoc)) ↔ arena.Law actual := Iff.rfl
theorem actual_law : arena.Law actual := by
  exact (@_root_.NatPresburger.environment_snoc)
theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h (m := 0) (n := 0) Fin.elim0 Fin.elim0 0
  change ([] : List Int) = [0] at hh
  cases hh

def evidence : Registration arena (type_of% (@_root_.NatPresburger.environment_snoc)) where
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
    refine ⟨⟨0,0,Fin.elim0,Fin.elim0⟩,0,1,?_⟩
    change environment Fin.elim0 (Fin.snoc Fin.elim0 0) ≠
      environment Fin.elim0 (Fin.snoc Fin.elim0 1)
    rw [environment_snoc, environment_snoc]
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.NatPresburger.environment_snoc)
      (type_of% (realize signature (fun _ a x => environment a.2.2.1 (Fin.snoc a.2.2.2 x)) (fun e => nomatch e)))
      (type_of% (Nat)) Unit := {
  unitName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_environment_snoc.unit,
  realizationName := `Reg.D5.S0.Computability.NatPresburgerEnvironment.Audit_environment_snoc.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by trivial),
  readout := some (realize signature (fun _ a x => environment a.2.2.1 (Fin.snoc a.2.2.2 x)) (fun e => nomatch e)),
  variation := .evidence ⟨(by trivial : True)⟩ (by trivial),
  sensitivity := .evidence ⟨(by trivial : True)⟩ (by trivial),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.NatPresburgerEnvironment,
    definition := none, coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false},
    { name := `relaxedAutoImplicit, value := .bool false}] }
end Audit_environment_snoc

end Reg.D5.S0.Computability.NatPresburgerEnvironment

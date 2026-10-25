import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
import Reg.Support.DependentFamily

/-! The audit reads the original state value on the full native solution domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
noncomputable section

abbrev signature : Signature where
  Params := Σ m : Nat, System m × Fin m
  State p := Fin p.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ p v => v p.2.2) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Nat} {S : System m} {v : Fin m → CompletionTree},
    Satisfies S v → ∀ {i : Fin m} (cycle : Walk S i i),
      IsFinite (R.readout () ⟨m, S, i⟩ v) → ¬ cycle.Strict

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let S : System 1 := fun i => some (.var 1 i)
  let v : Fin 1 → CompletionTree := fun _ => Omega
  have sat : Satisfies S v := by
    intro i E eq
    have ee : E = .var 1 i := (Option.some.inj eq).symm
    subst E
    change Omega = rho^[1] Omega
    exact (iterate_omega 1).symm
  let edge : Dependency S 0 0 := {
    expression := .var 1 0
    equation := rfl
    address := []
    power := 1
    occurrence := .var 1 0 }
  let cycle : Walk S 0 0 := .cons edge (.nil 0)
  have negative := law sat cycle ⟨.of true, rfl⟩
  exact negative (Or.inr (Or.inl (by decide)))

def evidence : Registration arena (type_of% (@finite_cycle_is_silent)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_cycle_is_silent, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ => none), 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro h
    change leaf true = leaf false at h
    have hs : (FreeMagma.of true :
        _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source) = .of false :=
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective h
    cases hs

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_cycle_is_silent) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.finite_cycle_is_silent.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => v p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "type", "arg"]
      stateBinder := 2
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration


namespace Extension

abbrev arena : Arena where
  signature := NativeFunctionalObstruction.signature
  Law R := ∀ {m : Nat} (S : System m) (B : Fin m → Prop) (v : Fin m → CompletionTree),
    BoundaryClosed S B →
    (∀ i E, B i → S i = some E → R.readout () ⟨m, S, i⟩ v = value v E) →
    ∃ w : Fin m → CompletionTree,
      (∀ i E, S i = some E → R.readout () ⟨m, S, i⟩ w = value w E) ∧
      ∀ i, B i → R.readout () ⟨m, S, i⟩ w = R.readout () ⟨m, S, i⟩ v

private theorem rejected_law : ¬ arena.Law NativeFunctionalObstruction.rejected := by
  intro law
  let S : System 1 := fun _ => some (.ground (.of false))
  obtain ⟨w, sat, _⟩ := law S (fun _ => False) (fun _ => Omega)
    (by intro i E no; exact no.elim) (by intro i E no; exact no.elim)
  have h := sat 0 (.ground (.of false)) rfl
  have hs : (FreeMagma.of true :
      _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source) = .of false :=
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective h
  cases hs

def evidence : Registration arena (type_of% (@whole_system_boundary_extension)) where
  actual := NativeFunctionalObstruction.actual
  bridge := Iff.rfl
  variation := ⟨@whole_system_boundary_extension, NativeFunctionalObstruction.rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨NativeFunctionalObstruction.rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ => none), 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro h
    have hs : (FreeMagma.of true :
        _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source) = .of false :=
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective h
    cases hs

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@whole_system_boundary_extension) (Realization NativeFunctionalObstruction.signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.whole_system_boundary_extension.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction.Extension.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NativeFunctionalObstruction.signature
    (fun _ p v => v p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Extension


namespace Perturbation

abbrev rejected : Realization NativeFunctionalObstruction.signature := by
  classical
  exact realize NativeFunctionalObstruction.signature
    (fun _ p v => if v p.2.2 = leaf true then leaf true else leaf false)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := NativeFunctionalObstruction.signature
  Law R := ∀ {m : Nat} {S : System m} {u v : Fin m → CompletionTree},
    Satisfies S u → Satisfies S v → ∀ {i : Fin m},
    IsFinite (R.readout () ⟨m, S, i⟩ v) →
    ∃ w : Fin m → CompletionTree, Satisfies S w ∧
      ∃ t : _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source,
        embed t = R.readout () ⟨m, S, i⟩ w ∧
          (R.readout () ⟨m, S, i⟩ u ≠ R.readout () ⟨m, S, i⟩ v →
            0 < _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.gamma t)

private theorem alpha_ne_beta : leaf true ≠ leaf false := by
  intro eq
  have h : (FreeMagma.of true :
      _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.Source) = .of false :=
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective eq
  cases h

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let S : System 1 := fun _ => none
  let u : Fin 1 → CompletionTree := fun _ => leaf true
  let v : Fin 1 → CompletionTree := fun _ => leaf false
  have satU : Satisfies S u := by intro i E eq; cases eq
  have satV : Satisfies S v := by intro i E eq; cases eq
  have finite : IsFinite (rejected.readout () ⟨1, S, 0⟩ v) := by
    change IsFinite (if leaf false = leaf true then leaf true else leaf false)
    rw [ite_eq_right alpha_ne_beta.symm]
    exact ⟨.of false, rfl⟩
  obtain ⟨w, _, t, ht, pos⟩ := law satU satV (i := 0) finite
  have diff : rejected.readout () ⟨1, S, 0⟩ u ≠ rejected.readout () ⟨1, S, 0⟩ v := by
    change (if leaf true = leaf true then leaf true else leaf false) ≠
      (if leaf false = leaf true then leaf true else leaf false)
    rw [ite_eq_left rfl, ite_eq_right alpha_ne_beta.symm]
    exact alpha_ne_beta
  have positive := pos diff
  change embed t = (if w 0 = leaf true then leaf true else leaf false) at ht
  split_ifs at ht with h
  · have eq : t = FreeMagma.of true :=
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective ht
    subst t
    exact (Nat.lt_irrefl 0) positive
  · have eq : t = FreeMagma.of false :=
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.embed_injective ht
    subst t
    exact (Nat.lt_irrefl 0) positive

def evidence : Registration arena (type_of% (@finite_coordinate_perturbation)) where
  actual := NativeFunctionalObstruction.actual
  bridge := Iff.rfl
  variation := ⟨@finite_coordinate_perturbation, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := NativeFunctionalObstruction.evidence.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_coordinate_perturbation) (Realization NativeFunctionalObstruction.signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.finite_coordinate_perturbation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction.Perturbation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NativeFunctionalObstruction.signature
    (fun _ p v => v p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "type", "arg"]
      stateBinder := 3
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Perturbation


namespace Obstruction

abbrev rejected : Realization NativeFunctionalObstruction.signature := by
  classical
  exact realize NativeFunctionalObstruction.signature
    (fun _ p v => if ∃ n, v p.2.2 = atomic n then v p.2.2 else Omega)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := NativeFunctionalObstruction.signature
  Law R := ∀ (a : Nat) (H : Homogeneous), PairRoot H →
    eval H (leaf true) = atomic a → ∀ family : List NativeComponent,
      {X : CompletionTree | rho^[a] X = eval H X} ≠
        {X : CompletionTree | ∃ C ∈ family, ∃ v,
          NativeSatisfies C.equations v ∧
          R.readout () ⟨C.states, (fun _ => none), C.designated⟩ v = X}

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro law
  let H : Homogeneous := .mul (.of 1) (.of 0)
  have root : PairRoot H := ⟨.of 1, .of 0, rfl⟩
  have anchor : eval H (leaf true) = atomic 2 := by
    change node (rho (leaf true)) (leaf true) = rho (rho (leaf true))
    rw [rho_alpha, rho_beta]
  let C : NativeComponent := ⟨1, (fun _ => none), 0⟩
  have impossible := law 2 H root anchor [C]
  apply impossible
  ext X
  change (rho^[2] X = eval H X) ↔
    ∃ D ∈ [C], ∃ v, NativeSatisfies D.equations v ∧
      rejected.readout () ⟨D.states, (fun _ => none), D.designated⟩ v = X
  have sat : ∀ v : Fin 1 → CompletionTree, NativeSatisfies C.equations v := by
    intro v i E eq
    cases eq
  constructor
  · intro feedback
    rcases (completed_homogeneous_split 2 H root X).mp feedback with rfl | ⟨_, n, rfl⟩
    · refine ⟨C, by simp, (fun _ => Omega), sat _, ?_⟩
      change (if ∃ n, Omega = atomic n then Omega else Omega) = Omega
      simp only [ite_self]
    · refine ⟨C, by simp, (fun _ => atomic n), sat _, ?_⟩
      change (if ∃ k, atomic n = atomic k then atomic n else Omega) = atomic n
      exact ite_eq_left ⟨n, rfl⟩
  · rintro ⟨D, mem, v, _, hx⟩
    have eqD : D = C := by simpa only [List.mem_singleton] using mem
    subst D
    change (if ∃ n, v 0 = atomic n then v 0 else Omega) = X at hx
    apply (completed_homogeneous_split 2 H root X).mpr
    by_cases h : ∃ n, v 0 = atomic n
    · rw [ite_eq_left h] at hx
      obtain ⟨n, hn⟩ := h
      exact Or.inr ⟨anchor, n, hx.symm.trans hn⟩
    · rw [ite_eq_right h] at hx
      exact Or.inl hx.symm

def evidence : Registration arena (type_of% (@rank_free_obstruction)) where
  actual := NativeFunctionalObstruction.actual
  bridge := Iff.rfl
  variation := ⟨rank_free_obstruction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := NativeFunctionalObstruction.evidence.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rank_free_obstruction) (Realization NativeFunctionalObstruction.signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.rank_free_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction.Obstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize NativeFunctionalObstruction.signature
    (fun _ p v => v p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
    definition := some {
      owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction
      name := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFunctionalObstruction.nativeProjected
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 2
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end Obstruction

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFunctionalObstruction

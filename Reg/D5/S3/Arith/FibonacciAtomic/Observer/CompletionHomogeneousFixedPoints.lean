import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
noncomputable section

abbrev signature : Signature where
  Params := Σ a : Nat, Homogeneous
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ q X => eval q.2 X) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Nat) (H : Homogeneous), PairRoot H → ∀ (X : CompletionTree),
      (rho^[a] X = R.readout () ⟨a, H⟩ X ↔
        X = Omega ∨
          (R.readout () ⟨a, H⟩ (leaf true) = atomic a ∧
            ∃ c : Nat, X = atomic c))

theorem actual_law : arena.Law actual := by
  intro a H root X
  simpa only [actual, realize] using completed_homogeneous_split a H root X

private theorem omega_ne_leaf_true : Omega ≠ leaf true := by
  have omega_node : Omega = node Omega Omega := by
    unfold Omega
    conv_lhs => rw [PFunctor.M.corec_def]
    simp only [PFunctor.map, Function.comp_def, node, ite_self]
    rfl
  have leaf_ne_node (b : Bool) (l r : CompletionTree) : leaf b ≠ node l r := by
    intro h
    have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
    have hh' : Sum.inl b = Sum.inr () := by
      simpa [leaf, node] using hh
    cases hh'
  intro h
  rw [omega_node] at h
  exact leaf_ne_node true Omega Omega h.symm

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad : Omega = leaf true := by
    have hbad := (h 0 (.mul (FreeMagma.of 0) (FreeMagma.of 0))
      (by refine ⟨FreeMagma.of 0, FreeMagma.of 0, rfl⟩) Omega).mpr (Or.inl rfl)
    simpa only [rejected, realize, Function.iterate_zero, id_eq] using hbad
  exact omega_ne_leaf_true bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0, FreeMagma.of 0⟩, leaf true, leaf false, ?_⟩
    have hleaf : leaf true ≠ leaf false := by
      intro h
      have hh := congrArg (fun X => (PFunctor.M.dest X).1) h
      have hh' : (Sum.inl true : Bool ⊕ Unit) = Sum.inl false := by
        simpa only [leaf, PFunctor.M.dest_mk] using hh
      have hbool : (true : Bool) = false := Sum.inl.inj hh'
      cases hbool
    simpa [actual, realize, eval, Function.iterate_zero] using hleaf

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints.completed_homogeneous_split)
    (type_of% (realize.{0, 0, 0, 0, 0} signature
      (fun _ q X => eval q.2 X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints.completed_homogeneous_split,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ q X => eval q.2 X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints,
    definition := none, coordinates := #[0, 1],
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints

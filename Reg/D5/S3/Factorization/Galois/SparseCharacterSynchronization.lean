import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Galois.SparseCharacterSynchronization
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ZMod

namespace Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization

open _root_.D5.S3.Factorization.Galois.SparseCharacterSynchronization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v

/-- Keep the source vertex type, graph, coefficient type and group instance.
The observed state is its additive homomorphism; the readout is the actual kernel. -/
def signature : Signature where
  Params := Σ (V : Type u), Σ (_ : SimpleGraph V), Σ (A : Type v), AddCommGroup A
  State p := by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact (p.1 → p.2.2.1) →+
      ({e : p.1 × p.1 // p.2.1.Adj e.1 e.2} → p.2.2.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact AddSubgroup (p.1 → p.2.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace only the selected kernel application. The entire original telescope,
constant subgroup and graph preconnectedness remain in the law. -/
def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {V : Type u} (G : SimpleGraph V) (A : Type v)
    [inst : AddCommGroup A] [Nontrivial A],
    r.readout () ⟨V, G, A, inst⟩ (edgeDifference G A) =
      (Pi.constAddMonoidHom V A).range ↔ G.Preconnected

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p f => by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact f.ker) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ => by
    letI : AddCommGroup p.2.2.1 := p.2.2.2
    exact (⊤ : AddSubgroup (p.1 → p.2.2.1))) (fun e => nomatch e)

/-- The intervention admits a nonconstant labeling on a connected two-vertex graph. -/
theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A := ULift.{v} (ZMod 2)
  let x : ULift.{u} Bool → A := fun i => if i.down then 1 else 0
  have heq := (h (⊤ : SimpleGraph (ULift.{u} Bool)) A).mpr
    SimpleGraph.preconnected_top
  have hx : x ∈ (Pi.constAddMonoidHom (ULift.{u} Bool) A).range :=
    heq ▸ (show x ∈ (⊤ : AddSubgroup (ULift.{u} Bool → A)) from trivial)
  obtain ⟨a, ha⟩ := hx
  have hzero : a = 0 := by
    have : a = x ⟨false⟩ := congrFun ha ⟨false⟩
    simpa [x] using this
  have hone : a = 1 := by
    have : a = x ⟨true⟩ := congrFun ha ⟨true⟩
    simpa [x] using this
  exact zero_ne_one (hzero.symm.trans hone)

def registration : Registration arena.{u,v}
    (∀ {V : Type u} (G : SimpleGraph V) (A : Type v)
      [AddCommGroup A] [Nontrivial A],
      (edgeDifference G A).ker = (Pi.constAddMonoidHom V A).range ↔ G.Preconnected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro V G A _ _; exact edge_difference_kernel_eq_constants_iff G A,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let V := ULift.{u} Bool
    let A := ULift.{v} (ZMod 2)
    let G : SimpleGraph V := ⊤
    let x : V → A := fun j => if j.down then 1 else 0
    refine ⟨⟨V, G, A, inferInstance⟩, edgeDifference G A,
      (0 : (V → A) →+ ({e : V × V // G.Adj e.1 e.2} → A)), ?_⟩
    change (edgeDifference G A).ker ≠ (0 : (V → A) →+ _).ker
    intro h
    have hx : x ∈ (edgeDifference G A).ker := by
      rw [h, AddMonoidHom.mem_ker]
      rfl
    have he := congrFun (AddMonoidHom.mem_ker.mp hx)
      ⟨(⟨false⟩, ⟨true⟩), by
        change (⟨false⟩ : V) ≠ ⟨true⟩
        intro heq
        cases congrArg ULift.down heq⟩
    have hbad : (0 : A) = 1 := by
      apply sub_eq_zero.mp
      simpa [edgeDifference, x] using he
    exact zero_ne_one hbad

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{max ((max u v) + 2) ((max (u + 1) (v + 1)) + 2), max ((max u v) + 2) ((max (u + 1) (v + 1)) + 2), max (u + 1) (v + 1), 1, 1, 0, 1, 1, 0, 0, 0, max (u + 1) (v + 1), max u v, 0, max u v, 0, 0} (@_root_.D5.S3.Factorization.Galois.SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff.{u, v}) (type_of% (arena.{u, v})) (type_of% (arena.{u, v})) (type_of% (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0} signature.{u, v}
    (fun (_ : Unit) (p : signature.Params) (f : signature.State p) => by
      letI : AddCommGroup.{v} p.2.2.1 := p.2.2.2
      exact f.ker)
    (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "Galois") "SparseCharacterSynchronization") "edge_difference_kernel_eq_constants_iff") "Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization/Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization.registration,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena.{u, v})⟩,
  objectArena := ⟨(arena.{u, v})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u, v}) ⟨(registration.{u, v})⟩,
  readout := some (realize.{max (u + 1) (v + 1), max u v, 0, max u v, 0} signature.{u, v}
    (fun (_ : Unit) (p : signature.Params) (f : signature.State p) => by
      letI : AddCommGroup.{v} p.2.2.1 := p.2.2.2
      exact f.ker)
    (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.Galois.SparseCharacterSynchronization, definition := none, coordinates := #[0, 1, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end Reg.D5.S3.Factorization.Galois.SparseCharacterSynchronization

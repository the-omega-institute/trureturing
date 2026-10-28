import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
open _root_.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

structure Parameters where
  index : Type u
  finite : Fintype index
  decidable : DecidableEq index
  generator : Matrix index index ℝ

abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Parameters.{u}
  State p := Matrix p.index p.index ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℝ → Matrix p.index p.index ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p X => by
    letI := p.finite
    letI := p.decidable
    exact conjugate p.generator X) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature
  (fun _ _ X t => if t = 0 then X else 0) (fun e => nomatch e)
abbrev arena : Arena.{u+1,u,0,u,0} where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    ∀ X k t, 0 ≤ t → R.readout () p ((_root_.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan.commutator p.generator)^[k] X) t ∈
      Submodule.span ℝ (R.readout () p X '' Set.Ici 0)

private theorem bridge :
    (type_of% (@commutator_jets_in_nonnegative_span.{u})) ↔ (arena.{u}).Law (actual.{u}) := by
  constructor
  · intro h p
    letI := p.finite
    letI := p.decidable
    exact h p.generator
  · intro h n finite decidable A X k t ht
    exact h ⟨n,finite,decidable,A⟩ X k t ht

private theorem rejected_law : ¬ arena.Law (rejected.{u}) := by
  intro h
  let n := ULift.{u} (Fin 2)
  let a : n := ⟨0⟩
  let b : n := ⟨1⟩
  have hab : a ≠ b := by decide
  let p : Parameters := ⟨n, inferInstance, inferInstance, Matrix.single a b 1⟩
  let X : Matrix n n ℝ := Matrix.single a a 1
  have hm := h p X 1 0 le_rfl
  let entry : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun M => M a b, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  have hs : Submodule.span ℝ ((fun t : ℝ => if t = 0 then X else 0) '' Set.Ici 0) ≤
      LinearMap.ker entry := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,rfl⟩
    by_cases hzero : t = 0 <;> simp [hzero, entry, X, Matrix.single_apply, hab, Ne.symm hab]
  have hz := hs hm
  norm_num [arena, rejected, realize, p, X, entry, Function.iterate_succ_apply',
    _root_.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan.commutator,
    Matrix.single_mul_single_same, Matrix.single_apply, hab, Ne.symm hab] at hz

def family : Registration (arena.{u}) (type_of% (@commutator_jets_in_nonnegative_span.{u})) where
  actual := actual
  bridge := bridge.{u}
  variation := ⟨bridge.{u}.mp (@commutator_jets_in_nonnegative_span.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    let n := ULift.{u} (Fin 1)
    let p : Parameters := ⟨n, inferInstance, inferInstance, 0⟩
    refine ⟨p, 0, 1, ?_⟩
    intro h
    have he := congrArg (fun f => f 0 ⟨0⟩ ⟨0⟩) h
    norm_num [actual, realize, conjugate, p] at he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan.commutator_jets_in_nonnegative_span.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p X => by
      letI := p.finite
      letI := p.decidable
      exact conjugate p.generator X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Fibers.NonnegativeConjugationSpan

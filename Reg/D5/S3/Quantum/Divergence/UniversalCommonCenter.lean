import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Divergence.UniversalCommonCenter

/-! The literal finite common-center source family and its actual quadratic readout. -/

noncomputable section
universe u v
open Set Matrix
open scoped ComplexOrder InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Quantum.Divergence.UniversalCommonCenter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UniversalCommonCenter

structure Parameters where
  r : Type u
  a : Type v
  fr : Fintype r
  dr : DecidableEq r
  fa : Fintype a
  da : DecidableEq a
  A : Matrix (r × a) (r × a) ℂ
  B : Matrix (r × a) (r × a) ℂ

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Matrix p.r p.r ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.r × p.a) (p.r × p.a) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p X => by
    letI := p.fr
    letI := p.dr
    letI := p.fa
    letI := p.da
    exact (p.A - Matrix.kronecker X (1 : Matrix p.a p.a ℂ)) *
      (p.A - Matrix.kronecker X (1 : Matrix p.a p.a ℂ))ᴴ)
    (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ p _ => by
    letI := p.dr
    letI := p.da
    exact p.B + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {r : Type u} {a : Type v} [fr : Fintype r] [dr : DecidableEq r]
    [fa : Fintype a] [da : DecidableEq a] [Nonempty a]
    (A B : Matrix (r × a) (r × a) ℂ) (hB : B.IsHermitian)
    (htrace : ∀ Z : Matrix (r × a) (r × a) ℂ, Z.PosDef →
      sInf (Set.range (fun X : Matrix r r ℂ =>
        (Z * ((A - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          (A - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ)).trace.re)) ≤ (Z * B).trace.re),
    ∃ X : Matrix r r ℂ,
      (B - R.readout () ⟨r, a, fr, dr, fa, da, A, B⟩ X).PosSemidef

theorem source_equivalence :
    (type_of% @exists_common_center_of_posDef_trace_inf_le.{u,v}) ↔
      arena.{u,v}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let r := ULift.{u} Unit
  let a := ULift.{v} Unit
  have ht : ∀ Z : Matrix (r × a) (r × a) ℂ, Z.PosDef →
      sInf (Set.range (fun X : Matrix r r ℂ =>
        (Z * (((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ)).trace.re)) ≤
        (Z * 0).trace.re := by
    intro Z hZ
    have hb : BddBelow (Set.range (fun X : Matrix r r ℂ =>
        (Z * (((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker X (1 : Matrix a a ℂ)) *
          ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker X (1 : Matrix a a ℂ))ᴴ)).trace.re)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨X, rfl⟩
      let Q := (0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker X (1 : Matrix a a ℂ)
      have hp := (hZ.posSemidef.conjTranspose_mul_mul_same Q).trace_nonneg
      have hre := (Complex.nonneg_iff.mp hp).1
      calc
        0 ≤ (Qᴴ * (Z * Q)).trace.re := by simpa only [Matrix.mul_assoc] using hre
        _ = (Q * (Qᴴ * Z)).trace.re := by
          rw [Matrix.trace_mul_cycle']
        _ = (Z * (Q * Qᴴ)).trace.re := by
          rw [Matrix.trace_mul_cycle']
    have hh := csInf_le hb (Set.mem_range_self (0 : Matrix r r ℂ))
    simpa using hh
  obtain ⟨X, hX⟩ := h (r := r) (a := a) 0 0 Matrix.isHermitian_zero ht
  change (0 - ((0 : Matrix (r × a) (r × a) ℂ) + 1)).PosSemidef at hX
  have hd := (Complex.nonneg_iff.mp (hX.diag_nonneg (i := (⟨()⟩, ⟨()⟩)))).1
  norm_num [Matrix.one_apply] at hd

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  let r := ULift.{u} Unit
  let a := ULift.{v} Unit
  let p : Parameters.{u,v} := ⟨r, a, inferInstance, inferInstance, inferInstance,
    inferInstance, 0, 0⟩
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have hzero : actual.readout i p 0 = 0 := by
    change ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker (0 : Matrix r r ℂ) 1) *
      ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker (0 : Matrix r r ℂ) 1)ᴴ = 0
    simp
  have hone : actual.readout i p 1 = 1 := by
    change ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker (1 : Matrix r r ℂ) 1) *
      ((0 : Matrix (r × a) (r × a) ℂ) - Matrix.kronecker (1 : Matrix r r ℂ) 1)ᴴ = 1
    simp [Matrix.kronecker]
  rw [hzero, hone] at he
  have hh := congrArg (fun M : Matrix (r × a) (r × a) ℂ => M (⟨()⟩, ⟨()⟩) (⟨()⟩, ⟨()⟩)) he
  exact zero_ne_one hh

def family : Registration arena.{u,v}
    (type_of% @exists_common_center_of_posDef_trace_inf_le.{u,v}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@exists_common_center_of_posDef_trace_inf_le.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_common_center_of_posDef_trace_inf_le.{u,v})
    (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UniversalCommonCenter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p X => by
    letI := p.fr
    letI := p.dr
    letI := p.fa
    letI := p.da
    exact (p.A - Matrix.kronecker X (1 : Matrix p.a p.a ℂ)) *
      (p.A - Matrix.kronecker X (1 : Matrix p.a p.a ℂ))ᴴ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UniversalCommonCenter
    definition := none
    coordinates := #[0, 1, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_equivalence
#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UniversalCommonCenter

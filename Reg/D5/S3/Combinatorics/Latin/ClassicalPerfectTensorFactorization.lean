module

public import LeanInformationAuditInterface.Contract.Registration
public import D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
public import Reg.Support.DependentFamily
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Source-bound audit of the first factor's four-column graph. -/

public section

namespace Reg.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization

open _root_.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
noncomputable section

abbrev signature : Signature where
  Params := Type u
  State x := x × x → x × x
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ x := x × x → Fin 4 → x
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ a => gateGraph a) (fun e => nomatch e)

/-- Collapse the graph to its first output column. -/
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ a t _ => (a t).1) (fun e => nomatch e)

/-- Keep all finite carriers, hypotheses and three factor conclusions. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (x : Type u) [Fintype x] [DecidableEq x] (a b c : x × x → x × x),
    IsIndexOneOA (circuitGraph a b c) 3 →
      IsIndexOneOA (R.readout () x a) 2 ∧ IsIndexOneOA (gateGraph b) 2 ∧
        IsIndexOneOA (gateGraph c) 2

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev Field := ULift.{u} (ZMod 5)

private def witnessA (t : Field × Field) : Field × Field :=
  (t.1 + t.2, t.1 + 4 * t.2)

private def witnessB (t : Field × Field) : Field × Field :=
  (t.1 + t.2, t.1 + 2 * t.2)

private def witnessC (t : Field × Field) : Field × Field :=
  (t.1 + 2 * t.2, t.1 + 3 * t.2)

/-- The six linear column forms of the explicit five-symbol circuit. -/
private def coefficients : Matrix (Fin 6) (Fin 3) Field :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1; 1, 1, 1; 3, 1, 4; 4, 2, 1]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem minors : ∀ cols : Fin 3 → Fin 6, Function.Injective cols →
    Matrix.det (fun i j => coefficients (cols i) j) ≠ 0 := by
  simp only [Matrix.det_fin_three]
  decide

private def vector (t : Field × Field × Field) : Fin 3 → Field :=
  ![t.1, t.2.1, t.2.2]

private theorem vector_bijective : Function.Bijective vector.{u} := by
  constructor
  · intro s t h
    exact Prod.ext (congrFun h 0) (Prod.ext (congrFun h 1) (congrFun h 2))
  · intro v
    refine ⟨(v 0, v 1, v 2), ?_⟩
    funext i
    fin_cases i <;> rfl

private theorem witness_graph (t : Field × Field × Field) (i : Fin 6) :
    circuitGraph witnessA witnessB witnessC t i =
      (coefficients *ᵥ vector t) i := by
  apply ULift.down_injective
  fin_cases i <;>
    simp [circuitGraph, circuit, witnessA, witnessB, witnessC, coefficients, vector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem witness_perfect :
    IsIndexOneOA (circuitGraph witnessA.{u} witnessB witnessC) 3 := by
  intro cols hc
  have hm := (Matrix.mulVec_injective_of_det_ne_zero (minors cols hc)).bijective_of_finite
  have he : (fun t => fun i => circuitGraph witnessA witnessB witnessC t (cols i)) =
      (fun v => (fun i j => coefficients (cols i) j) *ᵥ v) ∘ vector := by
    funext t i
    exact witness_graph t (cols i)
  rw [he]
  exact hm.comp vector_bijective

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have bad := (law Field witnessA witnessB witnessC witness_perfect).1
  have hinj : Function.Injective (![0, 1] : Fin 2 → Fin 4) := by decide
  have impossible := (bad ![0, 1] hinj).2 ![0, 1]
  obtain ⟨t, ht⟩ := impossible
  have hzero := congrFun ht 0
  have hone := congrFun ht 1
  change (witnessA t).1 = 0 at hzero
  change (witnessA t).1 = 1 at hone
  exact zero_ne_one (hzero.symm.trans hone)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Bool, (fun _ => (⟨false⟩, ⟨false⟩)),
    (fun _ => (⟨true⟩, ⟨true⟩)), ?_⟩
  intro h
  have he := congrFun (congrFun h (⟨false⟩, ⟨false⟩)) 2
  exact Bool.noConfusion (congrArg ULift.down he)

def source_registration : Registration arena.{u} claim.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.result.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => gateGraph a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
    definition := some {
      owner := `D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
      name := `D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.result
#print _root_.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization

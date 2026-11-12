import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.ThreeLegChoiCompression
import Reg.Support.DependentFamily

/-! Source-family audit attempt for the explicit three-leg Choi detector. -/

namespace Reg.D5.S3.Quantum.Foundation.ThreeLegChoiCompression

open _root_.D5.S3.Quantum.Foundation.ThreeLegChoiCompression
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ d : Type u, MatrixMap d d ℂ
  State p := MatrixMap p.1 p.1 ℂ → Matrix (p.1 × p.1) (p.1 × p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.1) (p.1 × p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p choi => choi p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {d : Type u} [Fintype d] [DecidableEq d] [Nonempty d]
    (Phi : MatrixMap d d ℂ) (alpha : Fin 3 → ℝ) (_ : ∑ l, alpha l = 1),
    ghz (d := d) = Matrix.vecMulVec ghzVector (star ghzVector) ∧
    (ghz (d := d)).PosSemidef ∧ Matrix.trace (ghz (d := d)) = 1 ∧
    (readout (d := d))ᴴ * averaged alpha Phi ghz * readout =
      (Fintype.card d : ℂ)⁻¹ • r.readout () ⟨d, Phi⟩
        (fun psi : MatrixMap d d ℂ => psi.choi_matrix) ∧
    (readout (d := d))ᴴ * readout =
      Matrix.diagonal (fun p => if p.1 = p.2 then (1 : ℂ) else 3) ∧
    Function.Injective (readout (d := d)).mulVec ∧
    ((3 : ℂ) • (1 : Matrix (d × d) (d × d) ℂ) -
      (readout (d := d))ᴴ * readout).PosSemidef ∧
    ((averaged alpha Phi ghz).PosSemidef → Phi.IsCompletelyPositive)

set_option maxRecDepth 4096 in
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Phi : MatrixMap (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ := LinearMap.id
  let alpha : Fin 3 → ℝ := ![1, 0, 0]
  have ha : ∑ l, alpha l = 1 := by norm_num [alpha, Fin.sum_univ_succ]
  have hbad := @h (ULift.{u} (Fin 1)) inferInstance inferInstance inferInstance Phi alpha ha
  have hgood := three_leg_choi_detector Phi alpha ha
  have heq := hgood.2.2.2.1.symm.trans hbad.2.2.2.1
  let p : ULift.{u} (Fin 1) × ULift.{u} (Fin 1) := (⟨0⟩, ⟨0⟩)
  have hv := congrArg (fun M => M p p) heq
  norm_num [rejected, realize, Phi, p, MatrixMap.choi_matrix, Matrix.single] at hv
  exact one_ne_zero hv

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : signature.{u}.Params := ⟨ULift.{u} (Fin 1), LinearMap.id⟩
  refine ⟨p, (fun _ => 0), (fun _ _ _ => 1), ?_⟩
  intro h
  let q : ULift.{u} (Fin 1) × ULift.{u} (Fin 1) := (⟨0⟩, ⟨0⟩)
  have hv := congrArg (fun M => M q q) h
  change (0 : ℂ) = 1 at hv
  exact zero_ne_one hv

def source_registration : Registration arena.{u} (type_of% @three_leg_choi_detector.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_leg_choi_detector, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence


namespace DirectSum
set_option backward.isDefEq.respectTransparency false
universe v

abbrev signature : Signature where
  Params := Σ I : Type u, I → Type v
  State p := TripleBlocks p.2 → TripleBlocks p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := TripleBlocks p.2 → TripleBlocks p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ lift => lift) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ Z => -Z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (D : I → Type v) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    [Nonempty I] [∀ i, Nonempty (D i)]
    (Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D)
    (alpha : Fin 3 → ℝ) (_ : ∀ l, 0 ≤ alpha l) (_ : ∑ l, alpha l = 1),
    TriplePositive D (probe D) ∧
    (∑ i, ∑ j, ∑ k, Matrix.trace (probe D i j k)) = 1 ∧
    (TriplePositive D (r.readout () ⟨I, D⟩ (blockAveraged D alpha Phi) (probe D)) ↔
      ∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi) ∧
    ((∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
        f.toLinearMap = canonicalLinear D Phi) ↔
      ∀ Z : TripleBlocks D, TriplePositive D Z →
        TriplePositive D (r.readout () ⟨I, D⟩ (blockAveraged D alpha Phi) Z))

set_option maxRecDepth 4096 in
theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let I := ULift.{u} (Fin 1)
  let D : I → Type v := fun _ => ULift.{v} (Fin 1)
  let Phi : BlockAlgebra D →ₗ[ℂ] BlockAlgebra D := LinearMap.id
  let alpha : Fin 3 → ℝ := ![1, 0, 0]
  have ha : ∀ l, 0 ≤ alpha l := by intro l; fin_cases l <;> norm_num [alpha]
  have hs : ∑ l, alpha l = 1 := by norm_num [alpha, Fin.sum_univ_succ]
  have hbad := h D Phi alpha ha hs
  have hid : ∃ f : CompletelyPositiveMap (CStarBlocks D) (CStarBlocks D),
      f.toLinearMap = canonicalLinear D Phi := by
    refine ⟨{toLinearMap := LinearMap.id, map_cstarMatrix_nonneg' := ?_}, ?_⟩
    · intro k M hM
      simpa using hM
    · rfl
  have hp := hbad.2.2.1.mpr hid
  let i : I := ⟨0⟩
  let a : D i := ⟨0⟩
  have hv := (hp i i i).diag_nonneg (i := (a, a, a))
  norm_num [rejected, realize, i, a, D, probe, seed, totalDimension,
    ghz, diagonalVector, Matrix.vecMulVec] at hv
  all_goals
    simp [Pi.single, i] at hv

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  let I := ULift.{u} (Fin 1)
  let D : I → Type v := fun _ => ULift.{v} (Fin 1)
  let p : signature.{u,v}.Params := ⟨I, D⟩
  let oneLift : signature.{u,v}.State p := fun _ _ _ _ => 1
  refine ⟨p, 0, oneLift, ?_⟩
  intro h
  let i : I := ⟨0⟩
  let a : D i := ⟨0⟩
  have hv := congrArg (fun L => L 0 i i i (a, a, a) (a, a, a)) h
  change (0 : ℂ) = 1 at hv
  exact zero_ne_one hv

def source_registration : Registration arena.{u,v} (type_of% @direct_sum_three_leg_detector.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@direct_sum_three_leg_detector, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence


def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@direct_sum_three_leg_detector.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.ThreeLegChoiCompression.DirectSum.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.ThreeLegChoiCompression.DirectSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ lift => lift) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end DirectSum

end
end Reg.D5.S3.Quantum.Foundation.ThreeLegChoiCompression

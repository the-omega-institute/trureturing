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

end
end Reg.D5.S3.Quantum.Foundation.ThreeLegChoiCompression

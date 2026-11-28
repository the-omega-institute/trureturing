import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Source-bound observation of the trinification subgroup in the cubic stabilizer. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Stabilizer
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def flipSL3 : Matrix.SpecialLinearGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal ![-1, -1, 1], by
    norm_num [Matrix.det_diagonal, Fin.prod_univ_succ]⟩

private def flipGroup : TrinifGroup := (flipSL3, 1, 1)

private theorem mapVaries : trinifInCubicGroup 1 ≠ trinifInCubicGroup flipGroup := by
  intro h
  have he := congrArg (fun a : E6CubicGroup =>
    (a.val ((1, 0, 0) : Trinif27)).1 0 0) h
  change (OmegaMath.CyclicMatrixCubic.changeBasis (1 : TrinifGroup)
    ((1, 0, 0) : Trinif27)).1 0 0 =
      (OmegaMath.CyclicMatrixCubic.changeBasis flipGroup
        ((1, 0, 0) : Trinif27)).1 0 0 at he
  norm_num [OmegaMath.CyclicMatrixCubic.changeBasis, flipGroup, flipSL3] at he


abbrev stabilizerSignature : Signature := signature Unit (fun _ => TrinifGroup) (fun _ => E6CubicGroup)

abbrev stabilizerArena : Arena where
  signature := stabilizerSignature
  Law R := ∀ (g : TrinifGroup),
    rotationInCubicGroup * R.readout () () g =
      trinifInCubicGroup (OmegaMath.CyclicMatrixCubic.rotateGroup g) * rotationInCubicGroup ∧
    rotationInCubicGroup ^ 3 = 1 ∧ rotationInCubicGroup ≠ 1

def stabilizerFamily : Registration stabilizerArena (type_of% (@trinif_cubic_stabilizer)) :=
  e6Family% stabilizerArena (@trinif_cubic_stabilizer) (realize stabilizerSignature (fun _ _ g => trinifInCubicGroup g) (fun e => nomatch e))
    (by
      exact ⟨(), 1, flipGroup, mapVaries⟩)
    (realize stabilizerSignature (fun _ _ _ => rotationInCubicGroup) (fun e => nomatch e))
    (by
      intro h
      have hh := (h 1).1
      have hr : OmegaMath.CyclicMatrixCubic.rotateGroup (1 : TrinifGroup) = 1 := rfl
      change rotationInCubicGroup * rotationInCubicGroup = _ at hh
      rw [hr, map_one, one_mul] at hh
      have he : rotationInCubicGroup = 1 := mul_left_cancel (hh.trans (mul_one _).symm)
      exact (trinif_cubic_stabilizer 1).2.2 he)

def stabilizerRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trinif_cubic_stabilizer) (Realization stabilizerSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trinif_cubic_stabilizer.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Stabilizer.stabilizerFamily
    stabilizerArena stabilizerFamily (realize stabilizerSignature (fun _ _ g => trinifInCubicGroup g) (fun e => nomatch e))
    #[] (e6Path% trinif_cubic_stabilizer DFunLike.coe 6 0) 0 false none

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Stabilizer

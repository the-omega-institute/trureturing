import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import Reg.Support.DependentFamily

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

namespace Reg.D5.S3.Geometry.Hyperideal.NativeRadicand

abbrev signature : Signature where
  Params := Σ _x : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => rad p.1 p.2 z)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x y z : ℝ) (_hx : 1 < x) (_hy : 1 < y) (_hz : 1 < z),
    0 < R.readout () ⟨x,y⟩ z

private def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 2 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected,realize] at hh

def radicand_family : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨2,2⟩,2,3,?_⟩
    norm_num [actual,realize,rad]

#print axioms radicand_family
end Reg.D5.S3.Geometry.Hyperideal.NativeRadicand

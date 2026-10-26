import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion
import Reg.Support.DependentFamily

/-! Complete dependent source coordinates for the actual occupied-position readback. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreJoint MiuraSlabIncidence
  MiuraFiberIndexed MiuraFiberInverseExpansion
open scoped BigOperators

abbrev Parameter := (ℕ × ℕ) × (ℕ × ℕ)

structure State (p : Parameter) where
  a : ℕ
  b : ℕ
  g : Cell p.1.1 p.1.2 → ℤ
  h : Cell p.2.1 p.2.2 → ℤ
  red : JointReduction g h
  hm : 2 ≤ p.1.1
  hn : 2 ≤ p.1.2
  hg : Residual a b g
  hM : 2 ≤ p.2.1
  hN : 2 ≤ p.2.2
  hh : IsHeight h

abbrev Readout (p : Parameter) := (Fin p.2.1 → ℕ) × (Fin p.2.2 → ℕ)

def Law {p : Parameter} (x : State p) (v : Readout p) : Prop :=
  (∀ i,0 < v.1 i → frozenColumn (transposeHeight x.h) i) ∧
  (∀ j,0 < v.2 j → frozenColumn x.h j) ∧
  p.1.1=p.2.1+∑ i,v.1 i ∧ p.1.2=p.2.2+∑ j,v.2 j ∧
  (∀ k,activeColumn x.g k ↔ ∃ j,activeColumn x.h j ∧ k.val=columnPosition v.2 j) ∧
  (∀ k,activeColumn (transposeHeight x.g) k ↔
    ∃ i,activeColumn (transposeHeight x.h) i ∧ k.val=columnPosition v.1 i)

theorem actual_law (p : Parameter) (x : State p) : ∃ v : Readout p,Law x v := by
  obtain ⟨r,c,H⟩ := reduction_indexed_active x.a x.b x.g x.h x.red
    x.hm x.hn x.hg x.hM x.hN x.hh
  exact ⟨(r,c),H⟩

theorem bridge : (type_of% (@reduction_indexed_active)) ↔
    ∀ p (x : State p),∃ v : Readout p,Law x v := by
  constructor
  · intro H p x
    obtain ⟨r,c,Hrc⟩ := H x.a x.b x.g x.h x.red x.hm x.hn x.hg x.hM x.hN x.hh
    exact ⟨(r,c),Hrc⟩
  · intro H a b m n M N g h red hm hn hg hM hN hh
    obtain ⟨v,hv⟩ := H ((m,n),(M,N)) ⟨a,b,g,h,red,hm,hn,hg,hM,hN,hh⟩
    exact ⟨v.1,v.2,hv⟩

end Reg.D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion

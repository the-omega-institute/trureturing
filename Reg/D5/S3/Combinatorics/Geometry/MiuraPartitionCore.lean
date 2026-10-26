import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraPartitionCore
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Exact dependent source family and the actual selected positive-run core. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraPartitionCore
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreJoint MiuraPolynomialCoreSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

structure Parameter where
  a : ℕ
  b : ℕ
  m : ℕ
  n : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hd : 5 ≤ a + b
  hm : 2 * (a + b) - 1 ≤ m
  hn : 2 * (a + b) - 1 ≤ n

abbrev State (p : Parameter) := {h : Cell p.m p.n → ℤ // Residual p.a p.b h}

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun p => Core p.a p.b)

def actual : Realization signature := realize signature
  (fun (_ : Unit) p x => Classical.choose
    (MiuraPartitionCore.residual_core_exists p.a p.b p.ha p.hb p.hd p.hm p.hn x.val x.property))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p),
    JointReduction x.val (R.readout () p x).2.2.val ∧
      ∀ sd, AllOnSide (fun v : Cell p.m p.n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
        (minima x.val) (p.m : ℤ) (p.n : ℤ) sd ↔
      AllOnSide (fun v : Cell (R.readout () p x).1.val (R.readout () p x).2.1.val =>
        ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
        (minima (R.readout () p x).2.2.val)
        ((R.readout () p x).1.val : ℤ) ((R.readout () p x).2.1.val : ℤ) sd

theorem actual_law : arena.Law actual := by
  intro p x
  exact Classical.choose_spec
    (MiuraPartitionCore.residual_core_exists p.a p.b p.ha p.hb p.hd p.hm p.hn x.val x.property)

theorem source_reconstruction : arena.Law actual →
    (type_of% (@MiuraPartitionCore.residual_core_exists)) := by
  intro law m n a b ha hb hd hm hn h hr
  let p : Parameter := ⟨a, b, m, n, ha, hb, hd, hm, hn⟩
  exact ⟨actual.readout () p ⟨h, hr⟩, law p ⟨h, hr⟩⟩

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraPartitionCore

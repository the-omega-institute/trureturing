import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraPartitionCount
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Original Core indices and original count readouts, with their full source telescopes. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraPartitionCount
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreJoint MiuraPolynomialCoreSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

namespace Unique
structure Parameter where
  a : ℕ
  b : ℕ
  m : ℕ
  n : ℕ

structure State (p : Parameter) where
  h : Cell p.m p.n → ℤ
  hh : IsHeight h
  K : Core p.a p.b
  L : Core p.a p.b
  hK : JointReduction h K.2.2.val
  hL : JointReduction h L.2.2.val

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun p => Core p.a p.b)

def actual : Realization signature := realize signature
  (fun (_ : Unit) _ x => x.K) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), R.readout () p x = x.L

theorem actual_law : arena.Law actual := by
  intro p x
  exact MiuraPartitionCount.residual_core_unique x.h x.hh x.hK x.hL

theorem bridge : (type_of% (@MiuraPartitionCount.residual_core_unique)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.h x.hh x.hK x.hL
  · intro h a b m n src hh K L hK hL
    exact h ⟨a, b, m, n⟩ ⟨src, hh, K, L, hK, hL⟩
end Unique

namespace Count
structure Parameter where
  a : ℕ
  b : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hd : 5 ≤ a + b

structure State (p : Parameter) where
  m : ℕ
  n : ℕ
  hm : 2 * (p.a + p.b) - 1 ≤ m
  hn : 2 * (p.a + p.b) - 1 ≤ n

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter State (fun _ => ℕ)

def actual : Realization signature := realize signature
  (fun (_ : Unit) p x => residualCount p.a p.b x.m x.n (by have := p.hd; have := x.hm; omega)
    (by have := p.hd; have := x.hn; omega)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), R.readout () p x =
    ∑ K : Core p.a p.b, Nat.card (MiuraPartitionCount.Fiber p.a p.b x.m x.n K)

theorem actual_law : arena.Law actual := by
  intro p x
  exact MiuraPartitionCount.residual_count_eq_sum_fibers p.a p.b x.m x.n p.ha p.hb p.hd x.hm x.hn

def rejected : Realization signature := realize signature
  (fun (_ : Unit) p x => actual.readout () p x + 1) (fun e => nomatch e)

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro law
  let p : Parameter := ⟨1, 4, by decide, by decide, by decide⟩
  let x : State p := ⟨9, 9, by decide, by decide⟩
  have good := actual_law p x
  have bad := law p x
  change actual.readout () p x =
    ∑ K : Core p.a p.b, Nat.card (MiuraPartitionCount.Fiber p.a p.b x.m x.n K) at good
  change actual.readout () p x + 1 =
    ∑ K : Core p.a p.b, Nat.card (MiuraPartitionCount.Fiber p.a p.b x.m x.n K) at bad
  exact Nat.succ_ne_self (actual.readout () p x) (bad.trans good.symm)

theorem variation : Variation arena actual := ⟨actual_law, rejected, rejected_not_law⟩

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law

theorem bridge : (type_of% (@MiuraPartitionCount.residual_count_eq_sum_fibers)) ↔
    arena.Law actual := by
  constructor
  · intro h p x
    exact h p.a p.b x.m x.n p.ha p.hb p.hd x.hm x.hn
  · intro h a b m n ha hb hd hm hn
    exact h ⟨a, b, ha, hb, hd⟩ ⟨m, n, hm, hn⟩
end Count

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraPartitionCount

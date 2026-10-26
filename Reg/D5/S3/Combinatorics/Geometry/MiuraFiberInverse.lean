import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraFiberInverse
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! The source telescope and actual complete-function readout. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraFiberInverse
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreJoint MiuraCoreNormal
  MiuraSlabIncidence MiuraFiberInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

structure State (p : ℕ × ℕ) where
  a : ℕ
  b : ℕ
  h : Cell p.1 p.2 → ℤ
  g : Cell p.1 p.2 → ℤ
  hm : 2 ≤ p.1
  hn : 2 ≤ p.2
  hh : Residual a b h
  hg : Residual a b g
  M : ℕ
  N : ℕ
  f : Cell M N → ℤ
  hf : NoAdjacentFrozen f
  hft : NoAdjacentFrozen (transposeHeight f)
  hr : JointReduction h f
  gr : JointReduction g f
  ha : ∀ j, activeColumn h j ↔ activeColumn g j
  hat : ∀ i, activeColumn (transposeHeight h) i ↔ activeColumn (transposeHeight g) i

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (ℕ × ℕ) State (fun p => Cell p.1 p.2 → ℤ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) _ x => x.h) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p),R.readout () p x=x.g

theorem actual_law : arena.Law actual := by
  intro p x
  exact same_core_same_active_equal x.a x.b x.h x.g x.hm x.hn x.hh x.hg
    x.f x.hf x.hft x.hr x.gr x.ha x.hat

theorem bridge : (type_of% (@same_core_same_active_equal)) ↔ arena.Law actual := by
  constructor
  · intro H p x
    exact H x.a x.b x.h x.g x.hm x.hn x.hh x.hg x.f x.hf x.hft x.hr x.gr x.ha x.hat
  · intro H m n M N a b h g hm hn hh hg f hf hft hr gr ha hat
    exact H (m,n) ⟨a,b,h,g,hm,hn,hh,hg,M,N,f,hf,hft,hr,gr,ha,hat⟩

end

end Reg.D5.S3.Combinatorics.Geometry.MiuraFiberInverse

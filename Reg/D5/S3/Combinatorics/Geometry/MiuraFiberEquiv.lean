import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraFiberEquiv
import Reg.Support.DependentFamily

/-! The complete positive-vector and actual-function fibers of the source statement. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraFiberEquiv
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreJoint MiuraSlabIncidence
  MiuraPolynomialCoreSum MiuraRunCompositions MiuraFiberEquiv

abbrev Parameter := Σ a : ℕ,Σ b : ℕ,Core a b × ℕ × ℕ

structure State (p : Parameter) where
  hm : 2*(p.1+p.2.1)-1 ≤ p.2.2.2.1
  hn : 2*(p.1+p.2.1)-1 ≤ p.2.2.2.2

abbrev Vector (p : Parameter) :=
  PositiveLengths (p.2.2.2.1-rowOccupied p.2.2.1) (rowRuns p.2.2.1) ×
  PositiveLengths (p.2.2.2.2-colOccupied p.2.2.1) (colRuns p.2.2.1)

abbrev Fiber (p : Parameter) :=
  {g : Cell p.2.2.2.1 p.2.2.2.2 → ℤ // Residual p.1 p.2.1 g ∧
    JointReduction g p.2.2.1.2.2.val ∧
    ∀ sd,AllOnSide (fun v : Cell p.2.2.2.1 p.2.2.2.2 =>
      ((v.1.val : ℤ)+1,(v.2.val : ℤ)+1)) (minima g)
        (p.2.2.2.1 : ℤ) (p.2.2.2.2 : ℤ) sd ↔
      AllOnSide (fun v : Cell p.2.2.1.1.val p.2.2.1.2.1.val =>
        ((v.1.val : ℤ)+1,(v.2.val : ℤ)+1)) (minima p.2.2.1.2.2.val)
          (p.2.2.1.1.val : ℤ) (p.2.2.1.2.1.val : ℤ) sd}

abbrev Readout (p : Parameter) := Vector p ≃ Fiber p

theorem actual_law (p : Parameter) (x : State p) : Nonempty (Readout p) :=
  core_positive_vectors_equiv p.1 p.2.1 p.2.2.2.1 p.2.2.2.2 p.2.2.1 x.hm x.hn

theorem bridge : (type_of% (@core_positive_vectors_equiv)) ↔
    ∀ p,State p → Nonempty (Readout p) := by
  constructor
  · intro H p x
    exact H p.1 p.2.1 p.2.2.2.1 p.2.2.2.2 p.2.2.1 x.hm x.hn
  · intro H a b m n K hm hn
    exact H ⟨a,b,K,m,n⟩ ⟨hm,hn⟩

end Reg.D5.S3.Combinatorics.Geometry.MiuraFiberEquiv

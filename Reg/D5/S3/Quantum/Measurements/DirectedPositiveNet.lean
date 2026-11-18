import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.DirectedPositiveNet

/-! Exact source reconstruction. Source-selection and four-slot certification
remain unfinished under https://github.com/the-omega-institute/trureturing/issues/29713. -/

open Set Filter Topology
open scoped ComplexOrder
noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Measurements.DirectedPositiveNet

def bounded_statement : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (X : J → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hpos : ∀ j, 0 ≤ X j) (hmono : Monotone X)
    (hupper : ∀ j, X j ≤ U),
    ∃ S : H →L[ℂ] H, IsLUB (Set.range X) S ∧
      (∀ j, ‖X j‖ ≤ ‖U‖) ∧
      (∀ v, Tendsto (fun j => X j v) atTop (𝓝 (S v)))

theorem bounded_source : bounded_statement.{u,v} :=
  @_root_.D5.S3.Quantum.Measurements.DirectedPositiveNet.exists_lub_strong_of_bdd

end Reg.D5.S3.Quantum.Measurements.DirectedPositiveNet

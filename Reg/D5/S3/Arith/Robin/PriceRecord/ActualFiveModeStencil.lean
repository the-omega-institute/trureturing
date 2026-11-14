import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeStencil
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Full-telescope actual laws and definitional source bridges.
Four-slot registration is unfinished: lawful enrolled-template application,
compiler occurrence/sourceSelection binding, whole-family intervention,
fixed-coordinate sensitivity and observational dependence remain unproved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeStencil
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace uniform_boundary_root_log_transfer
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => actualOffset p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount)
    (j : ℕ) (hj : 2 ≤ j),
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        |(j : ℝ) * log (layerPrime m j : ℝ) -
          (log (largestPrime m : ℝ) + (V.readout ()) j (largestPrime m : ℝ))| ≤
          A * (largestPrime m : ℝ) ^ (-priceExponent j)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.uniform_boundary_root_log_transfer

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.uniform_boundary_root_log_transfer)) ↔ arena.Law actual := Iff.rfl

end uniform_boundary_root_log_transfer

namespace actual_stencil_limits
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => mesh4 x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := Tendsto (fun X : ℝ => log X * (log 2 - mesh1 X)) atTop (𝓝 (log 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 2 * mesh2 X) atTop (𝓝 (log 2 ^ 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 3 * mesh3 X) atTop (𝓝 (2 * log 2 ^ 3)) ∧
    Tendsto (fun X : ℝ => log X ^ 4 * (V.readout () ()) X) atTop (𝓝 (6 * log 2 ^ 4))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_stencil_limits

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_stencil_limits)) ↔ arena.Law actual := Iff.rfl

end actual_stencil_limits

namespace actual_root_greedy_stencil
abbrev signature : Signature where
  Params := ℝ
  State _ := Fin 5
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => rootMasses p x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
    ∀ X : ℝ, T ≤ X → ∃ v : Fin 5 → ℤ,
      (∑ k : Fin 5, v k) = 0 ∧
      (∀ k : Fin 5, |(v k : ℝ)| ≤ B * log X) ∧
      0 < mesh4 X ∧ mesh4 X ≤ B / log X ^ 4 ∧
      2 * mesh4 X ≤ log 2 - ∑ k : Fin 5, (v k : ℝ) * (V.readout ()) X k ∧
      log 2 - ∑ k : Fin 5, (v k : ℝ) * (V.readout ()) X k < 3 * mesh4 X

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_root_greedy_stencil

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack.actual_root_greedy_stencil)) ↔ arena.Law actual := Iff.rfl

end actual_root_greedy_stencil

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualFiveModeStencil

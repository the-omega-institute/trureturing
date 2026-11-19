import D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- RegUNVALIDATED / UNCOMPILED_UNACCEPTED. Full-telescope typed ATTEMPTS only.
For EVERY target below:
 escapeFrom: named literal source readout; compiled occurrence binding is pending.
 readout: typed actual realization; lawful enrollment and sourceSelection are pending.
 realization: ENTIRE original telescope, actual_law, definitional source_bridge;
 rejected lawful families, whole-family intervention, other-readout/anchor-fixed
 sensitivity, actual observational dependence and axiom closure remain missing.
 continuation: unknown. No registration, binding or validation is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open Real Filter Finset
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace fixed_layer_root_offset_tendsto
/- Source readout: actual real beta cutoff. RegUNVALIDATED. -/
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
  realize signature (fun _ j x => cutoff j x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 2 ≤ j),
    Tendsto (fun X : ℝ => (j : ℝ) * log ((V.readout ()) j (referencePrice X)) - log X)
      atTop (𝓝 (log (j : ℝ)))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end fixed_layer_root_offset_tendsto

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic

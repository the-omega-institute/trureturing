import D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Source-bound typed ATTEMPTS.
escapeFrom: the selected literal readout; readout: the typed actual realization;
realization: full telescope, actual_law and definitional source_bridge below;
continuation: unknown. Lawful enrollment, rejected lawful family, whole-family
intervention, other-readout/anchor-fixed sensitivity, observational dependence,
sourceSelection/binder/occurrence reconstruction and native axiom closure remain
unverified. No registration, declared_validated, native or official acceptance. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
open Real Finset
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace insertion_regret
/- Literal readout: goldenLayerMarginal; every selected occurrence in the FULL telescope
is replaced below. Source SHA256 b3200f67a287c134e9aa0f296a1bd519931f12662cf65e141977cfaff07ed802.
This is a typed attempt: compiled occurrence/source binding is not asserted. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p j => goldenLayerMarginal p j) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j p : ℕ} (hj : 2 ≤ j) (hp : p.Prime)
        {u priceLambda κ : ℝ} (hu : 2 ≤ u) (hLambda : 0 < priceLambda) (hroot : beta j u = priceLambda)
        (hκ : 0 ≤ κ) (hpu : u ≤ (p : ℝ)) (hup : (p : ℝ) ≤ u * (1 + κ)),
    0 ≤ priceLambda - (V.readout ()) p j ∧
          priceLambda - (V.readout ()) p j ≤ 2 * j * κ * priceLambda

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret.insertion_regret

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret.insertion_regret)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end insertion_regret

end Reg.D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret

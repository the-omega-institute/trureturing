import D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
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

/- SOURCE ONLY. RegUNVALIDATED / UNCOMPILED_UNACCEPTED.
These are full-telescope typed ATTEMPTS, not registrations or validation.
Actual arithmetic realization, actual_law and definitional source_bridge are
provided. Compiled occurrence/sourceSelection binding, lawful enrollment,
rejected lawful families, whole-family intervention and realizability,
anchor/other-readout-fixed sensitivity, actual observational dependence and
axiom closure are UNKNOWN. No .unknown object closes a source proof gap. -/
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.CurvatureConsumed
open Real Filter Finset
open scoped Topology BigOperators
open _root_.D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRootAsymptotic
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace root_ratio
/- RegUNVALIDATED. Readout: actual cutoff. Full dependent telescope below. -/
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
  realize signature (fun _ j u => cutoff j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 2 ≤ j),
    Tendsto (fun X : ℝ => ((V.readout ()) j (referencePrice X)) / X ^ ((j : ℝ)⁻¹))
      atTop (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹)))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_ratio

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_ratio)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end root_ratio

namespace root_atTop
/- RegUNVALIDATED. Readout: actual cutoff. Full dependent telescope below. -/
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
  realize signature (fun _ j u => cutoff j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 2 ≤ j),
    Tendsto (fun X : ℝ => ((V.readout ()) j (referencePrice X))) atTop atTop

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_atTop

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_atTop)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end root_atTop

namespace root_log_ratio
/- RegUNVALIDATED. Readout: actual cutoff. Full dependent telescope below. -/
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
  realize signature (fun _ j u => cutoff j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 2 ≤ j),
    Tendsto (fun X : ℝ => log (((V.readout ()) j (referencePrice X))) / log X)
      atTop (𝓝 ((j : ℝ)⁻¹))

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_log_ratio

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.root_log_ratio)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end root_log_ratio

namespace fixed_layer_shrinking_prime_roster_power
/- RegUNVALIDATED. Readout: actual cutoff. Full dependent telescope below. -/
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
  realize signature (fun _ j u => cutoff j u) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {j : ℕ} (hj : 2 ≤ j)
    (w d : ℕ) (hw : 0 < w),
    ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →
      ∃ S : Finset ℕ,
        C * log X ^ d ≤ (S.card : ℝ) ∧
        (∀ p ∈ S, p.Prime ∧ ((V.readout ()) j (referencePrice X)) < (p : ℝ) ∧
          (p : ℝ) ≤ ((V.readout ()) j (referencePrice X)) * (1 + 1 / log X ^ w)) ∧
        ((V.readout ()) j (referencePrice X)) / (2 * log X ^ w) ≤
          ∑ p ∈ S, log p

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end fixed_layer_shrinking_prime_roster_power

end Reg.D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster.CurvatureConsumed

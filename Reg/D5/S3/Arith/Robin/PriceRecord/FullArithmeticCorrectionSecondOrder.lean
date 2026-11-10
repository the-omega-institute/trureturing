import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import Reg.Support.DependentFamily

/- Candidate source-bound registration attempt.  The exact universal law and
   source bridge are retained below.  Contract.Registration is intentionally
   not asserted until an independent audit supplies whole-family variation,
   sensitivity, sourceSelection, and current producer binding evidence. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder

open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime tail)
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => correction m) (fun e => nomatch e)

/-- The full original telescope is retained, with the same-integer correction
    as the realized readout.  Both P and X endpoints remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law V := ∀ epsilon : ℝ, 0 < epsilon →
    ∃ T : ℝ, 1 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ lambda : ℝ, 0 < lambda →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective lambda n < goldenResourceObjective lambda m) →
      T ≤ (largestPrime m : ℝ) →
      1 < Chebyshev.theta (largestPrime m : ℝ) ∧
      1 < Real.log (m : ℝ) ∧
      (let P : ℝ := largestPrime m
       let X := Real.log (m : ℝ)
       let C := V.readout () lambda m
       |Real.log P * (Real.sqrt P * Real.log P * C - 2 * Real.sqrt 2) +
          Real.sqrt 2 * (2 + Real.log 2)| < epsilon ∧
      |Real.log X * (Real.sqrt X * Real.log X * C - 2 * Real.sqrt 2) +
          Real.sqrt 2 * (2 + Real.log 2)| < epsilon)

private theorem actual_law : arena.Law actual := by
  exact @price_record_full_arithmetic_correction_second_order

private theorem source_bridge :
    (type_of% (@price_record_full_arithmetic_correction_second_order)) ↔ arena.Law actual := Iff.rfl

/- The dependent-family audit remains concrete and open: a later writer must
   provide a lawful rejected family, whole-family variation and sensitivity
   with the other coordinates fixed, observational dependence on both lambda
   and m, exact readout/sourceSelection coordinates for `correction`, and a
   current producer binding certificate.  This file does not fabricate any of
   those obligations or claim `declared_validated`. -/

#print axioms actual_law
#print axioms source_bridge

/- Exact source-law candidates for the three newly visible ORIGINAL suppliers
and the single consumed own-clock coefficient. No four-slot or binding claim. -/
universe u
open Filter
open scoped Topology
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity (layerPrime)

namespace record_layer_ratio
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
  realize signature (fun _ j m => (layerPrime m j : ℝ) ^ j / (largestPrime m : ℝ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type u} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop)
    (j : ℕ) (hj : 2 ≤ j),
    Tendsto (fun x => V.readout () j (m x)) l (𝓝 (j : ℝ))

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_layer_ratio
private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_layer_ratio)) ↔
      arena.Law actual := Iff.rfl
end record_layer_ratio

namespace record_mass_limits
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun i _ m =>
    if i = 0 then
      (Real.log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ)) / Real.sqrt (largestPrime m : ℝ)
    else if i = 1 then
      Real.log (largestPrime m : ℝ) *
        ((Real.log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ)) /
          Real.sqrt (largestPrime m : ℝ) - Real.sqrt 2)
    else Real.log (m : ℝ) / (largestPrime m : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type u} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop),
    Tendsto (fun x => V.readout 0 () (m x)) l (𝓝 (Real.sqrt 2)) ∧
    Tendsto (fun x => V.readout 1 () (m x)) l (𝓝 (-Real.sqrt 2 * Real.log 2 / 2)) ∧
    Tendsto (fun x => V.readout 2 () (m x)) l (𝓝 1) ∧
    Tendsto (fun x => Real.log (largestPrime (m x) : ℝ) *
      (V.readout 2 () (m x) - 1)) l (𝓝 0)

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_mass_limits
private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_mass_limits)) ↔
      arena.Law actual := Iff.rfl
end record_mass_limits

namespace record_log_envelope
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => Real.log (m : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} (hm : 2 ≤ m) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m),
    V.readout () () m ≤ (largestPrime m : ℝ) * Real.log (4 * (largestPrime m : ℝ) ^ 2)

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_log_envelope
private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_log_envelope)) ↔
      arena.Law actual := Iff.rfl
end record_log_envelope

namespace record_second_own_clock_limit
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => Real.log (Real.log (m : ℝ)) *
    ((layerPrime m 2 : ℝ) / Real.sqrt (Real.log (m : ℝ)) - Real.sqrt 2))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α : Type u} {l : Filter α}
    (m : α → ℕ) (lambda : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hlambda : ∀ x, 0 < lambda x)
    (hrecord : ∀ x n, 0 < n → n < m x →
      goldenResourceObjective (lambda x) n < goldenResourceObjective (lambda x) (m x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop),
    Tendsto (fun x => V.readout () () (m x)) l (𝓝 (-Real.log 2 / Real.sqrt 2))

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_second_own_clock_limit
private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_second_own_clock_limit)) ↔
      arena.Law actual := Iff.rfl
end record_second_own_clock_limit

#check @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_layer_ratio
#print axioms _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_layer_ratio
#print axioms record_layer_ratio.source_bridge
#check @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_mass_limits
#print axioms _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_mass_limits
#print axioms record_mass_limits.source_bridge
#check @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_log_envelope
#print axioms _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_log_envelope
#print axioms record_log_envelope.source_bridge
#check @_root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_second_own_clock_limit
#print axioms _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder.record_second_own_clock_limit
#print axioms record_second_own_clock_limit.source_bridge

end Reg.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder

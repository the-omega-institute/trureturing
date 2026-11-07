import D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Source-owner four-slot audit attempt. The full original telescope is kept
in each law; the actual readout uses the enrolled DependentFamily.realize.
The exact source bridge and actual-positive law below are kernel obligations.
Whole-family variation, fixed-other-readout sensitivity, actual observational
dependence, lawful sourceSelection and current binding evidence remain unpaid.
No Contract.Registration or declared_validated result is asserted. Continuation
is unknown. The delivery links the specific unfinished audit issue. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap

open Real Finset
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S0.Diagonal.MarginBound (bernoulliKL)
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace support_integer_log

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℕ) → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => supportInteger) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ),
    log ((V.readout () ()) S a : ℝ) = clock S (fun p => (a p : ℝ))

private theorem actual_law : arena.Law actual := @support_integer_log

private theorem source_bridge :
    (type_of% (@support_integer_log)) ↔ arena.Law actual := Iff.rfl

end support_integer_log

namespace phi_eq_robin_margin

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
  realize signature (fun _ _ => robinLogMargin) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (a : ℕ → ℕ),
    phi S (fun p => (a p : ℝ)) = (V.readout () ()) (supportInteger S a)

private theorem actual_law : arena.Law actual := @phi_eq_robin_margin

private theorem source_bridge :
    (type_of% (@phi_eq_robin_margin)) ↔ arena.Law actual := Iff.rfl

end phi_eq_robin_margin

namespace original_margin_own_clock_gap

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
  realize signature (fun _ _ => robinLogMargin) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p),
    let x : ℕ → ℝ := fun p => (a p : ℝ)
    let n := supportInteger S (fun p => (a p).toNat)
    n.primeFactors = S ∧
    log (n : ℝ) = clock S x ∧
    (V.readout () ()) n - realInfimum S =
      (phi S (ownBoundary S x) - realInfimum S) +
        (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) +
          tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ phi S (ownBoundary S x) - realInfimum S ∧
    (∀ p ∈ S, 0 ≤ priceLoss p (ownPrice S x) (x p)) ∧
    0 ≤ tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ roundingSum S x ∧ roundingSum S x ≤ (V.readout () ()) n - realInfimum S ∧
    (∀ p ∈ S,
      ((p : ℝ) ^ (2 : ℕ) < cutoff (ownPrice S x) →
        priceLoss p (ownPrice S x) (x p) =
          bernoulliKL (cutoff (ownPrice S x))⁻¹ (probability p (x p)) /
            (1 - (cutoff (ownPrice S x))⁻¹) ∧
        integerGap p (ownPrice S x) =
          min (bernoulliKL (cutoff (ownPrice S x))⁻¹
              (probability p (⌊critical p (ownPrice S x)⌋ : ℤ)) /
                (1 - (cutoff (ownPrice S x))⁻¹))
            (bernoulliKL (cutoff (ownPrice S x))⁻¹
              (probability p (⌈critical p (ownPrice S x)⌉ : ℤ)) /
                (1 - (cutoff (ownPrice S x))⁻¹))) ∧
      (cutoff (ownPrice S x) ≤ (p : ℝ) ^ (2 : ℕ) →
        boundary p (ownPrice S x) = 1 ∧ integerGap p (ownPrice S x) = 0 ∧
        0 ≤ ownPrice S x - 1 / ((p : ℝ) ^ (2 : ℕ) - 1) ∧
        0 ≤ bernoulliKL ((p : ℝ) ^ (-2 : ℝ)) (probability p (x p)) /
          (1 - (p : ℝ) ^ (-2 : ℝ)) ∧
        priceLoss p (ownPrice S x) (x p) =
          bernoulliKL ((p : ℝ) ^ (-2 : ℝ)) (probability p (x p)) /
            (1 - (p : ℝ) ^ (-2 : ℝ)) +
              (ownPrice S x - 1 / ((p : ℝ) ^ (2 : ℕ) - 1)) * (x p - 1) * log p))

private theorem actual_law : arena.Law actual := @original_margin_own_clock_gap

private theorem source_bridge :
    (type_of% (@original_margin_own_clock_gap)) ↔ arena.Law actual := Iff.rfl

end original_margin_own_clock_gap

end Reg.D5.S3.Arith.Robin.PriceRecord.OwnClockRobinGap

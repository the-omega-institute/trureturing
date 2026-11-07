import D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
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

namespace Reg.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace theta_gt_one

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => theta) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card),
    1 < (V.readout () ()) S

private theorem actual_law : arena.Law actual := @theta_gt_one

private theorem source_bridge :
    (type_of% (@theta_gt_one)) ↔ arena.Law actual := Iff.rfl

end theta_gt_one

namespace theta_le_clock

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => clock) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S)
    {x : ℕ → ℝ} (hx : admissible S x),
    theta S ≤ (V.readout () ()) S x

private theorem actual_law : arena.Law actual := @theta_le_clock

private theorem source_bridge :
    (type_of% (@theta_le_clock)) ↔ arena.Law actual := Iff.rfl

end theta_le_clock

namespace clock_gt_one

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => clock) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x),
    1 < (V.readout () ()) S x

private theorem actual_law : arena.Law actual := @clock_gt_one

private theorem source_bridge :
    (type_of% (@clock_gt_one)) ↔ arena.Law actual := Iff.rfl

end clock_gt_one

namespace own_price_pos

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => ownPrice) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x),
    0 < (V.readout () ()) S x

private theorem actual_law : arena.Law actual := @own_price_pos

private theorem source_bridge :
    (type_of% (@own_price_pos)) ↔ arena.Law actual := Iff.rfl

end own_price_pos

namespace own_boundary_admissible

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → (ℕ → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => ownBoundary) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (S : Finset ℕ) (x : ℕ → ℝ),
    admissible S ((V.readout () ()) S x)

private theorem actual_law : arena.Law actual := @own_boundary_admissible

private theorem source_bridge :
    (type_of% (@own_boundary_admissible)) ↔ arena.Law actual := Iff.rfl

end own_boundary_admissible

namespace real_values_nonempty_bdd_below

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => realValues) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card),
    ((V.readout () ()) S).Nonempty ∧ BddBelow ((V.readout () ()) S)

private theorem actual_law : arena.Law actual := @real_values_nonempty_bdd_below

private theorem source_bridge :
    (type_of% (@real_values_nonempty_bdd_below)) ↔ arena.Law actual := Iff.rfl

end real_values_nonempty_bdd_below

namespace real_infimum_bounds

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => realInfimum) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    {x : ℕ → ℝ} (hx : admissible S x),
    baseline S ≤ (V.readout () ()) S ∧ (V.readout () ()) S ≤ phi S x

private theorem actual_law : arena.Law actual := @real_infimum_bounds

private theorem source_bridge :
    (type_of% (@real_infimum_bounds)) ↔ arena.Law actual := Iff.rfl

end real_infimum_bounds

namespace tangent_remainder_nonnegative

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => tangentRemainder) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {L T : ℝ} (hL : 1 < L) (hT : 1 < T),
    0 ≤ (V.readout () ()) L T ∧ (0 < (V.readout () ()) L T ↔ L ≠ T)

private theorem actual_law : arena.Law actual := @tangent_remainder_nonnegative

private theorem source_bridge :
    (type_of% (@tangent_remainder_nonnegative)) ↔ arena.Law actual := Iff.rfl

end tangent_remainder_nonnegative

namespace own_clock_decomposition

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => phi) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) {x : ℕ → ℝ} (hx : admissible S x),
    (V.readout () ()) S x - realInfimum S =
      ((V.readout () ()) S (ownBoundary S x) - realInfimum S) +
        (∑ p ∈ S, priceLoss p (ownPrice S x) (x p)) +
          tangentRemainder (clock S x) (clock S (ownBoundary S x)) ∧
    0 ≤ (V.readout () ()) S (ownBoundary S x) - realInfimum S ∧
    (∀ p ∈ S, 0 ≤ priceLoss p (ownPrice S x) (x p)) ∧
    0 ≤ tangentRemainder (clock S x) (clock S (ownBoundary S x))

private theorem actual_law : arena.Law actual := @own_clock_decomposition

private theorem source_bridge :
    (type_of% (@own_clock_decomposition)) ↔ arena.Law actual := Iff.rfl

end own_clock_decomposition

namespace all_integer_gap

abbrev signature : Signature where
  Params := Unit
  State _ := Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℕ → ℝ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => roundingSum) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {S : Finset ℕ} (hS : primeSupport S) (hcard : 3 ≤ S.card)
    (a : ℕ → ℤ) (ha : ∀ p ∈ S, 1 ≤ a p),
    0 ≤ (V.readout () ()) S (fun p => (a p : ℝ)) ∧
      (V.readout () ()) S (fun p => (a p : ℝ)) ≤
        phi S (fun p => (a p : ℝ)) - realInfimum S

private theorem actual_law : arena.Law actual := @all_integer_gap

private theorem source_bridge :
    (type_of% (@all_integer_gap)) ↔ arena.Law actual := Iff.rfl

end all_integer_gap

end Reg.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport

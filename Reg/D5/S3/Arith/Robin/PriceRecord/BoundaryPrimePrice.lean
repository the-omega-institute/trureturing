import D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- Source-owner four-slot audit attempt. The full original telescope is kept
in each law; the actual readout uses the enrolled DependentFamily.realize.
The exact source bridge and actual-positive law below are kernel obligations.
Whole-family variation, fixed-other-readout sensitivity, actual observational
dependence, lawful sourceSelection and current binding evidence remain unpaid.
No Contract.Registration or declared_validated result is asserted. Continuation
is unknown. Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/27696. -/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice

open Real Set
open D5.S0.Diagonal.MarginBound (bernoulliKL)
open _root_.D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace probability_mem

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
  realize signature (fun _ _ => probability) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p t : ℝ} (hp : 1 < p) (ht : 1 ≤ t),
    0 < (V.readout () ()) p t ∧ (V.readout () ()) p t < 1

private theorem actual_law : arena.Law actual := @probability_mem

private theorem source_bridge :
    (type_of% (@probability_mem)) ↔ arena.Law actual := Iff.rfl

end probability_mem

namespace benefit_log

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
  realize signature (fun _ _ => benefit) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p t : ℝ} (hp : 1 < p) (ht : 1 ≤ t),
    (V.readout () ()) p t = log (1 - probability p t) - log (1 - p ^ (-1 : ℝ))

private theorem actual_law : arena.Law actual := @benefit_log

private theorem source_bridge :
    (type_of% (@benefit_log)) ↔ arena.Law actual := Iff.rfl

end benefit_log

namespace boundary_maximum

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceObjective) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam) (ht : 1 ≤ t),
    (V.readout () ()) p lam t ≤ (V.readout () ()) p lam (boundary p lam)

private theorem actual_law : arena.Law actual := @boundary_maximum

private theorem source_bridge :
    (type_of% (@boundary_maximum)) ↔ arena.Law actual := Iff.rfl

end boundary_maximum

namespace integer_candidates

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceObjective) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (k : ℤ) (hk : 1 ≤ k),
    (V.readout () ()) p lam k ≤
      max ((V.readout () ()) p lam (⌊boundary p lam⌋ : ℤ))
        ((V.readout () ()) p lam (⌈boundary p lam⌉ : ℤ))

private theorem actual_law : arena.Law actual := @integer_candidates

private theorem source_bridge :
    (type_of% (@integer_candidates)) ↔ arena.Law actual := Iff.rfl

end integer_candidates

namespace integer_gap_bounds

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceLoss) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (k : ℤ) (hk : 1 ≤ k),
    0 ≤ integerGap p lam ∧ integerGap p lam ≤ (V.readout () ()) p lam k

private theorem actual_law : arena.Law actual := @integer_gap_bounds

private theorem source_bridge :
    (type_of% (@integer_gap_bounds)) ↔ arena.Law actual := Iff.rfl

end integer_gap_bounds

namespace integer_gap_attained

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceObjective) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam),
    ∃ k : ℤ, 1 ≤ k ∧ integerGap p lam = priceLoss p lam k ∧
      ∀ j : ℤ, 1 ≤ j → (V.readout () ()) p lam j ≤ (V.readout () ()) p lam k

private theorem actual_law : arena.Law actual := @integer_gap_attained

private theorem source_bridge :
    (type_of% (@integer_gap_attained)) ↔ arena.Law actual := Iff.rfl

end integer_gap_attained

namespace price_difference_kl

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceObjective) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam x t : ℝ} (hp : 1 < p) (hx : 1 ≤ x) (ht : 1 ≤ t),
    (V.readout () ()) p lam x - (V.readout () ()) p lam t =
      bernoulliKL (probability p x) (probability p t) / (1 - probability p x) +
        (lam - 1 / (p ^ (x + 1) - 1)) * (t - x) * log p

private theorem actual_law : arena.Law actual := @price_difference_kl

private theorem source_bridge :
    (type_of% (@price_difference_kl)) ↔ arena.Law actual := Iff.rfl

end price_difference_kl

namespace active_loss

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceLoss) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hactive : p ^ (2 : ℕ) < cutoff lam) (ht : 1 ≤ t),
    (V.readout () ()) p lam t =
      bernoulliKL (cutoff lam)⁻¹ (probability p t) / (1 - (cutoff lam)⁻¹) ∧
    (V.readout () ()) p lam t =
      log ((1 - (cutoff lam)⁻¹) / (1 - probability p t)) -
        lam * log (cutoff lam / p ^ (t + 1))

private theorem actual_law : arena.Law actual := @active_loss

private theorem source_bridge :
    (type_of% (@active_loss)) ↔ arena.Law actual := Iff.rfl

end active_loss

namespace inactive_loss

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => priceLoss) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam t : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hinactive : cutoff lam ≤ p ^ (2 : ℕ)) (ht : 1 ≤ t),
    boundary p lam = 1 ∧ integerGap p lam = 0 ∧
      0 ≤ lam - 1 / (p ^ (2 : ℕ) - 1) ∧
      0 ≤ bernoulliKL (p ^ (-2 : ℝ)) (probability p t) / (1 - p ^ (-2 : ℝ)) ∧
      (V.readout () ()) p lam t =
        bernoulliKL (p ^ (-2 : ℝ)) (probability p t) / (1 - p ^ (-2 : ℝ)) +
          (lam - 1 / (p ^ (2 : ℕ) - 1)) * (t - 1) * log p

private theorem actual_law : arena.Law actual := @inactive_loss

private theorem source_bridge :
    (type_of% (@inactive_loss)) ↔ arena.Law actual := Iff.rfl

end inactive_loss

namespace active_integer_gap

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
  realize signature (fun _ _ => integerGap) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {p lam : ℝ} (hp : 1 < p) (hlam : 0 < lam)
    (hactive : p ^ (2 : ℕ) < cutoff lam),
    (V.readout () ()) p lam =
      min (bernoulliKL (cutoff lam)⁻¹ (probability p (⌊critical p lam⌋ : ℤ)) /
          (1 - (cutoff lam)⁻¹))
        (bernoulliKL (cutoff lam)⁻¹ (probability p (⌈critical p lam⌉ : ℤ)) /
          (1 - (cutoff lam)⁻¹))

private theorem actual_law : arena.Law actual := @active_integer_gap

private theorem source_bridge :
    (type_of% (@active_integer_gap)) ↔ arena.Law actual := Iff.rfl

end active_integer_gap

end Reg.D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice

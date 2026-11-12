import D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full-telescope actual laws, exact source bridges and actual observational
variation. Four-slot enrollment, source binding and law sensitivity remain
unfinished under the linked issue 29429 exception. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
open Finset Real
open scoped BigOperators
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
open _root_.D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m j => layerPrime m j) (fun e => nomatch e)

private theorem actual_observational_dependence :
    ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 2, ?_⟩
  change layerPrime 2 1 ≠ layerPrime 2 2
  norm_num [layerPrime, Finsupp.single_apply, Finset.filter_singleton]

namespace displaced_root_boundary_squeeze
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m j : ℕ} {mu lambda rho rm rp a b e q W : ℝ}
    (_hm : 2 ≤ m) (_hmu : 0 < mu) (_hrecord : FullRecord m mu) (_hj : 2 ≤ j)
    (_hLambda : lambda = beta 1 (largestPrime m : ℝ))
    (_hrho : 2 ≤ rho) (_hroot : beta j rho = lambda)
    (_hrm : 2 ≤ rm) (_hmrho : rm ≤ rho) (_hrhop : rho ≤ rp)
    (_he : 0 ≤ e) (_he1 : e ≤ 1) (_hq : 0 ≤ q)
    (FirstLo FirstHi Sm Sp : Finset ℕ)
    (_hFL : ∀ p ∈ FirstLo, p.Prime ∧ p ≤ largestPrime m ∧
      log (p : ℝ) ≤ W ∧ |beta 1 (p : ℝ) - lambda| ≤ e * lambda)
    (_hFU : ∀ p ∈ FirstHi, p.Prime ∧ largestPrime m < p ∧
      log (p : ℝ) ≤ W ∧ |beta 1 (p : ℝ) - lambda| ≤ e * lambda)
    (_hSm : ∀ p ∈ Sm, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ rm)
    (_hSp : ∀ p ∈ Sp, p.Prime ∧ rp ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (_hdisM : Disjoint FirstLo Sm) (_hdisP : Disjoint Sp FirstHi)
    (_hNm : 0 < logMass Sm) (_hNp : 0 < logMass Sp)
    (_hfullM : logMass Sm < logMass FirstLo) (_hfullP : logMass Sp ≤ logMass FirstHi)
    (_hWM : W ≤ q * logMass Sm) (_hWP : W ≤ q * logMass Sp)
    (_hsepM : e + q ≤ (j : ℝ) / 3 * log (rho / rm))
    (_hsepP : e + q ≤ (j : ℝ) / 6 * log (rp / rho))
    (_hsmallP : (j : ℝ) / 3 * log (rp / rho) ≤ 1),
    a ≤ ((V.readout ()) m j : ℝ) ∧ ((V.readout ()) m j : ℝ) < b

private theorem actual_law : arena.Law actual := by
  exact @displaced_root_boundary_squeeze

private theorem source_bridge :
    (type_of% (@displaced_root_boundary_squeeze)) ↔
      arena.Law actual := Iff.rfl

end displaced_root_boundary_squeeze

namespace counted_displaced_root_boundary_squeeze
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m j K : ℕ}
    {mu C c X P rho rm rp e q Z : ℝ}
    (_hm : 2 ≤ m) (_hmu : 0 < mu) (_hrecord : FullRecord m mu) (_hj : 2 ≤ j)
    (_hK : 1 ≤ K) (_hPdef : P = (largestPrime m : ℝ)) (_hP : 4 ≤ P)
    (_hC : 0 < C) (_hX : 2 ≤ X)
    (_hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (_hXP : X ≤ P) (_hXm : X ≤ rm) (_hXp : X ≤ rp)
    (_hcapP : (K : ℝ) + 1 ≤ c * P ^ bhpExponent / log P)
    (_hcapM : (K : ℝ) ≤ c * rm ^ bhpExponent / log rm)
    (_hcapR : (K : ℝ) ≤ c * rp ^ bhpExponent / log rp)
    (_hwidth : C * P ^ bhpExponent ≤ P / 2)
    (_hrho : 2 ≤ rho) (_hroot : beta j rho = beta 1 P)
    (_hrm : 2 ≤ rm - C * rm ^ bhpExponent)
    (_hmrho : rm ≤ rho) (_hrhop : rho ≤ rp)
    (_hprefix : rp + C * rp ^ bhpExponent < P - C * P ^ bhpExponent)
    (_he : 0 ≤ e) (_he1 : e ≤ 1) (_hq : 0 ≤ q)
    (_hprice : priceLip 1 (P / 2) * (C * P ^ bhpExponent) ≤ e * beta 1 P)
    (_hZ : 0 < Z) (_hZM : Z ≤ log (rm - C * rm ^ bhpExponent))
    (_hZP : Z ≤ log rp) (_hbudget : 2 * log P ≤ q * ((K : ℝ) * Z))
    (_hsepM : e + q ≤ (j : ℝ) / 3 * log (rho / rm))
    (_hsepP : e + q ≤ (j : ℝ) / 6 * log (rp / rho))
    (_hsmallP : (j : ℝ) / 3 * log (rp / rho) ≤ 1),
    rm - C * rm ^ bhpExponent ≤ ((V.readout ()) m j : ℝ) ∧
      ((V.readout ()) m j : ℝ) < rp + C * rp ^ bhpExponent

private theorem actual_law : arena.Law actual := by
  exact @counted_displaced_root_boundary_squeeze

private theorem source_bridge :
    (type_of% (@counted_displaced_root_boundary_squeeze)) ↔
      arena.Law actual := Iff.rfl

end counted_displaced_root_boundary_squeeze

namespace counted_displaced_cutoff_log_localization
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m j K : ℕ}
    {mu C c X P rho rm rp e q Z H t : ℝ}
    (_hm : 2 ≤ m) (_hmu : 0 < mu) (_hrecord : FullRecord m mu) (_hj : 2 ≤ j)
    (_hK : 1 ≤ K) (_hPdef : P = (largestPrime m : ℝ)) (_hP : 4 ≤ P)
    (_hC : 0 < C) (_hX : 2 ≤ X) (_hH : 0 < H)
    (_htdef : t = P ^ (-priceExponent j))
    (_hrhodef : rho = cutoff j (beta 1 P)) (_hactive : beta 1 P < beta j 2)
    (_hrmdef : rm = rho * exp (-(H * t))) (_hrpdef : rp = rho * exp (H * t))
    (_hcount : ∀ x : ℝ, X ≤ x →
      c * x ^ bhpExponent / log x ≤
        ((primesIn (x - C * x ^ bhpExponent) x).card : ℝ) ∧
      c * x ^ bhpExponent / log x ≤
        ((primesIn x (x + C * x ^ bhpExponent)).card : ℝ))
    (_hXP : X ≤ P) (_hXm : X ≤ rm) (_hXp : X ≤ rp)
    (_hcapP : (K : ℝ) + 1 ≤ c * P ^ bhpExponent / log P)
    (_hcapM : (K : ℝ) ≤ c * rm ^ bhpExponent / log rm)
    (_hcapR : (K : ℝ) ≤ c * rp ^ bhpExponent / log rp)
    (_hwidth : C * P ^ bhpExponent ≤ P / 2)
    (_hrm : 2 ≤ rm - C * rm ^ bhpExponent)
    (_hprefix : rp + C * rp ^ bhpExponent < P - C * P ^ bhpExponent)
    (_he : 0 ≤ e) (_he1 : e ≤ 1) (_hq : 0 ≤ q)
    (_hprice : priceLip 1 (P / 2) * (C * P ^ bhpExponent) ≤ e * beta 1 P)
    (_hZ : 0 < Z) (_hZM : Z ≤ log (rm - C * rm ^ bhpExponent))
    (_hZP : Z ≤ log rp) (_hbudget : 2 * log P ≤ q * ((K : ℝ) * Z))
    (_hseparate : e + q ≤ (j : ℝ) / 6 * (H * t))
    (_hsmall : (j : ℝ) / 3 * (H * t) ≤ 1)
    (_hwm : C * rm ^ bhpExponent / rm ≤ 4 * C * t)
    (_hwp : C * rp ^ bhpExponent / rp ≤ 4 * C * t)
    (_hshort : 4 * C * t ≤ 1 / 2),
    2 < cutoff j (beta 1 P) ∧ 0 < (V.readout ()) m j ∧
      |log ((V.readout ()) m j : ℝ) - log (cutoff j (beta 1 P))| ≤
        (H + 16 * C) * P ^ (-priceExponent j)

private theorem actual_law : arena.Law actual := by
  exact @counted_displaced_cutoff_log_localization

private theorem source_bridge :
    (type_of% (@counted_displaced_cutoff_log_localization)) ↔
      arena.Law actual := Iff.rfl

end counted_displaced_cutoff_log_localization

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization

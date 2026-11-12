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

abbrev betaSignature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def betaActual : Realization betaSignature :=
  realize betaSignature (fun _ j u => beta j u) (fun e => nomatch e)

private theorem beta_actual_observational_dependence :
    ObservationalDependence betaSignature betaActual := by
  intro i
  refine ⟨2, 2, 3, ?_⟩
  change beta 2 2 ≠ beta 2 3
  exact ne_of_gt (beta_strictAntiOn (by norm_num) (by norm_num) (by norm_num) (by norm_num))

namespace literal_root_geometry
abbrev arena : Arena where
  signature := betaSignature
  Law V := ∀ {j : ℕ} {P rho : ℝ} (_hj : 2 ≤ j)
    (_hP : 4 ≤ log P) (_hP0 : 0 < P) (_hrho : 2 ≤ rho)
    (_hroot : (V.readout ()) j rho = (V.readout ()) 1 P)
    (_hlog : log (2 * log P / log 2) ≤ log P / 4),
    P * log P / 2 ≤ rho ^ j * log rho ∧
      rho ^ j * log rho ≤ 2 * P * log P ∧
      log P - log 2 ≤ (j : ℝ) * log rho ∧
      (j : ℝ) * log rho ≤ 5 * log P / 4

private theorem actual_law : arena.Law betaActual := @literal_root_geometry

private theorem source_bridge :
    (type_of% (@literal_root_geometry)) ↔ arena.Law betaActual := Iff.rfl
end literal_root_geometry

namespace literal_cutoff_active
abbrev arena : Arena where
  signature := betaSignature
  Law V := ∀ {j : ℕ} {P : ℝ} (_hj : 2 ≤ j)
    (_hP0 : 0 < P) (_hP : 4 ≤ log P) (_hjx : (j : ℝ) ≤ log P / 4),
    (V.readout ()) 1 P < (V.readout ()) j 2

private theorem actual_law : arena.Law betaActual := @literal_cutoff_active

private theorem source_bridge :
    (type_of% (@literal_cutoff_active)) ↔ arena.Law betaActual := Iff.rfl
end literal_cutoff_active

namespace literal_displaced_probe_geometry
abbrev arena : Arena where
  signature := betaSignature
  Law V := ∀ {j : ℕ} {P rho H : ℝ}
    (_hj : 2 ≤ j) (_hP0 : 0 < P) (_hP : 4 ≤ log P) (_hrho : 2 ≤ rho)
    (_hroot : (V.readout ()) j rho = (V.readout ()) 1 P)
    (_hlog : log (2 * log P / log 2) ≤ log P / 4)
    (_hH : 0 < H) (_hsmall : H * P ^ (-priceExponent j) ≤ 1),
    let t := P ^ (-priceExponent j)
    let rm := rho * exp (-(H * t))
    let rp := rho * exp (H * t)
    log P / (j : ℝ) - 2 ≤ log rm ∧
      log P / (j : ℝ) - 1 ≤ log rp ∧
      log rp ≤ 5 * log P / (4 * (j : ℝ)) + 1 ∧
      rm ^ bhpExponent / rm ≤ 4 * t ∧
      rp ^ bhpExponent / rp ≤ 4 * t

private theorem actual_law : arena.Law betaActual := @literal_displaced_probe_geometry

private theorem source_bridge :
    (type_of% (@literal_displaced_probe_geometry)) ↔ arena.Law betaActual := Iff.rfl
end literal_displaced_probe_geometry

abbrev logSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def logActual : Realization logSignature :=
  realize logSignature (fun _ _ x => log x) (fun e => nomatch e)

private theorem log_actual_observational_dependence :
    ObservationalDependence logSignature logActual := by
  intro i
  refine ⟨(), 1, exp 1, ?_⟩
  change log 1 ≠ log (exp 1)
  simp

open Filter
open scoped Topology

namespace moving_window_log_scale
abbrev arena : Arena where
  signature := logSignature
  Law V := ∀ {delta A : ℝ} (_hdelta : 0 < delta) (_hA : 0 < A),
    ∀ᶠ x : ℝ in atTop, 1 ≤ (V.readout ()) () x ∧ 0 < x ∧
      ∀ u : ℝ, 0 < u → u ≤ delta * x / ((V.readout ()) () x) ^ 2 + 1 →
        A * (V.readout ()) () x ≤ x / u

private theorem actual_law : arena.Law logActual := @moving_window_log_scale

private theorem source_bridge :
    (type_of% (@moving_window_log_scale)) ↔ arena.Law logActual := Iff.rfl
end moving_window_log_scale

namespace moving_window_exp_small
abbrev arena : Arena where
  signature := logSignature
  Law V := ∀ {delta a : ℝ} (_hdelta : 0 < delta) (_ha : 0 < a) (k : ℕ),
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧
      ∀ u : ℝ, 0 < u → u ≤ delta * x / ((V.readout ()) () x) ^ 2 + 1 →
        x ^ k * exp (-a * x / u) ≤ 1 / x

private theorem actual_law : arena.Law logActual := @moving_window_exp_small

private theorem source_bridge :
    (type_of% (@moving_window_exp_small)) ↔ arena.Law logActual := Iff.rfl
end moving_window_exp_small

namespace bhp_uniform_moving_boundary_localization
abbrev arena : Arena where
  signature := signature
  Law V := BHPMaximumGap → BHPShortIntervalCount →
    ∃ B : ℝ, 0 < B ∧ ∀ delta : ℝ, 0 < delta →
      ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m →
        ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T ≤ (largestPrime m : ℝ) →
          ∀ j : ℕ, 2 ≤ j →
            (j : ℝ) ≤ delta * log (largestPrime m : ℝ) /
              (log (log (largestPrime m : ℝ))) ^ 2 + 1 →
            2 < cutoff j (beta 1 (largestPrime m : ℝ)) ∧
              0 < (V.readout ()) m j ∧
              |log ((V.readout ()) m j : ℝ) -
                log (cutoff j (beta 1 (largestPrime m : ℝ)))| ≤
                B * (largestPrime m : ℝ) ^ (-priceExponent j)

private theorem actual_law : arena.Law actual := @bhp_uniform_moving_boundary_localization

private theorem source_bridge :
    (type_of% (@bhp_uniform_moving_boundary_localization)) ↔ arena.Law actual := Iff.rfl
end bhp_uniform_moving_boundary_localization

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualMovingBoundaryLocalization

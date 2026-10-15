/- GID: D5/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict domination of Bernstein corrections after common elevation. -/

import D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic

noncomputable section
open Finset
open scoped Topology

namespace D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

open LorentzWeightedHolderControl LorentzCommonGridStability
open LorentzLowDegreeCoefficientRemainder LorentzLocalCoefficientKernel
open LorentzCoefficientRemainder OriginalRingEnvelopeScale
open Filter
open scoped Topology

private lemma correction_controls_delta {n r t : ℕ} {ρ θ : ℝ}
    (hn : 2 ≤ n) (ht : t ≤ n+r) (hρ : 2 ≤ ρ) (hθ : 0 < θ) :
    delta n ((t : ℝ)/(n+r))^ρ ≤
      ((1+θ⁻¹)*(2 : ℝ)^(ρ/2)) * lift (n+r) n t (correction ρ θ n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdR : (0 : ℝ) < n+r := by positivity
  let p : ℝ := (t : ℝ)/(n+r)
  have hp : p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hdR).mpr (by exact_mod_cast ht)⟩
  have hv : 0 ≤ p*(1-p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hlow := correction_lift_lower (θ := θ) (by omega : n ≤ n+r) ht hn hρ
  have hpow : 1 ≤ (2 : ℝ)^(ρ/2) := Real.one_le_rpow (by norm_num) (by linarith)
  have hconst : 0 ≤ θ/(n : ℝ)^ρ := by positivity
  have hvar : 0 ≤ (p*(1-p)/(2*n))^(ρ/2) := by positivity
  have hsum : 0 ≤ lift (n+r) n t (correction ρ θ n) :=
    (add_nonneg hconst hvar).trans (by simpa [p] using hlow)
  have hscale : (Real.sqrt (p*(1-p)/n))^ρ =
      (2 : ℝ)^(ρ/2)*(p*(1-p)/(2*n))^(ρ/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    congr 1
    · field_simp
    · ring
  have hfloor : (1/(n : ℝ))^ρ = 1/(n : ℝ)^ρ := by
    rw [Real.div_rpow (by norm_num) hnR.le, Real.one_rpow]
  have hfactor : 1 ≤ 1+θ⁻¹ := by linarith [inv_nonneg.mpr hθ.le]
  change (max (Real.sqrt (p*(1-p)/n)) (1/(n : ℝ)))^ρ ≤ _
  rw [Real.rpow_max (Real.sqrt_nonneg _) (by positivity) (by linarith)]
  apply max_le
  · rw [hscale]
    calc
      _ ≤ (2 : ℝ)^(ρ/2)*lift (n+r) n t (correction ρ θ n) :=
        mul_le_mul_of_nonneg_left
          (le_trans (le_add_of_nonneg_left hconst) (by simpa [p] using hlow)) (by positivity)
      _ = 1*((2 : ℝ)^(ρ/2)*lift (n+r) n t (correction ρ θ n)) := by ring
      _ ≤ (1+θ⁻¹)*((2 : ℝ)^(ρ/2)*lift (n+r) n t (correction ρ θ n)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
  · rw [hfloor]
    have hf : 1/(n : ℝ)^ρ ≤ θ⁻¹*lift (n+r) n t (correction ρ θ n) := by
      calc
        _ = θ⁻¹*(θ/(n : ℝ)^ρ) := by field_simp [ne_of_gt hθ]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((le_add_of_nonneg_right hvar).trans (by simpa [p] using hlow)) (by positivity)
    apply hf.trans
    apply mul_le_mul_of_nonneg_right _ hsum
    calc
      θ⁻¹ ≤ 1+θ⁻¹ := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hpow

lemma correction_uniform_bound {n r t : ℕ} {ρ θ : ℝ}
    (hn : 0 < n) (hr : r ≤ n) (ht : t ≤ n+r) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    lift (n+r) n t (correction ρ θ n) ≤ (θ+1)*(n : ℝ)^(-ρ/2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : (0 : ℝ) < n+r := by positivity
  let p : ℝ := (t : ℝ)/(n+r)
  have hp : p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hd).mpr (by exact_mod_cast ht)⟩
  have hv0 : 0 ≤ p*(1-p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hv : 0 ≤ 4*(p*(1-p))/n := by positivity
  have hv1 : 4*(p*(1-p))/n ≤ 1/(n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hn0.le
    nlinarith [sq_nonneg (2*p-1)]
  have he : (1/(n : ℝ))^(ρ/2) = (n : ℝ)^(-ρ/2) := by
    rw [one_div, Real.inv_rpow hn0.le, ← Real.rpow_neg hn0.le, neg_div]
  have hf : 1/(n : ℝ)^ρ ≤ (n : ℝ)^(-ρ/2) := by
    rw [one_div, ← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hvb := (Real.rpow_le_rpow hv hv1 (by linarith : 0 ≤ ρ/2)).trans_eq he
  have hu := correction_lift_upper (θ := θ) (by omega : n ≤ n+r) ht hn (by omega) hρ
  dsimp [p] at hvb
  push_cast at hu
  have hf' := mul_le_mul_of_nonneg_left hf hθ
  rw [mul_one_div] at hf'
  nlinarith

/-- One fixed initial degree and one fixed amplitude pay both the whole
center history and the original correction on every proportional ring.
The second bound compares the actual center increment with the decrease
of the twice-elevated old correction, including endpoint coefficients. -/
theorem uniform_ring_correction_budget (r : ℕ) (ρ θ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar A H ε : ℝ, 0 < xstar → 0 ≤ A → 0 ≤ H → 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ j : ℕ,
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤
          A*(ringScale xstar b j)^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤
            H*(ringScale xstar b j)^(-ρ)*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r,
          ‖bernsteinCoefficient ((N*b^j)*b^k+r) t (center (N*b^j) b r f k)-c‖ +
            D*(ringScale xstar b j)^(-ρ)*
              lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) t
                (correction ρ θ ((N*b^j)*b^k)) ≤ M+ε) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          ‖bernsteinCoefficient ((N*b^j)*b^(k+1)+r) t
            (center (N*b^j) b r f (k+1)-center (N*b^j) b r f k)‖ ≤
            D*(ringScale xstar b j)^(-ρ)*
              (lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t
                (fun i => lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) i
                  (correction ρ θ ((N*b^j)*b^k))) -
               lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^(k+1)) t
                (correction ρ θ ((N*b^j)*b^(k+1))))) := by
  obtain ⟨Bc,hBc,hcoeff⟩ := center_coefficient_control r ρ hρ hρ1
  obtain ⟨Bs,hBs,U,V,E,hU,hV,hE,hstable⟩ := common_grid_stability r ρ hρ hρ1
  obtain ⟨L,hL,hlocal⟩ := residual_coefficient_control r ρ hρ
  let B := max 16 (max Bc Bs)
  refine ⟨B,le_max_left _ _,?_⟩
  intro b hb xstar A H ε hx hA hH hε
  have hb16 : 16 ≤ b := (le_max_left _ _).trans hb
  have hbc : Bc ≤ b := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hb
  have hbs : Bs ≤ b := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hb
  have hb0 : 0 < b := by omega
  obtain ⟨K,hK,hcb⟩ := hcoeff b hbc
  let T := L*E*((b : ℝ)*((r : ℝ)+1))^ρ
  have hT : 0 < T := by dsimp [T]; positivity
  let Cθ := (1+θ⁻¹)*(2 : ℝ)^(ρ/2)
  have hCθ : 0 < Cθ := by dsimp [Cθ]; positivity
  let D := 1+T*H*Cθ
  have hD : 0 < D := by dsimp [D]; positivity
  let budget : ℕ → ℝ := fun N =>
    K*A*(∑ ν ∈ Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) +
      (K*H+(θ+1)*D)*(N : ℝ)^(-ρ/2)*xstar^(-ρ)
  have hlim : Tendsto budget atTop (𝓝 0) := by
    have hs : Tendsto (fun N : ℕ => ∑ ν ∈ Icc 1 r,
        (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) atTop (𝓝 0) := by
      have ht : ∀ ν ∈ Icc 1 r, Tendsto
          (fun N : ℕ => (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ))) atTop (𝓝 0) := by
        intro ν hν
        have hp : (0 : ℝ) < ν := by exact_mod_cast (mem_Icc.mp hν).1
        simpa [Function.comp_def,neg_div] using
          ((tendsto_rpow_neg_atTop (show 0 < (ν : ℝ)/2 by positivity)).comp
            tendsto_natCast_atTop_atTop).mul_const (xstar^(-(ν : ℝ)))
      simpa using tendsto_finsetSum (Icc 1 r) ht
    have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-ρ/2)) atTop (𝓝 0) := by
      simpa [Function.comp_def,neg_div] using
        (tendsto_rpow_neg_atTop (show 0 < ρ/2 by linarith)).comp tendsto_natCast_atTop_atTop
    simpa only [budget,mul_zero,zero_mul,add_zero] using
      (hs.const_mul (K*A)).add ((ht.const_mul (K*H+(θ+1)*D)).mul_const (xstar^(-ρ)))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  let N := max (3*r+2) N0
  have hN : 3*r+2 ≤ N := le_max_left _ _
  have hNpos : 0 < N := by omega
  have hbudget : budget N ≤ ε := (hN0 N (le_max_right _ _)).le
  refine ⟨D,hD,N,hN,?_⟩
  intro j f hf c M hM hfc hfd hfh k
  let τ := N*b^j
  let s := ringScale xstar b j
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hNτ : N ≤ τ := Nat.le_mul_of_pos_right N (pow_pos hb0 j)
  have hτr : r ≤ τ := by omega
  have hs : 0 < s := by dsimp [s,ringScale]; positivity
  have hτk (i : ℕ) : τ ≤ τ*b^i := Nat.le_mul_of_pos_right τ (pow_pos hb0 i)
  have hng (i : ℕ) : 0 < τ*b^i := Nat.mul_pos hτ (pow_pos hb0 i)
  have hst := hstable b hbs τ hτ f hf (H*s^(-ρ)) (by positivity) hfh
  constructor
  · intro t ht
    have hc := hcb τ hτ hτr f hf c M A (H*s^(-ρ)) s
      hM hA (by positivity) hs hfc hfd hfh k t ht
    have hcorr := correction_uniform_bound (hng k) (hτr.trans (hτk k)) ht
      (by linarith : 0 ≤ ρ) hθ.le
    have hdecay : ((τ*b^k : ℕ) : ℝ)^(-ρ/2) ≤ (τ : ℝ)^(-ρ/2) :=
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hτ) (by exact_mod_cast hτk k)
        (by linarith)
    have hcorr' : lift (τ*b^k+r) (τ*b^k) t (correction ρ θ (τ*b^k)) ≤
        (θ+1)*(τ : ℝ)^(-ρ/2) := hcorr.trans (by gcongr)
    have hcorr'' := mul_le_mul_of_nonneg_left hcorr' (show 0 ≤ D*s^(-ρ) by positivity)
    have hcancel : (τ : ℝ)^(-ρ/2)*s^(-ρ) = (N : ℝ)^(-ρ/2)*xstar^(-ρ) :=
      ring_scale_cancel hNpos hb0 hx j ρ
    have hsum : (∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) =
        ∑ ν ∈ Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)) := by
      apply sum_congr rfl
      intro ν _
      exact ring_scale_cancel hNpos hb0 hx j (ν : ℝ)
    rw [hsum] at hc
    have he : K*(H*s^(-ρ))*(τ : ℝ)^(-ρ/2)+D*s^(-ρ)*((θ+1)*(τ : ℝ)^(-ρ/2)) =
        (K*H+(θ+1)*D)*(N : ℝ)^(-ρ/2)*xstar^(-ρ) := by
      calc
        _ = (K*H+(θ+1)*D)*((τ : ℝ)^(-ρ/2)*s^(-ρ)) := by ring
        _ = _ := by rw [hcancel]; ring
    change ‖bernsteinCoefficient (τ*b^k+r) t (center τ b r f k)-c‖ +
      D*s^(-ρ)*lift (τ*b^k+r) (τ*b^k) t (correction ρ θ (τ*b^k)) ≤ M+ε
    dsimp [budget] at hbudget
    linarith
  · intro t ht
    change t ≤ τ*b^(k+1)+r at ht
    have hgrid : τ*b^k*b = τ*b^(k+1) := by rw [pow_succ]; ring
    have hnr : r ≤ τ*b^k*b := by rw [hgrid]; exact hτr.trans (hτk _)
    have hnb16 : 16*(τ*b^k) ≤ τ*b^(k+1) := by
      rw [← hgrid]
      nlinarith
    have hn2 : 2 ≤ τ*b^k := by have := hτk k; omega
    have hlow := (correction_lift_advantage (ρ := ρ) (θ := θ) hn2 hnb16
      (hτr.trans (hτk (k+1))) ht hρ2 hθ.le).1
    have hdelta := correction_controls_delta (n := τ*b^(k+1)) (r := r)
      (by have := hτk (k+1); omega) ht hρ2 hθ
    have hl := hlocal (τ*b^k) b (hng k) hnr (by omega) f hf (center τ b r f k)
      (E*(H*s^(-ρ))) (by positivity) (hst k).2.2.2 t (by rwa [hgrid])
    rw [hgrid] at hl
    have hc : 0 ≤ lift (τ*b^(k+1)+r) (τ*b^(k+1)) t
        (correction ρ θ (τ*b^(k+1))) :=
      (correction_lift_pos (N := τ*b^(k+1)+r) (Nat.le_add_right _ _) ht (hng (k+1)) hθ).le
    have hDlarge : T*H*Cθ ≤ D := by dsimp [D]; linarith
    have hscale := mul_le_mul_of_nonneg_left hdelta
      (show 0 ≤ L*(E*(H*s^(-ρ)))*((b : ℝ)*((r : ℝ)+1))^ρ by positivity)
    have hnorm : ‖bernsteinCoefficient (τ*b^(k+1)+r) t
        (center τ b r f (k+1)-center τ b r f k)‖ ≤
        T*H*Cθ*s^(-ρ)*
          lift (τ*b^(k+1)+r) (τ*b^(k+1)) t (correction ρ θ (τ*b^(k+1))) := by
      rw [center, add_sub_cancel_left]
      apply hl.trans
      convert hscale using 1 <;>
        simp only [T,Cθ,Nat.cast_mul,Nat.cast_pow,pow_succ,mul_assoc] <;> ring
    apply hnorm.trans
    calc
      _ ≤ D*s^(-ρ)*lift (τ*b^(k+1)+r) (τ*b^(k+1)) t
          (correction ρ θ (τ*b^(k+1))) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

open Filter Function
open Set hiding Icc
open scoped ContDiff NNReal ENNReal

namespace D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets

/-- The reference function. Its scale-zero value is only a totalization. -/
def reference (φ : ℝ → ℝ) (η a b x q : ℝ) : ℝ :=
  1 / 2 + η * φ ((a + b * q) / x)

/-- First take `ell` derivatives in `q`, then `m` in the positive scale `x`. -/
def xqJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv m (fun z => iteratedDeriv ell
    (fun u => reference φ η a b z u - 1 / 2) q) x

/-- First take `m` scale derivatives, then `ell` derivatives in `q`. -/
def qxJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv ell (fun u => iteratedDeriv m
    (fun z => reference φ η a b z u - 1 / 2) x) q

/-- The same mixed jet of the full reference, including its constant term. -/
def fullQxJet (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) : ℝ :=
  iteratedDeriv ell (fun u => iteratedDeriv m
    (fun z => reference φ η a b z u) x) q

lemma fullQxJet_eq (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ) :
    fullQxJet φ η a b m ell x q =
      qxJet φ η a b m ell x q + if m = 0 ∧ ell = 0 then 1 / 2 else 0 := by
  cases m with
  | zero =>
    cases ell with
    | zero => simp [fullQxJet, qxJet, reference]; ring
    | succ ell =>
      simp [fullQxJet, qxJet, reference, iteratedDeriv_const_add (Nat.succ_pos ell)]
  | succ m =>
    simp [fullQxJet, qxJet, reference, iteratedDeriv_const_add (Nat.succ_pos m)]

def profile (φ : ℝ → ℝ) (k : ℕ) : ℕ → ℝ → ℝ
  | 0 => φ
  | m + 1 => fun t => -((k + m : ℕ) : ℝ) * profile φ k m t -
      t * deriv (profile φ k m) t

lemma profile_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k m : ℕ) :
    ContDiff ℝ ∞ (profile φ k m) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    exact (contDiff_const.mul ih).sub
      (contDiff_id.mul (contDiff_infty_iff_deriv.mp ih).2)

lemma profile_compact {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) (k m : ℕ) :
    HasCompactSupport (profile φ k m) := by
  induction m with
  | zero => exact hφ
  | succ m ih =>
    exact ih.mul_left.sub ih.deriv.mul_left

lemma iterated_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv ell φ) := by
  rw [iteratedDeriv_eq_iterate]
  exact hφ.iterate_deriv ell

private lemma iterated_compact {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) (ell : ℕ) :
    HasCompactSupport (iteratedDeriv ell φ) := by
  induction ell with
  | zero => exact hφ
  | succ ell ih => simpa only [iteratedDeriv_succ] using ih.deriv

private lemma scaled_hasDerivAt {f : ℝ → ℝ} {x y : ℝ} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f (y / x)) (k : ℤ) :
    HasDerivAt (fun z => z ^ k * f (y / z))
      (x ^ (k - 1) * ((k : ℝ) * f (y / x) - y / x * deriv f (y / x))) x := by
  have hi := (hasDerivAt_id x).inv hx
  have hc := hf.hasDerivAt.comp x (hi.const_mul y)
  have hp := (hasDerivAt_zpow k x (Or.inl hx)).mul hc
  have hk : x ^ k = x ^ (k - 1) * x := by
    calc
      x ^ k = x ^ ((k - 1) + 1) := by congr 1; omega
      _ = x ^ (k - 1) * x := by rw [zpow_add₀ hx, zpow_one]
  convert! hp using 1
  rw [hk]
  dsimp
  field_simp
  ring

private lemma scaled_iterated {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (k m : ℕ) (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    iteratedDeriv m (fun z => z ^ (-(k : ℤ)) * φ (y / z)) x =
      x ^ (-((k + m : ℕ) : ℤ)) * profile φ k m (y / x) := by
  induction m generalizing x with
  | zero => simp [profile]
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have heq : (fun z => iteratedDeriv m
        (fun u => u ^ (-(k : ℤ)) * φ (y / u)) z) =ᶠ[𝓝 x]
        (fun z => z ^ (-((k + m : ℕ) : ℤ)) * profile φ k m (y / z)) := by
      filter_upwards [eventually_ne_nhds hx] with z hz
      exact ih hz
    rw [heq.deriv_eq]
    have hd := scaled_hasDerivAt hx
      ((profile_smooth hφ k m).differentiable (by simp) (y / x))
      (-((k + m : ℕ) : ℤ))
    rw [hd.deriv]
    have he : -((k + m : ℕ) : ℤ) - 1 = -((k + (m + 1) : ℕ) : ℤ) := by omega
    rw [he]
    simp [profile]

lemma affine_iterated {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ell : ℕ) (a b x q : ℝ) :
    iteratedDeriv ell (fun u => φ ((a + b * u) / x)) q =
      b ^ ell * x ^ (-(ell : ℤ)) * iteratedDeriv ell φ ((a + b * q) / x) := by
  have heq : (fun u => φ ((a + b * u) / x)) =
      (fun u => (fun t => φ (a / x + t)) ((b / x) * u)) := by
    ext u
    congr 1
    ring
  have hs : ContDiff ℝ ell (fun t => φ (a / x + t)) :=
    (hφ.comp (contDiff_const.add contDiff_id)).of_le
      (by exact_mod_cast (le_top : (ell : ℕ∞) ≤ ⊤))
  rw [heq, iteratedDeriv_comp_const_mul (f := fun t => φ (a / x + t)) hs (b / x),
    iteratedDeriv_comp_const_add]
  simp only [zpow_neg, zpow_natCast, div_pow]
  have ht : a / x + (b / x) * q = (a + b * q) / x := by ring
  rw [ht]
  ring

lemma xq_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    xqJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((ell + m : ℕ) : ℤ)) *
        profile (iteratedDeriv ell φ) ell m ((a + b * q) / x) := by
  have heq : (fun z => iteratedDeriv ell
      (fun u => reference φ η a b z u - 1 / 2) q) =
      (fun z => (η * b ^ ell) * (z ^ (-(ell : ℤ)) *
        iteratedDeriv ell φ ((a + b * q) / z))) := by
    ext z
    simp only [reference, add_sub_cancel_left, iteratedDeriv_const_mul_field,
      affine_iterated hφ]
    ring
  unfold xqJet
  rw [heq, iteratedDeriv_const_mul_field,
    scaled_iterated (iterated_smooth hφ ell) ell m _ hx]
  ring

lemma qx_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    qxJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((m + ell : ℕ) : ℤ)) *
        iteratedDeriv ell (profile φ 0 m) ((a + b * q) / x) := by
  have heq : (fun u => iteratedDeriv m
      (fun z => reference φ η a b z u - 1 / 2) x) =
      (fun u => (η * x ^ (-(m : ℤ))) * profile φ 0 m ((a + b * u) / x)) := by
    ext u
    have hs := scaled_iterated hφ 0 m (a + b * u) hx
    simp only [Nat.cast_zero, neg_zero, zpow_zero, one_mul, zero_add] at hs
    simp only [reference, add_sub_cancel_left, iteratedDeriv_const_mul_field, hs]
    ring
  unfold qxJet
  rw [heq, iteratedDeriv_const_mul_field, affine_iterated (profile_smooth hφ 0 m)]
  have hp : x ^ (-(m : ℤ)) * x ^ (-(ell : ℤ)) = x ^ (-((m + ell : ℕ) : ℤ)) := by
    rw [← zpow_add₀ hx]
    congr 1
    push_cast
    ring
  calc
    _ = η * b ^ ell * (x ^ (-(m : ℤ)) * x ^ (-(ell : ℤ))) *
        iteratedDeriv ell (profile φ 0 m) ((a + b * q) / x) := by ring
    _ = _ := by rw [hp]

private lemma positive_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ A : ℝ, 0 < A ∧ ∀ t, |f t| ≤ A := by
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hf
  refine ⟨max A 0 + 1, by positivity, fun t => ?_⟩
  have h := hA t
  rw [Real.norm_eq_abs] at h
  exact h.trans (by linarith [le_max_left A 0])

private lemma compact_holder {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, |f u - f v| ≤ C * |u - v| ^ α := by
  obtain ⟨A, hA, hbA⟩ := positive_bound hf.continuous hc
  obtain ⟨B, hB, hbB⟩ := positive_bound
    (contDiff_infty_iff_deriv.mp hf).2.continuous hc.deriv
  let A' : ℝ≥0 := ⟨2 * A, by positivity⟩
  let B' : ℝ≥0 := ⟨B, hB.le⟩
  have hzero : HolderWith A' 0 f := by
    intro u v
    simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
    apply ENNReal.ofReal_le_coe.mpr
    change |f u - f v| ≤ 2 * A
    have htri := norm_sub_le (f u) (f v)
    simp only [Real.norm_eq_abs] at htri
    exact htri.trans (by linarith [hbA u, hbA v])
  have hone : HolderWith B' 1 f := by
    apply LipschitzWith.holderWith
    apply lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by simp))
    intro t
    change ‖deriv f t‖ ≤ B
    simpa only [Real.norm_eq_abs] using hbB t
  have hall := hzero.of_le_of_le hone (t := (⟨α, hα⟩ : ℝ≥0)) (by exact hα) (by exact hα1)
  refine ⟨max (2 * A) B, lt_max_of_lt_left (by positivity), fun u v => ?_⟩
  convert! hall.dist_le u v using 1

private lemma scaled_bound {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (c a b : ℝ) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q : ℝ,
      |c * x ^ (-(p : ℤ)) * f ((a + b * q) / x)| ≤ K * x ^ (-(p : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := positive_bound hf hc
  refine ⟨|c| * A + 1, by positivity, fun x hx q => ?_⟩
  have hz : 0 < x ^ (-(p : ℤ)) := zpow_pos hx _
  rw [abs_mul, abs_mul, abs_of_pos hz]
  rw [show x ^ (-(p : ℝ)) = x ^ (-(p : ℤ)) by
    rw [← Real.rpow_intCast]; simp]
  nlinarith [mul_le_mul_of_nonneg_left (hb ((a + b * q) / x))
    (mul_nonneg (abs_nonneg c) hz.le)]

/-- Every mixed order has the same inverse scale in both derivative orders.
The constant is independent of the positive scale and of the evaluation point. -/
private theorem mixed_derivative_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m ell : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q : ℝ,
      |xqJet φ η a b m ell x q| ≤ K * x ^ (-((m + ell : ℕ) : ℝ)) ∧
      |qxJet φ η a b m ell x q| ≤ K * x ^ (-((m + ell : ℕ) : ℝ)) := by
  obtain ⟨A, hA, hbA⟩ := scaled_bound
    (profile_smooth (iterated_smooth hφ ell) ell m).continuous
    (profile_compact (iterated_compact hc ell) ell m) (η * b ^ ell) a b (ell + m)
  obtain ⟨B, hB, hbB⟩ := scaled_bound
    (iterated_smooth (profile_smooth hφ 0 m) ell).continuous
    (iterated_compact (profile_compact hc 0 m) ell) (η * b ^ ell) a b (m + ell)
  refine ⟨A + B, by positivity, fun x hx q => ?_⟩
  constructor
  · rw [xq_formula hφ η a b m ell hx.ne' q]
    have h := hbA x hx q
    rw [Nat.add_comm ell m] at h ⊢
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))
  · rw [qx_formula hφ η a b m ell hx.ne' q]
    exact (hbB x hx q).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx.le _))

private lemma scaled_holder {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (c a b : ℝ) (p : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ q q' : ℝ,
      |c * x ^ (-(p : ℤ)) * f ((a + b * q) / x) -
        c * x ^ (-(p : ℤ)) * f ((a + b * q') / x)| ≤
      K * x ^ (-(p : ℝ) - α) * |q - q'| ^ α := by
  obtain ⟨C, hC, hb⟩ := compact_holder hf hc hα.le hα1
  refine ⟨|c| * C * |b| ^ α + 1, by positivity, fun x hx q q' => ?_⟩
  have hdiff : |(a + b * q) / x - (a + b * q') / x| = |b| / x * |q - q'| := by
    rw [← sub_div, show a + b * q - (a + b * q') = b * (q - q') by ring,
      abs_div, abs_mul, abs_of_pos hx]
    ring
  have hbase := hb ((a + b * q) / x) ((a + b * q') / x)
  rw [hdiff, Real.mul_rpow (by positivity) (abs_nonneg _),
    Real.div_rpow (abs_nonneg _) hx.le] at hbase
  have hscale : x ^ (-(p : ℤ)) / x ^ α = x ^ (-(p : ℝ) - α) := by
    rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast, Real.rpow_sub hx]
  have hpos : 0 ≤ |c| * x ^ (-(p : ℤ)) := by positivity
  have h := mul_le_mul_of_nonneg_left hbase hpos
  rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (zpow_pos hx _)]
  calc
    _ ≤ (|c| * x ^ (-(p : ℤ))) *
        (C * (|b| ^ α / x ^ α * |q - q'| ^ α)) := h
    _ = (|c| * C * |b| ^ α) * x ^ (-(p : ℝ) - α) * |q - q'| ^ α := by
      rw [← hscale]
      ring
    _ ≤ _ := by gcongr; linarith

private lemma centered_holder_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m r : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∀ ell ≤ r, ∀ q : ℝ,
        |qxJet φ η a b m ell x q| ≤ K * x ^ (-((m + r : ℕ) : ℝ) - α)) ∧
      (∀ q q' : ℝ, |qxJet φ η a b m r x q - qxJet φ η a b m r x q'| ≤
        K * x ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α) := by
  classical
  obtain ⟨C, hC, hbC⟩ := scaled_holder
    (iterated_smooth (profile_smooth hφ 0 m) r)
    (iterated_compact (profile_compact hc 0 m) r) (η * b ^ r) a b (m + r) hα hα1
  choose A hA hbA using fun ell => mixed_derivative_scale hφ hc η a b m ell
  let T : ℝ := ∑ ell ∈ Finset.range (r + 1), A ell
  have hT : 0 ≤ T := Finset.sum_nonneg fun ell _ => (hA ell).le
  refine ⟨T + C, by positivity, fun x hx hx1 => ⟨?_, ?_⟩⟩
  · intro ell hell q
    have hAT : A ell ≤ T := Finset.single_le_sum
      (fun i _ => (hA i).le) (Finset.mem_range.mpr (by omega : ell < r + 1))
    have hpow : x ^ (-((m + ell : ℕ) : ℝ)) ≤ x ^ (-((m + r : ℕ) : ℝ) - α) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx hx1
      have he : (ell : ℝ) ≤ r := by exact_mod_cast hell
      push_cast
      linarith
    exact ((hbA ell x hx q).2).trans
      (mul_le_mul (by linarith : A ell ≤ T + C) hpow
        (Real.rpow_nonneg hx.le _) (by positivity))
  · intro q q'
    rw [qx_formula hφ η a b m r hx.ne' q, qx_formula hφ η a b m r hx.ne' q']
    exact (hbC x hx q q').trans (by
      gcongr
      linarith)

private lemma full_holder_scale {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (η a b : ℝ) (m r : ℕ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (∀ ell ≤ r, ∀ q : ℝ,
        |fullQxJet φ η a b m ell x q| ≤ K * x ^ (-((m + r : ℕ) : ℝ) - α)) ∧
      (∀ q q' : ℝ, |fullQxJet φ η a b m r x q - fullQxJet φ η a b m r x q'| ≤
        K * x ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α) := by
  obtain ⟨K, hK, hb⟩ := centered_holder_scale hφ hc η a b m r hα hα1
  refine ⟨K + 1, by positivity, fun x hx hx1 => ⟨?_, ?_⟩⟩
  · intro ell hell q
    rw [fullQxJet_eq]
    have hp : 1 ≤ x ^ (-((m + r : ℕ) : ℝ) - α) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by
        have : (0 : ℝ) ≤ (m + r : ℕ) := Nat.cast_nonneg _
        linarith)
    have hconst : |(if m = 0 ∧ ell = 0 then 1 / 2 else 0 : ℝ)| ≤ 1 := by
      split <;> norm_num
    have ht := abs_add_le (qxJet φ η a b m ell x q)
      (if m = 0 ∧ ell = 0 then 1 / 2 else 0)
    nlinarith [(hb x hx hx1).1 ell hell q]
  · intro q q'
    simp only [fullQxJet_eq, add_sub_add_right_eq_sub]
    exact ((hb x hx hx1).2 q q').trans (by gcongr; linarith)

/-- Positive-side power profile, extended by zero. -/
def cutoff (χ : ℝ → ℝ) (β t : ℝ) : ℝ :=
  if 0 < t then χ t * t ^ β else 0

private lemma cutoff_eq_mul {χ : ℝ → ℝ} (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) :
    cutoff χ β = fun t => χ t * t ^ β := by
  ext t
  by_cases ht : 0 < t
  · simp [cutoff, ht]
  · have hz : χ t = 0 := by
      by_contra hn
      exact ht (hs (subset_closure hn))
    simp [cutoff, ht, hz]

lemma cutoff_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) : ContDiff ℝ ∞ (cutoff χ β) := by
  rw [cutoff_eq_mul hs β]
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hz : (0 : ℝ) ∉ tsupport χ := fun h => lt_irrefl (0 : ℝ) (hs h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with t ht
    simp [ht]
  · exact hχ.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne ht)

private lemma cutoff_compact {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioi 0) (β : ℝ) : HasCompactSupport (cutoff χ β) := by
  rw [cutoff_eq_mul hs β]
  exact hc.mul_right

private lemma ring_scale {s c x p : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hxs : s / c ≤ x) (hp : 0 ≤ p) :
    x ^ (-p) ≤ c ^ p * s ^ (-p) := by
  calc
    x ^ (-p) ≤ (s / c) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hs hc) hxs (by linarith)
    _ = c ^ p * s ^ (-p) := by
      rw [Real.div_rpow hs.le hc.le, Real.rpow_neg hc.le p, div_inv_eq_mul]
      ring

/-- The cutoff reference has uniform bounds for every mixed order on every
proportional ring. Its scale derivatives have the full `C^(r+alpha)` bound:
all derivatives through order `r`, and the `alpha`-Hölder bound of the top
jet, use one constant independent of the ring, scale and evaluation points.
No differentiability or continuity at scale zero is asserted. -/
theorem cutoff_reference_mixed_scales {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ioi 0)
    (β η a b c : ℝ) (hc : 0 < c) :
    (∀ m ell : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ s x : ℝ, 0 < s → 0 < x → s / c ≤ x →
      ∀ q : ℝ,
        |xqJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ)) ∧
        |qxJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ))) ∧
    (∀ (m r : ℕ) (α : ℝ), 0 < α → α ≤ 1 → ∃ K : ℝ, 0 < K ∧
      ∀ s x : ℝ, 0 < s → 0 < x → x ≤ 1 → s / c ≤ x →
        (∀ ell ≤ r, ∀ q : ℝ,
          |fullQxJet (cutoff χ β) η a b m ell x q| ≤
            K * s ^ (-((m + r : ℕ) : ℝ) - α)) ∧
        (∀ q q' : ℝ,
          |fullQxJet (cutoff χ β) η a b m r x q - fullQxJet (cutoff χ β) η a b m r x q'| ≤
            K * s ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α)) := by
  have hφ := cutoff_smooth hχ hsχ β
  have hcφ := cutoff_compact hcχ hsχ β
  constructor
  · intro m ell
    obtain ⟨K, hK, hb⟩ := mixed_derivative_scale hφ hcφ η a b m ell
    refine ⟨K * c ^ ((m + ell : ℕ) : ℝ), by positivity, fun s x hs hx hxs q => ?_⟩
    have hr := ring_scale hs hc hxs (show (0 : ℝ) ≤ (m + ell : ℕ) by positivity)
    have h := mul_le_mul_of_nonneg_left hr hK.le
    rw [← mul_assoc] at h
    exact ⟨((hb x hx q).1).trans h, ((hb x hx q).2).trans h⟩
  · intro m r α hα hα1
    obtain ⟨K, hK, hb⟩ := full_holder_scale hφ hcφ η a b m r hα hα1
    refine ⟨K * c ^ (((m + r : ℕ) : ℝ) + α), by positivity,
      fun s x hs hx hx1 hxs => ?_⟩
    have hr := ring_scale hs hc hxs (show (0 : ℝ) ≤ ((m + r : ℕ) : ℝ) + α by positivity)
    rw [neg_add, ← sub_eq_add_neg] at hr
    have h : K * x ^ (-((m + r : ℕ) : ℝ) - α) ≤
        (K * c ^ (((m + r : ℕ) : ℝ) + α)) * s ^ (-((m + r : ℕ) : ℝ) - α) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr hK.le
    constructor
    · intro ell hell q
      exact ((hb x hx hx1).1 ell hell q).trans h
    · intro q q'
      exact ((hb x hx hx1).2 q q').trans
        (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (abs_nonneg _) _))

open LorentzCommonGridStability LorentzLowDegreeCoefficientRemainder
open LorentzLocalCoefficientKernel OriginalRingEnvelopeScale HNPCorrectionLiftAdvantage

lemma complex_jet {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (ν : ℕ)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin ν (fun q => (f q : ℂ)) (Set.Icc 0 1) q =
      ((iteratedDeriv ν f q : ℝ) : ℂ) := by
  have hν : (ν : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) := by
    exact_mod_cast (le_top : (ν : ℕ∞) ≤ ⊤)
  have hc := Complex.ofRealCLM.contDiff.comp hf
  have hc' : ContDiffAt ℝ ν (fun q => (f q : ℂ)) q := by
    simpa only [Function.comp_def,Complex.ofRealCLM_apply] using (hc.of_le hν).contDiffAt (x := q)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) hc' hq]
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left (hf.contDiffAt (x := q)) hν
  simpa only [iteratedDeriv,Function.comp_def,Complex.ofRealCLM_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe] using
      congrArg (fun p => p (fun _ : Fin ν => (1 : ℝ))) h

private lemma reference_range {χ : ℝ → ℝ} {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hs : tsupport χ ⊆ Ioo 0 T) (hχ : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d x q : ℝ) :
    |reference (cutoff χ β) (2/(5*T^β)) a d x q-7/10| ≤ 1/5 := by
  have hp (t : ℝ) : 0 ≤ cutoff χ β t ∧ cutoff χ β t ≤ T^β := by
    by_cases ht : 0 < t
    · by_cases hz : χ t = 0
      · simp [cutoff,ht,hz,Real.rpow_nonneg hT.le]
      · have hu := (hs (subset_closure hz)).2.le
        have hb := Real.rpow_le_rpow ht.le hu hβ
        simp only [cutoff,if_pos ht]
        constructor
        · exact mul_nonneg (hχ t).1 (Real.rpow_nonneg ht.le _)
        · exact (mul_le_of_le_one_left (Real.rpow_nonneg ht.le _) (hχ t).2).trans hb
    · simp [cutoff,ht,Real.rpow_nonneg hT.le]
  have hpow : 0 < T^β := Real.rpow_pos_of_pos hT _
  obtain ⟨hl,hu⟩ := hp ((a+d*q)/x)
  have heta : 0 ≤ 2/(5*T^β) := by positivity
  have hb := mul_le_mul_of_nonneg_left hu heta
  have he : (2/(5*T^β))*T^β = (2/5 : ℝ) := by field_simp
  rw [he] at hb
  rw [abs_le]
  unfold reference
  constructor <;> nlinarith [mul_nonneg heta hl]

/-- The original compact-cutoff reference uses one starting degree and one
ring amplitude for all positive scales. Its actual corrected coefficients
have the strict interval margin `[9/20,19/20]`; their center increments are
paid by the same elevated corrections. -/
private theorem cutoff_reference_ring_budget {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ j : ℕ, ∀ x : ℝ,
      0 < x → x ≤ 1 → ringScale xstar b j / Real.sqrt b ≤ x →
      let f := fun q : ℝ => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r,
          ‖bernsteinCoefficient ((N*b^j)*b^k+r) t (center (N*b^j) b r f k)-(7/10 : ℂ)‖ +
            D*(ringScale xstar b j)^(-ρ)*
              lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) t
                (correction ρ θ ((N*b^j)*b^k)) ≤ 1/4) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          ‖bernsteinCoefficient ((N*b^j)*b^(k+1)+r) t
            (center (N*b^j) b r f (k+1)-center (N*b^j) b r f k)‖ ≤
            D*(ringScale xstar b j)^(-ρ)*
              (lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t
                (fun i => lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) i
                  (correction ρ θ ((N*b^j)*b^k))) -
               lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^(k+1)) t
                (correction ρ θ ((N*b^j)*b^(k+1))))) := by
  have hs0 : tsupport χ ⊆ Ioi 0 := fun t ht => (hsχ ht).1
  have hφ := cutoff_smooth hχ hs0 β
  obtain ⟨B,hB,hbudget⟩ := uniform_ring_correction_budget r ρ θ hρ hρ1 hρ2 hθ
  refine ⟨B,hB,?_⟩
  intro b hb xstar hxstar
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hp := cutoff_reference_mixed_scales hχ hcχ hs0 β (2/(5*T^β)) a d
    (Real.sqrt b) hsqrt
  choose K hK hKb using hp.1 0
  let A := 1+∑ ν ∈ Finset.Icc 1 r, K ν
  have hA : 0 ≤ A := by
    have := Finset.sum_nonneg (s := Finset.Icc 1 r) (fun ν _ => (hK ν).le)
    dsimp [A]; linarith
  obtain ⟨H,hH,hHb⟩ := hp.2 0 r (ρ-r) (by linarith) (by linarith)
  obtain ⟨D,hD,N,hN,hNb⟩ := hbudget b hb xstar A H (1/20) hxstar hA hH.le (by norm_num)
  refine ⟨D,hD,N,hN,?_⟩
  intro j x hx hx1 hxs
  let g := reference (cutoff χ β) (2/(5*T^β)) a d x
  have hg : ContDiff ℝ ∞ g := by
    exact contDiff_const.add (contDiff_const.mul
      (hφ.comp ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const x)))
  have hgc : ContDiffOn ℝ r (fun q => (g q : ℂ)) (Set.Icc 0 1) :=
    (Complex.ofRealCLM.contDiff.comp hg).contDiffOn.of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  have hs : 0 < ringScale xstar b j := by unfold ringScale; positivity
  have hder (ν : ℕ) (hν : ν ∈ Finset.Icc 1 r) (q : ℝ) (_hq : q ∈ Set.Icc 0 1) :
      ‖iteratedDerivWithin ν (fun q => (g q : ℂ)) (Set.Icc 0 1) q‖ ≤
        A*(ringScale xstar b j)^(-(ν : ℝ)) := by
    rw [complex_jet hg ν _hq,Complex.norm_real,Real.norm_eq_abs]
    have hν0 : 0 < ν := (Finset.mem_Icc.mp hν).1
    have hh := (hKb ν (ringScale xstar b j) x hs hx hxs q).2
    have he : qxJet (cutoff χ β) (2/(5*T^β)) a d 0 ν x q = iteratedDeriv ν g q := by
      change iteratedDeriv ν (fun u => (1/2+(2/(5*T^β))*cutoff χ β ((a+d*u)/x))-1/2) q =
        iteratedDeriv ν (fun u => 1/2+(2/(5*T^β))*cutoff χ β ((a+d*u)/x)) q
      simp only [add_sub_cancel_left,iteratedDeriv_const_add hν0]
    rw [he] at hh
    have hKA : K ν ≤ A := by
      have := Finset.single_le_sum (s := Finset.Icc 1 r) (f := K)
        (fun i _ => (hK i).le) hν
      dsimp [A]; linarith
    have hh' : |iteratedDeriv ν g q| ≤ K ν*(ringScale xstar b j)^(-(ν : ℝ)) := by simpa using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right hKA (by positivity))
  have hholder (q : ℝ) (hq : q ∈ Set.Icc 0 1) (q' : ℝ) (hq' : q' ∈ Set.Icc 0 1) :
      ‖iteratedDerivWithin r (fun q => (g q : ℂ)) (Set.Icc 0 1) q -
        iteratedDerivWithin r (fun q => (g q : ℂ)) (Set.Icc 0 1) q'‖ ≤
          H*(ringScale xstar b j)^(-ρ)*|q-q'|^(ρ-(r : ℝ)) := by
    rw [complex_jet hg r hq,complex_jet hg r hq',← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    have hh := (hHb (ringScale xstar b j) x hs hx hx1 hxs).2 q q'
    simpa only [fullQxJet,iteratedDeriv_zero,g,Nat.zero_add,
      show -(r : ℝ)-(ρ-(r : ℝ)) = -ρ by ring] using hh
  have hf (q : ℝ) (_hq : q ∈ Set.Icc 0 1) : ‖(g q : ℂ)-(7/10 : ℂ)‖ ≤ 1/5 := by
    have hh := reference_range hT hβ hsχ hχrange a d x q
    rw [show (7/10 : ℂ) = ((7/10 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hh
  have ht := hNb j (fun q => (g q : ℂ)) hgc (7/10) (1/5) (by norm_num) hf hder hholder
  norm_num only [show (1/5 : ℝ)+1/20 = 1/4 by norm_num] at ht
  exact ht

open Polynomial Finset

/-- The original lower ring coefficient in the current common degree. -/
def ringLower (τ b r : ℕ) (ρ θ D : ℝ) (f : ℝ → ℂ) (k t : ℕ) : ℝ :=
  (bernsteinCoefficient (τ*b^k+r) t (center τ b r f k)).re -
    D*lift (τ*b^k+r) (τ*b^k) t (correction ρ θ (τ*b^k))

/-- The original upper ring coefficient in the current common degree. -/
def ringUpper (τ b r : ℕ) (ρ θ D : ℝ) (f : ℝ → ℂ) (k t : ℕ) : ℝ :=
  (bernsteinCoefficient (τ*b^k+r) t (center τ b r f k)).re +
    D*lift (τ*b^k+r) (τ*b^k) t (correction ρ θ (τ*b^k))

private lemma coefficient_elevation {d D t : ℕ} (hd : d ≤ D) (ht : t ≤ D)
    (P : ℂ[X]) (hP : P.natDegree ≤ d) :
    lift D d t (fun i => (bernsteinCoefficient d i P).re) =
      (bernsteinCoefficient D t P).re := by
  have hb (i : ℕ) (hi : i ≤ d) :
      bernsteinCoefficient D t (bernsteinPolynomial ℂ d i) =
        if i ≤ t then (weight D d t i : ℂ) else 0 := by
    have he : bernsteinPolynomial ℂ d i =
        C (d.choose i : ℂ)*(X^i*(1-X)^(d-i)) := by
      simp [bernsteinPolynomial,mul_assoc]
    rw [he,bernstein_coefficient_C_mul,coefficient_homogeneous_real ht (by omega)]
    unfold homogeneousWeight weight
    by_cases hit : i ≤ t
    · by_cases hdr : d-i ≤ D-t
      · simp only [hit,hdr,and_self,if_true]
        have he : D-i-(d-i) = D-d := by omega
        rw [he]
        push_cast
        ring
      · have hz : (D-d).choose (t-i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hit,hdr,hz]
    · simp [hit]
  have heq : (range (t+1)).filter (fun i => i ≤ d) =
      (range (d+1)).filter (fun i => i ≤ t) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  calc
    _ = ∑ i ∈ range (t+1), if i ≤ d then
        weight D d t i*(bernsteinCoefficient d i P).re else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ≤ d
      · simp [hi]
      · simp [hi,weight,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)]
    _ = ∑ i ∈ (range (t+1)).filter (fun i => i ≤ d),
        weight D d t i*(bernsteinCoefficient d i P).re := (Finset.sum_filter _ _).symm
    _ = ∑ i ∈ range (d+1), if i ≤ t then
        weight D d t i*(bernsteinCoefficient d i P).re else 0 := by
      rw [heq,sum_filter]
    _ = _ := by
      conv_rhs => rw [← bernstein_reconstruction P d hP,bernstein_coefficient_sum]
      rw [Complex.re_sum]
      apply sum_congr rfl
      intro i hi
      rw [bernstein_coefficient_C_mul,hb i (by have := Finset.mem_range.mp hi; omega)]
      split_ifs <;> simp [Complex.mul_re,mul_comm]

private lemma center_degree {τ b : ℕ} (hb : 0 < b) (r : ℕ) (f : ℝ → ℂ) (k : ℕ) :
    (center τ b r f k).natDegree ≤ τ*b^k+r := by
  induction k with
  | zero =>
    simpa only [LorentzCommonGridStability.center,LorentzWeightedHolderControl.holderOperator,pow_zero,mul_one] using
      (LorentzCoefficientRemainder.lorentz_degree τ r
        (fun ν i => iteratedDerivWithin ν f (Set.Icc 0 1) ((i : ℝ)/τ)))
  | succ k ih =>
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact ih.trans (Nat.add_le_add_right (Nat.mul_le_mul_left τ
        (Nat.pow_le_pow_right hb (by omega : k ≤ k+1))) r)
    · exact LorentzCoefficientRemainder.lorentz_degree _ _ _

/-- The original reference ring arrays have a common strict probability
margin and are compatible under the actual hypergeometric degree lift.
All rings use the same initial degree and fixed correction amplitude. -/
theorem reference_ring_envelopes {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ j : ℕ, ∀ x : ℝ,
      0 < x → x ≤ 1 → ringScale xstar b j / Real.sqrt b ≤ x →
      let f := fun q : ℝ => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
      let lower := ringLower (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f
      let upper := ringUpper (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r, (9/20 : ℝ) ≤ lower k t ∧
          lower k t ≤ upper k t ∧ upper k t ≤ 19/20) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (lower k) ≤ lower (k+1) t ∧
          upper (k+1) t ≤ lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (upper k)) := by
  obtain ⟨B,hB,hb⟩ := cutoff_reference_ring_budget hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ
  refine ⟨B,hB,?_⟩
  intro b hBb xstar hxstar
  obtain ⟨D,hD,N,hN,hh⟩ := hb b hBb xstar hxstar
  refine ⟨D,hD,N,hN,?_⟩
  intro j x hx hx1 hxs
  dsimp only
  let f := fun q : ℝ => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
  let τ := N*b^j
  let Dj := D*(ringScale xstar b j)^(-ρ)
  have hDj : 0 ≤ Dj := by dsimp [Dj,ringScale]; positivity
  have hbb : 0 < b := by omega
  intro k
  have h := hh j x hx hx1 hxs k
  constructor
  · intro t ht
    have hm := h.1 t ht
    have hc : 0 ≤ lift (τ*b^k+r) (τ*b^k) t (correction ρ θ (τ*b^k)) := by
      apply sum_nonneg
      intro i _
      exact mul_nonneg (by unfold weight; positivity) (by unfold correction sample; positivity)
    have hr := Complex.abs_re_le_norm
      (bernsteinCoefficient (τ*b^k+r) t (center τ b r f k)-(7/10 : ℂ))
    have hs := abs_le.mp hr
    norm_num only [Complex.sub_re,show (7/10 : ℂ).re = (7/10 : ℝ) by norm_num] at hs
    dsimp only [ringLower,ringUpper]
    change (9/20 : ℝ) ≤ (bernsteinCoefficient (τ*b^k+r) t (center τ b r f k)).re-Dj*_ ∧ _
    dsimp [τ,f,Dj] at hs hc ⊢
    constructor
    · nlinarith [mul_nonneg hDj hc]
    constructor <;> nlinarith [mul_nonneg hDj hc]
  · intro t ht
    let old := τ*b^k+r
    let next := τ*b^(k+1)+r
    have hle : old ≤ next := Nat.add_le_add_right
      (Nat.mul_le_mul_left τ (Nat.pow_le_pow_right hbb (by omega))) r
    have hlift := coefficient_elevation hle ht (center τ b r f k) (center_degree hbb r f k)
    have hlin (v w : ℕ → ℝ) :
        lift next old t (fun i => v i-Dj*w i) = lift next old t v-Dj*lift next old t w ∧
        lift next old t (fun i => v i+Dj*w i) = lift next old t v+Dj*lift next old t w := by
      have he : (∑ i ∈ range (t+1), weight next old t i*(Dj*w i)) =
          Dj*∑ i ∈ range (t+1), weight next old t i*w i := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      simp only [lift,mul_sub,mul_add,sum_sub_distrib,sum_add_distrib,he,and_self]
    have hm := h.2 t ht
    have hr := (Complex.abs_re_le_norm _).trans hm
    rw [LorentzCoefficientRemainder.coefficient_sub,Complex.sub_re,abs_le] at hr
    change lift next old t (fun i => (bernsteinCoefficient old i (center τ b r f k)).re -
        Dj*lift old (τ*b^k) i (correction ρ θ (τ*b^k))) ≤
          (bernsteinCoefficient next t (center τ b r f (k+1))).re-
            Dj*lift next (τ*b^(k+1)) t (correction ρ θ (τ*b^(k+1))) ∧
      (bernsteinCoefficient next t (center τ b r f (k+1))).re+
        Dj*lift next (τ*b^(k+1)) t (correction ρ θ (τ*b^(k+1))) ≤
          lift next old t (fun i => (bernsteinCoefficient old i (center τ b r f k)).re +
            Dj*lift old (τ*b^k) i (correction ρ θ (τ*b^k)))
    rw [(hlin _ _).1,(hlin _ _).2,hlift]
    dsimp [τ,f,Dj,old,next] at hr ⊢
    constructor <;> linarith [hr.1,hr.2]

end D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets

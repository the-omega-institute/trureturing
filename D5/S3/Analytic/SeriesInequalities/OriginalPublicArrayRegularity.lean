/- GID: D5/S3/Analytic/SeriesInequalities/OriginalPublicArrayRegularity
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/OriginalPublicArrayRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common weighted parameter jets of the original smooth public arrays. -/

import D5.S3.Analytic.SeriesInequalities.LogScalePartitionJets
import D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal
import Mathlib.Topology.MetricSpace.Holder

noncomputable section
open Finset Filter
open scoped Topology ContDiff NNReal

namespace D5.S3.Analytic.SeriesInequalities.OriginalPublicArrayRegularity

open ParametricLorentzJetTransport LogScalePartitionJets
open OriginalRingEnvelopeScale ReferenceProfileMixedJets LorentzCoefficientRemainder
open LorentzCommonGridStability LorentzLowDegreeCoefficientRemainder

/-- Legality of the original corrected rings on the same fixed public grid. -/
def RingEnvelopes (χ : ℝ → ℝ) (T β a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D X : ℝ) : Prop :=
  ∀ j x, 0 < x → x ≤ 1 → ringScale X b j/Real.sqrt b ≤ x →
  let f := fun q : ℝ => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
  let low := ringLower (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ)) f
  let upp := ringUpper (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ)) f
  ∀ k, (∀ t ≤ (N*b^j)*b^k+r, (9/20 : ℝ) ≤ low k t ∧
    low k t ≤ upp k t ∧ upp k t ≤ 19/20) ∧
    (∀ t ≤ (N*b^j)*b^(k+1)+r,
      HNPCorrectionLiftAdvantage.lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (low k) ≤ low (k+1) t ∧
      upp (k+1) t ≤ HNPCorrectionLiftAdvantage.lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (upp k))

private lemma ring_scale_jet_bound {X x : ℝ} {b j : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hb : 1 < b) (hz : |scaleCoordinate X b x-j| < 1) (m : ℕ) :
    (ringScale X b j)^(-(m : ℝ)) ≤ (Real.sqrt b)^(m : ℝ)*x^(-(m : ℝ)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hs := Real.sqrt_pos.mpr hbR
  apply (Real.rpow_le_rpow_of_nonpos (div_pos hx hs) (jet_ring_scale hX hx hb hz).2
    (neg_nonpos.mpr (Nat.cast_nonneg m))).trans_eq
  rw [Real.div_rpow hx.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul,mul_comm]


private lemma original_ring_jets {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ X : ℝ, 0 < X → X ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ RingEnvelopes χ T β a d r ρ θ b N D X ∧
      ∀ m : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ j k t : ℕ, t ≤ (N*b^j)*b^k+r → ∀ x : ℝ, 0 < x → x ≤ X →
        |scaleCoordinate X b x-j| < 1 →
        (|iteratedDeriv m (fun y => ringLower (N*b^j) b r ρ θ
          (D*(ringScale X b j)^(-ρ))
          (fun q => (reference (cutoff χ β) (2/(5*T^β)) a d y q : ℂ)) k t) x| ≤
            A*x^(-(m : ℝ))) ∧
        (|iteratedDeriv m (fun y => 1-ringUpper (N*b^j) b r ρ θ
          (D*(ringScale X b j)^(-ρ))
          (fun q => (reference (cutoff χ β) (2/(5*T^β)) a d y q : ℂ)) k t) x| ≤
            A*x^(-(m : ℝ))) := by
  obtain ⟨Br,hBr,hr⟩ := reference_ring_envelopes hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ
  obtain ⟨Bc,hBc,hc⟩ := reference_center_mixed_scales hχ hcχ
    (fun y hy => (hsχ hy).1) β (2/(5*T^β)) a d r ρ hρ hρ1
  refine ⟨max Br Bc,hBr.trans (le_max_left _ _),?_⟩
  intro b hb X hX hX1
  have hb1 : 1 < b := by have := le_trans (le_max_left Br Bc) hb; omega
  have hb0 : 0 < b := by omega
  obtain ⟨D,hD,N,hN,hring⟩ := hr b ((le_max_left _ _).trans hb) X hX
  have hN0 : 0 < N := by omega
  refine ⟨D,hD,N,hN,hring,?_⟩
  intro m
  by_cases hm : m = 0
  · subst m
    refine ⟨1,by norm_num,?_⟩
    intro j k t ht x hx hxx hz
    have hr := (hring j x hx (hxx.trans hX1) (jet_ring_scale hX hx hb1 hz).1 k).1 t ht
    simp only [iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one]
    rw [abs_le,abs_le]
    constructor <;> constructor <;> linarith [hr.1,hr.2.1,hr.2.2]
  obtain ⟨C,hC,hcb⟩ := hc b ((le_max_right _ _).trans hb) X hX N (by omega) m
  refine ⟨C*(Real.sqrt b)^(m : ℝ),by
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
    exact mul_pos hC (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hbR) _),?_⟩
  intro j k t ht x hx hxx hz
  let f : ℝ → ℂ := fun y => bernsteinCoefficient ((N*b^j)*b^k+r) t
    (center (N*b^j) b r (fun q => (reference (cutoff χ β) (2/(5*T^β)) a d y q : ℂ)) k)
  have hφ := cutoff_smooth hχ (fun y hy => (hsχ hy).1) β
  have hf : ContDiffAt ℝ m f x :=
    (coefficient_smooth (by positivity : 0 < N*b^j) hb0 hφ (2/(5*T^β))
      a d r k _ t hx).of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hfr : ContDiffAt ℝ m (fun y => (f y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hf
  have hest : |iteratedDeriv m (fun y => (f y).re) x| ≤
      (C*(Real.sqrt b)^(m : ℝ))*x^(-(m : ℝ)) := by
    change |iteratedDeriv m (fun y => Complex.reCLM (f y)) x| ≤ _
    rw [linear_iterated Complex.reCLM hf]
    apply (Complex.abs_re_le_norm _).trans
    apply ((hcb j x hx (hxx.trans hX1) (jet_ring_scale hX hx hb1 hz).1 k).1 t ht).trans
    calc
      _ ≤ C*((Real.sqrt b)^(m : ℝ)*x^(-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left (ring_scale_jet_bound hX hx hb1 hz m) hC.le
      _ = _ := by ring
  constructor
  · change |iteratedDeriv m (fun y => (f y).re - _) x| ≤ _
    rw [iteratedDeriv_fun_sub hfr contDiffAt_const,iteratedDeriv_const,if_neg hm,sub_zero]
    exact hest
  · change |iteratedDeriv m (fun y => 1-((f y).re + _)) x| ≤ _
    rw [iteratedDeriv_fun_sub contDiffAt_const (hfr.add contDiffAt_const),
      iteratedDeriv_const,if_neg hm,zero_sub,
      iteratedDeriv_fun_add hfr contDiffAt_const,iteratedDeriv_const,if_neg hm,add_zero,abs_neg]
    exact hest


/-- A single original grid and fixed ring corrections give all public parameter
jets a common weighted bound. Constants are chosen before the stage, coefficient
index and world parameter; the order zero bound is centered at one half. -/
theorem reference_public_weighted_jets {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ X : ℝ, 0 < X → X ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ RingEnvelopes χ T β a d r ρ θ b N D X ∧ ∀ W : ℝ, ∀ m : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ k t : ℕ, t ≤ N*b^k+r →
      ∀ x : ℝ, 0 < x → x ≤ X →
        (|iteratedDeriv m (fun y =>
          publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t y-1/2) x| ≤
            C*x^(β-m)) ∧
        (|iteratedDeriv m (fun y =>
          publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t y-1/2) x| ≤
            C*x^(β-m)) := by
  obtain ⟨B,hB,hb⟩ := original_ring_jets hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ
  refine ⟨B,hB,?_⟩
  intro b hBb X hX hX1
  obtain ⟨D,hD,N,hN,hring,hjets⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,hring,?_⟩
  intro W m
  have hb1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  have hN0 : 0 < N := by omega
  choose A hA hAb using hjets
  choose Q hQ hQb using fun i => mixture_jet_bound hX hb1 i A (fun i => (hA i).le)
  let P : ℕ → ℝ := fun i => |W| * |∏ j ∈ range i, (β-(j : ℝ))|
  let C := ∑ i ∈ range (m+1), (m.choose i : ℝ)*P i*(Q (m-i)+1)
  have hP (i : ℕ) : 0 ≤ P i := by dsimp [P]; positivity
  have hC : 0 ≤ C := sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP i)) (by have := hQ (m-i); linarith))
  refine ⟨C+1,by positivity,?_⟩
  intro k t ht x hx hxx
  let F (u : Bool) (j : ℕ) (y : ℝ) := if u then
    1-ringUpper (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ))
      (fun q => (reference (cutoff χ β) (2/(5*T^β)) a d y q : ℂ)) (k-j) t
    else ringLower (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ))
      (fun q => (reference (cutoff χ β) (2/(5*T^β)) a d y q : ℂ)) (k-j) t
  let M (u : Bool) (y : ℝ) := ∑ j ∈ range (k+1), scaleWeight X b j y*F u j y
  have hφ := cutoff_smooth hχ (fun y hy => (hsχ hy).1) β
  have hF (u : Bool) (j : ℕ) : ContDiffAt ℝ ∞ (F u j) x := by
    have hf := Complex.reCLM.contDiff.contDiffAt.comp x
      (coefficient_smooth (by positivity : 0 < N*b^j) hb0 hφ (2/(5*T^β)) a d r (k-j)
        ((N*b^j)*b^(k-j)+r) t hx)
    cases u
    · exact hf.sub contDiffAt_const
    · exact contDiffAt_const.sub (hf.add contDiffAt_const)
  have hM (u : Bool) : ContDiffAt ℝ ∞ (M u) x :=
    ContDiffAt.sum (fun j _ => (weight_smooth hX hx hxx hb1 j).mul (hF u j))
  have hMb (u : Bool) (i : ℕ) :
      |iteratedDeriv i (M u) x| ≤ Q i*x^(-(i : ℝ)) := by
    apply hQb i (range (k+1)) (F u) x hx hxx
    · intro j _
      exact (hF u j).of_le (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    · intro j hj hz ell _
      have hjk : j ≤ k := by simpa using Nat.le_of_lt_succ (mem_range.mp hj)
      have he : (N*b^j)*b^(k-j) = N*b^k := by
        rw [mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
      have hh := hAb ell j (k-j) t (by rwa [he]) x hx hxx hz
      cases u
      · exact hh.1
      · exact hh.2
  have hcenter (u : Bool) (i : ℕ) :
      |iteratedDeriv i (fun y => M u y-1/2) x| ≤ (Q i+1)*x^(-(i : ℝ)) := by
    rw [iteratedDeriv_fun_sub ((hM u).of_le
      (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))) contDiffAt_const,iteratedDeriv_const]
    by_cases hi : i = 0
    · subst i
      simp only [if_pos rfl,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one]
      have hh := hMb u 0
      simp only [iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] at hh
      exact (abs_sub _ _).trans (by norm_num; linarith)
    · rw [if_neg hi,sub_zero]
      exact (hMb u i).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hpow : ContDiffAt ℝ m (fun y : ℝ => W*y^β) x :=
    (contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hx.ne'))
  have hp (i : ℕ) : |iteratedDeriv i (fun y : ℝ => W*y^β) x| ≤ P i*x^(β-i) := by
    rw [iteratedDeriv_const_mul_field,
      D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos β i hx]
    rw [abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hx _)]
    dsimp [P]
    exact le_of_eq (by ring)
  have hprod (u : Bool) :
      |iteratedDeriv m (fun y => (W*y^β)*(M u y-1/2)) x| ≤ C*x^(β-m) := by
    simpa only [add_zero] using product_jet_bound (p := β) (q := 0) hx hpow
      (((hM u).sub contDiffAt_const).of_le
        (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) P (fun i => Q i+1) hP
      (fun i => by have := hQ i; linarith) (fun i _ => hp i)
      (fun i _ => by simpa only [zero_sub] using hcenter u i)
  have hl : (fun y => publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t y-1/2) =
      (fun y => (W*y^β)*(M false y-1/2)) := by
    ext y
    simp only [publicLower,M,F,Bool.false_eq_true,ite_false]
    ring
  have hu : (fun y => publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t y-1/2) =
      (fun y => (-1 : ℝ)*((W*y^β)*(M true y-1/2))) := by
    ext y
    simp only [publicUpper,M,F,ite_true]
    ring
  rw [hl,hu,iteratedDeriv_const_mul_field,abs_mul,abs_neg,abs_one,one_mul]
  constructor <;> apply (hprod _).trans <;>
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)


private lemma coordinate_tendsto_zero {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b) :
    Tendsto (scaleCoordinate X b) (𝓝[≠] (0 : ℝ)) atTop := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have h : Tendsto (fun x : ℝ => Real.log X - Real.log x) (𝓝[≠] (0 : ℝ)) atTop := by
    simpa only [sub_eq_add_neg,Function.comp_def] using tendsto_atTop_add_const_left _ (Real.log X)
      (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  have hh := h.const_mul_atTop (div_pos (by norm_num : (0 : ℝ) < 2) (Real.log_pos hbR))
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  dsimp [scaleCoordinate]
  rw [Real.log_div hX.ne' hx0]
  ring

private lemma public_zero_germ (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D X W β : ℝ) (hX : 0 < X) (hb : 1 < b) (hβ : 0 < β) (k t : ℕ) :
    publicLower φ η a d r ρ θ b N D X W β k t =ᶠ[𝓝 0] (fun x => (1-W*x^β)/2) ∧
    publicUpper φ η a d r ρ θ b N D X W β k t =ᶠ[𝓝 0] (fun x => (1+W*x^β)/2) := by
  have hz := (coordinate_tendsto_zero hX hb).eventually (eventually_gt_atTop ((k : ℝ)+1))
  have hz' := eventually_nhdsWithin_iff.mp hz
  have hboth : ∀ᶠ x : ℝ in 𝓝 0,
      publicLower φ η a d r ρ θ b N D X W β k t x = (1-W*x^β)/2 ∧
      publicUpper φ η a d r ρ θ b N D X W β k t x = (1+W*x^β)/2 := by
    filter_upwards [hz'] with x hx
    by_cases hx0 : x = 0
    · subst x
      simp [publicLower,publicUpper,Real.zero_rpow hβ.ne']
    have hw (j : ℕ) (hj : j ∈ range (k+1)) : scaleWeight X b j x = 0 := by
      have hjk : (j : ℝ) ≤ k := by exact_mod_cast (show j ≤ k by simpa using Nat.le_of_lt_succ (mem_range.mp hj))
      have hz := hx hx0
      exact (show scaleBump (scaleCoordinate X b x-j) / scaleDenominator (scaleCoordinate X b x) = 0 by
        rw [bump_zero (Or.inr (by linarith)),zero_div])
    have hs (F : ℕ → ℝ) : ∑ j ∈ range (k+1), scaleWeight X b j x*F j = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [hw j hj,zero_mul]
    simp only [publicLower,publicUpper,hs,mul_zero,add_zero,sub_zero,and_self]
  exact ⟨hboth.mono (fun _ h => h.1),hboth.mono (fun _ h => h.2)⟩

private lemma public_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ : ℝ) {b N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (D X W β : ℝ) (hX : 0 < X) (k t : ℕ) {x : ℝ} (hx : 0 < x) (hxx : x ≤ X) :
    ContDiffAt ℝ ∞ (publicLower φ η a d r ρ θ b N D X W β k t) x ∧
    ContDiffAt ℝ ∞ (publicUpper φ η a d r ρ θ b N D X W β k t) x := by
  have hpow : ContDiffAt ℝ ∞ (fun y : ℝ => W*y^β) x :=
    contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hx.ne')
  have hr (j : ℕ) := Complex.reCLM.contDiff.contDiffAt.comp x
    (coefficient_smooth (by positivity : 0 < N*b^j) (by omega : 0 < b) hφ η a d
      r (k-j) ((N*b^j)*b^(k-j)+r) t hx)
  constructor
  · exact ((contDiffAt_const.sub hpow).div_const 2).add (hpow.mul
      (ContDiffAt.sum (fun j _ => (weight_smooth hX hx hxx hb j).mul ((hr j).sub contDiffAt_const))))
  · exact ((contDiffAt_const.add hpow).div_const 2).sub (hpow.mul
      (ContDiffAt.sum (fun j _ => (weight_smooth hX hx hxx hb j).mul
        (contDiffAt_const.sub ((hr j).add contDiffAt_const)))))

private lemma public_closed_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ : ℝ) {b N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (D X W β : ℝ) (hX : 0 < X) (k t n : ℕ) (hβ : (n : ℝ) < β) :
    (∀ x ∈ Set.Icc 0 X, ContDiffAt ℝ n (publicLower φ η a d r ρ θ b N D X W β k t) x) ∧
    (∀ x ∈ Set.Icc 0 X, ContDiffAt ℝ n (publicUpper φ η a d r ρ θ b N D X W β k t) x) := by
  have hβ0 : 0 < β := lt_of_le_of_lt (Nat.cast_nonneg n) hβ
  have hz := public_zero_germ φ η a d r ρ θ b N D X W β hX hb hβ0 k t
  have hp : ContDiffAt ℝ n (fun y : ℝ => W*y^β) 0 :=
    contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_le hβ.le)
  constructor <;> intro x hx
  · rcases eq_or_lt_of_le hx.1 with he | he
    · subst x
      exact ContDiffAt.congr_of_eventuallyEq ((contDiffAt_const.sub hp).div_const 2) hz.1
    · exact ((public_smooth hφ η a d r ρ θ hb hN D X W β hX k t he hx.2).1).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  · rcases eq_or_lt_of_le hx.1 with he | he
    · subst x
      exact ContDiffAt.congr_of_eventuallyEq ((contDiffAt_const.add hp).div_const 2) hz.2
    · exact ((public_smooth hφ η a d r ρ θ hb hN D X W β hX k t he hx.2).2).of_le
        (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))


/-- The actual public arrays extend through zero with vanishing centered jets,
and one highest-order Hölder constant works for every stage and coefficient.
The polynomial approximation order `r` and parameter order `n` are distinct. -/
theorem reference_public_closed_holder {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 < β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ)
    (n : ℕ) (hn : (n : ℝ) < β) (hn1 : β < (n : ℝ)+1) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ X : ℝ, 0 < X → X ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ RingEnvelopes χ T β a d r ρ θ b N D X ∧ ∀ W : ℝ,
      ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∃ H : ℝ≥0,
      ∀ k t : ℕ, t ≤ N*b^k+r → ∀ u : Bool,
      let f := if u then publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t
        else publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t
      ContDiffOn ℝ n f (Set.Icc 0 X) ∧
      (∀ m ≤ n, iteratedDeriv m (fun x => f x-1/2) 0 = 0) ∧
      (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X,
        |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m)) ∧
      (∀ m x, 0 < x → x ≤ X →
        |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m)) ∧
      HolderOnWith H ⟨β-n,by linarith⟩
        (iteratedDeriv n (fun x => f x-1/2)) (Set.Icc 0 X) := by
  obtain ⟨B,hB,hb⟩ := reference_public_weighted_jets hχ hcχ hT hβ.le hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ
  refine ⟨B,hB,?_⟩
  intro b hBb X hX hX1
  obtain ⟨D,hD,N,hN,hring,hjets⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,hring,?_⟩
  intro W
  choose C hC hCb using hjets W
  let H : ℝ≥0 := ⟨max (C (n+1)) (C n*(1+2^(β-n))),
    (hC (n+1)).le.trans (le_max_left _ _)⟩
  refine ⟨C,hC,H,?_⟩
  intro k t ht u
  dsimp only
  let f := if u then publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t
    else publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β k t
  have hb1 : 1 < b := by omega
  have hN0 : 0 < N := by omega
  have hφ := cutoff_smooth hχ (fun y hy => (hsχ hy).1) β
  have hc : ∀ x ∈ Set.Icc 0 X, ContDiffAt ℝ n f x := by
    have hh := public_closed_smooth hφ (2/(5*T^β)) a d r ρ θ hb1 hN0 D X W β hX k t n hn
    cases u
    · exact hh.1
    · exact hh.2
  have hs : ∀ x, 0 < x → x ≤ X → ContDiffAt ℝ ∞ f x := by
    intro x hx hxx
    have hh := public_smooth hφ (2/(5*T^β)) a d r ρ θ hb1 hN0 D X W β hX k t hx hxx
    cases u
    · exact hh.1
    · exact hh.2
  have he : ∀ m x, 0 < x → x ≤ X →
      |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m) := by
    intro m x hx hxx
    have hh := hCb m k t ht x hx hxx
    cases u
    · exact hh.1
    · exact hh.2
  have hh := closed_jets_holder hX hn hn1 C hC
    (fun x hx => (hc x hx).sub contDiffAt_const)
    (fun x hx hxx => (hs x hx hxx).sub contDiffAt_const) he
  exact ⟨fun x hx => (hc x hx).contDiffWithinAt,hh.2.1,hh.2.2.1,he,hh.2.2.2⟩


private lemma public_width_formula (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D X W β : ℝ) (k t : ℕ) (x : ℝ) :
    publicUpper φ η a d r ρ θ b N D X W β k t x-
      publicLower φ η a d r ρ θ b N D X W β k t x =
    W*x^β*(1-(∑ j ∈ range (k+1), scaleWeight X b j x)+
      ∑ j ∈ range (k+1), scaleWeight X b j x*
        (2*D*(ringScale X b j)^(-ρ)*
          HNPCorrectionLiftAdvantage.lift (N*b^k+r) (N*b^k) t
            (HNPCorrectionLiftAdvantage.correction ρ θ (N*b^k)))) := by
  have he (j : ℕ) (hj : j ∈ range (k+1)) :
      (N*b^j)*b^(k-j) = N*b^k := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le (by have := mem_range.mp hj; omega)]
  let low (j : ℕ) := ringLower (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ))
    (fun q => (reference φ η a d x q : ℂ)) (k-j) t
  let upp (j : ℕ) := ringUpper (N*b^j) b r ρ θ (D*(ringScale X b j)^(-ρ))
    (fun q => (reference φ η a d x q : ℂ)) (k-j) t
  have hgap (j : ℕ) (hj : j ∈ range (k+1)) : upp j-low j =
      2*D*(ringScale X b j)^(-ρ)*HNPCorrectionLiftAdvantage.lift
        (N*b^k+r) (N*b^k) t (HNPCorrectionLiftAdvantage.correction ρ θ (N*b^k)) := by
    dsimp [upp,low,ringUpper,ringLower]
    rw [he j hj]
    ring
  change (1+W*x^β)/2-W*x^β*(∑ j ∈ range (k+1), scaleWeight X b j x*(1-upp j))-
    ((1-W*x^β)/2+W*x^β*(∑ j ∈ range (k+1), scaleWeight X b j x*low j)) = _
  rw [← sum_congr rfl (fun j hj => congrArg (fun z => scaleWeight X b j x*z) (hgap j hj))]
  simp only [mul_sub,mul_one,sum_sub_distrib]
  ring

private lemma public_width_endpoint_scale (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    {b N : ℕ} (hb : 1 < b) (hN : 2 ≤ N)
    (D X W β : ℝ) (hD : 0 < D) (hX : 0 < X) (hW : 0 < W)
    (hβ : 0 < β) (hρ : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k t : ℕ, t ≤ N*b^k+r → ∀ x ∈ Set.Icc 0 X,
      c*x^β*(max 1 (((N*b^k : ℕ) : ℝ)*x))^(-ρ) ≤
        publicUpper φ η a d r ρ θ b N D X W β k t x-
          publicLower φ η a d r ρ θ b N D X W β k t x := by
  have hb0 : 0 < b := by omega
  have hN0 : 0 < N := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  let K := 2*D*θ*(Real.sqrt b)^(-ρ)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨V,hV,hVb⟩ := weight_jets hX hb 0
  refine ⟨W*min 1 K,mul_pos hW (lt_min zero_lt_one hK),?_⟩
  intro k t ht x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst x
    simp [publicUpper,publicLower,Real.zero_rpow hβ.ne']
  let n := N*b^k
  let ν := (max 1 ((n : ℝ)*x))^(-ρ)
  let A := ∑ j ∈ range (k+1), scaleWeight X b j x
  let H := HNPCorrectionLiftAdvantage.lift (n+r) n t
    (HNPCorrectionLiftAdvantage.correction ρ θ n)
  let G (j : ℕ) := 2*D*(ringScale X b j)^(-ρ)*H
  have hn : 2 ≤ n := hN.trans (Nat.le_mul_of_pos_right N (pow_pos hb0 k))
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH : θ*(n : ℝ)^(-ρ) ≤ H := by
    have hh := HNPCorrectionLiftAdvantage.correction_lift_lower (θ := θ)
      (show n ≤ n+r by omega) ht hn hρ
    have hp : 0 ≤ (((t : ℝ)/(n+r)*(1-(t : ℝ)/(n+r)))/(2*n))^(ρ/2) := by
      apply Real.rpow_nonneg
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by positivity)
      apply sub_nonneg.mpr
      exact (div_le_one (by positivity)).mpr (by exact_mod_cast ht)
    push_cast at hh
    have hs := (le_add_of_nonneg_right hp).trans hh
    rw [Real.rpow_neg hnR.le,← div_eq_mul_inv]
    exact hs
  have hv := weight_mass hx0 hx.2 hb k
  have hA0 : 0 ≤ A := sum_nonneg (fun j _ => hv.1 j)
  have hA1 : A ≤ 1 := hv.2
  have hν0 : 0 ≤ ν := by dsimp [ν]; positivity
  have hν1 : ν ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith)
  have hν2 : ν ≤ ((n : ℝ)*x)^(-ρ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hnR hx0) (le_max_right _ _) (by linarith)
  have hfloor1 : min 1 K*ν ≤ 1 :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hν0).trans (by simpa using hν1)
  have hfloor2 : min 1 K*ν ≤ K*((n : ℝ)*x)^(-ρ) :=
    mul_le_mul (min_le_right _ _) hν2 hν0 hK.le
  have hG (j : ℕ) (hj : scaleWeight X b j x ≠ 0) : min 1 K*ν ≤ G j := by
    have hz : |scaleCoordinate X b x-j| < 1 := by
      by_contra h
      exact hj (by simpa only [iteratedDeriv_zero] using (hVb j x hx0 hx.2).2 (le_of_not_gt h))
    have hs := Real.sqrt_pos.mpr hbR
    have hsj : 0 < ringScale X b j := by dsimp [ringScale]; positivity
    have hupper : ringScale X b j ≤ x*Real.sqrt b :=
      (div_le_iff₀ hs).mp (jet_ring_scale hX hx0 hb hz).1
    have hsp := Real.rpow_le_rpow_of_nonpos hsj hupper (by linarith : -ρ ≤ 0)
    apply hfloor2.trans
    calc
      _ = (2*D*(x*Real.sqrt b)^(-ρ))*(θ*(n : ℝ)^(-ρ)) := by
        dsimp [K]
        rw [Real.mul_rpow hnR.le hx0.le,Real.mul_rpow hx0.le hs.le]
        ring
      _ ≤ (2*D*(ringScale X b j)^(-ρ))*(θ*(n : ℝ)^(-ρ)) := by gcongr
      _ ≤ G j := mul_le_mul_of_nonneg_left hH (by dsimp [ringScale]; positivity)
  have hsum : (min 1 K*ν)*A ≤ ∑ j ∈ range (k+1), scaleWeight X b j x*G j := by
    rw [mul_comm _ A]
    dsimp [A]
    rw [sum_mul]
    apply sum_le_sum
    intro j _
    by_cases hj : scaleWeight X b j x = 0
    · rw [hj,zero_mul,zero_mul]
    · exact mul_le_mul_of_nonneg_left (hG j hj) (hv.1 j)
  have htotal : min 1 K*ν ≤ 1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j := by
    have hh := mul_le_mul_of_nonneg_right hfloor1 (sub_nonneg.mpr hA1)
    nlinarith
  rw [public_width_formula]
  change (W*min 1 K)*x^β*ν ≤ W*x^β*(1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j)
  calc
    _ = W*x^β*(min 1 K*ν) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by positivity)

/-- Every actual width jet has the common minimum world scale. The fine-world
proof uses a neighborhood identity for the unstarted tail, and keeps the
original elevated correction coefficients. -/
theorem public_width_jets_min_scale (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    {b N : ℕ} (hb : 1 < b) (hN : 0 < N) (hNr : r ≤ N)
    (D X W β : ℝ) (hD : 0 ≤ D) (hX : 0 < X)
    (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k t : ℕ, t ≤ N*b^k+r → ∀ x : ℝ, 0 < x → x ≤ X →
      |iteratedDeriv m (fun y => publicUpper φ η a d r ρ θ b N D X W β k t y-
        publicLower φ η a d r ρ θ b N D X W β k t y) x| ≤
          C*x^(β-m)*(max 1 (((N*b^k : ℕ) : ℝ)*x^2))^(-ρ/2) := by
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  let K0 := 2*D*(θ+1)*(N : ℝ)^(-ρ/2)*X^(-ρ)
  let K1 := D*(Real.sqrt b)^ρ
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  obtain ⟨Q,hQ,hQb⟩ := power_mixture_jet_bound hX hb β 0 (K0+1) (by positivity) m
  obtain ⟨R,hR,hRb⟩ := power_mixture_jet_bound hX hb β (-ρ) K1 hK1 m
  let P := |∏ j ∈ range m, (β-(j : ℝ))|
  let A := |W| *(P+Q)
  let B := 2*|W| *(θ+1)*R
  let M := max 1 ((N : ℝ)*X^2)
  let C := max (A*M^(ρ/2)) B
  have hA : 0 ≤ A := by dsimp [A,P]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := hB.trans (le_max_right _ _)
  refine ⟨C+1,by positivity,?_⟩
  intro k t ht x hx hxx
  let n := N*b^k
  let H := HNPCorrectionLiftAdvantage.lift (n+r) n t
    (HNPCorrectionLiftAdvantage.correction ρ θ n)
  let G (j : ℕ) := 2*D*(ringScale X b j)^(-ρ)*H
  let f (y : ℝ) := publicUpper φ η a d r ρ θ b N D X W β k t y-
    publicLower φ η a d r ρ θ b N D X W β k t y
  have hn : 0 < n := by dsimp [n]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr : r ≤ n := hNr.trans (Nat.le_mul_of_pos_right N (pow_pos hb0 k))
  have hH0 : 0 ≤ H := by
    unfold H HNPCorrectionLiftAdvantage.lift HNPCorrectionLiftAdvantage.correction
    exact sum_nonneg (fun j _ => mul_nonneg (HNPCorrectionLiftAdvantage.weight_nonneg _ _ _ _)
      (add_nonneg (div_nonneg hθ (Real.rpow_pos_of_pos hnR _).le)
        (Real.rpow_nonneg (HNPCorrectionLiftAdvantage.sample_nonneg _ _) _)))
  have hH : H ≤ (θ+1)*(n : ℝ)^(-ρ/2) :=
    HNPCorrectionLiftAdvantage.correction_uniform_bound hn hnr ht hρ hθ
  have hG0 (j : ℕ) : 0 ≤ G j := by dsimp [G,ringScale]; positivity
  have hGc (j : ℕ) (hj : j ∈ range (k+1)) : G j ≤ K0 := by
    have hjk : j ≤ k := by have := mem_range.mp hj; omega
    have hnj : 0 < N*b^j := by positivity
    have hnjR : (0 : ℝ) < ((N*b^j : ℕ) : ℝ) := by exact_mod_cast hnj
    have hle : ((N*b^j : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left N (Nat.pow_le_pow_right hb0 hjk)
    have hp := Real.rpow_le_rpow_of_nonpos hnjR hle (by linarith : -ρ/2 ≤ 0)
    calc
      _ ≤ (2*D*(ringScale X b j)^(-ρ))*((θ+1)*(n : ℝ)^(-ρ/2)) :=
        mul_le_mul_of_nonneg_left hH (by dsimp [ringScale]; positivity)
      _ ≤ 2*D*(θ+1)*(ringScale X b j)^(-ρ)*((N*b^j : ℕ) : ℝ)^(-ρ/2) := by
        calc
          _ = (2*D*(θ+1)*(ringScale X b j)^(-ρ))*(n : ℝ)^(-ρ/2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hp (by dsimp [ringScale]; positivity)
      _ = K0 := by
        calc
          _ = (2*D*(θ+1))*(((N*b^j : ℕ) : ℝ)^(-ρ/2)*(ringScale X b j)^(-ρ)) := by ring
          _ = _ := by rw [ring_scale_cancel hN hb0 hX]; dsimp [K0]; ring
  have hformula : f = fun y => W*(y^β + y^β*∑ j ∈ range (k+1), scaleWeight X b j y*(G j-1)) := by
    ext y
    dsimp only [f]
    rw [public_width_formula]
    dsimp [G,H,n]
    simp only [mul_sub,mul_one,sum_sub_distrib]
    ring
  have hcoarse : |iteratedDeriv m f x| ≤ A*x^(β-m) := by
    have hs : ContDiffAt ℝ m (fun y => y^β*∑ j ∈ range (k+1), scaleWeight X b j y*(G j-1)) x :=
      (Real.contDiffAt_rpow_const_of_ne hx.ne').mul
        (ContDiffAt.sum (fun j _ => ((weight_smooth hX hx hxx hb j).of_le
          (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).mul contDiffAt_const))
    have hh := hQb (range (k+1)) (fun j => G j-1) x hx hxx (fun j hj _ => by
      rw [Real.rpow_zero,mul_one]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hG0 j)]; norm_num; linarith [hGc j hj]))
    rw [hformula,iteratedDeriv_const_mul_field,iteratedDeriv_fun_add
      (Real.contDiffAt_rpow_const_of_ne hx.ne') hs,abs_mul]
    have hp : |iteratedDeriv m (fun y : ℝ => y^β) x| = P*x^(β-m) := by
      rw [D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos β m hx,
        abs_mul,abs_of_pos (Real.rpow_pos_of_pos hx _)]
    apply (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (le_of_eq hp) hh)) (abs_nonneg W)).trans_eq
    dsimp [A]
    ring
  have hfine (hscale : M < (n : ℝ)*x^2) :
      |iteratedDeriv m f x| ≤ B*x^(β-m)*((n : ℝ)*x^2)^(-ρ/2) := by
    have hmass := full_mass_germ_of_scale hX hx hxx hb hN
      ((le_max_right _ _).trans_lt hscale)
    have he : f =ᶠ[𝓝 x] fun y => (2*W*H)*(y^β*∑ j ∈ range (k+1),
        scaleWeight X b j y*(D*(ringScale X b j)^(-ρ))) := by
      filter_upwards [hmass] with y hy
      dsimp [f]
      rw [public_width_formula,hy,sub_self,zero_add]
      change W*y^β*(∑ j ∈ range (k+1), scaleWeight X b j y*(2*D*(ringScale X b j)^(-ρ)*H)) = _
      simp only [mul_sum,sum_mul]
      apply sum_congr rfl
      intro j _
      ring
    have hh := hRb (range (k+1)) (fun j => D*(ringScale X b j)^(-ρ)) x hx hxx ?_
    · rw [he.iteratedDeriv_eq m,iteratedDeriv_const_mul_field,abs_mul]
      have hab : |2*W*H| = 2*|W| *H := by
        rw [abs_mul,abs_mul,abs_of_nonneg hH0]; norm_num
      rw [hab]
      calc
        _ ≤ (2*|W| *((θ+1)*(n : ℝ)^(-ρ/2)))*(R*x^(β+-ρ-m)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hh (abs_nonneg _) (by positivity)
        _ = B*x^(β-m)*((n : ℝ)*x^2)^(-ρ/2) := by
          rw [Real.mul_rpow hnR.le (sq_nonneg _),← Real.rpow_natCast x 2,← Real.rpow_mul hx.le]
          norm_num only [Nat.cast_ofNat]
          rw [show (2 : ℝ)*(-ρ/2) = -ρ by ring]
          rw [show β+-ρ-(m : ℝ) = (β-m)+-ρ by ring,Real.rpow_add hx]
          dsimp [B]
          ring
    · intro j _ hz
      have hs := Real.sqrt_pos.mpr hbR
      have hh := Real.rpow_le_rpow_of_nonpos (div_pos hx hs) (jet_ring_scale hX hx hb hz).2
        (neg_nonpos.mpr hρ)
      rw [Real.div_rpow hx.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul] at hh
      rw [abs_of_nonneg (by dsimp [ringScale]; positivity : 0 ≤ D*(ringScale X b j)^(-ρ))]
      exact (mul_le_mul_of_nonneg_left hh hD).trans_eq (by dsimp [K1]; ring)
  have hh := min_scale_combine (by positivity : 0 ≤ x^(β-m)) (le_max_left _ _)
    hA hρ hcoarse hfine
  exact hh.trans (by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))

/-- The actual coefficient width has a uniform world-scale upper bound,
including the unstarted tail. The endpoint correction is retained. -/
theorem public_width_min_scale (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    {b N : ℕ} (hb : 1 < b) (hN : 0 < N) (hNr : r ≤ N)
    (D X W β : ℝ) (hD : 0 ≤ D) (hX : 0 < X) (hW : 0 ≤ W)
    (hβ : 0 < β) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k t : ℕ, t ≤ N*b^k+r → ∀ x ∈ Set.Icc 0 X,
      publicUpper φ η a d r ρ θ b N D X W β k t x-
        publicLower φ η a d r ρ θ b N D X W β k t x ≤
          C*x^β*(max 1 (((N*b^k : ℕ) : ℝ)*x^2))^(-ρ/2) := by
  obtain ⟨C,hC,hbnd⟩ := public_width_jets_min_scale φ η a d r ρ θ hb hN hNr
    D X W β hD hX hρ hθ 0
  refine ⟨C,hC,?_⟩
  intro k t ht x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst x
    simp [publicUpper,publicLower,Real.zero_rpow hβ.ne']
  · exact (le_abs_self _).trans (by simpa using hbnd k t ht x hxpos hx.2)

private lemma public_width_closed {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ : ℝ) {b N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (hNr : r ≤ N) (D X W β : ℝ) (hD : 0 ≤ D) (hX : 0 < X)
    (hρβ : β ≤ ρ) (hθ : 0 < θ) (n : ℕ) (hn : (n : ℝ) < β)
    (hn1 : β < (n : ℝ)+1) :
    ∃ K : ℕ → ℝ, (∀ m, 0 < K m) ∧ ∃ H : ℝ≥0,
    ∀ k t : ℕ, t ≤ N*b^k+r →
    let g := fun y => publicUpper φ η a d r ρ θ b N D X W β k t y-
      publicLower φ η a d r ρ θ b N D X W β k t y
    ContDiffOn ℝ n g (Set.Icc 0 X) ∧
    (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
    (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤
      K m*x^(β-m)*(max 1 (((N*b^k : ℕ) : ℝ)*x^2))^(-ρ/2)) ∧
    (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X, |iteratedDeriv m g x| ≤
      K m*((N*b^k : ℕ) : ℝ)^(((m : ℝ)-β)/2)) ∧
    HolderOnWith H ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X) := by
  have hβ : 0 < β := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  have hρ : 0 ≤ ρ := hβ.le.trans hρβ
  choose K hK hKb using public_width_jets_min_scale φ η a d r ρ θ hb hN hNr D X W β hD hX hρ hθ.le
  let H : ℝ≥0 := ⟨max (K (n+1)) (K n*(1+2^(β-n))),
    (hK (n+1)).le.trans (le_max_left _ _)⟩
  refine ⟨K,hK,H,?_⟩
  intro k t ht
  dsimp only
  let g := fun y => publicUpper φ η a d r ρ θ b N D X W β k t y-
    publicLower φ η a d r ρ θ b N D X W β k t y
  have hc := public_closed_smooth hφ η a d r ρ θ hb hN D X W β hX k t n hn
  have hs (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :=
    public_smooth hφ η a d r ρ θ hb hN D X W β hX k t hx hxx
  have he (m : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :
      |iteratedDeriv m g x| ≤ K m*x^(β-m) := by
    apply (hKb m k t ht x hx hxx).trans
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith : -ρ/2 ≤ 0))
      (mul_nonneg (hK m).le (Real.rpow_pos_of_pos hx _).le)).trans_eq (mul_one _)
  have hh := closed_jets_holder hX hn hn1 K hK
    (fun x hx => (hc.2 x hx).sub (hc.1 x hx))
    (fun x hx hxx => (hs x hx hxx).2.sub (hs x hx hxx).1) he
  refine ⟨hh.1,hh.2.1,fun m x hx hxx => hKb m k t ht x hx hxx,?_,hh.2.2.2⟩
  intro m hm x hx
  rcases eq_or_lt_of_le hx.1 with heq | hxpos
  · subst x
    rw [hh.2.1 m hm,abs_zero]
    have hNk : (0 : ℝ) < ((N*b^k : ℕ) : ℝ) := by
      have hb0 : 0 < b := by omega
      exact_mod_cast (show 0 < N*b^k by positivity)
    exact mul_nonneg (hK m).le (Real.rpow_pos_of_pos hNk _).le
  · have hp : 0 < β-(m : ℝ) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hm
      linarith
    have hNk : (0 : ℝ) < ((N*b^k : ℕ) : ℝ) := by
      have hb0 : 0 < b := by omega
      exact_mod_cast (show 0 < N*b^k by positivity)
    apply (hKb m k t ht x hxpos hx.2).trans
    have hh := mul_le_mul_of_nonneg_left
      (min_scale_global (ρ := ρ) hNk hx.1 hp (by have := Nat.cast_nonneg (α := ℝ) m; linarith)) (hK m).le
    rw [show -(β-(m : ℝ))/2 = ((m : ℝ)-β)/2 by ring] at hh
    simpa only [mul_assoc] using hh

private lemma public_elevated_width_closed {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ : ℝ) {b N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (hNr : r ≤ N) (D X W β : ℝ) (hD : 0 ≤ D) (hX : 0 < X)
    (hρβ : β ≤ ρ) (hθ : 0 < θ) (n : ℕ) (hn : (n : ℝ) < β)
    (hn1 : β < (n : ℝ)+1) :
    ∃ K : ℕ → ℝ, (∀ m, 0 < K m) ∧ ∃ H : ℝ≥0,
    ∀ k t : ℕ, t ≤ N*b^(k+1)+r →
    let g := fun y => HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
      (fun j => publicUpper φ η a d r ρ θ b N D X W β k j y-
        publicLower φ η a d r ρ θ b N D X W β k j y)
    ContDiffOn ℝ n g (Set.Icc 0 X) ∧
    (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
    (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤
      K m*x^(β-m)*(max 1 (((N*b^(k+1) : ℕ) : ℝ)*x^2))^(-ρ/2)) ∧
    (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X, |iteratedDeriv m g x| ≤
      K m*((N*b^(k+1) : ℕ) : ℝ)^(((m : ℝ)-β)/2)) ∧
    HolderOnWith H ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X) := by
  have hβ : 0 < β := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  have hρ : 0 ≤ ρ := hβ.le.trans hρβ
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  choose A hA hAb using public_width_jets_min_scale φ η a d r ρ θ hb hN hNr D X W β hD hX hρ hθ.le
  let K (m : ℕ) := A m*(b : ℝ)^(ρ/2)
  have hK (m : ℕ) : 0 < K m := mul_pos (hA m) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hbR) _)
  let H : ℝ≥0 := ⟨max (K (n+1)) (K n*(1+2^(β-n))),
    (hK (n+1)).le.trans (le_max_left _ _)⟩
  refine ⟨K,hK,H,?_⟩
  intro k t ht
  dsimp only
  let f (j : ℕ) (y : ℝ) := publicUpper φ η a d r ρ θ b N D X W β k j y-
    publicLower φ η a d r ρ θ b N D X W β k j y
  let g (y : ℝ) := HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun j => f j y)
  have hdegree : N*b^k+r ≤ N*b^(k+1)+r :=
    Nat.add_le_add_right (Nat.mul_le_mul_left N (Nat.pow_le_pow_right hb0 (by omega))) r
  have hc (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 X) : ContDiffAt ℝ n (f j) x := by
    have hh := public_closed_smooth hφ η a d r ρ θ hb hN D X W β hX k j n hn
    exact (hh.2 x hx).sub (hh.1 x hx)
  have hs (j : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) : ContDiffAt ℝ ∞ (f j) x := by
    have hh := public_smooth hφ η a d r ρ θ hb hN D X W β hX k j hx hxx
    exact hh.2.sub hh.1
  have hgc (x : ℝ) (hx : x ∈ Set.Icc 0 X) : ContDiffAt ℝ n g x :=
    ContDiffAt.sum (fun j _ => contDiffAt_const.mul (hc j x hx))
  have hgs (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) : ContDiffAt ℝ ∞ g x :=
    ContDiffAt.sum (fun j _ => contDiffAt_const.mul (hs j x hx hxx))
  have he (m : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :
      |iteratedDeriv m g x| ≤ K m*x^(β-m)*(max 1 (((N*b^(k+1) : ℕ) : ℝ)*x^2))^(-ρ/2) := by
    have hh := lift_jet_bound hdegree ht f (fun j => (hs j x hx hxx).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) (fun j hj => hAb m k j hj x hx hxx)
    apply hh.trans
    have hp := min_scale_step hbR (by positivity : 0 ≤ ((N*b^k : ℕ) : ℝ)*x^2) hρ
    have heq : (b : ℝ)*(((N*b^k : ℕ) : ℝ)*x^2) = ((N*b^(k+1) : ℕ) : ℝ)*x^2 := by
      push_cast
      rw [pow_succ]
      ring
    rw [heq] at hp
    exact (mul_le_mul_of_nonneg_left hp
      (mul_nonneg (hA m).le (Real.rpow_pos_of_pos hx _).le)).trans_eq (by dsimp [K]; ring)
  have hbnd (m : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :
      |iteratedDeriv m g x| ≤ K m*x^(β-m) := by
    apply (he m x hx hxx).trans
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by linarith : -ρ/2 ≤ 0))
      (mul_nonneg (hK m).le (Real.rpow_pos_of_pos hx _).le)).trans_eq (mul_one _)
  have hh := closed_jets_holder hX hn hn1 K hK hgc hgs hbnd
  refine ⟨hh.1,hh.2.1,he,?_,hh.2.2.2⟩
  intro m hm x hx
  have hNk : (0 : ℝ) < ((N*b^(k+1) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < N*b^(k+1) by positivity)
  rcases eq_or_lt_of_le hx.1 with heq | hxpos
  · subst x
    rw [hh.2.1 m hm,abs_zero]
    exact mul_nonneg (hK m).le (Real.rpow_pos_of_pos hNk _).le
  · have hp : 0 < β-(m : ℝ) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hm
      linarith
    apply (he m x hxpos hx.2).trans
    have hs := mul_le_mul_of_nonneg_left
      (min_scale_global (ρ := ρ) hNk hx.1 hp
        (by have := Nat.cast_nonneg (α := ℝ) m; linarith)) (hK m).le
    rw [show -(β-(m : ℝ))/2 = ((m : ℝ)-β)/2 by ring] at hs
    simpa only [mul_assoc] using hs

set_option maxHeartbeats 600000 in
private lemma public_increment_closed {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ : ℝ) {b N : ℕ} (hb : 1 < b) (hN : 0 < N)
    (D X W β : ℝ) (hX : 0 < X) (n : ℕ) (hn : (n : ℝ) < β)
    (hn1 : β < (n : ℝ)+1) (C : ℕ → ℝ) (hC : ∀ m, 0 < C m)
    (hbnd : ∀ k j, j ≤ N*b^k+r → ∀ u : Bool,
      let f := if u then publicUpper φ η a d r ρ θ b N D X W β k j
        else publicLower φ η a d r ρ θ b N D X W β k j
      ∀ m x, 0 < x → x ≤ X → |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m)) :
    ∃ H : ℝ≥0, ∀ k t, t ≤ N*b^(k+1)+r → ∀ u : Bool,
      let low := publicLower φ η a d r ρ θ b N D X W β
      let upp := publicUpper φ η a d r ρ θ b N D X W β
      let g := if u then fun y => HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
          (fun j => upp k j y)-upp (k+1) t y
        else fun y => low (k+1) t y-HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
          (fun j => low k j y)
      ContDiffOn ℝ n g (Set.Icc 0 X) ∧
      (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
      (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤ (2*C m)*x^(β-m)) ∧
      HolderOnWith H ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X) := by
  let K (m : ℕ) := 2*C m
  have hK (m : ℕ) : 0 < K m := mul_pos (by norm_num) (hC m)
  let H : ℝ≥0 := ⟨max (K (n+1)) (K n*(1+2^(β-n))),
    (hK (n+1)).le.trans (le_max_left _ _)⟩
  refine ⟨H,?_⟩
  intro k t ht u
  dsimp only
  let F (stage j : ℕ) := if u then publicUpper φ η a d r ρ θ b N D X W β stage j
    else publicLower φ η a d r ρ θ b N D X W β stage j
  let f (j : ℕ) (y : ℝ) := F k j y-1/2
  let fnew (y : ℝ) := F (k+1) t y-1/2
  let L (y : ℝ) := HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun j => f j y)
  let g (y : ℝ) := (if u then (-1 : ℝ) else 1)*(fnew y-L y)
  have hd : N*b^k+r ≤ N*b^(k+1)+r :=
    Nat.add_le_add_right (Nat.mul_le_mul_left N (Nat.pow_le_pow_right (by omega : 0 < b) (by omega))) r
  have hsame : (if u then fun y => HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
      (fun j => publicUpper φ η a d r ρ θ b N D X W β k j y)-
        publicUpper φ η a d r ρ θ b N D X W β (k+1) t y
    else fun y => publicLower φ η a d r ρ θ b N D X W β (k+1) t y-
      HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
        (fun j => publicLower φ η a d r ρ θ b N D X W β k j y)) = g := by
    ext y
    dsimp [g,fnew,L,f,F]
    cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true,HNPCorrectionLiftAdvantage.lift,
      mul_sub,sum_sub_distrib,← sum_mul,HNPCorrectionLiftAdvantage.weight_sum hd ht] <;> ring
  rw [hsame]
  have hc (stage j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 X) : ContDiffAt ℝ n (F stage j) x := by
    have hh := public_closed_smooth hφ η a d r ρ θ hb hN D X W β hX stage j n hn
    cases u
    · exact hh.1 x hx
    · exact hh.2 x hx
  have hs (stage j : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) : ContDiffAt ℝ ∞ (F stage j) x := by
    have hh := public_smooth hφ η a d r ρ θ hb hN D X W β hX stage j hx hxx
    cases u
    · exact hh.1
    · exact hh.2
  have hgc (x : ℝ) (hx : x ∈ Set.Icc 0 X) : ContDiffAt ℝ n g x :=
    contDiffAt_const.mul (((hc (k+1) t x hx).sub contDiffAt_const).sub
      (ContDiffAt.sum (fun j _ => contDiffAt_const.mul ((hc k j x hx).sub contDiffAt_const))))
  have hgs (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) : ContDiffAt ℝ ∞ g x :=
    contDiffAt_const.mul (((hs (k+1) t x hx hxx).sub contDiffAt_const).sub
      (ContDiffAt.sum (fun j _ => contDiffAt_const.mul ((hs k j x hx hxx).sub contDiffAt_const))))
  have he (m : ℕ) (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :
      |iteratedDeriv m g x| ≤ K m*x^(β-m) := by
    have hsm (stage j : ℕ) : ContDiffAt ℝ m (fun y => F stage j y-1/2) x :=
      ((hs stage j x hx hxx).sub contDiffAt_const).of_le
        (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
    have hl := lift_jet_bound hd ht f (fun j => hsm k j)
      (fun j hj => hbnd k j hj u m x hx hxx)
    have hnew := hbnd (k+1) t ht u m x hx hxx
    have hLm : ContDiffAt ℝ m L x :=
      ContDiffAt.sum (fun j _ => contDiffAt_const.mul (hsm k j))
    dsimp only [g]
    rw [iteratedDeriv_const_mul_field,abs_mul,iteratedDeriv_fun_sub (hsm (k+1) t) hLm]
    have hsign : |if u then (-1 : ℝ) else 1| = 1 := by cases u <;> norm_num
    rw [hsign,one_mul]
    exact ((abs_sub _ _).trans (add_le_add hnew hl)).trans_eq (by dsimp [K]; ring)
  have hh := closed_jets_holder hX hn hn1 K hK hgc hgs he
  exact ⟨hh.1,hh.2.1,he,hh.2.2.2⟩

/-- The same original public arrays have uniformly bounded closed parameter
jets and Hölder seminorms, a coarse min-scale width upper bound, and the finer
endpoint-scale positive width lower bound. -/
theorem reference_public_regularity {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 < β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ)
    (hρβ : β ≤ ρ) (n : ℕ) (hn : (n : ℝ) < β) (hn1 : β < (n : ℝ)+1) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ X : ℝ, 0 < X → X ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ RingEnvelopes χ T β a d r ρ θ b N D X ∧ ∀ W : ℝ, 0 < W →
      ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∃ H : ℝ≥0, ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      ∃ K : ℕ → ℝ, (∀ m, 0 < K m) ∧ ∃ HΓ : ℝ≥0,
      ∃ KE : ℕ → ℝ, (∀ m, 0 < KE m) ∧ ∃ HE HI : ℝ≥0,
      let lower := publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β
      let upper := publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β
      (∀ k t : ℕ, t ≤ N*b^k+r →
      (∀ u : Bool, let f := if u then upper k t else lower k t
        ContDiffOn ℝ n f (Set.Icc 0 X) ∧
        (∀ m ≤ n, iteratedDeriv m (fun x => f x-1/2) 0 = 0) ∧
        (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X,
          |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m)) ∧
        (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m (fun y => f y-1/2) x| ≤ C m*x^(β-m)) ∧
        HolderOnWith H ⟨β-n,by linarith⟩ (iteratedDeriv n (fun x => f x-1/2)) (Set.Icc 0 X)) ∧
      (∀ x ∈ Set.Icc 0 X,
        c*x^β*(max 1 (((N*b^k : ℕ) : ℝ)*x))^(-ρ) ≤ upper k t x-lower k t x ∧
        upper k t x-lower k t x ≤ U*x^β*(max 1 (((N*b^k : ℕ) : ℝ)*x^2))^(-ρ/2) ∧
        upper k t x-lower k t x ≤ U*((N*b^k : ℕ) : ℝ)^(-β/2)) ∧
      (let g := fun y => upper k t y-lower k t y
       ContDiffOn ℝ n g (Set.Icc 0 X) ∧
       (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
       (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤
         K m*x^(β-m)*(max 1 (((N*b^k : ℕ) : ℝ)*x^2))^(-ρ/2)) ∧
       (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X, |iteratedDeriv m g x| ≤
         K m*((N*b^k : ℕ) : ℝ)^(((m : ℝ)-β)/2)) ∧
       HolderOnWith HΓ ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X))) ∧
      (∀ k t : ℕ, t ≤ N*b^(k+1)+r →
       let g := fun y => HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
         (fun j => upper k j y-lower k j y)
       ContDiffOn ℝ n g (Set.Icc 0 X) ∧
       (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
       (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤
         KE m*x^(β-m)*(max 1 (((N*b^(k+1) : ℕ) : ℝ)*x^2))^(-ρ/2)) ∧
       (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X, |iteratedDeriv m g x| ≤
         KE m*((N*b^(k+1) : ℕ) : ℝ)^(((m : ℝ)-β)/2)) ∧
       HolderOnWith HE ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X)) ∧
      (∀ k t, t ≤ N*b^(k+1)+r → ∀ u : Bool,
       let g := if u then fun y => HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
           (fun j => upper k j y)-upper (k+1) t y
         else fun y => lower (k+1) t y-HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t
           (fun j => lower k j y)
       ContDiffOn ℝ n g (Set.Icc 0 X) ∧
       (∀ m ≤ n, iteratedDeriv m g 0 = 0) ∧
       (∀ m x, 0 < x → x ≤ X → |iteratedDeriv m g x| ≤ (2*C m)*x^(β-m)) ∧
       HolderOnWith HI ⟨β-n,by linarith⟩ (iteratedDeriv n g) (Set.Icc 0 X)) := by
  obtain ⟨B,hB,hb⟩ := reference_public_closed_holder hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ n hn hn1
  refine ⟨B,hB,?_⟩
  intro b hBb X hX hX1
  obtain ⟨D,hD,N,hN,hring,h⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,hring,?_⟩
  intro W hW
  obtain ⟨C,hC,H,h⟩ := h W
  obtain ⟨U,hU,hUb⟩ := public_width_min_scale (cutoff χ β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 0 < N) (by omega : r ≤ N) D X W β hD.le hX hW.le hβ
    (by linarith) hθ.le
  obtain ⟨c,hc,hcb⟩ := public_width_endpoint_scale (cutoff χ β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 2 ≤ N) D X W β hD hX hW hβ hρ2 hθ
  obtain ⟨K,hK,HΓ,hΓ⟩ := public_width_closed
    (cutoff_smooth hχ (fun y hy => (hsχ hy).1) β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 0 < N) (by omega : r ≤ N)
    D X W β hD.le hX hρβ hθ n hn hn1
  obtain ⟨KE,hKE,HE,hE⟩ := public_elevated_width_closed
    (cutoff_smooth hχ (fun y hy => (hsχ hy).1) β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 0 < N) (by omega : r ≤ N)
    D X W β hD.le hX hρβ hθ n hn hn1
  obtain ⟨HI,hI⟩ := public_increment_closed
    (cutoff_smooth hχ (fun y hy => (hsχ hy).1) β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 0 < N) D X W β hX n hn hn1 C hC
    (fun k j hj u => (h k j hj u).2.2.2.1)
  refine ⟨C,hC,H,c,U,hc,hU,K,hK,HΓ,KE,hKE,HE,HI,?_,hE,hI⟩
  dsimp only
  intro k t ht
  refine ⟨h k t ht,?_,hΓ k t ht⟩
  intro x hx
  refine ⟨hcb k t ht x hx,hUb k t ht x hx,?_⟩
  apply (hUb k t ht x hx).trans
  have hnR : (0 : ℝ) < ((N*b^k : ℕ) : ℝ) := by
    have hN0 : 0 < N := by omega
    have hb0 : 0 < b := by omega
    exact_mod_cast (show 0 < N*b^k by positivity)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (min_scale_global hnR hx.1 hβ hρβ) hU.le

end D5.S3.Analytic.SeriesInequalities.OriginalPublicArrayRegularity

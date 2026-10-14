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

private lemma product_jet_bound {f g : ℝ → ℝ} {x p q : ℝ} {m : ℕ}
    (hx : 0 < x) (hf : ContDiffAt ℝ m f x) (hg : ContDiffAt ℝ m g x)
    (A B : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (ha : ∀ i ≤ m, |iteratedDeriv i f x| ≤ A i*x^(p-i))
    (hb : ∀ i ≤ m, |iteratedDeriv i g x| ≤ B i*x^(q-i)) :
    |iteratedDeriv m (fun y => f y*g y) x| ≤
      (∑ i ∈ range (m+1), (m.choose i : ℝ)*A i*B (m-i))*x^(p+q-m) := by
  rw [iteratedDeriv_fun_mul hf hg]
  apply (abs_sum_le_sum_abs _ _).trans
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hi' : i ≤ m := by simpa using Nat.le_of_lt_succ (mem_range.mp hi)
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  calc
    _ ≤ ((m.choose i : ℝ)*(A i*x^(p-i)))*(B (m-i)*x^(q-((m-i : ℕ) : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (ha i hi') (Nat.cast_nonneg _))
        (hb (m-i) (by omega)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (by positivity)))
    _ = ((m.choose i : ℝ)*A i*B (m-i))*x^((p-i)+(q-((m-i : ℕ) : ℝ))) := by
      rw [Real.rpow_add hx]; ring
    _ = _ := by rw [Nat.cast_sub hi']; congr 2; ring

private lemma mixture_jet_bound {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b)
    (m : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ f : ℕ → ℝ → ℝ, ∀ x : ℝ,
      0 < x → x ≤ X →
      (∀ j ∈ s, ContDiffAt ℝ m (f j) x) →
      (∀ j ∈ s, |scaleCoordinate X b x-j| < 1 → ∀ i ≤ m,
        |iteratedDeriv i (f j) x| ≤ A i*x^(-(i : ℝ))) →
      |iteratedDeriv m (fun y => ∑ j ∈ s, scaleWeight X b j y*f j y) x| ≤
        C*x^(-(m : ℝ)) := by
  choose B hB hBb using weight_jets hX hb
  let C := ∑ i ∈ range (m+1), (m.choose i : ℝ)*B i*A (m-i)
  have hC : 0 ≤ C := sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i).le) (hA _))
  refine ⟨2*C+1,by positivity,?_⟩
  intro s f x hx hxx hf hfb
  have hw (j : ℕ) : ContDiffAt ℝ m (scaleWeight X b j) x :=
    (weight_smooth hX hx hxx hb j).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_fun_sum (fun j hj => (hw j).mul (hf j hj))]
  have hbound := sum_active_bound (coordinate_nonneg hx hxx hb)
    (show 0 ≤ C*x^(-(m : ℝ)) by positivity) s
    (fun j => iteratedDeriv m (fun y => scaleWeight X b j y*f j y) x) ?_ ?_
  · exact hbound.trans (by
      calc
        2*(C*x^(-(m : ℝ))) = (2*C)*x^(-(m : ℝ)) := by ring
        _ ≤ (2*C+1)*x^(-(m : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · intro j hj hz
    simpa only [zero_sub,zero_add] using product_jet_bound (p := 0) (q := 0) hx (hw j) (hf j hj) B A
      (fun i => (hB i).le) hA (fun i _ => by simpa only [zero_sub] using (hBb i j x hx hxx).1)
      (fun i hi => by simpa only [zero_sub] using hfb j hj hz i hi)
  · intro j hj hz
    rw [iteratedDeriv_fun_mul (hw j) (hf j hj)]
    apply sum_eq_zero
    intro i _
    rw [(hBb i j x hx hxx).2 hz]
    ring

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
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ m : ℕ, ∃ A : ℝ, 0 < A ∧
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
  refine ⟨D,hD,N,hN,?_⟩
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
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ W : ℝ, ∀ m : ℕ,
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
  obtain ⟨D,hD,N,hN,hjets⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,?_⟩
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


private lemma jet_continuous {f : ℝ → ℝ} {m : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ m f x) : ContinuousAt (iteratedDeriv m f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm.continuous.continuousAt.comp
    (hf.continuousAt_iteratedFDeriv le_rfl)

private lemma jet_zero_of_weighted_bound {f : ℝ → ℝ} {m : ℕ} {X β C : ℝ}
    (hX : 0 < X) (hm : (m : ℝ) < β) (hf : ContDiffAt ℝ m f 0)
    (hb : ∀ x, 0 < x → x ≤ X → |iteratedDeriv m f x| ≤ C*x^(β-m)) :
    iteratedDeriv m f 0 = 0 := by
  have hc : Tendsto (fun x => |iteratedDeriv m f x|) (𝓝[>] 0)
      (𝓝 |iteratedDeriv m f 0|) :=
    (jet_continuous hf).abs.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun x : ℝ => C*x^(β-m)) (𝓝[>] 0) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => C*x^(β-m)) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith)))
    simpa [Real.zero_rpow (by linarith : β-(m : ℝ) ≠ 0)] using
      hh.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun x => |iteratedDeriv m f x|) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun x => abs_nonneg _)) _ hp
    filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds (Iio_mem_nhds hX) : Set.Iio X ∈ 𝓝[>] (0 : ℝ))] with x hx hxx
    exact hb x hx hxx.le
  exact abs_eq_zero.mp (tendsto_nhds_unique hc hz)

private lemma weighted_holder {f : ℝ → ℝ} {X θ A L : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hA : 0 ≤ A) (hL : 0 ≤ L) (hf0 : f 0 = 0)
    (hf : ∀ x, 0 < x → x ≤ X → DifferentiableAt ℝ f x)
    (ha : ∀ x, 0 < x → x ≤ X → |f x| ≤ A*x^θ)
    (hl : ∀ x, 0 < x → x ≤ X → |deriv f x| ≤ L*x^(θ-1)) :
    ∀ x ∈ Set.Icc 0 X, ∀ y ∈ Set.Icc 0 X,
      |f y-f x| ≤ max L (A*(1+2^θ))*|y-x|^θ := by
  let H := max L (A*(1+2^θ))
  have hHL : L ≤ H := le_max_left _ _
  have hHA : A*(1+2^θ) ≤ H := le_max_right _ _
  have hHA' : A ≤ H := by
    have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) θ
    nlinarith
  have hH : 0 ≤ H := hL.trans hHL
  have ordered : ∀ x ∈ Set.Icc 0 X, ∀ y ∈ Set.Icc 0 X, x ≤ y →
      |f y-f x| ≤ H*|y-x|^θ := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with he | he
    · subst y
      simp only [sub_self,abs_zero]
      positivity
    have hd : 0 < y-x := sub_pos.mpr he
    rw [abs_of_pos hd]
    by_cases hx0 : x = 0
    · subst x
      rw [hf0,sub_zero,sub_zero]
      exact (ha y (by linarith) hy.2).trans
        (mul_le_mul_of_nonneg_right hHA' (by positivity))
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    by_cases hnear : y ≤ 2*x
    · have hdle : y-x ≤ x := by linarith
      have hmv := (convex_Icc x y).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hf z (hxpos.trans_le hz.1) (hz.2.trans hy.2))
        (fun z hz => show ‖deriv f z‖ ≤ L*x^(θ-1) by
          rw [Real.norm_eq_abs]
          exact (hl z (hxpos.trans_le hz.1) (hz.2.trans hy.2)).trans
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hxpos hz.1 (by linarith)) hL))
        ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hd] at hmv
      have hs : x^(θ-1)*(y-x) ≤ (y-x)^θ := by
        calc
          _ ≤ (y-x)^(θ-1)*(y-x) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hd hdle (by linarith)) hd.le
          _ = (y-x)^θ := by
            conv_lhs => rhs; rw [← Real.rpow_one (y-x)]
            rw [← Real.rpow_add hd]
            congr 1
            ring
      calc
        _ ≤ L*x^(θ-1)*(y-x) := hmv
        _ = L*(x^(θ-1)*(y-x)) := by ring
        _ ≤ L*(y-x)^θ := mul_le_mul_of_nonneg_left hs hL
        _ ≤ H*(y-x)^θ := mul_le_mul_of_nonneg_right hHL (by positivity)
    · have hxle : x ≤ y-x := by linarith
      have hyle : y ≤ 2*(y-x) := by linarith
      calc
        _ ≤ |f y|+|f x| := abs_sub _ _
        _ ≤ A*y^θ+A*x^θ := add_le_add (ha y (hxpos.trans he) hy.2) (ha x hxpos hx.2)
        _ ≤ A*(2*(y-x))^θ+A*(y-x)^θ :=
          add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.1 hyle hθ.le) hA)
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hxle hθ.le) hA)
        _ = (A*(1+2^θ))*(y-x)^θ := by rw [Real.mul_rpow (by norm_num) hd.le]; ring
        _ ≤ H*(y-x)^θ := mul_le_mul_of_nonneg_right hHA (by positivity)
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact ordered x hx y hy hxy
  · simpa only [abs_sub_comm] using ordered y hy x hx hyx


private lemma closed_jets_holder {f : ℝ → ℝ} {X β : ℝ} {n : ℕ}
    (hX : 0 < X) (hn : (n : ℝ) < β) (hn1 : β < (n : ℝ)+1)
    (C : ℕ → ℝ) (hC : ∀ m, 0 < C m)
    (hclosed : ∀ x ∈ Set.Icc 0 X, ContDiffAt ℝ n f x)
    (hsmooth : ∀ x, 0 < x → x ≤ X → ContDiffAt ℝ ∞ f x)
    (hb : ∀ m x, 0 < x → x ≤ X → |iteratedDeriv m f x| ≤ C m*x^(β-m)) :
    ContDiffOn ℝ n f (Set.Icc 0 X) ∧
    (∀ m ≤ n, iteratedDeriv m f 0 = 0) ∧
    (∀ m ≤ n, ∀ x ∈ Set.Icc 0 X, |iteratedDeriv m f x| ≤ C m*x^(β-m)) ∧
    HolderOnWith ⟨max (C (n+1)) (C n*(1+2^(β-n))), (hC (n+1)).le.trans (le_max_left _ _)⟩
      ⟨β-n,by linarith⟩ (iteratedDeriv n f) (Set.Icc 0 X) := by
  have hz (m : ℕ) (hm : m ≤ n) : iteratedDeriv m f 0 = 0 := by
    apply jet_zero_of_weighted_bound hX (lt_of_le_of_lt (by exact_mod_cast hm) hn)
      ((hclosed 0 ⟨le_rfl,hX.le⟩).of_le (by exact_mod_cast hm))
    exact hb m
  refine ⟨fun x hx => (hclosed x hx).contDiffWithinAt,hz,?_,?_⟩
  · intro m hm x hx
    rcases eq_or_lt_of_le hx.1 with he | he
    · subst x
      rw [hz m hm,abs_zero]
      exact mul_nonneg (hC m).le (Real.rpow_nonneg (by norm_num) _)
    · exact hb m x he hx.2
  have hd (x : ℝ) (hx : 0 < x) (hxx : x ≤ X) :
      DifferentiableAt ℝ (iteratedDeriv n f) x := by
    have hh : ContDiffAt ℝ 1 (iteratedDeriv n f) x := by
      rw [iteratedDeriv_eq_equiv_comp]
      exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin n) ℝ).symm.contDiff.contDiffAt.comp x
        ((hsmooth x hx hxx).iteratedFDeriv_right
          (by exact_mod_cast (le_top : (1+(n : ℕ∞)) ≤ ⊤)))
    exact hh.differentiableAt one_ne_zero
  have hh := weighted_holder (f := iteratedDeriv n f) (θ := β-n)
    (by linarith) (by linarith) (hC n).le (hC (n+1)).le (hz n le_rfl) hd (hb n) (fun x hx hxx => ?_)
  · let K : ℝ≥0 := ⟨max (C (n+1)) (C n*(1+2^(β-n))),
      (hC (n+1)).le.trans (le_max_left _ _)⟩
    change HolderOnWith K ⟨β-n,by linarith⟩ (iteratedDeriv n f) (Set.Icc 0 X)
    intro x hx y hy
    rw [edist_dist,edist_dist]
    change ENNReal.ofReal (dist (iteratedDeriv n f x) (iteratedDeriv n f y)) ≤
      (K : ENNReal) * ENNReal.ofReal (dist x y)^(β-n)
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by linarith),
      ENNReal.coe_nnreal_eq K,← ENNReal.ofReal_mul K.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change dist (iteratedDeriv n f x) (iteratedDeriv n f y) ≤
      max (C (n+1)) (C n*(1+2^(β-n))) * dist x y^(β-n)
    simpa only [Real.dist_eq,abs_sub_comm] using hh x hx y hy
  · rw [← iteratedDeriv_succ]
    convert hb (n+1) x hx hxx using 1 <;> push_cast <;> congr 2 <;> ring

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
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ W : ℝ,
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
  obtain ⟨D,hD,N,hN,hjets⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,?_⟩
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
  have hb0 : 0 < b := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  let K0 := 2*D*(θ+1)*(N : ℝ)^(-ρ/2)*X^(-ρ)
  let K1 := 2*D*(θ+1)*(Real.sqrt b)^ρ
  let M := max 1 ((N : ℝ)*X^2)
  let K := max ((1+K0)*M^(ρ/2)) K1
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK : 0 ≤ K := hK1.trans (le_max_right _ _)
  obtain ⟨V,hV,hVb⟩ := weight_jets hX hb 0
  refine ⟨W*K+1,by positivity,?_⟩
  intro k t ht x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst x
    simp [publicUpper,publicLower,Real.zero_rpow hβ.ne']
  let n := N*b^k
  let y := (n : ℝ)*x^2
  let A := ∑ j ∈ range (k+1), scaleWeight X b j x
  let H := HNPCorrectionLiftAdvantage.lift (n+r) n t
    (HNPCorrectionLiftAdvantage.correction ρ θ n)
  let G (j : ℕ) := 2*D*(ringScale X b j)^(-ρ)*H
  have hn : 0 < n := by dsimp [n]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr : r ≤ n := hNr.trans (Nat.le_mul_of_pos_right N (pow_pos hb0 k))
  have hH : H ≤ (θ+1)*(n : ℝ)^(-ρ/2) :=
    HNPCorrectionLiftAdvantage.correction_uniform_bound hn hnr ht hρ hθ
  have hv := weight_mass hx0 hx.2 hb k
  have hA0 : 0 ≤ A := sum_nonneg (fun j _ => hv.1 j)
  have hA1 : A ≤ 1 := hv.2
  have hw : 0 ≤ W*x^β := by positivity
  have hG (j : ℕ) : G j ≤ 2*D*(θ+1)*(ringScale X b j)^(-ρ)*(n : ℝ)^(-ρ/2) := by
    have hs : 0 < ringScale X b j := by dsimp [ringScale]; positivity
    exact (mul_le_mul_of_nonneg_left hH (show 0 ≤ 2*D*(ringScale X b j)^(-ρ) by positivity)).trans_eq
      (by ring)
  have hGc (j : ℕ) (hj : j ∈ range (k+1)) : G j ≤ K0 := by
    have hjk : j ≤ k := by have := mem_range.mp hj; omega
    have hnj : 0 < N*b^j := by positivity
    have hnjR : (0 : ℝ) < ((N*b^j : ℕ) : ℝ) := by exact_mod_cast hnj
    have hle : ((N*b^j : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left N (Nat.pow_le_pow_right hb0 hjk)
    have hp := Real.rpow_le_rpow_of_nonpos hnjR hle (by linarith : -ρ/2 ≤ 0)
    apply (hG j).trans
    calc
      _ ≤ 2*D*(θ+1)*(ringScale X b j)^(-ρ)*((N*b^j : ℕ) : ℝ)^(-ρ/2) := by
        apply mul_le_mul_of_nonneg_left hp
        dsimp [ringScale]
        positivity
      _ = K0 := by
        dsimp [K0]
        calc
          _ = (2*D*(θ+1))*(((N*b^j : ℕ) : ℝ)^(-ρ/2)*(ringScale X b j)^(-ρ)) := by ring
          _ = _ := by rw [ring_scale_cancel hN hb0 hX]; ring
  have hGa (j : ℕ) (hj : scaleWeight X b j x ≠ 0) : G j ≤ K1*y^(-ρ/2) := by
    have hz : |scaleCoordinate X b x-j| < 1 := by
      by_contra h
      exact hj (by simpa only [iteratedDeriv_zero] using (hVb j x hx0 hx.2).2 (le_of_not_gt h))
    have hs := Real.sqrt_pos.mpr hbR
    have hsr := Real.rpow_le_rpow_of_nonpos (div_pos hx0 hs) (jet_ring_scale hX hx0 hb hz).2
      (neg_nonpos.mpr hρ)
    have hsre : (ringScale X b j)^(-ρ) ≤ (Real.sqrt b)^ρ*x^(-ρ) := by
      apply hsr.trans_eq
      rw [Real.div_rpow hx0.le hs.le,Real.rpow_neg hs.le,div_inv_eq_mul,mul_comm]
    have he : y^(-ρ/2) = (n : ℝ)^(-ρ/2)*x^(-ρ) := by
      dsimp [y]
      rw [Real.mul_rpow hnR.le (sq_nonneg _),← Real.rpow_natCast x 2,← Real.rpow_mul hx0.le]
      congr 2
      norm_num
      ring
    apply (hG j).trans
    calc
      _ ≤ 2*D*(θ+1)*((Real.sqrt b)^ρ*x^(-ρ))*(n : ℝ)^(-ρ/2) := by gcongr
      _ = K1*y^(-ρ/2) := by rw [he]; dsimp [K1]; ring
  rw [public_width_formula]
  change W*x^β*(1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j) ≤ _
  have hcoarse : 1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j ≤ 1+K0 := by
    have hh := sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hGc j hj) (hv.1 j))
    rw [← sum_mul] at hh
    change (∑ j ∈ range (k+1), scaleWeight X b j x*G j) ≤ A*K0 at hh
    nlinarith
  have hdecay (hy : M < y) : 1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j ≤ K1*y^(-ρ/2) := by
    have hm : A = 1 := full_mass_of_scale hX hx0 hx.2 hb hN
      ((le_max_right _ _).trans_lt hy)
    rw [hm,sub_self,zero_add]
    calc
      _ ≤ ∑ j ∈ range (k+1), scaleWeight X b j x*(K1*y^(-ρ/2)) := by
        apply sum_le_sum
        intro j _
        by_cases hj : scaleWeight X b j x = 0
        · rw [hj,zero_mul,zero_mul]
        · exact mul_le_mul_of_nonneg_left (hGa j hj) (hv.1 j)
      _ = K1*y^(-ρ/2) := by rw [← sum_mul]; change A*_ = _; rw [hm,one_mul]
  have htotal : 1-A+∑ j ∈ range (k+1), scaleWeight X b j x*G j ≤ K*(max 1 y)^(-ρ/2) := by
    by_cases hy : y ≤ M
    · have hmax : max 1 y ≤ M := max_le (le_max_left _ _) hy
      have hh := Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left 1 y)) hmax
        (by linarith : -ρ/2 ≤ 0)
      have he : M^(ρ/2)*M^(-ρ/2) = 1 := by
        rw [← Real.rpow_add hM,show ρ/2 + -ρ/2 = 0 by ring,Real.rpow_zero]
      calc
        _ ≤ 1+K0 := hcoarse
        _ = ((1+K0)*M^(ρ/2))*M^(-ρ/2) := by rw [mul_assoc,he,mul_one]
        _ ≤ ((1+K0)*M^(ρ/2))*(max 1 y)^(-ρ/2) := by gcongr
        _ ≤ K*(max 1 y)^(-ρ/2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hy' := lt_of_not_ge hy
      rw [max_eq_right ((le_max_left _ _).trans hy'.le)]
      exact (hdecay hy').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  calc
    _ ≤ W*x^β*(K*(max 1 y)^(-ρ/2)) := mul_le_mul_of_nonneg_left htotal hw
    _ = (W*K)*x^β*(max 1 y)^(-ρ/2) := by ring
    _ ≤ (W*K+1)*x^β*(max 1 y)^(-ρ/2) := by gcongr; linarith


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
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ W : ℝ, 0 < W →
      ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∃ H : ℝ≥0, ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      let lower := publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β
      let upper := publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D X W β
      ∀ k t : ℕ, t ≤ N*b^k+r →
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
        upper k t x-lower k t x ≤ U*((N*b^k : ℕ) : ℝ)^(-β/2)) := by
  obtain ⟨B,hB,hb⟩ := reference_public_closed_holder hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ n hn hn1
  refine ⟨B,hB,?_⟩
  intro b hBb X hX hX1
  obtain ⟨D,hD,N,hN,h⟩ := hb b hBb X hX hX1
  refine ⟨D,hD,N,hN,?_⟩
  intro W hW
  obtain ⟨C,hC,H,h⟩ := h W
  obtain ⟨U,hU,hUb⟩ := public_width_min_scale (cutoff χ β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 0 < N) (by omega : r ≤ N) D X W β hD.le hX hW.le hβ
    (by linarith) hθ.le
  obtain ⟨c,hc,hcb⟩ := public_width_endpoint_scale (cutoff χ β) (2/(5*T^β)) a d r ρ θ
    (by omega : 1 < b) (by omega : 2 ≤ N) D X W β hD hX hW hβ hρ2 hθ
  refine ⟨C,hC,H,c,U,hc,hU,?_⟩
  dsimp only
  intro k t ht
  refine ⟨h k t ht,?_⟩
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

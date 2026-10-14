/- GID: D5/S3/Analytic/SeriesInequalities/LogScalePartitionJets
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LogScalePartitionJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform jets of the original normalized logarithmic scale partition. -/

import D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.ZPow

noncomputable section
open Finset Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.SeriesInequalities.LogScalePartitionJets

open ParametricLorentzJetTransport

private lemma bump_zero_of_far {z : ℝ} (h : 3/4 ≤ |z|) : scaleBump z = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  have := sq_abs z
  nlinarith [sq_nonneg (|z|-3/4)]

private lemma bump_locally_zero {z : ℝ} (h : 1 ≤ |z|) :
    scaleBump =ᶠ[𝓝 z] fun _ => 0 := by
  have hz : (3/4 : ℝ) < |z| := by linarith
  filter_upwards [isOpen_lt continuous_const continuous_abs |>.mem_nhds hz] with y hy
  exact bump_zero_of_far hy.le

private lemma bump_jet_zero (m : ℕ) {z : ℝ} (h : 1 ≤ |z|) :
    iteratedDeriv m scaleBump z = 0 := by
  rw [(bump_locally_zero h).iteratedDeriv_eq m]
  simp

private lemma bump_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, |iteratedDeriv m scaleBump z| ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-1 : ℝ) 1)
    (bump_smooth.continuous_iteratedDeriv m (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro z
  by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
  · exact (show |iteratedDeriv m scaleBump z| ≤ C by simpa only [Real.norm_eq_abs] using hC z hz).trans
      (by linarith [le_abs_self C])
  · rw [bump_jet_zero m (z := z) (by
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h]; simp only [Set.mem_Icc,not_and_or,not_le] at hz
        rcases hz with hz | hz <;> linarith
      · rw [abs_of_nonpos h]; simp only [Set.mem_Icc,not_and_or,not_le] at hz
        rcases hz with hz | hz <;> linarith)]
    simp only [abs_zero]
    linarith [abs_nonneg C]

private lemma denominator_shift {z : ℝ} (hz : -(1/4 : ℝ) < z) :
    scaleDenominator (z+1) = scaleDenominator z := by
  obtain ⟨K,hK⟩ := exists_nat_gt (z+2)
  rw [denominator_finite (K := K+1) (by push_cast; linarith),
    denominator_finite (K := K) (by linarith),sum_range_succ']
  have hb : scaleBump (z+1-0) = 0 :=
    bump_zero_of_far (by rw [sub_zero,abs_of_pos (by linarith : 0 < z+1)]; linarith)
  simp only [Nat.cast_zero] at *
  rw [hb,add_zero]
  apply sum_congr rfl
  intro i _
  congr 1
  push_cast
  ring

private lemma denominator_shift_nat (n : ℕ) {z : ℝ} (hz : -(1/4 : ℝ) < z) :
    scaleDenominator (z+n) = scaleDenominator z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,denominator_shift (by have := Nat.cast_nonneg (α := ℝ) n; linarith),ih]

private lemma inverse_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, 0 ≤ z →
      |iteratedDeriv m (fun y => (scaleDenominator y)⁻¹) z| ≤ C := by
  let f : ℝ → ℝ := fun y => (scaleDenominator y)⁻¹
  have hcont : ContinuousOn (iteratedDeriv m f) (Set.Icc 0 1) := by
    intro y hy
    have hsm : ContDiffAt ℝ ∞ f y :=
      (denominator_smooth y).inv (denominator_positive hy.1).ne'
    rw [iteratedDeriv_eq_equiv_comp]
    exact ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) ℝ).symm.continuous.continuousAt.comp
      (hsm.continuousAt_iteratedFDeriv (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|+1,by positivity,?_⟩
  intro z hz
  let n := ⌊z⌋₊
  let y := z-n
  have hy0 : 0 ≤ y := sub_nonneg.mpr (Nat.floor_le hz)
  have hy1 : y ≤ 1 := by have := Nat.lt_floor_add_one z; dsimp [y,n]; linarith
  have he : (fun w => f (w+n)) =ᶠ[𝓝 y] f := by
    filter_upwards [Ioi_mem_nhds (by linarith : -(1/4 : ℝ) < y)] with w hw
    exact congrArg Inv.inv (denominator_shift_nat n hw)
  have hd := he.iteratedDeriv_eq m
  rw [iteratedDeriv_comp_add_const] at hd
  have hyn : y+n = z := by dsimp [y]; ring
  dsimp only at hd
  rw [hyn] at hd
  change |iteratedDeriv m f z| ≤ _
  rw [hd]
  exact (show |iteratedDeriv m f y| ≤ C by simpa only [Real.norm_eq_abs] using hC y ⟨hy0,hy1⟩).trans
    (by linarith [le_abs_self C])

/-- The original weight as a function of the logarithmic coordinate. -/
def coordinateWeight (j : ℕ) (z : ℝ) : ℝ :=
  scaleBump (z-j)/scaleDenominator z

private lemma coordinate_weight_smooth {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    ContDiffAt ℝ ∞ (coordinateWeight j) z :=
  ((bump_smooth.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const)).div
    (denominator_smooth z) (denominator_positive hz).ne')

private lemma coordinate_weight_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j z, 0 ≤ z → |iteratedDeriv m (coordinateWeight j) z| ≤ C := by
  choose A hA hAb using bump_jet_bound
  choose R hR hRb using inverse_jet_bound
  let C := ∑ i ∈ range (m+1), (m.choose i : ℝ)*A i*R (m-i)
  have hC : 0 ≤ C := sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i).le) (hR (m-i)).le)
  refine ⟨C+1,by positivity,?_⟩
  intro j z hz
  have he : coordinateWeight j = fun y => scaleBump (y-j)*(scaleDenominator y)⁻¹ := by
    ext y; exact div_eq_mul_inv _ _
  have hf : ContDiffAt ℝ m (fun y : ℝ => scaleBump (y-j)) z :=
    ((bump_smooth.comp (contDiff_id.sub contDiff_const)).contDiffAt).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hg : ContDiffAt ℝ m (fun y => (scaleDenominator y)⁻¹) z :=
    ((denominator_smooth z).inv (denominator_positive hz).ne').of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  rw [he,iteratedDeriv_fun_mul hf hg]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (fun i hi => ?_)).trans (by dsimp [C]; linarith)
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),iteratedDeriv_comp_sub_const]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb i (z-j)) (Nat.cast_nonneg _))
    (hRb (m-i) z hz) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i).le)


private lemma coordinate_smooth {X x : ℝ} (hX : 0 < X) (hx : 0 < x) (b : ℕ) :
    ContDiffAt ℝ ∞ (scaleCoordinate X b) x := by
  exact (contDiffAt_const.mul ((contDiffAt_const.div contDiffAt_id hx.ne').log
    (div_ne_zero hX.ne' hx.ne'))).div_const _

private lemma coordinate_jet (X : ℝ) (hX : 0 < X) (b n : ℕ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv (n+1) (scaleCoordinate X b) x| =
      |2 / Real.log b| * (n.factorial : ℝ) * x^(-((n+1 : ℕ) : ℝ)) := by
  have he : scaleCoordinate X b =ᶠ[𝓝 x]
      fun y => (2 / Real.log b) * (Real.log X - Real.log y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    dsimp [scaleCoordinate]
    rw [Real.log_div hX.ne' (ne_of_gt hy)]
    ring
  rw [he.iteratedDeriv_eq (n+1),iteratedDeriv_const_mul_field]
  have hs : ContDiffAt ℝ (n+1 : ℕ) Real.log x :=
    Real.contDiffAt_log.mpr hx.ne'
  rw [iteratedDeriv_fun_sub contDiffAt_const hs,iteratedDeriv_const]
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,zero_sub,abs_mul,abs_neg]
  rw [iteratedDeriv_succ',Real.deriv_log',iteratedDeriv_eq_iterate,iter_deriv_inv]
  rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n.factorial),abs_of_pos (zpow_pos hx (-1-(n : ℤ)))]
  rw [← Real.rpow_intCast]
  have he : ((-1-(n : ℤ) : ℤ) : ℝ) = -((n+1 : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  ring

private lemma weight_jet_zero (m j : ℕ) {X x : ℝ} {b : ℕ}
    (hX : 0 < X) (hx : 0 < x) (hz : 1 ≤ |scaleCoordinate X b x-j|) :
    iteratedDeriv m (scaleWeight X b j) x = 0 := by
  have he : scaleWeight X b j =ᶠ[𝓝 x] fun _ => 0 := by
    have ht : Tendsto (fun y => scaleCoordinate X b y-j) (𝓝 x)
        (𝓝 (scaleCoordinate X b x-j)) :=
      ((coordinate_smooth hX hx b).continuousAt.sub continuousAt_const)
    filter_upwards [ht.eventually (bump_locally_zero hz)] with y hy
    simp only [scaleWeight,hy,zero_div]
  rw [he.iteratedDeriv_eq m]
  simp

/-- All parameter jets of the actual normalized weights have one scale bound,
independent of the ring index, including the rightmost endpoint. -/
theorem weight_jets {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j x, 0 < x → x ≤ X →
      |iteratedDeriv m (scaleWeight X b j) x| ≤ C*x^(-(m : ℝ)) ∧
      (1 ≤ |scaleCoordinate X b x-j| → iteratedDeriv m (scaleWeight X b j) x = 0) := by
  choose A hA hAb using coordinate_weight_bound
  let L : ℕ → ℝ := fun i => |2 / Real.log b| * ((i-1).factorial : ℝ)
  let C := ∑ c : OrderedFinpartition m, A c.length * ∏ j, L (c.partSize j)
  have hL (i : ℕ) : 0 ≤ L i := by dsimp [L]; positivity
  have hC : 0 ≤ C := sum_nonneg (fun c _ =>
    mul_nonneg (hA c.length).le (prod_nonneg (fun j _ => hL _)))
  refine ⟨C+1,by positivity,?_⟩
  intro j x hx hxx
  refine ⟨?_,fun hz => weight_jet_zero m j hX hx hz⟩
  have hz := coordinate_nonneg hx hxx hb
  have hco : ∀ i : ℕ, 0 < i → |iteratedDeriv i (scaleCoordinate X b) x| =
      L i * x^(-(i : ℝ)) := by
    intro i hi
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
    simpa [L] using coordinate_jet X hX b n hx
  change |iteratedDeriv m (coordinateWeight j ∘ scaleCoordinate X b) x| ≤ _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    ((coordinate_weight_smooth hz j).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)))
    ((coordinate_smooth hX hx b).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) le_rfl]
  apply (abs_sum_le_sum_abs _ _).trans
  have hp (c : OrderedFinpartition m) :
      |iteratedDeriv c.length (coordinateWeight j) (scaleCoordinate X b x) *
        ∏ i, iteratedDeriv (c.partSize i) (scaleCoordinate X b) x| ≤
        (A c.length * ∏ i, L (c.partSize i))*x^(-(m : ℝ)) := by
    rw [abs_mul,Finset.abs_prod]
    simp_rw [hco _ (c.partSize_pos _)]
    have hc : ∑ i, c.partSize i = m := by
      simpa using Fintype.card_congr c.equivSigma
    have he : (∏ i, x^(-((c.partSize i : ℕ) : ℝ))) = x^(-(m : ℝ)) := by
      rw [← Real.rpow_sum_of_pos hx,Finset.sum_neg_distrib]
      congr 2
      exact_mod_cast hc
    rw [prod_mul_distrib,he]
    calc
      _ ≤ A c.length * ((∏ i, L (c.partSize i)) * x^(-(m : ℝ))) :=
        mul_le_mul_of_nonneg_right (hAb c.length j _ hz)
          (mul_nonneg (prod_nonneg (fun i _ => hL _)) (by positivity))
      _ = _ := by ring
  calc
    _ ≤ ∑ c : OrderedFinpartition m,
        (A c.length * ∏ i, L (c.partSize i))*x^(-(m : ℝ)) := sum_le_sum (fun c _ => hp c)
    _ = C*x^(-(m : ℝ)) := by rw [sum_mul]
    _ ≤ (C+1)*x^(-(m : ℝ)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)


private lemma active_indices {z : ℝ} (hz : 0 ≤ z) {j : ℕ} (hj : |z-j| < 1) :
    j ∈ ({⌊z⌋₊,⌊z⌋₊+1} : Finset ℕ) := by
  have hfloor := Nat.floor_le hz
  have hfrac := Nat.lt_floor_add_one z
  obtain ⟨hjl,hju⟩ := abs_lt.mp hj
  have hlo : ⌊z⌋₊ ≤ j := by
    by_contra h
    have hn : j+1 ≤ ⌊z⌋₊ := by omega
    have hnR : (j : ℝ)+1 ≤ ⌊z⌋₊ := by exact_mod_cast hn
    linarith
  have hhi : j < ⌊z⌋₊+2 := by
    have hnR : (j : ℝ) < (⌊z⌋₊ : ℝ)+2 := by linarith
    exact_mod_cast hnR
  simp only [mem_insert,mem_singleton]
  omega

/-- A finite sum supported on the actual two overlapping scale rings has
no dependence on the number of indices in the stage. -/
lemma sum_active_bound {z C : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C)
    (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ j ∈ s, |z-j| < 1 → |f j| ≤ C)
    (hzero : ∀ j ∈ s, 1 ≤ |z-j| → f j = 0) :
    |∑ j ∈ s, f j| ≤ 2*C := by
  classical
  let t := s.filter (fun j : ℕ => |z-(j : ℝ)| < 1)
  have ht : t ⊆ {⌊z⌋₊,⌊z⌋₊+1} := fun j hj =>
    active_indices hz (mem_filter.mp hj).2
  have hcard : t.card ≤ 2 := (card_le_card ht).trans (by simp)
  have he : ∑ j ∈ s, f j = ∑ j ∈ t, f j := by
    symm
    apply sum_subset (filter_subset _ _)
    intro j hj hjt
    exact hzero j hj (le_of_not_gt (by simpa [t,hj] using hjt))
  rw [he]
  calc
    _ ≤ ∑ j ∈ t, |f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ t, C := sum_le_sum (fun j hj => hf j (mem_filter.mp hj).1 (mem_filter.mp hj).2)
    _ = (t.card : ℝ)*C := by simp
    _ ≤ 2*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

/-- Every possibly nonzero weight jet lies in its proportional scale ring. -/
lemma jet_ring_scale {X x : ℝ} {b j : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hb : 1 < b) (hz : |scaleCoordinate X b x-j| < 1) :
    OriginalRingEnvelopeScale.ringScale X b j / Real.sqrt b ≤ x ∧
      x / Real.sqrt b ≤ OriginalRingEnvelopeScale.ringScale X b j := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 := lt_trans zero_lt_one hbR
  have hlog := Real.log_pos hbR
  have hsqrt := Real.sqrt_pos.mpr hb0
  obtain ⟨hzl,hzu⟩ := abs_lt.mp hz
  have hl : (j-1)*Real.log b < 2*Real.log (X/x) := by
    apply (lt_div_iff₀ hlog).mp
    change (j : ℝ)-1 < scaleCoordinate X b x
    linarith
  have hu : 2*Real.log (X/x) < (j+1)*Real.log b := by
    apply (div_lt_iff₀ hlog).mp
    change scaleCoordinate X b x < (j : ℝ)+1
    linarith
  have hlo : (b : ℝ)^(-((j : ℝ)+1)/2) ≤ x/X := by
    rw [Real.rpow_def_of_pos hb0,← Real.exp_log (div_pos hx hX)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hx.ne' hX.ne']
    rw [Real.log_div hX.ne' hx.ne'] at hu
    nlinarith
  have hhi : x/X ≤ (b : ℝ)^((1-(j : ℝ))/2) := by
    rw [Real.rpow_def_of_pos hb0,← Real.exp_log (div_pos hx hX)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hx.ne' hX.ne']
    rw [Real.log_div hX.ne' hx.ne'] at hl
    nlinarith
  have hs₁ : OriginalRingEnvelopeScale.ringScale X b j / Real.sqrt b =
      X*(b : ℝ)^(-((j : ℝ)+1)/2) := by
    rw [OriginalRingEnvelopeScale.ringScale,Real.sqrt_eq_rpow,mul_div_assoc,← Real.rpow_sub hb0]
    congr 2
    ring
  have hs₂ : OriginalRingEnvelopeScale.ringScale X b j * Real.sqrt b =
      X*(b : ℝ)^((1-(j : ℝ))/2) := by
    rw [OriginalRingEnvelopeScale.ringScale,Real.sqrt_eq_rpow,mul_assoc,← Real.rpow_add hb0]
    congr 2
    ring
  constructor
  · rw [hs₁]
    exact (mul_le_mul_of_nonneg_left hlo hX.le).trans_eq (by field_simp)
  · apply (div_le_iff₀ hsqrt).mpr
    rw [hs₂]
    exact (mul_le_mul_of_nonneg_left hhi hX.le).trans_eq' (by field_simp)


/-- Once the current grid is finer than the world's starting scale, the whole
normalized partition has already entered the finite public stage. -/
lemma full_mass_of_scale {X x : ℝ} {b N k : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hxx : x ≤ X) (hb : 1 < b) (hN : 0 < N)
    (hscale : (N : ℝ)*X^2 < ((N*b^k : ℕ) : ℝ)*x^2) :
    ∑ j ∈ range (k+1), scaleWeight X b j x = 1 := by
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hs : 0 < OriginalRingEnvelopeScale.ringScale X b k := by
    dsimp [OriginalRingEnvelopeScale.ringScale]; positivity
  have hz : scaleCoordinate X b x < k := by
    by_contra h
    have hcoord : (k : ℝ) ≤ scaleCoordinate X b x := le_of_not_gt h
    have hlog : (k : ℝ)*Real.log b ≤ 2*Real.log (X/x) :=
      (le_div_iff₀ (Real.log_pos hbR)).mp hcoord
    have hxs : x ≤ OriginalRingEnvelopeScale.ringScale X b k := by
      rw [← Real.exp_log hx,← Real.exp_log hs]
      apply Real.exp_le_exp.mpr
      rw [OriginalRingEnvelopeScale.ringScale,
        Real.log_mul hX.ne' (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < b) _).ne',
        Real.log_rpow (by linarith : (0 : ℝ) < b)]
      rw [Real.log_div hX.ne' hx.ne'] at hlog
      nlinarith
    have he := OriginalRingEnvelopeScale.ring_scale_cancel hN hb0 hX k (-2)
    norm_num [Real.rpow_two] at he
    have hx2 : x^2 ≤ (OriginalRingEnvelopeScale.ringScale X b k)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ ((N*b^k : ℕ) : ℝ) by positivity)
    push_cast at hh hscale
    rw [he] at hh
    exact (not_lt_of_ge hh) hscale
  simp only [scaleWeight,← sum_div]
  rw [← denominator_finite (by push_cast; linarith : scaleCoordinate X b x+1 < (k+1 : ℕ))]
  exact div_self (denominator_positive (coordinate_nonneg hx hxx hb)).ne'


/-- Weighted world-scale decay gives a uniform grid-scale bound. -/
lemma min_scale_global {n x p ρ : ℝ} (hn : 0 < n) (hx : 0 ≤ x)
    (hp : 0 < p) (hpρ : p ≤ ρ) :
    x^p*(max 1 (n*x^2))^(-ρ/2) ≤ n^(-p/2) := by
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    simp only [Real.zero_rpow hp.ne',zero_mul]
    positivity
  let y := n*x^2
  have hy : 0 < y := by dsimp [y]; positivity
  have he : x^p = n^(-p/2)*y^(p/2) := by
    dsimp [y]
    rw [Real.mul_rpow hn.le (sq_nonneg _),← Real.rpow_natCast x 2,← Real.rpow_mul hx.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ)*(p/2) = p by ring]
    rw [← mul_assoc,← Real.rpow_add hn,show -p/2+p/2 = 0 by ring,Real.rpow_zero,one_mul]
  rw [he,mul_assoc]
  change n^(-p/2)*(y^(p/2)*(max 1 y)^(-ρ/2)) ≤ n^(-p/2)
  suffices hh : y^(p/2)*(max 1 y)^(-ρ/2) ≤ 1 from
    (mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hn _).le).trans_eq (mul_one _)
  by_cases hy1 : y ≤ 1
  · rw [max_eq_left hy1,Real.one_rpow,mul_one]
    exact Real.rpow_le_one hy.le hy1 (by linarith)
  · rw [max_eq_right (le_of_not_ge hy1),← Real.rpow_add hy]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hy1) (by linarith)

end D5.S3.Analytic.SeriesInequalities.LogScalePartitionJets

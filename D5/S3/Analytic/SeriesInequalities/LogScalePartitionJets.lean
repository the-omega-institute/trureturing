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
import D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal
noncomputable section
open Finset Filter
open scoped Topology ContDiff NNReal
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

private lemma coordinate_lt_of_scale {X x : ℝ} {b N k : ℕ}
    (hX : 0 < X) (hx : 0 < x) (hb : 1 < b) (hN : 0 < N)
    (hscale : (N : ℝ)*X^2 < ((N*b^k : ℕ) : ℝ)*x^2) :
    scaleCoordinate X b x < k := by
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
  exact hz

/-- The unstarted tail vanishes on a neighborhood in a fine world, including
worlds at the right endpoint of the public parameter interval. -/
lemma full_mass_germ_of_scale {X x : ℝ} {b N k : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hxx : x ≤ X) (hb : 1 < b) (hN : 0 < N)
    (hscale : (N : ℝ)*X^2 < ((N*b^k : ℕ) : ℝ)*x^2) :
    (fun y => ∑ j ∈ range (k+1), scaleWeight X b j y) =ᶠ[𝓝 x] fun _ => 1 := by
  have hz := coordinate_lt_of_scale hX hx hb hN hscale
  have hc := (coordinate_smooth hX hx b).continuousAt
  have hp := ((denominator_smooth _).continuousAt.comp hc).tendsto.eventually
    (Ioi_mem_nhds (denominator_positive (coordinate_nonneg hx hxx hb)))
  filter_upwards [hc.tendsto.eventually (Iio_mem_nhds hz),hp] with y hy hpy
  simp only [scaleWeight,← sum_div]
  rw [← denominator_finite (by push_cast; linarith : scaleCoordinate X b y+1 < (k+1 : ℕ))]
  exact div_self (ne_of_gt hpy)

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

lemma product_jet_bound {f g : ℝ → ℝ} {x p q : ℝ} {m : ℕ}
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

lemma scaled_mixture_jet_bound {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b)
    (q : ℝ) (m : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ f : ℕ → ℝ → ℝ, ∀ x : ℝ,
      0 < x → x ≤ X →
      (∀ j ∈ s, ContDiffAt ℝ m (f j) x) →
      (∀ j ∈ s, |scaleCoordinate X b x-j| < 1 → ∀ i ≤ m,
        |iteratedDeriv i (f j) x| ≤ A i*x^(q-i)) →
      |iteratedDeriv m (fun y => ∑ j ∈ s, scaleWeight X b j y*f j y) x| ≤
        C*x^(q-m) := by
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
    (show 0 ≤ C*x^(q-m) by positivity) s
    (fun j => iteratedDeriv m (fun y => scaleWeight X b j y*f j y) x) ?_ ?_
  · exact hbound.trans (by
      calc
        2*(C*x^(q-m)) = (2*C)*x^(q-m) := by ring
        _ ≤ (2*C+1)*x^(q-m) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · intro j hj hz
    simpa only [zero_sub,zero_add] using product_jet_bound (p := 0) (q := q) hx (hw j) (hf j hj) B A
      (fun i => (hB i).le) hA (fun i _ => by simpa only [zero_sub] using (hBb i j x hx hxx).1)
      (fun i hi => by simpa only [zero_sub] using hfb j hj hz i hi)
  · intro j hj hz
    rw [iteratedDeriv_fun_mul (hw j) (hf j hj)]
    apply sum_eq_zero
    intro i _
    rw [(hBb i j x hx hxx).2 hz]
    ring

lemma mixture_jet_bound {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b)
    (m : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ f : ℕ → ℝ → ℝ, ∀ x : ℝ,
      0 < x → x ≤ X →
      (∀ j ∈ s, ContDiffAt ℝ m (f j) x) →
      (∀ j ∈ s, |scaleCoordinate X b x-j| < 1 → ∀ i ≤ m,
        |iteratedDeriv i (f j) x| ≤ A i*x^(-(i : ℝ))) →
      |iteratedDeriv m (fun y => ∑ j ∈ s, scaleWeight X b j y*f j y) x| ≤
        C*x^(-(m : ℝ)) := by
  simpa only [zero_sub] using scaled_mixture_jet_bound hX hb 0 m A hA

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

lemma closed_jets_holder {f : ℝ → ℝ} {X β : ℝ} {n : ℕ}
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

lemma min_scale_combine {a w y M A B ρ : ℝ} (hw : 0 ≤ w) (hM : 1 ≤ M)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (ha : a ≤ A*w)
    (hb : M < y → a ≤ B*w*y^(-ρ/2)) :
    a ≤ max (A*M^(ρ/2)) B*w*(max 1 y)^(-ρ/2) := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  by_cases hy : y ≤ M
  · have hmax : max 1 y ≤ M := max_le hM hy
    have hh := Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_left 1 y)) hmax
      (by linarith : -ρ/2 ≤ 0)
    have he : M^(ρ/2)*M^(-ρ/2) = 1 := by
      rw [← Real.rpow_add hM0,show ρ/2 + -ρ/2 = 0 by ring,Real.rpow_zero]
    calc
      _ ≤ A*w := ha
      _ = (A*M^(ρ/2))*w*M^(-ρ/2) := by nlinarith [congrArg (fun z => A*w*z) he]
      _ ≤ (A*M^(ρ/2))*w*(max 1 y)^(-ρ/2) := by gcongr
      _ ≤ max (A*M^(ρ/2)) B*w*(max 1 y)^(-ρ/2) := by
        gcongr
        exact le_max_left _ _
  · have hy' := lt_of_not_ge hy
    rw [max_eq_right (hM.trans hy'.le)]
    exact (hb hy').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (A*M^(ρ/2)) B) hw) (Real.rpow_pos_of_pos (hM0.trans hy') _).le)

/-- A normalized finite mixture with constant ring amplitudes retains its
weighted derivative scale after multiplication by a fixed power. -/
lemma power_mixture_jet_bound {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b)
    (β q A : ℝ) (hA : 0 ≤ A) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ a : ℕ → ℝ, ∀ x : ℝ,
      0 < x → x ≤ X →
      (∀ j ∈ s, |scaleCoordinate X b x-j| < 1 → |a j| ≤ A*x^q) →
      |iteratedDeriv m (fun y => y^β * ∑ j ∈ s, scaleWeight X b j y*a j) x| ≤
        C*x^(β+q-m) := by
  choose Q hQ hQb using fun i => scaled_mixture_jet_bound hX hb q i (fun _ => A) (fun _ => hA)
  let P : ℕ → ℝ := fun i => |∏ j ∈ range i, (β-(j : ℝ))|
  let C := ∑ i ∈ range (m+1), (m.choose i : ℝ)*P i*Q (m-i)
  have hP (i : ℕ) : 0 ≤ P i := abs_nonneg _
  have hC : 0 ≤ C := sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP i)) (hQ _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro s a x hx hxx ha
  let F (y : ℝ) := ∑ j ∈ s, scaleWeight X b j y*a j
  have hs : ContDiffAt ℝ ∞ F x :=
    ContDiffAt.sum (fun j _ => (weight_smooth hX hx hxx hb j).mul contDiffAt_const)
  have hF (i : ℕ) : |iteratedDeriv i F x| ≤ Q i*x^(q-i) := by
    apply hQb i s (fun j _ => a j) x hx hxx (fun _ _ => contDiffAt_const)
    intro j hj hz ell _
    rw [iteratedDeriv_const]
    by_cases he : ell = 0
    · subst ell
      simpa only [if_true,Nat.cast_zero,sub_zero] using ha j hj hz
    · rw [if_neg he,abs_zero]
      positivity
  have hp (i : ℕ) : |iteratedDeriv i (fun y : ℝ => y^β) x| ≤ P i*x^(β-i) := by
    rw [D5.S3.Estimation.SequentialDecisionRisk.NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos β i hx,
      abs_mul,abs_of_pos (Real.rpow_pos_of_pos hx _)]
  have hh := product_jet_bound (p := β) (q := q) hx
    (Real.contDiffAt_rpow_const_of_ne hx.ne')
    (hs.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))) P Q hP (fun i => (hQ i).le)
    (fun i _ => hp i) (fun i _ => hF i)
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))

/-- Parameter derivatives commute with the actual hypergeometric elevation,
whose nonnegative coefficients preserve a common jet bound. -/
lemma lift_jet_bound {n d t m : ℕ} (hd : d ≤ n) (ht : t ≤ n)
    (f : ℕ → ℝ → ℝ) {x C : ℝ}
    (hs : ∀ j, ContDiffAt ℝ m (f j) x)
    (hc : ∀ j ≤ d, |iteratedDeriv m (f j) x| ≤ C) :
    |iteratedDeriv m (fun y => HNPCorrectionLiftAdvantage.lift n d t (fun j => f j y)) x| ≤ C := by
  unfold HNPCorrectionLiftAdvantage.lift
  rw [iteratedDeriv_fun_sum (fun j _ => contDiffAt_const.mul (hs j))]
  simp_rw [iteratedDeriv_const_mul_field]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ range (t+1), HNPCorrectionLiftAdvantage.weight n d t j*C := by
      apply sum_le_sum
      intro j _
      by_cases hj : j ≤ d
      · rw [abs_mul,abs_of_nonneg (HNPCorrectionLiftAdvantage.weight_nonneg _ _ _ _)]
        exact mul_le_mul_of_nonneg_left (hc j hj)
          (HNPCorrectionLiftAdvantage.weight_nonneg _ _ _ _)
      · have hz : HNPCorrectionLiftAdvantage.weight n d t j = 0 := by
          exact HNPCorrectionLiftAdvantage.weight_eq_zero (Or.inl (lt_of_not_ge hj))
        rw [hz,zero_mul,zero_mul,abs_zero]
    _ = C := by rw [← sum_mul,HNPCorrectionLiftAdvantage.weight_sum hd ht,one_mul]

/-- One fixed geometric grid step changes the minimum scale by at most its
fixed power, uniformly in the world parameter. -/
lemma min_scale_step {b y ρ : ℝ} (hb : 1 ≤ b) (hy : 0 ≤ y) (hρ : 0 ≤ ρ) :
    (max 1 y)^(-ρ/2) ≤ b^(ρ/2)*(max 1 (b*y))^(-ρ/2) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hmax : max 1 (b*y) ≤ b*max 1 y := by
    apply max_le
    · exact hb.trans (le_mul_of_one_le_right hb0.le (le_max_left _ _))
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hb0.le
  have hp := Real.rpow_le_rpow_of_nonpos
    (zero_lt_one.trans_le (le_max_left 1 (b*y))) hmax (by linarith : -ρ/2 ≤ 0)
  have he : b^(ρ/2)*(b*max 1 y)^(-ρ/2) = (max 1 y)^(-ρ/2) := by
    rw [Real.mul_rpow hb0.le (zero_le_one.trans (le_max_left _ _)),← mul_assoc,
      ← Real.rpow_add hb0,show ρ/2 + -ρ/2 = 0 by ring,Real.rpow_zero,one_mul]
  exact he ▸ mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hb0 _).le

/-- A common scalar factor is retained through the finite active mixture. -/
lemma scaled_mixture_factor {X : ℝ} (hX : 0 < X) {b : ℕ} (hb : 1 < b)
    (q : ℝ) (m : ℕ) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, ∀ f : ℕ → ℝ → ℝ, ∀ x c : ℝ,
      0 < x → x ≤ X → 0 < c → (∀ j ∈ s, ContDiffAt ℝ m (f j) x) →
      (∀ j ∈ s, |scaleCoordinate X b x-j| < 1 → ∀ i ≤ m,
        |iteratedDeriv i (f j) x| ≤ c*A i*x^(q-i)) →
      |iteratedDeriv m (fun y => ∑ j ∈ s, scaleWeight X b j y*f j y) x| ≤
        c*C*x^(q-m) := by
  obtain ⟨C,hC,hbnd⟩ := scaled_mixture_jet_bound hX hb q m A hA
  refine ⟨C,hC,?_⟩
  intro s f x c hx hxx hc hs hf
  have hh := hbnd s (fun j y => c⁻¹*f j y) x hx hxx
    (fun j hj => contDiffAt_const.mul (hs j hj)) (fun j hj hz i hi => ?_)
  · have he : (fun y => ∑ j ∈ s, scaleWeight X b j y*f j y) =
        fun y => c*(∑ j ∈ s, scaleWeight X b j y*(c⁻¹*f j y)) := by
      ext y
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    rw [he,iteratedDeriv_const_mul_field,abs_mul,abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by ring)
  · rw [iteratedDeriv_const_mul_field,abs_mul,abs_of_pos (inv_pos.mpr hc)]
    exact (mul_le_mul_of_nonneg_left (hf j hj hz i hi) (inv_pos.mpr hc).le).trans_eq
      (by field_simp)

lemma new_weight_zero_germ {X x : ℝ} {b N k : ℕ} (hX : 0 < X) (hx : 0 < x)
    (hb : 1 < b) (hN : 0 < N)
    (hscale : (b : ℝ)*N*X^2 < ((N*b^(k+1) : ℕ) : ℝ)*x^2) :
    scaleWeight X b (k+1) =ᶠ[𝓝 x] fun _ => 0 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have he : ((N*b^(k+1) : ℕ) : ℝ)*x^2 = (b : ℝ)*(((N*b^k : ℕ) : ℝ)*x^2) := by
    push_cast; rw [pow_succ]; ring
  rw [he] at hscale
  have hz := coordinate_lt_of_scale hX hx hb hN
    (show (N : ℝ)*X^2 < ((N*b^k : ℕ) : ℝ)*x^2 by nlinarith)
  filter_upwards [(coordinate_smooth hX hx b).continuousAt.tendsto.eventually
    (Iio_mem_nhds hz)] with y hy
  dsimp [scaleWeight]
  rw [bump_zero (Or.inl (by push_cast; linarith)),zero_div]

end D5.S3.Analytic.SeriesInequalities.LogScalePartitionJets

namespace D5.S3.Analytic.SeriesInequalities.OriginalPublicArrayRegularity
open ParametricLorentzJetTransport LogScalePartitionJets
open OriginalRingEnvelopeScale ReferenceProfileMixedJets LorentzCoefficientRemainder
open LorentzCommonGridStability LorentzLowDegreeCoefficientRemainder

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

lemma public_zero_germ (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
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

lemma public_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
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

lemma public_closed_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
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

set_option maxHeartbeats 600000 in
lemma public_increment_closed {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
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

open HNPCorrectionLiftAdvantage

private lemma correction_abs {n r t : ℕ} {ρ θ : ℝ}
    (hn : 0 < n) (hr : r ≤ n) (ht : t ≤ n+r) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    |lift (n+r) n t (correction ρ θ n)| ≤ (θ+1)*(n : ℝ)^(-ρ/2) := by
  rw [abs_of_nonneg (show 0 ≤ lift (n+r) n t (correction ρ θ n) from
    sum_nonneg (fun i _ => mul_nonneg (weight_nonneg _ _ _ _)
      (add_nonneg (by positivity) (Real.rpow_nonneg (sample_nonneg _ _) _))))]
  exact correction_uniform_bound hn hr ht hρ hθ

lemma ring_increment_jets {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (r : ℕ) (ρ θ A : ℝ) {τ b : ℕ} (hτ : 0 < τ)
    (hb : 1 < b) (hr : r ≤ τ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (k t m : ℕ) (ht : t ≤ τ*b^(k+1)+r) {x C : ℝ} (hx : 0 < x)
    (hc : ‖iteratedDeriv m (fun y => bernsteinCoefficient (τ*b^(k+1)+r) t
      (center τ b r (fun q => (reference φ η a d y q : ℂ)) (k+1)-
       center τ b r (fun q => (reference φ η a d y q : ℂ)) k)) x‖ ≤ C) (u : Bool) :
    let R := fun l i y => if u then 1-ringUpper τ b r ρ θ A
      (fun q => (reference φ η a d y q : ℂ)) l i
      else ringLower τ b r ρ θ A (fun q => (reference φ η a d y q : ℂ)) l i
    |iteratedDeriv m (fun y => R (k+1) t y-lift (τ*b^(k+1)+r) (τ*b^k+r) t
      (fun i => R k i y)) x| ≤ C + if m = 0 then
        A*(θ+1)*((b : ℝ)^(ρ/2)+1)*((τ*b^(k+1) : ℕ) : ℝ)^(-ρ/2) else 0 := by
  dsimp only
  let no := τ*b^k
  let nn := τ*b^(k+1)
  have hb0 : 0 < b := by omega
  have hno : 0 < no := by dsimp [no]; positivity
  have hnn : 0 < nn := by dsimp [nn]; positivity
  have hnon : no ≤ nn := Nat.mul_le_mul_left τ (Nat.pow_le_pow_right hb0 (by omega))
  have hro : r ≤ no := hr.trans (Nat.le_mul_of_pos_right τ (pow_pos hb0 k))
  let H (n i : ℕ) := lift (n+r) n i (correction ρ θ n)
  let Z := A*(lift (nn+r) (no+r) t (H no)-H nn t)
  let F (y : ℝ) := bernsteinCoefficient (nn+r) t
    (center τ b r (fun q => (reference φ η a d y q : ℂ)) (k+1)-
     center τ b r (fun q => (reference φ η a d y q : ℂ)) k)
  have hd : no+r ≤ nn+r := by omega
  have he : (fun y => (if u then 1-ringUpper τ b r ρ θ A
      (fun q => (reference φ η a d y q : ℂ)) (k+1) t else
      ringLower τ b r ρ θ A (fun q => (reference φ η a d y q : ℂ)) (k+1) t)-
      lift (nn+r) (no+r) t (fun i => if u then 1-ringUpper τ b r ρ θ A
      (fun q => (reference φ η a d y q : ℂ)) k i else
      ringLower τ b r ρ θ A (fun q => (reference φ η a d y q : ℂ)) k i)) =
      fun y => (if u then (-1 : ℝ) else 1)*(F y).re+Z := by
    ext y
    have hel := coefficient_elevation hd ht
      (center τ b r (fun q => (reference φ η a d y q : ℂ)) k) (center_degree hb0 r _ k)
    dsimp only [F,Z,H,no,nn] at *
    cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true,ringLower,ringUpper,
      coefficient_sub,Complex.sub_re,lift,mul_sub,mul_add,sum_sub_distrib,sum_add_distrib,
      ← mul_assoc,← mul_sum,← sum_mul,weight_sum hd ht,mul_one] at hel ⊢ <;> rw [hel] <;> simp only [mul_sum,mul_assoc] <;> ring
  rw [he]
  have hs : ContDiffAt ℝ m F x := by
    have hh (l : ℕ) := coefficient_smooth hτ hb0 hφ η a d r l (nn+r) t hx
    simpa only [F,coefficient_sub] using ((hh (k+1)).sub (hh k)).of_le
      (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hsre : ContDiffAt ℝ m (fun y => (F y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hs
  rw [iteratedDeriv_fun_add (contDiffAt_const.mul hsre) contDiffAt_const,
    iteratedDeriv_const_mul_field,iteratedDeriv_const]
  change |(if u then (-1 : ℝ) else 1)*iteratedDeriv m (fun y => Complex.reCLM (F y)) x + _| ≤ _
  rw [linear_iterated Complex.reCLM hs]
  have hsign : |if u then (-1 : ℝ) else 1| = 1 := by cases u <;> norm_num
  have hc' : |(if u then (-1 : ℝ) else 1)*(iteratedDeriv m F x).re| ≤ C := by
    rw [abs_mul,hsign,one_mul]
    exact (Complex.abs_re_le_norm _).trans hc
  by_cases hm : m = 0
  · rw [if_pos hm,if_pos hm]
    apply (abs_add_le _ _).trans (add_le_add hc' ?_)
    have ho : |lift (nn+r) (no+r) t (H no)| ≤ (θ+1)*(no : ℝ)^(-ρ/2) := by
      simpa only [iteratedDeriv_zero] using lift_jet_bound (m := 0) (x := x) hd ht
        (fun i _ => H no i) (fun _ => contDiffAt_const)
        (fun i hi => correction_abs hno hro hi hρ hθ)
    have hn := correction_abs hnn (hro.trans hnon) ht hρ hθ
    have hp : (no : ℝ)^(-ρ/2) = (b : ℝ)^(ρ/2)*(nn : ℝ)^(-ρ/2) := by
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
      have hnoR : (0 : ℝ) < no := by exact_mod_cast hno
      have hmul : (nn : ℝ) = (no : ℝ)*(b : ℝ) := by dsimp [no,nn]; push_cast; rw [pow_succ]; ring
      rw [hmul,Real.mul_rpow hnoR.le hbR.le]
      calc
        _ = (no : ℝ)^(-ρ/2)*((b : ℝ)^(ρ/2)*(b : ℝ)^(-ρ/2)) := by
          rw [← Real.rpow_add hbR,show ρ/2+-ρ/2 = 0 by ring,Real.rpow_zero,mul_one]
        _ = _ := by ring
    dsimp only [Z]
    rw [abs_mul,abs_of_nonneg hA]
    apply (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ho hn)) hA).trans_eq
    rw [hp]
    dsimp [nn]
    ring
  · rw [if_neg hm,if_neg hm,add_zero,add_zero]
    exact hc'

end D5.S3.Analytic.SeriesInequalities.OriginalPublicArrayRegularity

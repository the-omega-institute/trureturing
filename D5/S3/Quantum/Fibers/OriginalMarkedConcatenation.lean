/- GID: D5/S3/Quantum/Fibers/OriginalMarkedConcatenation
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/OriginalMarkedConcatenation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native hazard, survival and chronological Kraus composition. -/

import D5.S3.Quantum.Fibers.OriginalControlMarkedJump
import D5.S3.Quantum.Fibers.OriginalControlSurvivalInstability

/-! The native derivative hazard and original Kraus measure of concatenated controls. -/

noncomputable section
namespace D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
open Set Filter Topology MeasureTheory intervalIntegral
open OriginalControlComposition OriginalControlMarkedJump
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The concatenation proofs consume the frozen scalar supplier directly while
   retaining the local names used by the marked-law interface. -/
abbrev hazard := OriginalControlSurvivalInstability.hazard
abbrev survival := OriginalControlSurvivalInstability.survival

/-- The logarithmic jump rate of the actual concatenated programme. -/
def jumpRate (c : ℝ) (k : ℝ → ℝ) (t : ℝ) (i : Fin 5) : ℝ :=
  hazard c k t - deriv (fun u => Real.log (p c (k u) i)) t

/-- Failure is measured from the original absorbing Kraus output. -/
def failureDensity (c a beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (i : Fin 5) (t : ℝ) : ℝ :=
  Complex.normSq ((jumpKraus c a (k t) (survival c k t) (jumpRate c k t) i *ᵥ
    source c a beta m theta) 0)

def failureMeasure (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (i : Fin 5) : Measure ℝ :=
  (volume.restrict (Ioc 0 T)).withDensity
    (fun t => ENNReal.ofReal (failureDensity c a beta m theta k i t))

def markedLaw (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) : Measure Leg.Record :=
  ENNReal.ofReal (∑ i, Complex.normSq
    ((successfulKraus c a (k T) (survival c k T) *ᵥ source c a beta m theta) i)) •
      Measure.dirac (Sum.inl ()) +
    ∑ i : Fin 5, (failureMeasure c a beta T m theta k i).map (fun t => Sum.inr (i, t))

theorem markedLaw_apply (c a beta T : ℝ) (m : ℤ) (theta : Fin 5 → ℝ)
    (k : ℝ → ℝ) (E : Set Leg.Record) (hE : MeasurableSet E) :
    markedLaw c a beta T m theta k E = (if Sum.inl () ∈ E then ENNReal.ofReal (∑ i, Complex.normSq
        ((successfulKraus c a (k T) (survival c k T) *ᵥ source c a beta m theta) i)) else 0)+
      ∑ i : Fin 5, ∫⁻ t in (Ioc 0 T) ∩ {t | Sum.inr (i, t) ∈ E},
        ENNReal.ofReal (failureDensity c a beta m theta k i t) := by
  have hm (i : Fin 5) : Measurable (fun t : ℝ => (Sum.inr (i, t) : Leg.Record)) :=
    measurable_inr.comp (measurable_const.prodMk measurable_id)
  simp only [markedLaw, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hE, Set.indicator_apply, Measure.finsetSum_apply]
  congr 1
  · split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Measure.map_apply (hm i) hE, failureMeasure,
      withDensity_apply _ (hE.preimage (hm i)),
      Measure.restrict_restrict (hE.preimage (hm i)), inter_comm]
    rfl

theorem deriv_before (f g : ℝ → ℝ) (T t : ℝ) (ht : t < T) :
    deriv (concatenate f g T) t = deriv f t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Iio_mem_nhds ht] with u hu
  change u < T at hu
  simp [concatenate, hu.le]

theorem deriv_after (f g : ℝ → ℝ) (T t : ℝ) (ht : T < t) :
    deriv (concatenate f g T) t = deriv g (t-T) := by
  calc
    _ = deriv (fun u => f T + g (u-T) - g 0) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds ht] with u hu
      change T < u at hu
      simp [concatenate, not_le.mpr hu]
    _ = _ := by rw [deriv_sub_const, deriv_const_add, deriv_comp_sub_const]

private theorem hazard_before (c T : ℝ) (k K : ℝ → ℝ) (t : ℝ) (ht : t < T) :
    hazard c (concatenate k K T) t = hazard c k t := by
  simp [hazard, deriv_before k K T t ht, concatenate, ht.le]

private theorem hazard_after (c T : ℝ) (k K : ℝ → ℝ) (hj : k T = K 0)
    (t : ℝ) (ht : T < t) :
    hazard c (concatenate k K T) t = hazard c K (t-T) := by
  simp [hazard, deriv_after k K T t ht, concatenate, not_le.mpr ht, hj]

theorem hazard_integral (c T s : ℝ) (k K : ℝ → ℝ)
    (hT : 0 ≤ T) (hs : 0 ≤ s) (hj : k T = K 0)
    (hk : IntervalIntegrable (hazard c k) volume 0 T)
    (hK : IntervalIntegrable (hazard c K) volume 0 s) :
    (∫ u in (0:ℝ)..(T + s), hazard c (concatenate k K T) u) = (∫ u in (0:ℝ)..T, hazard c k u) + (∫ u in (0:ℝ)..s, hazard c K u) := by
  have hi0 : IntervalIntegrable (hazard c (concatenate k K T)) volume 0 T := by
    apply hk.congr_uIoo
    intro u hu
    rw [uIoo_of_le hT] at hu
    exact (hazard_before c T k K u hu.2).symm
  have hi1 : IntervalIntegrable (fun u => hazard c K (u-T)) volume T (T + s) := by
    simpa [add_comm] using hK.comp_sub_right T
  have hi1' : IntervalIntegrable (hazard c (concatenate k K T)) volume T (T + s) := by
    apply hi1.congr_uIoo
    intro u hu
    rw [uIoo_of_le (by linarith : T ≤ T + s)] at hu
    exact (hazard_after c T k K hj u hu.1).symm
  rw [← integral_add_adjacent_intervals hi0 hi1']
  rw [integral_congr_Ioo_of_le hT (fun u hu => hazard_before c T k K u hu.2)]
  rw [integral_congr_Ioo_of_le (by linarith : T ≤ T + s)
    (fun u hu => hazard_after c T k K hj u hu.1)]
  rw [integral_comp_sub_right (hazard c K) T, sub_self, add_sub_cancel_left]

private theorem sqrt_factor (A B x y z : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (Real.sqrt B * Real.sqrt (z / y)) * (Real.sqrt A * Real.sqrt (y / x)) = Real.sqrt (A * B) * Real.sqrt (z / x) := by
  rw [← Real.sqrt_mul hB, ← Real.sqrt_mul hA,
    ← Real.sqrt_mul (mul_nonneg hB (div_nonneg hz.le hy.le)),
    ← Real.sqrt_mul (mul_nonneg hA hB)]
  congr 1
  field_simp
  <;> ring

private theorem successful_compose (c a b k A B : ℝ) (hc : c < 1 / 2)
    (ha : a ∈ Ioo 0 c) (hb : b ∈ Ioo 0 c) (hk : k ∈ Ioo 0 c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    successfulKraus c b k B * successfulKraus c a b A = successfulKraus c a k (A * B) := by
  simp only [successfulKraus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact_mod_cast sqrt_factor A B (p c a i) (p c b i) (p c k i) hA hB
    (p_pos c a hc ha i) (p_pos c b hc hb i) (p_pos c k hc hk i)

theorem hazard_integrable (c T chi : ℝ) (k : ℝ → ℝ)
    (hk : OriginalControl (c, c, 1-2 * c) T k (fun _ => chi)) :
    IntervalIntegrable (hazard c k) volume 0 T := by
  have hd := (original_ac _ _ _ _ hk).1.intervalIntegrable_deriv
  have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 T := intervalIntegrable_const
  have hp : IntervalIntegrable (fun t => max (deriv k t) 0) volume 0 T :=
    ⟨hd.1.sup hz.1, hd.2.sup hz.2⟩
  have hn : IntervalIntegrable (fun t => max (-deriv k t) 0) volume 0 T :=
    ⟨hd.neg.1.sup hz.1, hd.neg.2.sup hz.2⟩
  have hl : FiniteRectangleTransport.lower (c, c, 1-2 * c) = 0 := by
    dsimp [FiniteRectangleTransport.lower]
    ring_nf
    simp
  have hb : ∀ t ∈ uIcc 0 T, k t ∈ Ioo 0 c := by
    intro t ht
    simpa [hl, FiniteRectangleTransport.upper] using hk.2.2.2.1 t ht
  have hi0 := hp.mul_continuousOn (hk.2.1.inv₀ (fun t ht => (hb t ht).1.ne'))
  have hi1 := hn.mul_continuousOn
    ((continuousOn_const.sub hk.2.1).inv₀ (fun t ht => (sub_pos.mpr (hb t ht).2).ne'))
  change IntervalIntegrable (fun t => max (deriv k t) 0 / k t +
    max (-deriv k t) 0 / (c-k t)) volume 0 T
  simpa only [div_eq_mul_inv, Pi.inv_apply, Pi.sub_apply] using hi0.add hi1

private theorem leg_hazard (L : Leg) : hazard L.c L.height = L.hazard := by
  funext t
  simp [hazard, Leg.hazard, (L.height_deriv t).deriv]

theorem leg_survival (L : Leg) : survival L.c L.height = L.survival := by
  funext t
  simp [survival, Leg.survival, leg_hazard]

theorem leg_rate (L : Leg) : jumpRate L.c L.height = L.jumpRate := by
  funext t i
  simp [jumpRate, Leg.jumpRate, leg_hazard]

private theorem height_end (L : Leg) : L.height L.duration = L.y := by
  dsimp [Leg.height, Leg.speed]
  field_simp [L.duration_pos.ne']
  <;> ring

private theorem leg_integrable (L : Leg) (t : ℝ) (ht : t ∈ Icc 0 L.duration) :
    IntervalIntegrable (hazard L.c L.height) volume 0 t := by
  rw [leg_hazard]
  exact (L.hazard_cont.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

theorem rate_before (c T : ℝ) (k K : ℝ → ℝ) (t : ℝ) (ht : t < T) :
    jumpRate c (concatenate k K T) t = jumpRate c k t := by
  funext i
  rw [jumpRate, jumpRate, hazard_before c T k K t ht]
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Iio_mem_nhds ht] with u hu
  change u < T at hu
  simp [concatenate, hu.le]

theorem rate_after (c T : ℝ) (k K : ℝ → ℝ) (hj : k T = K 0)
    (t : ℝ) (ht : T < t) :
    jumpRate c (concatenate k K T) t = jumpRate c K (t-T) := by
  funext i
  rw [jumpRate, jumpRate, hazard_after c T k K hj t ht]
  congr 1
  calc
    _ = deriv (fun u => Real.log (p c (K (u-T)) i)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds ht] with u hu
      change T < u at hu
      simp [concatenate, not_le.mpr hu, hj]
    _ = _ := deriv_comp_sub_const (fun u => Real.log (p c (K u) i)) T t

theorem survival_before (c T t : ℝ) (k K : ℝ → ℝ)
    (ht : 0 ≤ t) (htT : t ≤ T) :
    survival c (concatenate k K T) t = survival c k t := by
  rw [survival, survival]
  congr 2
  exact integral_congr_Ioo_of_le ht
    (fun u hu => hazard_before c T k K u (hu.2.trans_le htT))

private theorem joined_survival (L R : Leg) (hC : R.c = L.c) (hj : L.y = R.x)
    (s : ℝ) (hs : s ∈ Icc 0 R.duration) :
    survival L.c (concatenate L.height R.height L.duration) (L.duration + s) = L.survival L.duration * R.survival s := by
  have hjoin : L.height L.duration = R.height 0 := by
    rw [height_end]
    simpa [Leg.height] using hj
  have hi1 : IntervalIntegrable (hazard L.c R.height) volume 0 s := by
    rw [← hC]
    exact leg_integrable R s hs
  rw [survival, hazard_integral L.c L.duration s L.height R.height L.duration_pos.le
    hs.1 hjoin (leg_integrable L L.duration ⟨L.duration_pos.le, le_rfl⟩) hi1,
    neg_add, Real.exp_add]
  change survival L.c L.height L.duration * survival L.c R.height s = _
  rw [leg_survival L, ← hC, leg_survival R]

private theorem density_before (L R : Leg) (beta : ℝ) (m : ℤ)
    (theta : Fin 5 → ℝ) (i : Fin 5) (t : ℝ) (ht : t ∈ Ioo 0 L.duration) :
    failureDensity L.c L.x beta m theta (concatenate L.height R.height L.duration) i t = L.density t i := by
  have hheight : concatenate L.height R.height L.duration t = L.height t := by
    simp [concatenate, ht.2.le]
  have hS : survival L.c (concatenate L.height R.height L.duration) t = L.survival t := by
    rw [survival_before L.c L.duration t L.height R.height ht.1.le ht.2.le, leg_survival]
  have hg : jumpRate L.c (concatenate L.height R.height L.duration) t = L.jumpRate t := by
    rw [rate_before L.c L.duration L.height R.height t ht.2, leg_rate]
  rw [failureDensity, hheight, hS, hg, jump_action,
    source_jump_density L.c L.x (L.height t) (L.survival t) beta m theta
      (L.jumpRate t) L.c_lt ⟨L.x_pos, L.x_lt⟩
      (L.height_bounds t ⟨ht.1.le, ht.2.le⟩) (Real.exp_pos _).le
      (fun j => L.jumpRate_nonneg t ⟨ht.1.le, ht.2.le⟩ j)]
  rfl

private theorem density_after (L R : Leg) (hC : R.c = L.c) (hj : L.y = R.x)
    (beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) (i : Fin 5) (t : ℝ)
    (ht : t ∈ Ioc L.duration (L.duration + R.duration)) :
    failureDensity L.c L.x beta m theta (concatenate L.height R.height L.duration) i t = L.survival L.duration * R.density (t-L.duration) i := by
  have hs : t-L.duration ∈ Icc 0 R.duration := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hjoin : L.height L.duration = R.height 0 := by
    rw [height_end]
    simpa [Leg.height] using hj
  have hheight : concatenate L.height R.height L.duration t = R.height (t-L.duration) := by
    simp [concatenate, not_le.mpr ht.1, hjoin]
  have hS : survival L.c (concatenate L.height R.height L.duration) t = L.survival L.duration * R.survival (t-L.duration) := by
    convert joined_survival L R hC hj (t-L.duration) hs using 1 <;> ring
  have hg : jumpRate L.c (concatenate L.height R.height L.duration) t = R.jumpRate (t-L.duration) := by
    rw [rate_after L.c L.duration L.height R.height hjoin t ht.1, ← hC, leg_rate]
  have hb : R.height (t-L.duration) ∈ Ioo 0 L.c := by
    rw [← hC]
    exact R.height_bounds _ hs
  rw [failureDensity, hheight, hS, hg, jump_action,
    source_jump_density L.c L.x (R.height (t-L.duration))
      (L.survival L.duration * R.survival (t-L.duration)) beta m theta
      (R.jumpRate (t-L.duration)) L.c_lt ⟨L.x_pos, L.x_lt⟩ hb
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (fun j => R.jumpRate_nonneg _ hs j)]
  simp only [Leg.density, hC]
  ring

/-- The seam is negligible for the native hazard. Survival is obtained by
splitting its exponential integral, and the matrices act chronologically on
one unchanged, possibly unnormalized input. -/
theorem native_concatenation (c T s a chi : ℝ) (k K : ℝ → ℝ)
    (hc : c < 1 / 2) (hT : 0 ≤ T) (hs : 0 ≤ s) (hj : k T = K 0)
    (ha : a ∈ Ioo 0 c) (hb : k T ∈ Ioo 0 c) (hk : K s ∈ Ioo 0 c)
    (h0 : OriginalControl (c, c, 1-2 * c) T k (fun _ => chi))
    (h1 : OriginalControl (c, c, 1-2 * c) s K (fun _ => chi)) :
    (∀ᵐ t : ℝ ∂volume, hazard c (concatenate k K T) t = if t ≤ T then hazard c k t else hazard c K (t-T)) ∧
    survival c (concatenate k K T) (T + s) = survival c k T * survival c K s ∧
    (∀ psi : Fin 5 → ℂ,
      successfulKraus c (k T) (K s) (survival c K s) *ᵥ
        (successfulKraus c a (k T) (survival c k T) *ᵥ psi) = successfulKraus c a (K s) (survival c (concatenate k K T) (T + s)) *ᵥ psi) ∧
    (∀ (g : Fin 5 → ℝ) (i : Fin 5) (psi : Fin 5 → ℂ),
      jumpKraus c (k T) (K s) (survival c K s) g i *ᵥ
        (successfulKraus c a (k T) (survival c k T) *ᵥ psi) = jumpKraus c a (K s) (survival c (concatenate k K T) (T + s)) g i *ᵥ psi) := by
  have hi := hazard_integrable c T chi k h0
  have hI := hazard_integrable c s chi K h1
  have hS : survival c (concatenate k K T) (T + s) = survival c k T * survival c K s := by
    rw [survival, hazard_integral c T s k K hT hs hj hi hI, neg_add, Real.exp_add]
    rfl
  have hmat := successful_compose c a (k T) (K s) (survival c k T)
    (survival c K s) hc ha hb hk (Real.exp_pos _).le (Real.exp_pos _).le
  rw [← hS] at hmat
  refine ⟨?_, hS, ?_, ?_⟩
  · filter_upwards [volume.ae_ne T] with t ht
    by_cases h : t ≤ T
    · rw [ite_eq_left h]
      exact hazard_before c T k K t (lt_of_le_of_ne h ht)
    · rw [ite_eq_right h]
      exact hazard_after c T k K hj t (lt_of_not_ge h)
  · intro psi
    rw [Matrix.mulVec_mulVec, hmat]
  · intro g i psi
    rw [jumpKraus, Matrix.mulVec_mulVec, Matrix.mul_assoc, hmat]
    rfl

/-- Every Borel record event of the actual joined programme is the sum of
first-piece failures, survival-weighted second-piece failures with the actual
shifted clock, and the final success atom. -/
theorem native_marked_join (L R : Leg) (hC : R.c = L.c) (hj : L.y = R.x)
    (chi beta : ℝ) (m : ℤ) (theta : Fin 5 → ℝ) :
    OriginalControl (L.c, L.c, 1-2 * L.c) (L.duration + R.duration)
      (concatenate L.height R.height L.duration) (fun _ => chi) ∧
    ∀ E : Set Leg.Record, MeasurableSet E →
      markedLaw L.c L.x beta (L.duration + R.duration) m theta
        (concatenate L.height R.height L.duration) E = (if Sum.inl () ∈ E then
        ENNReal.ofReal (L.survival L.duration * R.survival R.duration) else 0) +
      (∑ i : Fin 5, ∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i, t) ∈ E},
        ENNReal.ofReal (L.density t i)) +
      ENNReal.ofReal (L.survival L.duration) *
        (∑ i : Fin 5, ∫⁻ t in (Ioc L.duration (L.duration + R.duration)) ∩
            {t | Sum.inr (i, t) ∈ E},
          ENNReal.ofReal (R.density (t-L.duration) i)) := by
  have h0 := (L.affine_marked_probability chi beta m theta).1
  have h1 := (R.affine_marked_probability chi beta m theta).1
  rw [hC] at h1
  have hjoin : L.height L.duration = R.height 0 := by
    rw [height_end]
    simpa [Leg.height] using hj
  have horiginal := (concatenate_original _ _ _ _ _ _ _ h0 h1 hjoin).1
  have hphase : concatenate (fun _ => chi) (fun _ => chi) L.duration = (fun _ => chi) := by
    funext t
    simp [concatenate]
  rw [hphase] at horiginal
  refine ⟨horiginal, ?_⟩
  intro E hE
  have hend : concatenate L.height R.height L.duration (L.duration + R.duration) = R.y := by
    rw [concatenate, ite_eq_right (by linarith [R.duration_pos]), height_end,
      add_sub_cancel_left, height_end]
    simp [Leg.height, hj]
  have hS := joined_survival L R hC hj R.duration ⟨R.duration_pos.le, le_rfl⟩
  rw [markedLaw_apply _ _ _ _ _ _ _ E hE, hend,
    source_live_mass L.c L.x R.y
      (survival L.c (concatenate L.height R.height L.duration) (L.duration + R.duration))
      beta m theta L.c_lt ⟨L.x_pos, L.x_lt⟩
      (by rw [← hC]; exact ⟨R.y_pos, R.y_lt⟩) (Real.exp_pos _).le, hS]
  have hsplit (i : Fin 5) :
      (∫⁻ t in (Ioc 0 (L.duration + R.duration)) ∩ {t | Sum.inr (i, t) ∈ E},
        ENNReal.ofReal (failureDensity L.c L.x beta m theta
          (concatenate L.height R.height L.duration) i t)) = (∫⁻ t in (Ioc 0 L.duration) ∩ {t | Sum.inr (i, t) ∈ E},
        ENNReal.ofReal (L.density t i)) +
      ENNReal.ofReal (L.survival L.duration) *
        (∫⁻ t in (Ioc L.duration (L.duration + R.duration)) ∩ {t | Sum.inr (i, t) ∈ E},
          ENNReal.ofReal (R.density (t-L.duration) i)) := by
    have hm : MeasurableSet {t : ℝ | Sum.inr (i, t) ∈ E} :=
      hE.preimage (measurable_inr.comp (measurable_const.prodMk measurable_id))
    have hsets : (Ioc 0 (L.duration + R.duration)) ∩ {t | Sum.inr (i, t) ∈ E} = ((Ioc 0 L.duration) ∩ {t | Sum.inr (i, t) ∈ E}) ∪
        ((Ioc L.duration (L.duration + R.duration)) ∩ {t | Sum.inr (i, t) ∈ E}) := by
      rw [← Ioc_union_Ioc_eq_Ioc L.duration_pos.le
        (le_add_of_nonneg_right R.duration_pos.le), union_inter_distrib_right]
    rw [hsets, lintegral_union (measurableSet_Ioc.inter hm) (by
      apply Disjoint.mono inter_subset_left inter_subset_left
      exact Ioc_disjoint_Ioc_of_le le_rfl)]
    congr 1
    · apply setLIntegral_congr_fun_ae (measurableSet_Ioc.inter hm)
      filter_upwards [volume.ae_ne L.duration] with t ht hmem
      rw [density_before L R beta m theta i t
        ⟨hmem.1.1, lt_of_le_of_ne hmem.1.2 ht⟩]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun (measurableSet_Ioc.inter hm)
      intro t ht
      dsimp only
      rw [density_after L R hC hj beta m theta i t ht.1]
      exact ENNReal.ofReal_mul (show 0 ≤ L.survival L.duration from (Real.exp_pos _).le)
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact (add_assoc _ _ _).symm

end D5.S3.Quantum.Fibers.OriginalMarkedConcatenation

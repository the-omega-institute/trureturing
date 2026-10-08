/- GID: D5/S1/Words/Forbidden/ForbiddenWordRationalBoundary
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/ForbiddenWordRationalBoundary
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The avoidance denominator vanishes at the reciprocal growth rate. -/
/-
proof_shape: tail_imbalance: bind-only; consumer: reciprocal_overlapMoment
proof_shape: coeff_mul_monomial_real: bind-only; consumer: seriesSummable_mul_monomial
proof_shape: seriesSummable_mul_monomial: bind-only; consumer: seriesEval_mul_monomial
proof_shape: seriesEval_mul_monomial: bind-only; consumer: seriesEval_mul_finite
proof_shape: seriesSummable_one: bind-only; consumer: seriesEval_realOverlapSeries
proof_shape: seriesEval_one: bind-only; consumer: seriesEval_realOverlapSeries
proof_shape: seriesSummable_add: bind-only; consumer: seriesSummable_mul_finite
proof_shape: seriesEval_add: bind-only; consumer: seriesEval_mul_finite
proof_shape: seriesSummable_sub: bind-only; consumer: seriesSummable_mul_denominator_form
proof_shape: seriesEval_sub: bind-only; consumer: seriesEval_mul_denominator_form
proof_shape: seriesSummable_mul_finite: bind-only; consumer: seriesEval_mul_finite
proof_shape: seriesEval_mul_finite: bind-only; consumer: seriesEval_mul_denominator_form
proof_shape: powerSeries_map_monomial: bind-only; consumer: realOverlapSeries_map
proof_shape: realCountSeries_map: bind-only; consumer: real_counting_identity
proof_shape: realOverlapSeries_map: bind-only; consumer: real_counting_identity
proof_shape: realWordMonomial_map: bind-only; consumer: real_counting_identity
proof_shape: realLetterSeries_map: bind-only; consumer: real_counting_identity
proof_shape: real_counting_identity: bind-only; consumer: scalar_counting_identity
proof_shape: realImbalanceSeries_map: bind-only; consumer: real_moment_identity
proof_shape: realOverlapMoment_map: bind-only; consumer: realDenominatorMoment_map
proof_shape: realWordMoment_map: bind-only; consumer: realDenominatorMoment_map
proof_shape: realDenominatorMoment_map: bind-only; consumer: real_moment_identity
proof_shape: real_moment_identity: bind-only; consumer: scalar_moment_identity
proof_shape: reciprocal_overlapMoment: bind-only; consumer: reciprocal_denomMoment_root
proof_shape: reciprocal_denomMoment_root: bind-only; consumer: unbalanced_boundary_moment_ne_zero
proof_shape: unbalanced_boundary_moment_ne_zero: bind-only; consumer: tendsto_half_implies_balanced_long
proof_shape: realLetterSeries_eq_monomial: bind-only; consumer: seriesSummable_mul_denominator_form
proof_shape: seriesSummable_mul_denominator_form: bind-only; consumer: scalar_length_identity
proof_shape: seriesEval_mul_denominator_form: bind-only; consumer: seriesEval_mul_realDenominator
proof_shape: seriesEval_mul_realDenominator: bind-only; consumer: scalar_counting_identity
proof_shape: seriesEval_realOverlapSeries: bind-only; consumer: scalar_counting_identity
proof_shape: realCountSeries_summable: bind-only; consumer: scalar_counting_identity
proof_shape: scalar_counting_identity: bind-only; consumer: denomEval_growthApproach_bound
proof_shape: coeff_lengthMoment: bind-only; consumer: lengthMoment_monomial
proof_shape: lengthMoment_mul: bind-only; consumer: real_length_identity
proof_shape: lengthMoment_add: bind-only; consumer: lengthMoment_sum
proof_shape: lengthMoment_sub: bind-only; consumer: seriesEval_mul_lengthDenominator
proof_shape: lengthMoment_one: bind-only; consumer: seriesEval_mul_lengthDenominator
proof_shape: lengthMoment_monomial: bind-only; consumer: seriesEval_mul_lengthOverlap
proof_shape: lengthMoment_sum: bind-only; consumer: seriesEval_mul_lengthOverlap
proof_shape: real_length_identity: bind-only; consumer: scalar_length_identity
proof_shape: realLengthSeries_summable: bind-only; consumer: scalar_length_identity
proof_shape: seriesEval_mul_lengthOverlap: bind-only; consumer: seriesEval_lengthOverlap
proof_shape: seriesEval_lengthOverlap: bind-only; consumer: scalar_length_identity
proof_shape: seriesEval_mul_lengthDenominator: bind-only; consumer: scalar_length_identity
proof_shape: seriesSummable_mul_lengthDenominator: bind-only; consumer: scalar_length_identity
proof_shape: scalar_length_identity: bind-only; consumer: moment_ratio_cross
proof_shape: realImbalanceSeries_summable: bind-only; consumer: scalar_moment_identity
proof_shape: seriesEval_mul_realDenominatorMoment: bind-only; consumer: scalar_moment_identity
proof_shape: seriesEval_realOverlapMoment: bind-only; consumer: scalar_moment_identity
proof_shape: scalar_moment_identity: bind-only; consumer: moment_ratio_cross
proof_shape: rootPolyEval_continuous: bind-only; consumer: root_exists_three_halves_two
proof_shape: rootPolyEval_three_halves_pos: bind-only; consumer: root_exists_three_halves_two
proof_shape: root_exists_three_halves_two: bind-only; consumer: growthRate_gt_three_halves
proof_shape: growthApproach_pos: bind-only; consumer: countSeriesEval_growthApproach
proof_shape: growthApproach_product: bind-only; consumer: growthApproach_inside
proof_shape: growthApproach_inside: bind-only; consumer: countSeriesEval_growthApproach
proof_shape: growthApproach_tendsto: bind-only; consumer: growthRadius_denominator_zero
proof_shape: overlapEval_ge_one: bind-only; consumer: denomEval_growthApproach_bound
proof_shape: overlapEval_continuous: bind-only; consumer: growthRadius_denominator_zero
proof_shape: denomEval_continuous: bind-only; consumer: growthRadius_denominator_zero
proof_shape: countSeriesEval_ge_geometric: bind-only; consumer: countSeriesEval_growthApproach
proof_shape: countSeriesEval_growthApproach: bind-only; consumer: denomEval_growthApproach_bound
proof_shape: denomEval_growthApproach_bound: bind-only; consumer: growthRadius_denominator_zero
proof_shape: growthRadius_denominator_zero: content
proof_shape: corrEval_reciprocal_overlap: bind-only; consumer: reciprocal_denom_cross
proof_shape: reciprocal_denom_cross: bind-only; consumer: reciprocal_denom_zero_iff
proof_shape: reciprocal_denom_zero_iff: bind-only; consumer: growthRate_root
proof_shape: growthRate_root: bind-only; consumer: tendsto_half_implies_balanced_long
proof_shape: growthRate_gt_three_halves: content
escape_witness: growthRadius_denominator_zero on result's live proof path.
admission_basis: escape-witness
Direct frozen dependencies: none on the protected baseline.
Same-delivery dependencies: BalancedBordersHalfFrequency.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Forbidden.BalancedBordersHalfFrequency

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.ForbiddenWordRationalBoundary
open Set
open D5.S1.Words.Forbidden.ForbiddenWordCounting
open D5.S1.Words.Forbidden.ForbiddenWordGrowth
open D5.S1.Words.Forbidden.BorderImbalanceExclusion
open D5.S1.Words.Forbidden.BalancedBordersHalfFrequency

private theorem tail_imbalance (w : List Bool) {j : ℕ} (hj : j ≤ w.length) :
    2*((w.drop j).count true:ℝ)-(w.length-j:ℕ)=
      (2*(w.count true:ℝ)-w.length)-(imbalance w j:ℝ) := by
  have hc := congrArg (fun u : List Bool => u.count true) (List.take_append_drop j w)
  simp only [List.count_append] at hc
  have hl := List.length_take_of_le hj
  have he : w.length=j+(w.length-j) := by omega
  unfold imbalance
  rw [hl]
  push_cast
  have hcr : ((w.take j).count true:ℝ)+((w.drop j).count true:ℝ)=(w.count true:ℝ) := by exact_mod_cast hc
  have her : (w.length:ℝ)=(j:ℝ)+(w.length-j:ℕ) := by exact_mod_cast he
  linarith

noncomputable def seriesEval (f : PowerSeries ℝ) (x : ℝ) : ℝ :=
  ∑' m, PowerSeries.coeff m f*x^m

private def SeriesSummable (f : PowerSeries ℝ) (x : ℝ) : Prop :=
  Summable (fun m => PowerSeries.coeff m f*x^m)

private theorem coeff_mul_monomial_real (f : PowerSeries ℝ) (m n : ℕ) (a : ℝ) :
    PowerSeries.coeff m (f*PowerSeries.monomial n a) =
      if n ≤ m then PowerSeries.coeff (m-n) f*a else 0 := by
  simpa [PowerSeries.coeff, PowerSeries.monomial] using
    MvPowerSeries.coeff_mul_monomial (Finsupp.single () m) (Finsupp.single () n) f a

private theorem seriesSummable_mul_monomial {f : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (n : ℕ) (a : ℝ) :
    SeriesSummable (f*PowerSeries.monomial n a) x := by
  apply (summable_nat_add_iff n).mp
  have he : (fun m => PowerSeries.coeff (m+n) (f*PowerSeries.monomial n a)*x^(m+n)) =
      (fun m => (a*x^n)*(PowerSeries.coeff m f*x^m)) := by
    funext m
    rw [coeff_mul_monomial_real,if_pos (by omega),Nat.add_sub_cancel_right,pow_add]
    ring
  change Summable (fun m => PowerSeries.coeff (m+n) (f*PowerSeries.monomial n a)*x^(m+n))
  rw [he]
  exact hf.mul_left (a*x^n)

private theorem seriesEval_mul_monomial {f : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (n : ℕ) (a : ℝ) :
    seriesEval (f*PowerSeries.monomial n a) x=seriesEval f x*(a*x^n) := by
  have hprod := seriesSummable_mul_monomial hf n a
  have hinit : (∑ m ∈ range n, PowerSeries.coeff m (f*PowerSeries.monomial n a)*x^m)=0 := by
    apply sum_eq_zero
    intro m hm
    rw [coeff_mul_monomial_real,if_neg (by simp only [Finset.mem_range] at hm; omega),zero_mul]
  unfold seriesEval
  rw [← hprod.sum_add_tsum_nat_add n,hinit,zero_add]
  calc
    _ = ∑' m, (PowerSeries.coeff m f*x^m)*(a*x^n) := by
      apply tsum_congr
      intro m
      rw [coeff_mul_monomial_real,if_pos (by omega),Nat.add_sub_cancel_right,pow_add]
      ring
    _ = _ := tsum_mul_right

private theorem seriesSummable_one (x : ℝ) : SeriesSummable 1 x := by
  apply summable_of_ne_finset_zero (s := {0})
  intro m hm
  have hm0 : m≠0 := by simpa using hm
  simp [PowerSeries.coeff_one,hm0]

private theorem seriesEval_one (x : ℝ) : seriesEval 1 x=1 := by
  unfold seriesEval
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    simp [PowerSeries.coeff_one,hm]

private theorem seriesSummable_add {f g : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (hg : SeriesSummable g x) : SeriesSummable (f+g) x := by
  simpa [SeriesSummable,map_add,add_mul] using hf.add hg

private theorem seriesEval_add {f g : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (hg : SeriesSummable g x) :
    seriesEval (f+g) x=seriesEval f x+seriesEval g x := by
  simpa [seriesEval,map_add,add_mul] using hf.tsum_add hg

private theorem seriesSummable_sub {f g : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (hg : SeriesSummable g x) : SeriesSummable (f-g) x := by
  simpa [SeriesSummable,map_sub,sub_mul] using hf.sub hg

private theorem seriesEval_sub {f g : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) (hg : SeriesSummable g x) :
    seriesEval (f-g) x=seriesEval f x-seriesEval g x := by
  simpa [seriesEval,map_sub,sub_mul] using hf.tsum_sub hg

private noncomputable def finiteSeries {ι : Type*} (S : Finset ι) (n : ι → ℕ) (a : ι → ℝ) : PowerSeries ℝ :=
  ∑ i ∈ S,PowerSeries.monomial (n i) (a i)

private theorem seriesSummable_mul_finite {ι : Type*} (S : Finset ι) (n : ι → ℕ) (a : ι → ℝ)
    {f : PowerSeries ℝ} {x : ℝ} (hf : SeriesSummable f x) :
    SeriesSummable (f*finiteSeries S n a) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteSeries,SeriesSummable]
  | @insert i S hi ih =>
    simp only [finiteSeries,sum_insert hi,mul_add]
    exact seriesSummable_add (seriesSummable_mul_monomial hf _ _) ih

private theorem seriesEval_mul_finite {ι : Type*} (S : Finset ι) (n : ι → ℕ) (a : ι → ℝ)
    {f : PowerSeries ℝ} {x : ℝ} (hf : SeriesSummable f x) :
    seriesEval (f*finiteSeries S n a) x=seriesEval f x*(∑ i ∈ S,a i*x^(n i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteSeries,seriesEval]
  | @insert i S hi ih =>
    simp only [finiteSeries,sum_insert hi,mul_add]
    change seriesEval (f*PowerSeries.monomial (n i) (a i)+f*finiteSeries S n a) x =
      seriesEval f x*(a i*x^(n i))+seriesEval f x*(∑ j ∈ S,a j*x^(n j))
    rw [seriesEval_add (seriesSummable_mul_monomial hf _ _)
      (seriesSummable_mul_finite S n a hf),seriesEval_mul_monomial hf,ih]

private noncomputable def evalOneRealHom : Polynomial ℚ →+* ℝ :=
  (Rat.castHom ℝ).comp (Polynomial.evalRingHom 1)

noncomputable def realCountSeries (w : List Bool) : PowerSeries ℝ := PowerSeries.mk (avoidCount w)

private noncomputable def realOverlapSeries (w : List Bool) : PowerSeries ℝ :=
  ∑ j ∈ borderLengths w,PowerSeries.monomial (w.length-j) 1

private noncomputable def realWordMonomial (w : List Bool) : PowerSeries ℝ := PowerSeries.monomial w.length 1

private noncomputable def realLetterSeries : PowerSeries ℝ := PowerSeries.X*PowerSeries.C 2

private noncomputable def realDenominator (w : List Bool) : PowerSeries ℝ :=
  (1-realLetterSeries)*realOverlapSeries w+realWordMonomial w

noncomputable def realImbalanceSeries (w : List Bool) : PowerSeries ℝ :=
  PowerSeries.mk fun m => 2*avoidOnes w m-(m:ℝ)*avoidCount w m

private noncomputable def realOverlapMoment (w : List Bool) : PowerSeries ℝ :=
  ∑ j ∈ borderLengths w,PowerSeries.monomial (w.length-j)
    (2*((w.drop j).count true : ℝ)-(w.length-j : ℕ))

private noncomputable def realWordMoment (w : List Bool) : PowerSeries ℝ :=
  PowerSeries.monomial w.length (2*(w.count true : ℝ)-w.length)

private noncomputable def realDenominatorMoment (w : List Bool) : PowerSeries ℝ :=
  (1-realLetterSeries)*realOverlapMoment w+realWordMoment w

private theorem powerSeries_map_monomial {R T : Type*} [Semiring R] [Semiring T]
    (h : R →+* T) (n : ℕ) (a : R) :
    PowerSeries.map h (PowerSeries.monomial n a)=PowerSeries.monomial n (h a) := by
  exact MvPowerSeries.map_monomial h (Finsupp.single () n) a

private theorem realCountSeries_map (w : List Bool) :
    PowerSeries.map evalOneRealHom (avoidSeries w)=realCountSeries w := by
  apply PowerSeries.ext
  intro m
  simp [realCountSeries,avoidSeries,avoidCoeff,avoidCount,evalOneRealHom,
    Polynomial.eval_finsetSum]

private theorem realOverlapSeries_map (w : List Bool) :
    PowerSeries.map evalOneRealHom (overlapSeries w)=realOverlapSeries w := by
  unfold overlapSeries realOverlapSeries
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [powerSeries_map_monomial]
  simp [evalOneRealHom]

private theorem realWordMonomial_map (w : List Bool) :
    PowerSeries.map evalOneRealHom (wordMonomial w)=realWordMonomial w := by
  unfold wordMonomial realWordMonomial
  rw [powerSeries_map_monomial]
  simp [evalOneRealHom]

private theorem realLetterSeries_map :
    PowerSeries.map evalOneRealHom letterSeries=realLetterSeries := by
  simp [letterSeries,realLetterSeries,evalOneRealHom]
  apply PowerSeries.ext
  intro m
  simp [PowerSeries.coeff_C]
  split_ifs <;> norm_num

private theorem real_counting_identity {w : List Bool} (hw : w ≠ []) :
    realCountSeries w*realDenominator w=realOverlapSeries w := by
  have hh := congrArg (PowerSeries.map evalOneRealHom) (forbidden_word_counting_identity hw)
  unfold countingIdentity at hh
  simpa only [map_mul,map_add,map_sub,map_one,realCountSeries_map,
    realOverlapSeries_map,realWordMonomial_map,realLetterSeries_map,realDenominator] using hh

private theorem realImbalanceSeries_map (w : List Bool) :
    PowerSeries.map (Rat.castHom ℝ) (signedMoment (avoidSeries w))=realImbalanceSeries w := by
  apply PowerSeries.ext
  intro m
  simp [signedMoment,realImbalanceSeries,avoidSeries,avoidCoeff,avoidCount,avoidOnes,
    Polynomial.derivative_sum,Polynomial.derivative_X_pow,Polynomial.eval_finsetSum]

private theorem realOverlapMoment_map (w : List Bool) :
    PowerSeries.map (Rat.castHom ℝ) (signedMoment (overlapSeries w))=realOverlapMoment w := by
  unfold overlapSeries realOverlapMoment
  rw [signedMoment_sum,map_sum]
  apply sum_congr rfl
  intro j _
  rw [signedMoment_monomial,powerSeries_map_monomial]
  simp

private theorem realWordMoment_map (w : List Bool) :
    PowerSeries.map (Rat.castHom ℝ) (signedMoment (wordMonomial w))=realWordMoment w := by
  unfold wordMonomial realWordMoment
  rw [signedMoment_monomial,powerSeries_map_monomial]
  simp

private theorem realDenominatorMoment_map (w : List Bool) :
    PowerSeries.map (Rat.castHom ℝ) (signedMoment (avoidDenominator w))=realDenominatorMoment w := by
  unfold avoidDenominator realDenominatorMoment
  rw [signedMoment_add,signedMoment_mul,signedMoment_sub,signedMoment_one,signedMoment_letterSeries]
  simp only [sub_self,zero_mul,zero_add,map_add,map_mul,map_sub,map_one,map_zero,
    realOverlapMoment_map,realWordMoment_map]
  have he : PowerSeries.map (Rat.castHom ℝ) ((PowerSeries.map (Polynomial.evalRingHom 1)) letterSeries)=realLetterSeries := by
    have hh : PowerSeries.map (Rat.castHom ℝ) ((PowerSeries.map (Polynomial.evalRingHom 1)) letterSeries)=
        PowerSeries.map evalOneRealHom letterSeries := by
      apply PowerSeries.ext
      intro m
      simp [PowerSeries.coeff_map,evalOneRealHom]
    rw [hh,realLetterSeries_map]
  rw [he]

private theorem real_moment_identity {w : List Bool} (hw : w ≠ []) :
    realImbalanceSeries w*realDenominator w+
      realCountSeries w*realDenominatorMoment w=realOverlapMoment w := by
  have hc : avoidSeries w*avoidDenominator w=overlapSeries w := forbidden_word_counting_identity hw
  have hh := congrArg (PowerSeries.map (Rat.castHom ℝ)) (congrArg signedMoment hc)
  rw [signedMoment_mul] at hh
  have he (f : PowerSeries (Polynomial ℚ)) :
      PowerSeries.map (Rat.castHom ℝ) ((PowerSeries.map (Polynomial.evalRingHom 1)) f)=PowerSeries.map evalOneRealHom f := by
    apply PowerSeries.ext
    intro m
    simp [PowerSeries.coeff_map,evalOneRealHom]
  simp only [map_add,map_mul,he,realImbalanceSeries_map,realDenominatorMoment_map,
    realCountSeries_map,realOverlapMoment_map] at hh
  have hden : PowerSeries.map evalOneRealHom (avoidDenominator w)=realDenominator w := by
    simp [avoidDenominator,realDenominator,realLetterSeries_map,realOverlapSeries_map,realWordMonomial_map]
  rwa [hden] at hh

noncomputable def overlapEval (w : List Bool) (x : ℝ) : ℝ :=
  ∑ j ∈ borderLengths w,x^(w.length-j)

noncomputable def denomEval (w : List Bool) (x : ℝ) : ℝ :=
  (1-2*x)*overlapEval w x+x^w.length

noncomputable def overlapMomentEval (w : List Bool) (x : ℝ) : ℝ :=
  ∑ j ∈ borderLengths w,(2*((w.drop j).count true : ℝ)-(w.length-j : ℕ))*x^(w.length-j)

private theorem reciprocal_overlapMoment (w : List Bool) {z : ℝ} (hz : z≠0) :
    z^w.length*overlapMomentEval w (1/z)=
      (2*(w.count true:ℝ)-w.length)*corrEval w z-hEval w z := by
  rw [hEval_eq_border_sum]
  unfold overlapMomentEval corrEval
  rw [mul_sum,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have hjn := (mem_borderLengths.mp hj).2.1
  rw [tail_imbalance w hjn]
  have hp : z^w.length*(1/z)^(w.length-j)=z^j := by
    have hp : z^w.length=z^j*z^(w.length-j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp,one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hz),mul_one]
  calc
    _ = ((2*(w.count true:ℝ)-w.length)-(imbalance w j:ℝ))*
      (z^w.length*(1/z)^(w.length-j)) := by ring
    _ = _ := by rw [hp]; ring

noncomputable def denomMomentEval (w : List Bool) (x : ℝ) : ℝ :=
  (1-2*x)*overlapMomentEval w x+(2*(w.count true : ℝ)-w.length)*x^w.length

private theorem reciprocal_denomMoment_root (w : List Bool) {z : ℝ} (hz : z≠0)
    (hroot : (2-z)*corrEval w z=z) :
    z^(w.length+1)*denomMomentEval w (1/z)=(2-z)*hEval w z := by
  have hp : z^w.length*(1/z)^w.length=1 := by
    rw [one_div,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hz)]
  unfold denomMomentEval
  rw [pow_succ]
  calc
    _ = z*((1-2/z)*(z^w.length*overlapMomentEval w (1/z))+
      (2*(w.count true:ℝ)-w.length)*(z^w.length*(1/z)^w.length)) := by ring
    _ = _ := by
      rw [reciprocal_overlapMoment w hz,hp]
      have hc : (z-2)*corrEval w z+z=0 := by nlinarith
      calc
        _ = (2*(w.count true:ℝ)-w.length)*((z-2)*corrEval w z+z)+(2-z)*hEval w z := by
          field_simp
          <;> ring
        _ = _ := by rw [hc]; ring

theorem unbalanced_boundary_moment_ne_zero {w : List Bool} (hn : 3 ≤ w.length)
    (hnb : ¬ BalancedBorders w) {z : ℝ} (hz : 3/2 < z) (hz2 : z < 2)
    (hroot : (2-z)*corrEval w z=z) : denomMomentEval w (1/z)≠0 := by
  have hw : w≠[] := by intro h; simp [h] at hn
  have henv := root_equation_envelope hw (by linarith) hz2 hroot
  have hH := unbalanced_hEval_ne_zero hnb (by linarith) hz2 henv
  have he := reciprocal_denomMoment_root w (by linarith) hroot
  intro hzero
  rw [hzero,mul_zero] at he
  exact hH ((mul_eq_zero.mp he.symm).resolve_left (by linarith))

private theorem realLetterSeries_eq_monomial : realLetterSeries=PowerSeries.monomial 1 (2:ℝ) := by
  unfold realLetterSeries
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  simp [mul_comm]

private theorem seriesSummable_mul_denominator_form {ι : Type*} (S : Finset ι)
    (e : ι → ℕ) (a : ι → ℝ) (n : ℕ) (c : ℝ) {f : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) :
    SeriesSummable (f*((1-realLetterSeries)*finiteSeries S e a+PowerSeries.monomial n c)) x := by
  have hfL : SeriesSummable (f*realLetterSeries) x := by
    rw [realLetterSeries_eq_monomial]
    exact seriesSummable_mul_monomial hf 1 2
  have he : f*((1-realLetterSeries)*finiteSeries S e a+PowerSeries.monomial n c)=
      f*finiteSeries S e a-(f*realLetterSeries)*finiteSeries S e a+f*PowerSeries.monomial n c := by ring
  rw [he]
  exact seriesSummable_add (seriesSummable_sub (seriesSummable_mul_finite S e a hf)
    (seriesSummable_mul_finite S e a hfL)) (seriesSummable_mul_monomial hf n c)

private theorem seriesEval_mul_denominator_form {ι : Type*} (S : Finset ι)
    (e : ι → ℕ) (a : ι → ℝ) (n : ℕ) (c : ℝ) {f : PowerSeries ℝ} {x : ℝ}
    (hf : SeriesSummable f x) :
    seriesEval (f*((1-realLetterSeries)*finiteSeries S e a+PowerSeries.monomial n c)) x=
      seriesEval f x*((1-2*x)*(∑ i ∈ S,a i*x^(e i))+c*x^n) := by
  have hfL : SeriesSummable (f*realLetterSeries) x := by
    rw [realLetterSeries_eq_monomial]
    exact seriesSummable_mul_monomial hf 1 2
  have hL : seriesEval (f*realLetterSeries) x=seriesEval f x*(2*x) := by
    rw [realLetterSeries_eq_monomial,seriesEval_mul_monomial hf]
    simp
  have he : f*((1-realLetterSeries)*finiteSeries S e a+PowerSeries.monomial n c)=
      f*finiteSeries S e a-(f*realLetterSeries)*finiteSeries S e a+f*PowerSeries.monomial n c := by
    ring
  rw [he,seriesEval_add
    (seriesSummable_sub (seriesSummable_mul_finite S e a hf) (seriesSummable_mul_finite S e a hfL))
    (seriesSummable_mul_monomial hf n c),
    seriesEval_sub (seriesSummable_mul_finite S e a hf) (seriesSummable_mul_finite S e a hfL),
    seriesEval_mul_finite S e a hf,seriesEval_mul_finite S e a hfL,
    seriesEval_mul_monomial hf n c,hL]
  ring

private theorem seriesEval_mul_realDenominator {f : PowerSeries ℝ} {w : List Bool} {x : ℝ}
    (hf : SeriesSummable f x) :
    seriesEval (f*realDenominator w) x=seriesEval f x*denomEval w x := by
  simpa [realDenominator,realOverlapSeries,realWordMonomial,finiteSeries,denomEval,overlapEval]
    using seriesEval_mul_denominator_form (borderLengths w) (fun j => w.length-j)
      (fun _ => (1:ℝ)) w.length 1 hf

private theorem seriesEval_realOverlapSeries (w : List Bool) (x : ℝ) :
    seriesEval (realOverlapSeries w) x=overlapEval w x := by
  simpa [realOverlapSeries,finiteSeries,overlapEval,seriesEval_one]
    using seriesEval_mul_finite (borderLengths w) (fun j => w.length-j) (fun _ => (1:ℝ))
      (seriesSummable_one x)

private theorem realCountSeries_summable {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x<1) : SeriesSummable (realCountSeries w) x := by
  simpa [SeriesSummable,realCountSeries,PowerSeries.coeff_mk] using avoidCount_summable hw hx0 hx

theorem scalar_counting_identity {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x<1) :
    seriesEval (realCountSeries w) x*denomEval w x=overlapEval w x := by
  rw [← seriesEval_mul_realDenominator (realCountSeries_summable hw hx0 hx),
    real_counting_identity hw,seriesEval_realOverlapSeries]

noncomputable def lengthMoment (f : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.X * PowerSeries.derivative ℝ f

theorem coeff_lengthMoment (f : PowerSeries ℝ) (m : ℕ) :
    PowerSeries.coeff m (lengthMoment f)=(m:ℝ)*PowerSeries.coeff m f := by
  cases m with
  | zero => simp [lengthMoment]
  | succ m =>
    unfold lengthMoment
    rw [mul_comm,← pow_one (PowerSeries.X : PowerSeries ℝ),PowerSeries.coeff_mul_X_pow,
      PowerSeries.coeff_derivative]
    push_cast
    ring

private theorem lengthMoment_mul (f g : PowerSeries ℝ) :
    lengthMoment (f*g)=lengthMoment f*g+f*lengthMoment g := by
  unfold lengthMoment
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

private theorem lengthMoment_add (f g : PowerSeries ℝ) :
    lengthMoment (f+g)=lengthMoment f+lengthMoment g := by
  simp [lengthMoment,map_add,mul_add]

private theorem lengthMoment_sub (f g : PowerSeries ℝ) :
    lengthMoment (f-g)=lengthMoment f-lengthMoment g := by
  simp [lengthMoment,map_sub,mul_sub]

private theorem lengthMoment_one : lengthMoment 1=0 := by simp [lengthMoment,PowerSeries.derivative_one]

private theorem lengthMoment_monomial (n : ℕ) (a : ℝ) :
    lengthMoment (PowerSeries.monomial n a)=PowerSeries.monomial n ((n:ℝ)*a) := by
  apply PowerSeries.ext
  intro m
  rw [coeff_lengthMoment]
  simp only [PowerSeries.coeff_monomial]
  split_ifs with h
  · subst m; rfl
  · ring

private theorem lengthMoment_sum {ι : Type*} (S : Finset ι) (f : ι → PowerSeries ℝ) :
    lengthMoment (∑ i ∈ S,f i)=∑ i ∈ S,lengthMoment (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lengthMoment]
  | @insert i S hi ih => rw [sum_insert hi,lengthMoment_add,ih,sum_insert hi]

noncomputable def realLengthSeries (w : List Bool) : PowerSeries ℝ := lengthMoment (realCountSeries w)

noncomputable def overlapLengthEval (w : List Bool) (x : ℝ) : ℝ :=
  ∑ j ∈ borderLengths w,((w.length-j : ℕ):ℝ)*x^(w.length-j)

noncomputable def denomLengthEval (w : List Bool) (x : ℝ) : ℝ :=
  -2*x*overlapEval w x+(1-2*x)*overlapLengthEval w x+(w.length:ℝ)*x^w.length

private theorem real_length_identity {w : List Bool} (hw : w ≠ []) :
    realLengthSeries w*realDenominator w+
      realCountSeries w*lengthMoment (realDenominator w)=lengthMoment (realOverlapSeries w) := by
  simpa [lengthMoment_mul,realLengthSeries] using congrArg lengthMoment (real_counting_identity hw)

private theorem realLengthSeries_summable {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x < 1) : SeriesSummable (realLengthSeries w) x := by
  simpa [SeriesSummable,realLengthSeries,coeff_lengthMoment,realCountSeries]
    using weighted_avoidCount_summable hw 1 hx0 hx

private theorem seriesEval_mul_lengthOverlap {f : PowerSeries ℝ} {w : List Bool} {x : ℝ}
    (hf : SeriesSummable f x) :
    seriesEval (f*lengthMoment (realOverlapSeries w)) x=seriesEval f x*overlapLengthEval w x := by
  simp only [realOverlapSeries,lengthMoment_sum,lengthMoment_monomial,mul_one]
  exact seriesEval_mul_finite (borderLengths w) _ _ hf

private theorem seriesEval_lengthOverlap (w : List Bool) (x : ℝ) :
    seriesEval (lengthMoment (realOverlapSeries w)) x=overlapLengthEval w x := by
  simpa [seriesEval_one] using seriesEval_mul_lengthOverlap (w := w) (seriesSummable_one x)

private theorem seriesEval_mul_lengthDenominator {f : PowerSeries ℝ} {w : List Bool} {x : ℝ}
    (hf : SeriesSummable f x) :
    seriesEval (f*lengthMoment (realDenominator w)) x=seriesEval f x*denomLengthEval w x := by
  have hl : lengthMoment realLetterSeries=realLetterSeries := by
    rw [realLetterSeries_eq_monomial,lengthMoment_monomial]
    norm_num
  have he : f*lengthMoment (realDenominator w)=
      -(f*realLetterSeries)*realOverlapSeries w+
      (f-f*realLetterSeries)*lengthMoment (realOverlapSeries w)+
      f*PowerSeries.monomial w.length ((w.length:ℝ)*1) := by
    rw [realDenominator,lengthMoment_add,lengthMoment_mul,lengthMoment_sub,lengthMoment_one,
      hl,realWordMonomial,lengthMoment_monomial]
    ring
  have hfL : SeriesSummable (f*realLetterSeries) x := by
    rw [realLetterSeries_eq_monomial]
    exact seriesSummable_mul_monomial hf 1 2
  have hhL : seriesEval (f*realLetterSeries) x=seriesEval f x*(2*x) := by
    rw [realLetterSeries_eq_monomial,seriesEval_mul_monomial hf]
    simp
  have hfR : SeriesSummable ((f*realLetterSeries)*realOverlapSeries w) x :=
    seriesSummable_mul_finite _ _ _ hfL
  have hfsub := seriesSummable_sub hf hfL
  have hflR : SeriesSummable ((f-f*realLetterSeries)*lengthMoment (realOverlapSeries w)) x := by
    simp only [realOverlapSeries,lengthMoment_sum,lengthMoment_monomial,mul_one]
    exact seriesSummable_mul_finite _ _ _ hfsub
  rw [he,seriesEval_add (seriesSummable_add (by simpa [SeriesSummable] using hfR.neg) hflR)
    (seriesSummable_mul_monomial hf _ _),
    seriesEval_add (by simpa [SeriesSummable] using hfR.neg) hflR]
  have hneg : seriesEval (-((f*realLetterSeries)*realOverlapSeries w)) x=
      -seriesEval ((f*realLetterSeries)*realOverlapSeries w) x := by
    simp [seriesEval,tsum_neg]
  rw [neg_mul,hneg,seriesEval_mul_lengthOverlap hfsub,
    seriesEval_sub hf hfL,seriesEval_mul_monomial hf,hhL]
  rw [show realOverlapSeries w=finiteSeries (borderLengths w) (fun j => w.length-j) (fun _ => 1) by rfl,
    seriesEval_mul_finite _ _ _ hfL,hhL]
  simp only [one_mul,mul_one]
  unfold denomLengthEval overlapEval
  ring

private theorem seriesSummable_mul_lengthDenominator {f : PowerSeries ℝ} {w : List Bool} {x : ℝ}
    (hf : SeriesSummable f x) : SeriesSummable (f*lengthMoment (realDenominator w)) x := by
  have hl : lengthMoment realLetterSeries=realLetterSeries := by
    rw [realLetterSeries_eq_monomial,lengthMoment_monomial]
    norm_num
  have hfL : SeriesSummable (f*realLetterSeries) x := by
    rw [realLetterSeries_eq_monomial]
    exact seriesSummable_mul_monomial hf 1 2
  have he : f*lengthMoment (realDenominator w)=
      -(f*realLetterSeries)*realOverlapSeries w+
      (f-f*realLetterSeries)*lengthMoment (realOverlapSeries w)+
      f*PowerSeries.monomial w.length ((w.length:ℝ)*1) := by
    rw [realDenominator,lengthMoment_add,lengthMoment_mul,lengthMoment_sub,lengthMoment_one,
      hl,realWordMonomial,lengthMoment_monomial]
    ring
  rw [he]
  apply seriesSummable_add _ (seriesSummable_mul_monomial hf _ _)
  apply seriesSummable_add
  · rw [neg_mul]
    have hh : SeriesSummable ((f*realLetterSeries)*realOverlapSeries w) x :=
      seriesSummable_mul_finite _ _ _ hfL
    simpa [SeriesSummable] using hh.neg
  · simp only [realOverlapSeries,lengthMoment_sum,lengthMoment_monomial,mul_one]
    exact seriesSummable_mul_finite _ _ _ (seriesSummable_sub hf hfL)

theorem scalar_length_identity {w : List Bool} (hw : w≠[]) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x < 1) :
    seriesEval (realLengthSeries w) x*denomEval w x+
      seriesEval (realCountSeries w) x*denomLengthEval w x=overlapLengthEval w x := by
  have ha := realCountSeries_summable hw hx0 hx
  have hl := realLengthSeries_summable hw hx0 hx
  have he := congrArg (fun f => seriesEval f x) (real_length_identity hw)
  have hQ : SeriesSummable (realLengthSeries w*realDenominator w) x :=
    seriesSummable_mul_denominator_form _ _ _ _ _ hl
  have hU : SeriesSummable (realCountSeries w*lengthMoment (realDenominator w)) x :=
    seriesSummable_mul_lengthDenominator ha
  rw [seriesEval_add hQ hU,seriesEval_mul_realDenominator hl,
    seriesEval_mul_lengthDenominator ha,seriesEval_lengthOverlap] at he
  exact he

private theorem realImbalanceSeries_summable {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x < 1) : SeriesSummable (realImbalanceSeries w) x := by
  apply Summable.of_norm_bounded (weighted_avoidCount_summable hw 1 hx0 hx)
  intro m
  have hb := avoidOnes_bounds w m
  have ha : 0 ≤ (m:ℝ)*avoidCount w m :=
    mul_nonneg (Nat.cast_nonneg m) (avoidCount_pos hw m).le
  simp only [realImbalanceSeries,PowerSeries.coeff_mk,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (pow_nonneg hx0 m)]
  simp only [pow_one]
  gcongr
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem seriesEval_mul_realDenominatorMoment {f : PowerSeries ℝ} {w : List Bool} {x : ℝ}
    (hf : SeriesSummable f x) :
    seriesEval (f*realDenominatorMoment w) x=seriesEval f x*denomMomentEval w x := by
  exact seriesEval_mul_denominator_form (borderLengths w) (fun j => w.length-j)
    (fun j => 2*((w.drop j).count true:ℝ)-(w.length-j:ℕ))
    w.length (2*(w.count true:ℝ)-w.length) hf

private theorem seriesEval_realOverlapMoment (w : List Bool) (x : ℝ) :
    seriesEval (realOverlapMoment w) x=overlapMomentEval w x := by
  simpa [seriesEval_one,realOverlapMoment,overlapMomentEval,finiteSeries] using
    seriesEval_mul_finite (borderLengths w) (fun j => w.length-j)
      (fun j => 2*((w.drop j).count true:ℝ)-(w.length-j:ℕ)) (seriesSummable_one x)

theorem scalar_moment_identity {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x < 1) :
    seriesEval (realImbalanceSeries w) x*denomEval w x+
      seriesEval (realCountSeries w) x*denomMomentEval w x=overlapMomentEval w x := by
  have ha := realCountSeries_summable hw hx0 hx
  have hs := realImbalanceSeries_summable hw hx0 hx
  have he := congrArg (fun f => seriesEval f x) (real_moment_identity hw)
  have hQ : SeriesSummable (realImbalanceSeries w*realDenominator w) x :=
    seriesSummable_mul_denominator_form _ _ _ _ _ hs
  have hT : SeriesSummable (realCountSeries w*realDenominatorMoment w) x :=
    seriesSummable_mul_denominator_form _ _ _ _ _ ha
  rw [seriesEval_add hQ hT,
    seriesEval_mul_realDenominator hs,seriesEval_mul_realDenominatorMoment ha,
    seriesEval_realOverlapMoment] at he
  exact he

private noncomputable def rootPolyEval (w : List Bool) (x : ℝ) : ℝ := (2-x)*corrEval w x-x

private theorem rootPolyEval_continuous (w : List Bool) : Continuous (rootPolyEval w) := by
  unfold rootPolyEval corrEval
  fun_prop

private theorem rootPolyEval_three_halves_pos {w : List Bool} (hn : 3 ≤ w.length) :
    0 < rootPolyEval w (3/2) := by
  have hw : w ≠ [] := by intro h; simp [h] at hn
  have hC := corrEval_ge_full hw (by norm_num : (0:ℝ) ≤ 3/2)
  have hpow : (3/2:ℝ)^3 ≤ (3/2:ℝ)^w.length :=
    pow_le_pow_right₀ (by norm_num) hn
  unfold rootPolyEval
  norm_num at hC hpow ⊢
  linarith

private theorem root_exists_three_halves_two {w : List Bool} (hn : 3 ≤ w.length) :
    ∃ x : ℝ, 3/2 < x ∧ x < 2 ∧ (2-x)*corrEval w x=x := by
  have hl := rootPolyEval_three_halves_pos hn
  have hr : rootPolyEval w 2 < 0 := by simp [rootPolyEval]
  have hz : (0:ℝ) ∈ Icc (rootPolyEval w 2) (rootPolyEval w (3/2)) := ⟨hr.le,hl.le⟩
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc' (by norm_num : (3/2:ℝ) ≤ 2)
    (rootPolyEval_continuous w).continuousOn hz
  refine ⟨x,?_,?_,?_⟩
  · by_contra! hnlt
    have he : x=3/2 := le_antisymm hnlt hx.1
    have hh : rootPolyEval w (3/2)=0 := by simpa [he] using hzero
    linarith
  · by_contra! hnlt
    have he : x=2 := le_antisymm hx.2 hnlt
    have hh : rootPolyEval w 2=0 := by simpa [he] using hzero
    linarith
  · unfold rootPolyEval at hzero
    linarith

noncomputable def growthApproach (w : List Bool) (hw : w ≠ []) (m : ℕ) : ℝ :=
  (1-1/((m:ℝ)+2))/growthRate w hw

theorem growthApproach_pos {w : List Bool} (hw : w ≠ []) (m : ℕ) : 0 < growthApproach w hw m := by
  have hd : (0:ℝ)<(m:ℝ)+2 := by positivity
  have hf : 1/((m:ℝ)+2)<1 := (div_lt_one hd).mpr (by have hm:=Nat.cast_nonneg (α:=ℝ) m; linarith)
  exact div_pos (by linarith) (Real.exp_pos _)

private theorem growthApproach_product {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    growthRate w hw*growthApproach w hw m=1-1/((m:ℝ)+2) := by
  unfold growthApproach
  field_simp [show growthRate w hw ≠ 0 from Real.exp_ne_zero _]

theorem growthApproach_inside {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    growthRate w hw*growthApproach w hw m<1 := by
  rw [growthApproach_product]
  have hh : (0:ℝ)<1/((m:ℝ)+2) := by positivity
  linarith

theorem growthApproach_tendsto {w : List Bool} (hw : w ≠ []) :
    Tendsto (growthApproach w hw) atTop (𝓝 (1/growthRate w hw)) := by
  have hi : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun m : ℕ => (1:ℝ)/(m:ℝ)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 2)
    simpa [Function.comp_def] using hh
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := (hc.sub hi).div_const (growthRate w hw)
  change Tendsto (fun m : ℕ => (1-1/((m:ℝ)+2))/growthRate w hw) atTop (𝓝 (1/growthRate w hw))
  simpa using hh

theorem overlapEval_ge_one {w : List Bool} (hw : w ≠ []) {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ overlapEval w x := by
  have hh := single_le_sum (fun j _ => pow_nonneg hx (w.length-j)) (full_mem_borderLengths hw)
  simpa [overlapEval] using hh

private theorem overlapEval_continuous (w : List Bool) : Continuous (overlapEval w) := by
  unfold overlapEval
  fun_prop

private theorem denomEval_continuous (w : List Bool) : Continuous (denomEval w) := by
  unfold denomEval overlapEval
  fun_prop

private theorem countSeriesEval_ge_geometric {w : List Bool} (hw : w ≠ []) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : growthRate w hw*x<1) :
    (1-growthRate w hw*x)⁻¹ ≤ seriesEval (realCountSeries w) x := by
  have hr0 : 0 ≤ growthRate w hw*x := mul_nonneg (Real.exp_pos _).le hx0
  have hgeo := summable_geometric_of_lt_one hr0 hx
  have hcount := avoidCount_summable hw hx0 hx
  rw [← tsum_geometric_of_lt_one hr0 hx]
  unfold seriesEval realCountSeries
  simp only [PowerSeries.coeff_mk]
  apply Summable.tsum_le_tsum _ hgeo hcount
  intro m
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (growthRate_lower_power hw m) (pow_nonneg hx0 m)

theorem countSeriesEval_growthApproach {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    (m:ℝ)+2 ≤ seriesEval (realCountSeries w) (growthApproach w hw m) := by
  have hh := countSeriesEval_ge_geometric hw (growthApproach_pos hw m).le (growthApproach_inside hw m)
  rw [growthApproach_product] at hh
  simpa using hh

private theorem denomEval_growthApproach_bound {w : List Bool} (hw : w ≠ []) (m : ℕ) :
    0 ≤ denomEval w (growthApproach w hw m) ∧
      denomEval w (growthApproach w hw m) ≤ overlapEval w (growthApproach w hw m)/((m:ℝ)+2) := by
  have hcount := countSeriesEval_growthApproach hw m
  have hId := scalar_counting_identity hw (growthApproach_pos hw m).le (growthApproach_inside hw m)
  have hR := overlapEval_ge_one hw (growthApproach_pos hw m).le
  have hA : 0 < seriesEval (realCountSeries w) (growthApproach w hw m) := by
    have hm:=Nat.cast_nonneg (α:=ℝ) m
    linarith
  have hQ : 0 ≤ denomEval w (growthApproach w hw m) := by nlinarith
  refine ⟨hQ,?_⟩
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(m:ℝ)+2)).mpr
  nlinarith

theorem growthRadius_denominator_zero {w : List Bool} (hw : w ≠ []) :
    denomEval w (1/growthRate w hw)=0 := by
  have hR := (overlapEval_continuous w).tendsto (1/growthRate w hw) |>.comp (growthApproach_tendsto hw)
  have hd : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop := tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hupper := hR.div_atTop hd
  have hz : Tendsto (fun m => denomEval w (growthApproach w hw m)) atTop (𝓝 (0:ℝ)) :=
    squeeze_zero (fun m => (denomEval_growthApproach_bound hw m).1)
      (fun m => (denomEval_growthApproach_bound hw m).2) hupper
  have hc := (denomEval_continuous w).tendsto (1/growthRate w hw) |>.comp (growthApproach_tendsto hw)
  exact (tendsto_nhds_unique hz hc).symm

private theorem corrEval_reciprocal_overlap (w : List Bool) {x : ℝ} (hx : x≠0) :
    x^w.length*overlapEval w (1/x)=corrEval w x := by
  unfold overlapEval corrEval
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn := (mem_borderLengths.mp hj).2.1
  have hp : x^w.length=x^j*x^(w.length-j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp,one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hx),mul_one]

private theorem reciprocal_denom_cross (w : List Bool) {x : ℝ} (hx : x≠0) :
    x^(w.length+1)*denomEval w (1/x)=(x-2)*corrEval w x+x := by
  have hpow : x^w.length*(1/x)^w.length=1 := by
    rw [one_div,inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hx)]
  unfold denomEval
  rw [pow_succ]
  calc
    _ = x*((1-2*(1/x))*(x^w.length*overlapEval w (1/x))+x^w.length*(1/x)^w.length) := by ring
    _ = _ := by
      rw [corrEval_reciprocal_overlap w hx,hpow]
      field_simp <;> ring

private theorem reciprocal_denom_zero_iff (w : List Bool) {x : ℝ} (hx : x≠0) :
    denomEval w (1/x)=0 ↔ (2-x)*corrEval w x=x := by
  have he := reciprocal_denom_cross w hx
  constructor
  · intro h
    rw [h,mul_zero] at he
    nlinarith
  · intro h
    have hz : (x-2)*corrEval w x+x=0 := by nlinarith
    rw [hz] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hx)

theorem growthRate_root {w : List Bool} (hw : w ≠ []) :
    (2-growthRate w hw)*corrEval w (growthRate w hw)=growthRate w hw :=
  (reciprocal_denom_zero_iff w (ne_of_gt (Real.exp_pos _))).mp (growthRadius_denominator_zero hw)

theorem growthRate_gt_three_halves {w : List Bool} (hn : 3 ≤ w.length)
    (hw : w ≠ []) : 3/2 < growthRate w hw := by
  obtain ⟨t,htlo,hthi,htroot⟩ := root_exists_three_halves_two hn
  have htpos : 0 < t := by linarith
  have htr := (reciprocal_denom_zero_iff w htpos.ne').mpr htroot
  have htbound : t ≤ growthRate w hw := by
    by_contra! hlt
    have hinside : growthRate w hw*(1/t)<1 := by
      rw [mul_one_div]
      exact (div_lt_one htpos).mpr hlt
    have hc := scalar_counting_identity hw (by positivity : (0:ℝ) ≤ 1/t) hinside
    rw [htr,mul_zero] at hc
    have hR := overlapEval_ge_one hw (by positivity : (0:ℝ) ≤ 1/t)
    linarith
  exact htlo.trans_le htbound

end D5.S1.Words.Forbidden.ForbiddenWordRationalBoundary

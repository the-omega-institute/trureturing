/- GID: D5/S1/Words/Forbidden/BalancedBordersHalfFrequency
   generality: G
   mirror-B: D5/B/S1/Words/Forbidden/BalancedBordersHalfFrequency
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Balanced borders force exact half frequency; short unbalanced words exclude it. -/
/-
proof_shape: rho_nonneg: bind-only; consumer: signedDensity_bound
proof_shape: rho_le_one: bind-only; consumer: signedDensity_bound
proof_shape: omega_singleton: bind-only; consumer: rho_singleton
proof_shape: rho_singleton: bind-only; consumer: singleton_not_tendsto_half
proof_shape: singleton_not_tendsto_half: bind-only; consumer: result
proof_shape: flip_mem_omega: bind-only; consumer: flip_rho_complement
proof_shape: flip_rho_complement: bind-only; consumer: flip_tendsto_half_iff
proof_shape: flip_tendsto_half_iff: bind-only; consumer: not_tendsto_half_00
proof_shape: avoid11_false_cons: bind-only; consumer: omega11_rec
proof_shape: omega11_rec: bind-only; consumer: avoidCoeff11_rec, onesTotal11_rec
proof_shape: avoidCoeff_eval_one: bind-only; consumer: avoidCard11_rec
proof_shape: omega11_rec_disjoint: bind-only; consumer: avoidCoeff11_rec
proof_shape: avoidCoeff11_rec: bind-only; consumer: avoidCard11_rec
proof_shape: avoidCard11_rec: bind-only; consumer: onesTotal11_bound
proof_shape: onesTotal11_rec: bind-only; consumer: onesTotal11_bound
proof_shape: avoidCard11_monotone: content
proof_shape: onesTotal11_bound: content
proof_shape: rho11_le_third: bind-only; consumer: not_tendsto_half_11
proof_shape: not_tendsto_half_11: bind-only; consumer: not_tendsto_half_00
proof_shape: coeff_evalAtOne: bind-only; consumer: signedMoment_mul
proof_shape: signedMoment_add: bind-only; consumer: signedMoment_sub
proof_shape: signedMoment_neg: bind-only; consumer: signedMoment_sub
proof_shape: signedMoment_sub: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: signedMoment_mul: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: signedMoment_one: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: signedMoment_monomial: bind-only; consumer: balanced_signedMoment_overlap
proof_shape: signedMoment_letterSeries: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: signedMoment_zero: bind-only; consumer: signedMoment_sum
proof_shape: signedMoment_sum: bind-only; consumer: balanced_signedMoment_overlap
proof_shape: balanced_tail: bind-only; consumer: balanced_signedMoment_overlap
proof_shape: balanced_signedMoment_overlap: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: balanced_signedMoment_word: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: overlap_constantCoeff: bind-only; consumer: avoidDenominator_eval_ne_zero
proof_shape: avoidDenominator_eval_ne_zero: bind-only; consumer: balanced_signedMoment_avoidSeries
proof_shape: balanced_signedMoment_avoidSeries: content
proof_shape: balanced_rho_eq_half: bind-only; consumer: balanced_tendsto_half
proof_shape: balanced_tendsto_half: bind-only; consumer: result
Classification totals: 3 content, 34 bind-only.
escape_witness: onesTotal11_bound on result's live proof path.
admission_basis: escape-witness
Direct frozen dependencies: none on the protected baseline.
Same-delivery dependencies: ForbiddenWordGrowth, BorderImbalanceExclusion.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Words.Forbidden.ForbiddenWordGrowth
import D5.S1.Words.Forbidden.BorderImbalanceExclusion

open Filter Finset
open scoped Topology

namespace D5.S1.Words.Forbidden.BalancedBordersHalfFrequency
open D5.S1.Words.Forbidden.ForbiddenWordCounting
open D5.S1.Words.Forbidden.ForbiddenWordGrowth
open D5.S1.Words.Forbidden.BorderImbalanceExclusion

theorem rho_nonneg (w : List Bool) (m : ℕ) : 0 ≤ rho w m := by
  unfold rho
  exact div_nonneg (avoidOnes_bounds w m).1
    (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg _))

theorem rho_le_one {w : List Bool} (hw : w ≠ []) {m : ℕ} (hm : 0 < m) :
    rho w m ≤ 1 := by
  have hc : 0 < (omega w m).card := card_pos.mpr (omega_nonempty hw m)
  have hden : 0 < (m : ℝ) * (omega w m).card := by positivity
  unfold rho
  apply (div_le_one hden).mpr
  simpa only [avoidOnes, avoidCount] using (avoidOnes_bounds w m).2

private theorem omega_singleton (b : Bool) (m : ℕ) :
    omega [b] m = {List.replicate m (!b)} := by
  ext u
  rw [mem_omega, mem_singleton]
  constructor
  · rintro ⟨hlen, havoid⟩
    rw [List.singleton_infix_iff] at havoid
    apply (List.eq_replicate_iff).mpr
    refine ⟨hlen, ?_⟩
    intro a ha
    cases b <;> cases a <;> simp_all
  · rintro rfl
    refine ⟨by simp, ?_⟩
    rw [List.singleton_infix_iff]
    cases b <;> simp

private theorem rho_singleton {b : Bool} {m : ℕ} (hm : 0 < m) :
    rho [b] m = if b then 0 else 1 := by
  unfold rho
  rw [omega_singleton]
  cases b <;> simp [List.count_replicate, (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]

theorem singleton_not_tendsto_half (b : Bool) :
    ¬ Tendsto (rho [b]) atTop (𝓝 (1 / 2 : ℝ)) := by
  intro h
  have ht : Tendsto (rho [b]) atTop (𝓝 (if b then 0 else 1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact (rho_singleton hm).symm
  have heq := tendsto_nhds_unique h ht
  cases b <;> norm_num at heq

private theorem flip_mem_omega {w u : List Bool} {m : ℕ} :
    u ∈ omega w m ↔ (List.map Bool.not) u ∈ omega ((List.map Bool.not) w) m := by
  simp only [mem_omega,flip_infix_iff]
  simp []

private theorem flip_rho_complement {w : List Bool} (hw : w≠[]) {m : ℕ} (hm : 0 < m) :
    rho ((List.map Bool.not) w) m=1-rho w m := by
  have hcard : (omega ((List.map Bool.not) w) m).card=(omega w m).card := by
    have he : omega ((List.map Bool.not) w) m=(omega w m).image (List.map Bool.not) := by
      ext u
      constructor
      · intro hu
        refine mem_image.mpr ⟨(List.map Bool.not) u,?_,D5.S1.Words.Forbidden.BorderImbalanceExclusion.flip_flip u⟩
        simpa only [D5.S1.Words.Forbidden.BorderImbalanceExclusion.flip_flip] using (flip_mem_omega (w := (List.map Bool.not) w) (u := u)).mp hu
      · intro hu
        obtain ⟨v,hv,he⟩ := mem_image.mp hu
        rw [← he]
        exact flip_mem_omega.mp hv
    rw [he,card_image_of_injective _ (Function.Involutive.injective D5.S1.Words.Forbidden.BorderImbalanceExclusion.flip_flip)]
  have hsum : (∑ u ∈ omega ((List.map Bool.not) w) m,(u.count true:ℝ))=
      ∑ u ∈ omega w m,(((List.map Bool.not) u).count true:ℝ) := by
    symm
    apply sum_bijective (List.map Bool.not) (Function.Involutive.bijective D5.S1.Words.Forbidden.BorderImbalanceExclusion.flip_flip)
    · exact fun u => flip_mem_omega
    · intro u _; rfl
  have hcomp : (∑ u ∈ omega ((List.map Bool.not) w) m,(u.count true:ℝ))+
      (∑ u ∈ omega w m,(u.count true:ℝ))=(m:ℝ)*(omega w m).card := by
    rw [hsum,← sum_add_distrib]
    calc
      _ = ∑ u ∈ omega w m,(m:ℝ) := by
        apply sum_congr rfl
        intro u hu
        have hc := List.count_false_add_count_true u
        rw [← count_flip u] at hc
        have hl := (mem_omega.mp hu).1
        exact_mod_cast hc.trans hl
      _ = _ := by simp [mul_comm]
  have hd : (m:ℝ)*(omega w m).card ≠ 0 := by
    exact ne_of_gt (mul_pos (by positivity) (by exact_mod_cast card_pos.mpr (omega_nonempty hw m)))
  unfold rho
  rw [hcard]
  have hc : ((omega w m).card:ℝ)≠0 := by exact_mod_cast (card_pos.mpr (omega_nonempty hw m)).ne'
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp [hc,hmR]
  linarith

theorem flip_tendsto_half_iff {w : List Bool} (hw : w≠[]) :
    Tendsto (rho ((List.map Bool.not) w)) atTop (𝓝 (1/2:ℝ)) ↔ Tendsto (rho w) atTop (𝓝 (1/2:ℝ)) := by
  have hforward {v : List Bool} (hv : v≠[])
      (hh : Tendsto (rho v) atTop (𝓝 (1/2:ℝ))) :
      Tendsto (rho ((List.map Bool.not) v)) atTop (𝓝 (1/2:ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have ht := hc.sub hh
    norm_num at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    exact (flip_rho_complement hv hm).symm
  constructor
  · intro hh
    have hf : (List.map Bool.not) w≠[] := by simpa [] using hw
    simpa only [D5.S1.Words.Forbidden.BorderImbalanceExclusion.flip_flip] using hforward hf hh
  · exact hforward hw

private theorem avoid11_false_cons (u : List Bool) :
    ¬ [true,true] <:+: false::u ↔ ¬ [true,true] <:+: u := by
  rw [List.infix_cons_iff]
  simp

private theorem omega11_rec (m : ℕ) :
    omega [true,true] (m+2) =
      (omega [true,true] (m+1)).image (false::·) ∪
        (omega [true,true] m).image (fun u => true::false::u) := by
  ext u
  cases u with
  | nil => simp [mem_omega]
  | cons b u =>
    cases b with
    | false => simp [mem_omega,avoid11_false_cons]
    | true =>
      cases u with
      | nil => simp [mem_omega]
      | cons c u =>
        cases c <;> simp [mem_omega,List.infix_cons_iff]

private theorem avoidCoeff_eval_one (w : List Bool) (m : ℕ) :
    (avoidCoeff w m).eval 1 = ((omega w m).card : ℚ) := by
  classical
  simp [avoidCoeff,Polynomial.eval_finset_sum]

private theorem omega11_rec_disjoint (m : ℕ) :
    Disjoint ((omega [true,true] (m+1)).image (false::·))
      ((omega [true,true] m).image (fun u => true::false::u)) := by
  rw [disjoint_left]
  intro u hf ht
  obtain ⟨v,_,rfl⟩ := mem_image.mp hf
  obtain ⟨v',_,he⟩ := mem_image.mp ht
  simp at he

private theorem avoidCoeff11_rec (m : ℕ) :
    avoidCoeff [true,true] (m+2)=avoidCoeff [true,true] (m+1)+Polynomial.X*avoidCoeff [true,true] m := by
  classical
  unfold avoidCoeff
  rw [omega11_rec,sum_union (omega11_rec_disjoint m)]
  rw [sum_image (fun a _ b _ h => by simpa using h),
    sum_image (fun a _ b _ h => by simpa using h)]
  simp [List.count_cons,pow_succ,mul_sum,mul_comm]

private theorem avoidCard11_rec (m : ℕ) :
    avoidCount [true,true] (m+2)=avoidCount [true,true] (m+1)+avoidCount [true,true] m := by
  have hh := congrArg (Polynomial.eval 1) (avoidCoeff11_rec m)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,one_mul,
    avoidCoeff_eval_one] at hh
  unfold avoidCount
  exact_mod_cast hh

private theorem onesTotal11_rec (m : ℕ) :
    avoidOnes [true,true] (m+2)=avoidOnes [true,true] (m+1)+
      avoidOnes [true,true] m+avoidCount [true,true] m := by
  classical
  unfold avoidOnes
  rw [omega11_rec,sum_union (omega11_rec_disjoint m)]
  rw [sum_image (fun a _ b _ h => by simpa using h),
    sum_image (fun a _ b _ h => by simpa using h)]
  simp [List.count_cons,sum_add_distrib,avoidCount,add_comm,add_left_comm,add_assoc]

private theorem avoidCard11_monotone (m : ℕ) : avoidCount [true,true] m ≤ avoidCount [true,true] (m+1) := by
  have hh : (omega [true,true] m).card ≤ (omega [true,true] (m+1)).card := by
    apply card_le_card_of_injOn (false::·)
    · intro u hu
      obtain ⟨hlen,ha⟩ := mem_omega.mp hu
      exact mem_omega.mpr ⟨by simp [hlen],avoid11_false_cons u |>.mpr ha⟩
    · intro u _ v _ he
      simpa using he
  unfold avoidCount
  exact_mod_cast hh

theorem onesTotal11_bound (k : ℕ) :
    3*avoidOnes [true,true] (k+2) ≤ ((k+2:ℕ):ℝ)*avoidCount [true,true] (k+2) ∧
    3*avoidOnes [true,true] (k+3) ≤ ((k+3:ℕ):ℝ)*avoidCount [true,true] (k+3) := by
  induction k with
  | zero =>
    have h2 : omega [true,true] 2={[false,false],[false,true],[true,false]} := by decide
    have h3 : omega [true,true] 3={[false,false,false],[false,false,true],[false,true,false],
      [true,false,false],[true,false,true]} := by decide
    norm_num [avoidOnes,avoidCount,h2,h3]
  | succ k ih =>
    constructor
    · simpa [Nat.add_assoc] using ih.2
    · have ha := avoidCard11_rec (k+2)
      have hb := onesTotal11_rec (k+2)
      have hm := avoidCard11_monotone (k+2)
      have he : k+1+3=(k+2)+2 := by omega
      rw [he,ha,hb]
      push_cast at *
      nlinarith [ih.1,ih.2]

private theorem rho11_le_third {m : ℕ} (hm : 2 ≤ m) : rho [true,true] m ≤ 1/3 := by
  have hb := (onesTotal11_bound (m-2)).1
  have he : m-2+2=m := by omega
  rw [he] at hb
  have hcard : 0 < (omega [true,true] m).card := card_pos.mpr (omega_nonempty (by simp) m)
  have hden : 0 < (m:ℝ)*(omega [true,true] m).card := by positivity
  unfold rho
  apply (div_le_iff₀ hden).mpr
  unfold avoidOnes avoidCount at hb
  linarith

theorem not_tendsto_half_11 : ¬ Tendsto (rho [true,true]) atTop (𝓝 (1/2:ℝ)) := by
  intro h
  have hh : (1/2:ℝ) ≤ 1/3 := le_of_tendsto h (by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with m hm
    exact rho11_le_third hm)
  norm_num at hh


noncomputable def signedMoment (f : PowerSeries (Polynomial ℚ)) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    2 * (PowerSeries.coeff n f).derivative.eval 1 - (n : ℚ) * (PowerSeries.coeff n f).eval 1

private theorem coeff_evalAtOne (f : PowerSeries (Polynomial ℚ)) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.map (Polynomial.evalRingHom 1)) f) = (PowerSeries.coeff n f).eval 1 := by
  simp []

theorem signedMoment_add (f g : PowerSeries (Polynomial ℚ)) :
    signedMoment (f+g) = signedMoment f + signedMoment g := by
  ext n
  simp [signedMoment,Polynomial.derivative_add,Polynomial.eval_add]
  ring

private theorem signedMoment_neg (f : PowerSeries (Polynomial ℚ)) :
    signedMoment (-f) = -signedMoment f := by
  ext n
  simp [signedMoment,Polynomial.derivative_neg,Polynomial.eval_neg]
  ring

theorem signedMoment_sub (f g : PowerSeries (Polynomial ℚ)) :
    signedMoment (f-g) = signedMoment f - signedMoment g := by
  rw [sub_eq_add_neg,signedMoment_add,signedMoment_neg,sub_eq_add_neg]

theorem signedMoment_mul (f g : PowerSeries (Polynomial ℚ)) :
    signedMoment (f*g) = signedMoment f * (PowerSeries.map (Polynomial.evalRingHom 1)) g + (PowerSeries.map (Polynomial.evalRingHom 1)) f * signedMoment g := by
  ext n
  simp only [signedMoment,PowerSeries.coeff_mk,map_add,PowerSeries.coeff_mul,
    Polynomial.derivative_sum,Polynomial.eval_finset_sum,Polynomial.derivative_mul,
    Polynomial.eval_add,Polynomial.eval_mul,coeff_evalAtOne,mul_sum,sum_sub_distrib]
  rw [← sum_add_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hn : p.1+p.2=n := mem_antidiagonal.mp hp
  have hc : (p.1 : ℚ)+(p.2 : ℚ)=(n : ℚ) := by exact_mod_cast hn
  rw [← hc]
  ring

theorem signedMoment_one : signedMoment 1 = 0 := by
  ext n
  cases n <;> simp [signedMoment,PowerSeries.coeff_one]

theorem signedMoment_monomial (n k : ℕ) :
    signedMoment (PowerSeries.monomial n (Polynomial.X^k)) =
      PowerSeries.monomial n ((2*k:ℚ)-n) := by
  ext m
  by_cases hm : m=n
  · subst m
    simp [signedMoment,PowerSeries.coeff_monomial,Polynomial.derivative_X_pow]
  · simp [signedMoment,PowerSeries.coeff_monomial,hm]

theorem signedMoment_letterSeries : signedMoment letterSeries = 0 := by
  ext n
  cases n with
  | zero => simp [signedMoment,letterSeries]
  | succ n =>
    cases n <;> norm_num [signedMoment,letterSeries,PowerSeries.coeff_succ_X_mul,
      Polynomial.derivative_add]

private theorem signedMoment_zero : signedMoment 0=0 := by
  ext n
  simp [signedMoment]

theorem signedMoment_sum {ι : Type*} (S : Finset ι)
    (f : ι → PowerSeries (Polynomial ℚ)) :
    signedMoment (∑ i ∈ S, f i) = ∑ i ∈ S, signedMoment (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [signedMoment_zero]
  | @insert i S hi ih => simp [hi,signedMoment_add,ih]

private theorem balanced_tail {w : List Bool} (hw0 : w ≠ []) (hw : BalancedBorders w)
    {j : ℕ} (hj : j ∈ borderLengths w) :
    2*(w.drop j).count true = w.length-j := by
  have hn := hw w (self_border hw0)
  have hb := hw (w.take j) (borderLengths_iff_border.mpr ⟨j,hj,rfl⟩)
  have hlen := List.length_take_of_le (mem_borderLengths.mp hj).2.1
  have he := congrArg (fun u : List Bool => u.count true) (List.take_append_drop j w)
  rw [List.count_append] at he
  omega

private theorem balanced_signedMoment_overlap {w : List Bool} (hw0 : w ≠ [])
    (hw : BalancedBorders w) : signedMoment (overlapSeries w)=0 := by
  unfold overlapSeries
  rw [signedMoment_sum]
  apply sum_eq_zero
  intro j hj
  rw [signedMoment_monomial]
  have hn := balanced_tail hw0 hw hj
  have hcast : (2*((w.drop j).count true : ℚ)) = ((w.length-j : ℕ):ℚ) := by exact_mod_cast hn
  simp only [hcast,sub_self,map_zero]

private theorem balanced_signedMoment_word {w : List Bool} (hw0 : w ≠ [])
    (hw : BalancedBorders w) : signedMoment (wordMonomial w)=0 := by
  unfold wordMonomial
  rw [signedMoment_monomial]
  have hn := hw w (self_border hw0)
  have hcast : (2*(w.count true : ℚ)) = (w.length : ℚ) := by exact_mod_cast hn
  simp [hcast]

noncomputable def avoidDenominator (w : List Bool) : PowerSeries (Polynomial ℚ) :=
  (1-letterSeries)*overlapSeries w+wordMonomial w

private theorem overlap_constantCoeff {w : List Bool} (hw : w ≠ []) :
    PowerSeries.constantCoeff (overlapSeries w)=1 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold overlapSeries
  rw [map_sum,sum_eq_single w.length]
  · simp [PowerSeries.coeff_monomial]
  · intro j hj hne
    have hjn := (mem_borderLengths.mp hj).2.1
    have hn : (0:ℕ) ≠ w.length-j := by omega
    simp [PowerSeries.coeff_monomial,hn]
  · intro hnot
    exact False.elim (hnot (full_mem_borderLengths hw))

private theorem avoidDenominator_eval_ne_zero {w : List Bool} (hw : w ≠ []) :
    (PowerSeries.map (Polynomial.evalRingHom 1)) (avoidDenominator w) ≠ 0 := by
  have hconst : PowerSeries.constantCoeff (avoidDenominator w)=1 := by
    have hn : w.length ≠ 0 := (List.length_pos_iff.mpr hw).ne'
    have hwm : PowerSeries.constantCoeff (wordMonomial w)=0 := by
      rw [wordMonomial,← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_monomial,if_neg (by omega)]
    unfold avoidDenominator
    rw [map_add,map_mul,map_sub,map_one,overlap_constantCoeff hw,hwm]
    simp [letterSeries]
  intro hz
  have hh := congrArg (PowerSeries.coeff 0) hz
  rw [coeff_evalAtOne,PowerSeries.coeff_zero_eq_constantCoeff_apply,hconst] at hh
  norm_num at hh

theorem balanced_signedMoment_avoidSeries {w : List Bool} (hw0 : w ≠ [])
    (hw : BalancedBorders w) : signedMoment (avoidSeries w)=0 := by
  have hden : signedMoment (avoidDenominator w)=0 := by
    unfold avoidDenominator
    rw [signedMoment_add,signedMoment_mul,signedMoment_sub,signedMoment_one,
      signedMoment_letterSeries,balanced_signedMoment_overlap hw0 hw,
      balanced_signedMoment_word hw0 hw]
    ring
  have hcount : avoidSeries w*avoidDenominator w=overlapSeries w :=
    forbidden_word_counting_identity hw0
  have hh := congrArg signedMoment hcount
  rw [signedMoment_mul,hden,balanced_signedMoment_overlap hw0 hw,mul_zero,add_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_right (avoidDenominator_eval_ne_zero hw0)

private theorem balanced_rho_eq_half {w : List Bool} (hw0 : w ≠ []) (hw : BalancedBorders w)
    {m : ℕ} (hm : 0 < m) : rho w m=1/2 := by
  classical
  have hh := congrArg (PowerSeries.coeff m) (balanced_signedMoment_avoidSeries hw0 hw)
  simp only [signedMoment,PowerSeries.coeff_mk,avoidSeries,avoidCoeff,
    Polynomial.derivative_sum,Polynomial.eval_finset_sum,Polynomial.derivative_X_pow,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    one_pow,mul_one,sum_const,nsmul_eq_mul,map_zero] at hh
  have hcomp : 2*(∑ u ∈ omega w m,(u.count true : ℝ))=
      (m:ℝ)*(omega w m).card := by exact_mod_cast (sub_eq_zero.mp hh)
  have hcard : 0 < (omega w m).card := card_pos.mpr (omega_nonempty hw0 m)
  have hden : (m:ℝ)*(omega w m).card ≠ 0 := by positivity
  unfold rho
  apply (div_eq_iff hden).mpr
  linarith

theorem balanced_tendsto_half {w : List Bool} (hw0 : w ≠ []) (hw : BalancedBorders w) :
    Filter.Tendsto (rho w) Filter.atTop (nhds (1/2:ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  exact (balanced_rho_eq_half hw0 hw hm).symm

end D5.S1.Words.Forbidden.BalancedBordersHalfFrequency

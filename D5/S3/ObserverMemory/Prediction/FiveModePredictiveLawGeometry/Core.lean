/- GID: D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-horizon mixture geometry and exact startup cutoffs of the actual five-mode source. -/

import D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
import D5.S3.TotalVariation.Metric

namespace D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators

noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev LawProfile := (H : Nat) → (Fin H → Visible) → ℝ

noncomputable def pureLaw (p q r : ℝ) (i : State) : LawProfile :=
  futureWordWeight p q r (pureVector i)

noncomputable def emptyLaw (p q r : ℝ) : LawProfile :=
  initialWordWeight p q r uniformPi

noncomputable def mixtureLaw (p q r x : ℝ) : LawProfile :=
  fun H w => x * pureLaw p q r 2 H w + (1-x) * pureLaw p q r 4 H w

def ProbabilityProfile (F : LawProfile) : Prop :=
  ∀ H, (∀ w, 0 ≤ F H w) ∧ (∑ w, F H w) = 1

def CoherentProfile (F : LawProfile) : Prop :=
  ProbabilityProfile F ∧ ∀ H w, (∑ y : Visible, F (H+1) (Fin.snoc w y)) = F H w

noncomputable def profileDistance (F G : LawProfile) : ℝ :=
  ⨆ H : Nat, totalVariation (F H) (G H)

lemma holding_bounds {p q r : ℝ} (hp : admissible p q r) :
    0 < a p q ∧ a p q < 1 ∧ 0 < b r ∧ b r < 1 ∧ 0 < c p q r := by
  rcases hp with ⟨hp,hq,hr,hs⟩
  dsimp [a,b,c]
  constructor; linarith
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

lemma pure_probability {p q r : ℝ} (hp : admissible p q r) (i : State) :
    ProbabilityProfile (pureLaw p q r i) := by
  intro H
  constructor
  · exact future_word_nonnegative hp _ (by intro j; simp [pureVector]; positivity) H
  · rw [pureLaw, sum_future_words]
    simp [pureVector]

lemma mixture_probability {p q r x : ℝ} (hp : admissible p q r)
    (hx : x ∈ Set.Icc 0 1) : ProbabilityProfile (mixtureLaw p q r x) := by
  intro H
  have h2 := pure_probability hp (2 : State) H
  have h4 := pure_probability hp (4 : State) H
  constructor
  · intro w
    exact add_nonneg (mul_nonneg hx.1 (h2.1 w)) (mul_nonneg (sub_nonneg.mpr hx.2) (h4.1 w))
  · simp only [mixtureLaw, Finset.sum_add_distrib, ← Finset.mul_sum, h2.2, h4.2]
    ring

lemma empty_probability {p q r : ℝ} (hp : admissible p q r) :
    ProbabilityProfile (emptyLaw p q r) := by
  intro H
  exact ⟨initial_word_nonnegative hp H, sum_initial_words H⟩

lemma finite_le_profile {F G : LawProfile} (hF : ProbabilityProfile F)
    (hG : ProbabilityProfile G) (H : Nat) :
    totalVariation (F H) (G H) ≤ profileDistance F G := by
  unfold profileDistance
  apply le_ciSup (f := fun n => totalVariation (F n) (G n)) _ H
  refine ⟨1, ?_⟩
  rintro _ ⟨n,rfl⟩
  exact total_variation_le_one _ _ (hF n) (hG n)

lemma profile_le {F G : LawProfile} {d : ℝ}
    (h : ∀ H, totalVariation (F H) (G H) ≤ d) : profileDistance F G ≤ d := by
  exact ciSup_le h

lemma branch2_step (p q r : ℝ) (y : Visible) :
    filterAt (advance p q r (pureVector 2)) y =
      fun i => (if y = B then a p q else if y = 1 then q else if y = 3 then p else 0) *
        pureVector (if y = B then 2 else if y = 1 then 1 else 3) i := by
  funext i
  fin_cases y <;> fin_cases i <;>
    simp [filterAt,advance,pureVector,observation,transition,B,a,Fin.sum_univ_succ] <;> ring

lemma branch4_step (p q r : ℝ) (y : Visible) :
    filterAt (advance p q r (pureVector 4)) y =
      fun i => (if y = B then b r else if y = 0 then r else 0) *
        pureVector (if y = B then 4 else 0) i := by
  funext i
  fin_cases y <;> fin_cases i <;>
    simp [filterAt,advance,pureVector,observation,transition,B,b,Fin.sum_univ_succ] <;> ring

lemma branch2_cons (p q r : ℝ) (H : Nat) (w : Fin (H+1) → Visible) :
    pureLaw p q r 2 (H+1) w =
      (if w 0 = B then a p q else if w 0 = 1 then q else if w 0 = 3 then p else 0) *
        pureLaw p q r (if w 0 = B then 2 else if w 0 = 1 then 1 else 3) H (fun k => w k.succ) := by
  unfold pureLaw
  rw [futureWordWeight, branch2_step, future_word_scale]

lemma branch4_cons (p q r : ℝ) (H : Nat) (w : Fin (H+1) → Visible) :
    pureLaw p q r 4 (H+1) w =
      (if w 0 = B then b r else if w 0 = 0 then r else 0) *
        pureLaw p q r (if w 0 = B then 4 else 0) H (fun k => w k.succ) := by
  unfold pureLaw
  rw [futureWordWeight, branch4_step, future_word_scale]

/-- Both branch laws give the all-B word their literal holding powers. -/
theorem branch_all_B (p q r : ℝ) (H : Nat) :
    pureLaw p q r 2 H (fun _ => B) = (a p q)^H ∧
    pureLaw p q r 4 H (fun _ => B) = (b r)^H := by
  induction H with
  | zero => norm_num [pureLaw,futureWordWeight,pureVector,Fin.sum_univ_succ]
  | succ H ih =>
    rw [branch2_cons,branch4_cons]
    simp only [ite_true,ih.1,ih.2]
    constructor <;> rw [pow_succ] <;> ring

/-- The common positive support is exactly B^H, including the empty word. -/
theorem branch_word_overlap {p q r : ℝ} (hp : admissible p q r)
    (H : Nat) (w : Fin H → Visible) :
    (0 < pureLaw p q r 2 H w ∧ 0 < pureLaw p q r 4 H w) ↔ w = (fun _ => B) := by
  induction H with
  | zero =>
    have hw : w = (fun _ => B) := Subsingleton.elim _ _
    subst w
    norm_num [pureLaw,futureWordWeight,pureVector,Fin.sum_univ_succ]
  | succ H ih =>
    constructor
    · intro h
      rw [branch2_cons,branch4_cons] at h
      have hy : w 0 = B := by
        by_contra hn
        have hzero : w 0 = 0 ∨ w 0 = 1 ∨ w 0 = 3 := by
          generalize he : w 0 = y at *
          fin_cases y <;> simp_all [B]
        rcases hzero with hy | hy | hy <;> simp [hy, B] at h
      simp only [hy,ite_true] at h
      have ht := (ih (fun k => w k.succ)).mp
        ⟨(mul_pos_iff_of_pos_left (holding_bounds hp).1).mp h.1,
         (mul_pos_iff_of_pos_left (holding_bounds hp).2.2.1).mp h.2⟩
      funext i
      refine Fin.cases hy (fun k => congrFun ht k) i
    · intro hw
      subst w
      rw [(branch_all_B p q r (H+1)).1,(branch_all_B p q r (H+1)).2]
      exact ⟨pow_pos (holding_bounds hp).1 _,pow_pos (holding_bounds hp).2.2.1 _⟩

lemma finite_overlap_identity {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1)
    (hg : (∀ i, 0 ≤ g i) ∧ ∑ i, g i = 1) :
    totalVariation f g = 1 - ∑ i, min (f i) (g i) := by
  have he (i : ι) : |f i-g i| = f i+g i-2*min (f i) (g i) := by
    rcases le_total (f i) (g i) with h | h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp only [totalVariation,he,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,hf.2,hg.2]
  ring

/-- The finite branch TV retains its horizon factor; it is zero at H=0. -/
theorem branch_finite_tv {p q r : ℝ} (hp : admissible p q r) (H : Nat) :
    totalVariation (pureLaw p q r 2 H) (pureLaw p q r 4 H) =
      1-(min (a p q) (b r))^H := by
  classical
  rw [finite_overlap_identity _ _ (pure_probability hp 2 H) (pure_probability hp 4 H)]
  have he : ∑ w : Fin H → Visible, min (pureLaw p q r 2 H w) (pureLaw p q r 4 H w) =
      min ((a p q)^H) ((b r)^H) := by
    rw [Finset.sum_eq_single (fun _ => B)]
    · rw [(branch_all_B p q r H).1,(branch_all_B p q r H).2]
    · intro w _ hw
      have hn := mt (branch_word_overlap hp H w).mp hw
      have h2 := (pure_probability hp 2 H).1 w
      have h4 := (pure_probability hp 4 H).1 w
      rcases le_total (pureLaw p q r 2 H w) (pureLaw p q r 4 H w) with hl | hl
      · rw [min_eq_left hl]; by_contra hz; exact hn ⟨lt_of_le_of_ne h2 (Ne.symm hz),lt_of_lt_of_le (lt_of_le_of_ne h2 (Ne.symm hz)) hl⟩
      · rw [min_eq_right hl]; by_contra hz; exact hn ⟨lt_of_lt_of_le (lt_of_le_of_ne h4 (Ne.symm hz)) hl,lt_of_le_of_ne h4 (Ne.symm hz)⟩
    · simp
  rw [he]
  congr 1
  rcases le_total (a p q) (b r) with h | h
  · rw [min_eq_left h,min_eq_left (pow_le_pow_left₀ (holding_bounds hp).1.le h H)]
  · rw [min_eq_right h,min_eq_right (pow_le_pow_left₀ (holding_bounds hp).2.2.1.le h H)]

/-- At every finite horizon the actual mixtures have this exact TV. -/
theorem mixture_finite_tv {p q r : ℝ} (hp : admissible p q r) (x z : ℝ) (H : Nat) :
    totalVariation (mixtureLaw p q r x H) (mixtureLaw p q r z H) =
      |x-z| * (1-(min (a p q) (b r))^H) := by
  have he (w : Fin H → Visible) :
      mixtureLaw p q r x H w-mixtureLaw p q r z H w =
        (x-z)*(pureLaw p q r 2 H w-pureLaw p q r 4 H w) := by
    unfold mixtureLaw; ring
  simp only [totalVariation,he,abs_mul,← Finset.mul_sum]
  rw [show (1/2:ℝ) * (|x-z| * ∑ w, |pureLaw p q r 2 H w-pureLaw p q r 4 H w|) =
    |x-z| * totalVariation (pureLaw p q r 2 H) (pureLaw p q r 4 H) by unfold totalVariation; ring]
  rw [branch_finite_tv hp]


/-- The supremum over finite laws is the mixture-coordinate distance. -/
theorem mixture_profile_distance {p q r : ℝ} (hp : admissible p q r)
    {x z : ℝ} (hx : x ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    profileDistance (mixtureLaw p q r x) (mixtureLaw p q r z) = |x-z| := by
  have hu0 : 0 ≤ min (a p q) (b r) := le_min (holding_bounds hp).1.le (holding_bounds hp).2.2.1.le
  have hu1 : min (a p q) (b r) < 1 := lt_of_le_of_lt (min_le_left _ _) (holding_bounds hp).2.1
  apply le_antisymm
  · apply profile_le
    intro H
    rw [mixture_finite_tv hp]
    nlinarith [mul_nonneg (abs_nonneg (x-z)) (pow_nonneg hu0 H)]
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hu1).const_sub (1 : ℝ)
    have hm := ht.const_mul |x-z|
    simp only [sub_zero,mul_one] at hm
    apply le_of_tendsto hm
    exact Filter.Eventually.of_forall fun H => by
      rw [← mixture_finite_tv hp x z H]
      exact finite_le_profile (mixture_probability hp hx) (mixture_probability hp hz) H

lemma profile_comm (F G : LawProfile) : profileDistance F G = profileDistance G F := by
  simp only [profileDistance,total_variation_comm]

lemma future_word_add (p q r : ℝ) (v u : State → ℝ) (H : Nat) (w : Fin H → Visible) :
    futureWordWeight p q r (fun i => v i+u i) H w =
      futureWordWeight p q r v H w+futureWordWeight p q r u H w := by
  induction H generalizing v u with
  | zero => simp [futureWordWeight,Finset.sum_add_distrib]
  | succ H ih =>
    have he : filterAt (advance p q r (fun i => v i+u i)) (w 0) =
        fun i => filterAt (advance p q r v) (w 0) i+filterAt (advance p q r u) (w 0) i := by
      funext i
      simp only [filterAt,advance,add_mul,Finset.sum_add_distrib]
      split_ifs <;> ring
    simp only [futureWordWeight,he]
    exact ih _ _ (fun k => w k.succ)

lemma future_word_mixture (p q r x : ℝ) (H : Nat) (w : Fin H → Visible) :
    futureWordWeight p q r (fun i => x*pureVector 2 i+(1-x)*pureVector 4 i) H w =
      mixtureLaw p q r x H w := by
  rw [future_word_add,future_word_scale,future_word_scale]
  rfl

noncomputable def startupCoordinate (p q r : ℝ) (k : Nat) : ℝ :=
  (a p q)^k/((a p q)^k+(b r)^k)

lemma startup_coordinate_bounds {p q r : ℝ} (hp : admissible p q r) (k : Nat) :
    0 < startupCoordinate p q r k ∧ startupCoordinate p q r k < 1 := by
  have ha := pow_pos (holding_bounds hp).1 k
  have hb := pow_pos (holding_bounds hp).2.2.1 k
  constructor
  · exact div_pos ha (add_pos ha hb)
  · unfold startupCoordinate
    exact (div_lt_one (add_pos ha hb)).mpr (by linarith)

lemma actual_startup_mixture {p q r : ℝ} (hp : admissible p q r) (k : Nat)
    (H : Nat) (w : Fin H → Visible) :
    actualFutureWordWeight p q r (List.replicate (k+1) B) H w =
      mixtureLaw p q r (startupCoordinate p q r k) H w := by
  have hne : List.replicate (k+1) B ≠ [] := by simp
  simp only [actualFutureWordWeight,hne,if_false]
  rw [actual_all_B_posterior hp]
  have ha := pow_pos (holding_bounds hp).1 k
  have hb := pow_pos (holding_bounds hp).2.2.1 k
  have he : (fun i : State => if i=2 then (a p q)^k/((a p q)^k+(b r)^k)
      else if i=4 then (b r)^k/((a p q)^k+(b r)^k) else 0) =
      (fun i => startupCoordinate p q r k*pureVector 2 i+
        (1-startupCoordinate p q r k)*pureVector 4 i) := by
    funext i
    fin_cases i <;> simp [pureVector,startupCoordinate]
    field_simp [ne_of_gt (add_pos ha hb)]
    ring
  rw [he,future_word_mixture]

lemma pure_coherent {p q r : ℝ} (hp : admissible p q r) (i : State) :
    CoherentProfile (pureLaw p q r i) :=
  ⟨pure_probability hp i,fun H w => final_symbol_coherence (pureVector i) H w⟩

lemma mixture_coherent {p q r x : ℝ} (hp : admissible p q r) (hx : x ∈ Set.Icc 0 1) :
    CoherentProfile (mixtureLaw p q r x) := by
  refine ⟨mixture_probability hp hx,?_⟩
  intro H w
  simp only [mixtureLaw,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [(pure_coherent hp 2).2 H w,(pure_coherent hp 4).2 H w]

lemma empty_coherent {p q r : ℝ} (hp : admissible p q r) :
    CoherentProfile (emptyLaw p q r) :=
  ⟨empty_probability hp,fun H w => initial_final_symbol_coherence H w⟩

lemma one_horizon_sum (f : (Fin 1 → Visible) → ℝ) :
    (∑ w, f w) = ∑ y : Visible, f (fun _ => y) := by
  rw [sum_words_succ 0]
  apply Finset.sum_congr rfl
  intro y _
  have he (w : Fin 0 → Visible) : Fin.cons y w = (fun _ => y) := by
    funext i; fin_cases i; rfl
  simp only [he]
  simp

lemma one_horizon_tv (F G : LawProfile) :
    totalVariation (F 1) (G 1) =
      totalVariation (fun y : Visible => F 1 (fun _ => y)) (fun y => G 1 (fun _ => y)) := by
  unfold totalVariation
  rw [one_horizon_sum]

lemma row_event_gap {F G : LawProfile} (hF : ProbabilityProfile F)
    (hG : ProbabilityProfile G) (E : Finset Visible) :
    |(∑ y ∈ E, F 1 (fun _ => y))-(∑ y ∈ E, G 1 (fun _ => y))| ≤ profileDistance F G := by
  have hsF : (∑ y : Visible, F 1 (fun _ => y)) = 1 := by rw [← one_horizon_sum]; exact (hF 1).2
  have hsG : (∑ y : Visible, G 1 (fun _ => y)) = 1 := by rw [← one_horizon_sum]; exact (hG 1).2
  have he := (total_variation_eq_sup_event_gap
    (fun y : Visible => F 1 (fun _ => y)) (fun y => G 1 (fun _ => y)) (hsF.trans hsG.symm)).2
      (Set.mem_range_self E)
  rw [← one_horizon_tv] at he
  exact he.trans (finite_le_profile hF hG 1)

lemma row_coordinate_gap {F G : LawProfile} (hF : ProbabilityProfile F)
    (hG : ProbabilityProfile G) (y : Visible) :
    |F 1 (fun _ => y)-G 1 (fun _ => y)| ≤ profileDistance F G := by
  simpa using row_event_gap hF hG {y}

noncomputable def pureRow (p q r : ℝ) : State → Visible → ℝ :=
  ![![c p q r,p,r,q],![q,a p q,p,0],![0,q,a p q,p],![p,0,q,a p q],![r,0,b r,0]]

lemma pure_one_step (p q r : ℝ) (i : State) (y : Visible) :
    pureLaw p q r i 1 (fun _ => y) = pureRow p q r i y := by
  fin_cases i <;> fin_cases y <;>
    simp [pureLaw,futureWordWeight,filterAt,advance,pureVector,transition,observation,
      pureRow,a,b,c,Fin.sum_univ_succ] <;> ring

lemma empty_one_step (p q r : ℝ) (y : Visible) :
    emptyLaw p q r 1 (fun _ => y) = if y=B then 2/5 else 1/5 := by
  fin_cases y <;> simp [emptyLaw,initialWordWeight,futureWordWeight,uniformPi,
    filterAt,observation,B,Fin.sum_univ_succ] <;> norm_num

noncomputable def s (p q : ℝ) : ℝ := p+q

noncomputable def kappa (p q r : ℝ) : ℝ :=
  min (min (min (c p q r) p) (min q (a p q)))
    (min (min (c p q r*s p q/(s p q+r)) (a p q*p/s p q))
      (min (a p q*q/s p q) (1/25)))

/-- The explicit separation constant is positive for every admissible triple. -/
theorem kappa_positive {p q r : ℝ} (hp : admissible p q r) : 0 < kappa p q r := by
  have hs : 0 < s p q := by unfold s; linarith [hp.1,hp.2.1]
  have hp0 := hp.1
  have hq0 := hp.2.1
  have hr := hp.2.2.1
  have ha := (holding_bounds hp).1
  have hc := (holding_bounds hp).2.2.2.2
  unfold kappa
  positivity

lemma kappa_bounds (p q r : ℝ) :
    kappa p q r ≤ c p q r ∧ kappa p q r ≤ p ∧ kappa p q r ≤ q ∧
    kappa p q r ≤ a p q ∧ kappa p q r ≤ c p q r*s p q/(s p q+r) ∧
    kappa p q r ≤ a p q*p/s p q ∧ kappa p q r ≤ a p q*q/s p q ∧
    kappa p q r ≤ 1/25 := by
  unfold kappa
  repeat' constructor
  all_goals simp [min_le_iff]

/-- The three singleton laws are uniformly separated from every branch mixture. -/
theorem singleton_mixture_separation {p q r x : ℝ} (hp : admissible p q r)
    (hx : x ∈ Set.Icc 0 1) (j : State) (hj : j=0 ∨ j=1 ∨ j=3) :
    kappa p q r ≤ profileDistance (pureLaw p q r j) (mixtureLaw p q r x) := by
  classical
  let D := profileDistance (pureLaw p q r j) (mixtureLaw p q r x)
  have h0 := row_coordinate_gap (pure_probability hp j) (mixture_probability hp hx) 0
  have h1 := row_coordinate_gap (pure_probability hp j) (mixture_probability hp hx) 1
  have h3 := row_coordinate_gap (pure_probability hp j) (mixture_probability hp hx) 3
  have h13 := row_event_gap (pure_probability hp j) (mixture_probability hp hx) {1,3}
  simp only [mixtureLaw,pure_one_step] at h0 h1 h3 h13
  have hs : 0 < s p q := by unfold s; linarith [hp.1,hp.2.1]
  have hd : 0 < s p q+r := by linarith [hp.2.2.1]
  rcases hj with rfl | rfl | rfl
  · have hb := (kappa_bounds p q r).2.2.2.2.1
    apply hb.trans
    apply (div_le_iff₀ hd).mpr
    have h13' : s p q*(1-x) ≤ D := by
      have hh : |p+q-(x*q+x*p)| ≤ D := by simpa [pureRow,D] using h13
      have heq : p+q-(x*q+x*p) = s p q*(1-x) := by unfold s; ring
      rw [heq,abs_of_nonneg (mul_nonneg hs.le (sub_nonneg.mpr hx.2))] at hh
      exact hh
    have h0' : |c p q r-r*(1-x)| ≤ D := by simpa [pureRow,mul_comm,D] using h0
    have he := (le_abs_self (c p q r-r*(1-x))).trans h0'
    have hmul := mul_le_mul_of_nonneg_left h13' hp.2.2.1.le
    have hm0 := mul_le_mul_of_nonneg_left he hs.le
    change c p q r*s p q ≤ D*(s p q+r)
    nlinarith
  · have hb := (kappa_bounds p q r).2.2.2.2.2.1
    apply hb.trans
    apply (div_le_iff₀ hs).mpr
    have h3' : x*p ≤ D := by simpa [pureRow,abs_of_nonneg (mul_nonneg hx.1 hp.1.le),D] using h3
    have h1' : |a p q-x*q| ≤ D := by simpa [pureRow,D] using h1
    have he := (le_abs_self (a p q-x*q)).trans h1'
    have hm := mul_le_mul_of_nonneg_left h3' hp.2.1.le
    have hm1 := mul_le_mul_of_nonneg_left he hp.1.le
    change a p q*p ≤ D*s p q
    dsimp [s] at *
    nlinarith
  · have hb := (kappa_bounds p q r).2.2.2.2.2.2.1
    apply hb.trans
    apply (div_le_iff₀ hs).mpr
    have h1' : x*q ≤ D := by simpa [pureRow,abs_of_nonneg (mul_nonneg hx.1 hp.2.1.le),D] using h1
    have h3' : |a p q-x*p| ≤ D := by simpa [pureRow,D] using h3
    have he := (le_abs_self (a p q-x*p)).trans h3'
    have hm := mul_le_mul_of_nonneg_left h1' hp.1.le
    have hm3 := mul_le_mul_of_nonneg_left he hp.2.1.le
    change a p q*q ≤ D*s p q
    dsimp [s] at *
    nlinarith

/-- Empty-history laws stay at least one twenty-fifth from every mixture. -/
theorem empty_mixture_separation {p q r x : ℝ} (hp : admissible p q r)
    (hx : x ∈ Set.Icc 0 1) :
    (1/25:ℝ) ≤ profileDistance (emptyLaw p q r) (mixtureLaw p q r x) := by
  classical
  let D := profileDistance (emptyLaw p q r) (mixtureLaw p q r x)
  have h0 := row_coordinate_gap (empty_probability hp) (mixture_probability hp hx) 0
  have h13 := row_event_gap (empty_probability hp) (mixture_probability hp hx) {1,3}
  simp only [mixtureLaw,pure_one_step,empty_one_step] at h0 h13
  have h0' : |1/5-(1-x)*r| ≤ D := by simpa [pureRow,B,D] using h0
  have h13' : |2/5-x*s p q| ≤ D := by
    have hh : |(1/5:ℝ)+1/5-(x*q+x*p)| ≤ D := by simpa [pureRow,B,D] using h13
    convert hh using 1
    congr 1
    unfold s
    ring
  have hs : 0 < s p q := by dsimp [s]; linarith [hp.1,hp.2.1]
  have hd : 0 < s p q+r := by linarith [hp.2.2.1]
  have hsum : s p q+r < 1 := by simpa [s,add_assoc] using hp.2.2.2
  have he0 := (le_abs_self (1/5-(1-x)*r)).trans h0'
  have he13 := (le_abs_self (2/5-x*s p q)).trans h13'
  have hm0 := mul_le_mul_of_nonneg_left he0 hs.le
  have hm13 := mul_le_mul_of_nonneg_left he13 hp.2.2.1.le
  have hl : (2*r/5+s p q/5-s p q*r)/(s p q+r) ≤ D := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  apply le_trans _ hl
  apply (le_div_iff₀ hd).mpr
  have hsq := sq_nonneg (s p q-3*(s p q+r)/5)
  have hprod : s p q*r*(s p q+r) ≤ s p q*r :=
    mul_le_of_le_one_right (mul_pos hs hp.2.2.1).le hsum.le
  have he : 0 ≤ (2*r/5+s p q/5-s p q*r-(s p q+r)/25)*(s p q+r) := by nlinarith
  have hh := nonneg_of_mul_nonneg_left he hd
  linarith


noncomputable def theta (p q r : ℝ) : ℝ := min (a p q) (b r)/max (a p q) (b r)

noncomputable def minority (t : ℝ) (k : Nat) : ℝ := t^k/(1+t^k)

noncomputable def dominantLaw (p q r : ℝ) : LawProfile :=
  if b r < a p q then pureLaw p q r 2 else pureLaw p q r 4

noncomputable def orientedMixture (p q r z : ℝ) : LawProfile :=
  if b r < a p q then mixtureLaw p q r (1-z) else mixtureLaw p q r z

lemma theta_bounds {p q r : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r) :
    0 < theta p q r ∧ theta p q r < 1 := by
  have ha := (holding_bounds hp).1
  have hb := (holding_bounds hp).2.2.1
  have hmax : 0 < max (a p q) (b r) := lt_of_lt_of_le ha (le_max_left _ _)
  constructor
  · exact div_pos (lt_min ha hb) hmax
  · unfold theta
    apply (div_lt_one hmax).mpr
    rcases lt_or_gt_of_ne hne with h | h
    · rw [min_eq_left h.le,max_eq_right h.le]; exact h
    · rw [min_eq_right h.le,max_eq_left h.le]; exact h

lemma minority_positive {t : ℝ} (ht : 0 < t) (k : Nat) : 0 < minority t k := by
  unfold minority
  positivity

lemma minority_le_half {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (k : Nat) :
    minority t k ≤ 1/2 := by
  have hp := pow_le_one₀ (n := k) ht ht1
  have hden : 0 < 1+t^k := by positivity
  unfold minority
  apply (div_le_iff₀ hden).mpr
  linarith

/-- The minority coordinate decreases strictly at every finite startup step. -/
theorem minority_strictAnti {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    StrictAnti (minority t) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  have hk := pow_pos ht k
  have hkp := pow_pos ht (k+1)
  unfold minority
  apply (div_lt_div_iff₀ (by positivity : 0 < 1+t^(k+1)) (by positivity : 0 < 1+t^k)).mpr
  rw [pow_succ]
  nlinarith [mul_pos hk (sub_pos.mpr ht1)]

/-- Decay is a limit of the positive finite-history coordinates. -/
theorem minority_tendsto_zero {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Filter.Tendsto (minority t) Filter.atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one ht.le ht1
  have hden := hpow.const_add (1 : ℝ)
  have hd : (1 : ℝ)+0 ≠ 0 := by norm_num
  unfold minority
  have hh := hpow.div hden hd
  have hh' : Filter.Tendsto (fun n : Nat => t^n/(1+t^n)) Filter.atTop (nhds (0/(1+0):ℝ)) :=
    hh.congr' (Filter.Eventually.of_forall fun n => by rfl)
  simpa only [zero_div] using hh'

noncomputable def cutoff (t e : ℝ) : Nat :=
  ⌈Real.log ((1-e)/e)/|Real.log t|⌉₊

lemma minority_threshold_iff {t e : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (he : 0 < e) (he1 : e < 1/2) (k : Nat) :
    minority t k ≤ e ↔ cutoff t e ≤ k := by
  have h1e : 0 < 1-e := by linarith
  have hpow := pow_pos ht k
  have hden : 0 < 1+t^k := by positivity
  have halg : minority t k ≤ e ↔ t^k ≤ e/(1-e) := by
    rw [minority,div_le_iff₀ hden,le_div_iff₀ h1e]
    constructor <;> intro h <;> nlinarith
  have hneg := Real.log_neg ht ht1
  have hlogabs : 0 < |Real.log t| := abs_pos.mpr (ne_of_lt hneg)
  have hlog : Real.log (e/(1-e)) = -Real.log ((1-e)/e) := by
    rw [Real.log_div (ne_of_gt he) (ne_of_gt h1e),Real.log_div (ne_of_gt h1e) (ne_of_gt he)]
    ring
  rw [halg,← Real.log_le_log_iff hpow (div_pos he h1e),Real.log_pow,hlog,
    cutoff,Nat.ceil_le,div_le_iff₀ hlogabs,abs_of_neg hneg]
  constructor <;> intro h <;> nlinarith

/-- The literal ceiling is the first non-strict threshold, with exact ties. -/
theorem cutoff_first_nonstrict {t e : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (he : 0 < e) (he1 : e < 1/2) :
    0 < cutoff t e ∧ minority t (cutoff t e) ≤ e ∧
    (∀ i < cutoff t e, e < minority t i) ∧
    (∀ k, minority t k ≤ e ↔ cutoff t e ≤ k) ∧
    (minority t (cutoff t e) = e ↔
      Real.log ((1-e)/e)/|Real.log t| = (cutoff t e : ℝ)) := by
  have h1e : 0 < 1-e := by linarith
  have hneg := Real.log_neg ht ht1
  have hlogabs : 0 < |Real.log t| := abs_pos.mpr (ne_of_lt hneg)
  have hratio : 1 < (1-e)/e := (one_lt_div he).mpr (by linarith)
  have hcrit : 0 < Real.log ((1-e)/e)/|Real.log t| := div_pos (Real.log_pos hratio) hlogabs
  refine ⟨Nat.ceil_pos.mpr hcrit,(minority_threshold_iff ht ht1 he he1 _).mpr le_rfl,
    ?_,fun k => minority_threshold_iff ht ht1 he he1 k,?_⟩
  · intro i hi
    exact lt_of_not_ge fun h => (Nat.not_le_of_gt hi) ((minority_threshold_iff ht ht1 he he1 i).mp h)
  · have hn := pow_pos ht (cutoff t e)
    have hden : 0 < 1+t^(cutoff t e) := by positivity
    have halg : minority t (cutoff t e) = e ↔ t^(cutoff t e) = e/(1-e) := by
      rw [minority,div_eq_iff hden.ne',eq_div_iff h1e.ne']
      constructor <;> intro h <;> nlinarith
    have hlog : Real.log (e/(1-e)) = -Real.log ((1-e)/e) := by
      rw [Real.log_div (ne_of_gt he) (ne_of_gt h1e),Real.log_div (ne_of_gt h1e) (ne_of_gt he)]
      ring
    rw [halg,← Real.log_injOn_pos.eq_iff hn (div_pos he h1e),Real.log_pow,hlog,
      div_eq_iff hlogabs.ne',abs_of_neg hneg]
    constructor <;> intro h <;> nlinarith

noncomputable def N2 (p q r ε : ℝ) : Nat := cutoff (theta p q r) (2*ε)

lemma oriented_startup_coordinate {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (k : Nat) :
    startupCoordinate p q r k =
      if b r < a p q then 1-minority (theta p q r) k else minority (theta p q r) k := by
  have ha := pow_pos (holding_bounds hp).1 k
  have hb := pow_pos (holding_bounds hp).2.2.1 k
  rcases lt_or_gt_of_ne hne with h | h
  · have hn : ¬ b r < a p q := not_lt_of_ge h.le
    rw [if_neg hn]
    simp only [startupCoordinate,minority,theta,min_eq_left h.le,max_eq_right h.le,div_pow]
    field_simp [ha.ne',hb.ne',ne_of_gt (add_pos ha hb)]
    ring
  · rw [if_pos h]
    simp only [startupCoordinate,minority,theta,min_eq_right h.le,max_eq_left h.le,div_pow]
    field_simp [ha.ne',hb.ne',ne_of_gt (add_pos ha hb)]
    ring

/-- Both unequal orientations give G_delta on the actual acquired B^(k+1). -/
theorem actual_oriented_startup {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (k : Nat) (H : Nat) (w : Fin H → Visible) :
    actualFutureWordWeight p q r (List.replicate (k+1) B) H w =
      orientedMixture p q r (minority (theta p q r) k) H w := by
  rw [actual_startup_mixture hp,oriented_startup_coordinate hp hne]
  unfold orientedMixture
  split_ifs <;> rfl

/-- The actual startup metric and exact cutoff use the acquired-length index k+1. -/
theorem actual_startup_cutoff {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    0 < N2 p q r ε ∧
    minority (theta p q r) (N2 p q r ε) ≤ 2*ε ∧
    (∀ i < N2 p q r ε, 2*ε < minority (theta p q r) i) ∧
    (∀ k, minority (theta p q r) k ≤ 2*ε ↔ N2 p q r ε ≤ k) ∧
    (minority (theta p q r) (N2 p q r ε) = 2*ε ↔
      Real.log ((1-2*ε)/(2*ε))/|Real.log (theta p q r)| = (N2 p q r ε : ℝ)) := by
  have ht := theta_bounds hp hne
  have he1 : 2*ε < 1/2 := lt_of_lt_of_le hεk (by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2])
  exact cutoff_first_nonstrict ht.1 ht.2 hε he1


end

end D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry

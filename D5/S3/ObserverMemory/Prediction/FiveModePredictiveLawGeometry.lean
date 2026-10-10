/- GID: D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-horizon geometry and exact startup cutoffs of the actual five-mode source. -/

import D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry.Core

namespace D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators

noncomputable section
attribute [local instance] propDecidable

/-- A finite word's first non-B symbol has the selected branch exit category. -/
def FirstExit (zeroBranch : Bool) : (H : Nat) → (Fin H → Visible) → Prop
  | 0, _ => False
  | H+1, w => if w 0=B then FirstExit zeroBranch H (fun k => w k.succ)
      else if zeroBranch then w 0=0 else w 0=1 ∨ w 0=3

noncomputable def exitMass (F : LawProfile) (H : Nat) (zeroBranch : Bool) : ℝ :=
  ∑ w, if FirstExit zeroBranch H w then F H w else 0

noncomputable def firstBExitMass (F : LawProfile) (H : Nat) (zeroBranch : Bool) : ℝ :=
  ∑ w : Fin (H+1) → Visible,
    @ite ℝ (w 0=B ∧ FirstExit zeroBranch H (fun k => w k.succ))
      (propDecidable _) (F (H+1) w) 0

lemma branch_exit_recursion {p q r : ℝ} (hp : admissible p q r) (H : Nat) :
    exitMass (pureLaw p q r 2) (H+1) true = a p q*exitMass (pureLaw p q r 2) H true ∧
    exitMass (pureLaw p q r 4) (H+1) true = r+b r*exitMass (pureLaw p q r 4) H true ∧
    exitMass (pureLaw p q r 2) (H+1) false = p+q+a p q*exitMass (pureLaw p q r 2) H false ∧
    exitMass (pureLaw p q r 4) (H+1) false = b r*exitMass (pureLaw p q r 4) H false := by
  have hsum (i : State) : (∑ w : Fin H → Visible, pureLaw p q r i H w) = 1 := (pure_probability hp i H).2
  unfold exitMass
  simp only [sum_words_succ,FirstExit,Fin.cons_zero,Fin.cons_succ]
  simp [branch2_cons,branch4_cons,B,Fin.sum_univ_succ,hsum,Finset.mul_sum,mul_ite,mul_zero]
  have heta (w : Fin H → Visible) : (fun k => w k) = w := rfl
  simp [heta,← Finset.mul_sum,hsum,mul_one,add_assoc,add_comm,add_left_comm]

/-- Finite first-exit events distinguish the branches before any later motion. -/
theorem branch_exit_masses {p q r : ℝ} (hp : admissible p q r) (H : Nat) :
    exitMass (pureLaw p q r 2) H true = 0 ∧
    exitMass (pureLaw p q r 4) H true = 1-(b r)^H ∧
    exitMass (pureLaw p q r 2) H false = 1-(a p q)^H ∧
    exitMass (pureLaw p q r 4) H false = 0 := by
  induction H with
  | zero => simp [exitMass,FirstExit]
  | succ H ih =>
    rcases branch_exit_recursion hp H with ⟨h2,h4,h2',h4'⟩
    rw [ih.1] at h2
    rw [ih.2.1] at h4
    rw [ih.2.2.1] at h2'
    rw [ih.2.2.2] at h4'
    refine ⟨by simpa using h2,?_,?_,by simpa using h4'⟩
    · rw [h4,pow_succ]; unfold b; ring
    · rw [h2',pow_succ]; unfold a; ring

lemma pure_B_word (p q r : ℝ) (i : State) (H : Nat) (w : Fin H → Visible) :
    pureLaw p q r i (H+1) (Fin.cons B w) =
      pureBMass p q r i*pureLaw p q r (pureBSuccessor i) H w := by
  unfold pureLaw
  rw [futureWordWeight]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rw [pure_B_step,future_word_scale]

lemma empty_B_word (p q r : ℝ) (H : Nat) (w : Fin H → Visible) :
    emptyLaw p q r (H+1) (Fin.cons B w) =
      (pureLaw p q r 2 H w+pureLaw p q r 4 H w)/5 := by
  unfold emptyLaw
  rw [initialWordWeight]
  simp only [Fin.cons_zero,Fin.cons_succ]
  have he : filterAt uniformPi B =
      (fun i => (1/5:ℝ)*pureVector 2 i+(1/5:ℝ)*pureVector 4 i) := by
    funext i
    fin_cases i <;> simp [filterAt,uniformPi,B,observation,pureVector]
  rw [he,future_word_add,future_word_scale,future_word_scale]
  unfold pureLaw
  ring

lemma first_B_event_reduction (F : LawProfile) (H : Nat) (z : Bool) :
    firstBExitMass F H z = ∑ w : Fin H → Visible,
      if FirstExit z H w then F (H+1) (Fin.cons B w) else 0 := by
  unfold firstBExitMass
  rw [sum_words_succ]
  simp [B,Fin.sum_univ_succ]

lemma pure_firstB_exit_factor (p q r : ℝ) (i : State) (H : Nat) (z : Bool) :
    firstBExitMass (pureLaw p q r i) H z =
      pureBMass p q r i*exitMass (pureLaw p q r (pureBSuccessor i)) H z := by
  rw [first_B_event_reduction]
  simp_rw [pure_B_word]
  simp [exitMass,Finset.mul_sum,mul_ite]

/-- The empty-law first-B/first-exit cylinder masses at horizon H+1. -/
theorem empty_first_B_exit_masses {p q r : ℝ} (hp : admissible p q r) (H : Nat) :
    firstBExitMass (emptyLaw p q r) H true = (1-(b r)^H)/5 ∧
    firstBExitMass (emptyLaw p q r) H false = (1-(a p q)^H)/5 := by
  have he (z : Bool) : firstBExitMass (emptyLaw p q r) H z =
      (exitMass (pureLaw p q r 2) H z+exitMass (pureLaw p q r 4) H z)/5 := by
    rw [first_B_event_reduction]
    simp_rw [empty_B_word]
    unfold exitMass
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hh : FirstExit z H w <;> simp [hh]
  rcases branch_exit_masses hp H with ⟨h2,h4,h2',h4'⟩
  rw [he true,he false,h2,h4,h2',h4']
  simp

/-- A pure start has one impossible first-B exit category, at every finite H. -/
theorem pure_first_B_exit_zero {p q r : ℝ} (hp : admissible p q r) (i : State) :
    (∀ H, firstBExitMass (pureLaw p q r i) H true = 0) ∨
    (∀ H, firstBExitMass (pureLaw p q r i) H false = 0) := by
  fin_cases i
  · right; intro H; rw [pure_firstB_exit_factor]; simp [pureBSuccessor,(branch_exit_masses hp H).2.2.2]
  · left; intro H; rw [pure_firstB_exit_factor]; simp [pureBSuccessor,(branch_exit_masses hp H).1]
  · left; intro H; rw [pure_firstB_exit_factor]; simp [pureBSuccessor,(branch_exit_masses hp H).1]
  · left; intro H; rw [pure_firstB_exit_factor]; simp [pureBSuccessor,(branch_exit_masses hp H).1]
  · right; intro H; rw [pure_firstB_exit_factor]; simp [pureBSuccessor,(branch_exit_masses hp H).2.2.2]

lemma finite_event_gap {F G : LawProfile} (hF : ProbabilityProfile F)
    (hG : ProbabilityProfile G) (H : Nat) (E : (Fin H → Visible) → Prop) :
    |(∑ w, if E w then F H w else 0)-(∑ w, if E w then G H w else 0)| ≤
      totalVariation (F H) (G H) := by
  classical
  have he := (total_variation_eq_sup_event_gap (F H) (G H)
    ((hF H).2.trans (hG H).2.symm)).2 (Set.mem_range_self (Finset.univ.filter E))
  simpa [Finset.sum_filter] using he

/-- Empty and pure actual laws are separated using limits of finite cylinders. -/
theorem empty_pure_separation {p q r : ℝ} (hp : admissible p q r) (i : State) :
    (1/5:ℝ) ≤ profileDistance (emptyLaw p q r) (pureLaw p q r i) := by
  have hgap (H : Nat) (z : Bool) :
      |firstBExitMass (emptyLaw p q r) H z-firstBExitMass (pureLaw p q r i) H z| ≤
        profileDistance (emptyLaw p q r) (pureLaw p q r i) := by
    simpa only [firstBExitMass] using (finite_event_gap (empty_probability hp) (pure_probability hp i) (H+1)
      (fun w => w 0=B ∧ FirstExit z H (fun k => w k.succ))).trans
        (finite_le_profile (empty_probability hp) (pure_probability hp i) (H+1))
  rcases pure_first_B_exit_zero hp i with h | h
  · have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (holding_bounds hp).2.2.1.le (holding_bounds hp).2.2.2.1).const_sub (1 : ℝ)).div_const 5
    simp only [sub_zero] at ht
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall fun H => by
      have hh := hgap H true
      rw [(empty_first_B_exit_masses hp H).1,h H,sub_zero] at hh
      exact (le_abs_self _).trans hh
  · have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (holding_bounds hp).1.le (holding_bounds hp).2.1).const_sub (1 : ℝ)).div_const 5
    simp only [sub_zero] at ht
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall fun H => by
      have hh := hgap H false
      rw [(empty_first_B_exit_masses hp H).2,h H,sub_zero] at hh
      exact (le_abs_self _).trans hh


/-- The same coherent actual branch laws realize the finite and supremum geometry. -/
theorem coherent_mixture_geometry {p q r x z : ℝ} (hp : admissible p q r)
    (hx : x ∈ Set.Icc 0 1) (hz : z ∈ Set.Icc 0 1) :
    CoherentProfile (mixtureLaw p q r x) ∧
    (∀ H, totalVariation (mixtureLaw p q r x H) (mixtureLaw p q r z H) =
      |x-z| *(1-(min (a p q) (b r))^H)) ∧
    profileDistance (mixtureLaw p q r x) (mixtureLaw p q r z) = |x-z| :=
  ⟨mixture_coherent hp hx,mixture_finite_tv hp x z,mixture_profile_distance hp hx hz⟩

lemma mixture_endpoints (p q r : ℝ) :
    mixtureLaw p q r 0 = pureLaw p q r 4 ∧ mixtureLaw p q r 1 = pureLaw p q r 2 := by
  constructor <;> funext H w <;> simp [mixtureLaw]

lemma branch_profile_distance {p q r : ℝ} (hp : admissible p q r) :
    profileDistance (pureLaw p q r 2) (pureLaw p q r 4) = 1 := by
  have h := mixture_profile_distance hp (x := 1) (z := 0)
    (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
  rw [(mixture_endpoints p q r).1,(mixture_endpoints p q r).2] at h
  norm_num at h
  exact h

/-- All distinct pure modes remain separated, including p=q and r=p+q. -/
theorem pure_pair_separation {p q r : ℝ} (hp : admissible p q r) (i j : State)
    (hne : i ≠ j) : kappa p q r ≤ profileDistance (pureLaw p q r i) (pureLaw p q r j) := by
  have hk := kappa_bounds p q r
  have h24 := branch_profile_distance hp
  have h42 : profileDistance (pureLaw p q r 4) (pureLaw p q r 2) = 1 := by rw [profile_comm]; exact h24
  by_cases hspecial : (i=2 ∧ j=4) ∨ (i=4 ∧ j=2)
  · rcases hspecial with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals rw [show profileDistance (pureLaw p q r _) (pureLaw p q r _) = 1 by first | exact h24 | exact h42]
    all_goals linarith [hk.2.2.2.2.2.2.2]
  · have h0 := row_coordinate_gap (pure_probability hp i) (pure_probability hp j) 0
    have h1 := row_coordinate_gap (pure_probability hp i) (pure_probability hp j) 1
    have h3 := row_coordinate_gap (pure_probability hp i) (pure_probability hp j) 3
    simp only [pure_one_step] at h0 h1 h3
    have ha := (holding_bounds hp).1
    have hc := (holding_bounds hp).2.2.2.2
    have hp0 := hp.1
    have hq0 := hp.2.1
    fin_cases i <;> fin_cases j <;>
      simp_all [pureRow,abs_of_pos ha,abs_of_pos hc,abs_of_pos hp0,abs_of_pos hq0,abs_neg]
    all_goals linarith [hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1]

/-- Reversing the holding-probability orientation preserves the exact metric. -/
theorem oriented_geometry {p q r z w : ℝ} (hp : admissible p q r)
    (hz : z ∈ Set.Icc 0 1) (hw : w ∈ Set.Icc 0 1) :
    CoherentProfile (orientedMixture p q r z) ∧
    (∀ H, totalVariation (orientedMixture p q r z H) (orientedMixture p q r w H) =
      |z-w| *(1-(min (a p q) (b r))^H)) ∧
    profileDistance (orientedMixture p q r z) (orientedMixture p q r w) = |z-w| := by
  have hz' : 1-z ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hw' : 1-w ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hw.2],by linarith [hw.1]⟩
  unfold orientedMixture
  split_ifs with h
  · have hh := coherent_mixture_geometry hp hz' hw'
    have he : |(1-z)-(1-w)| = |z-w| := by rw [show (1-z)-(1-w) = -(z-w) by ring,abs_neg]
    simpa only [he] using hh
  · exact coherent_mixture_geometry hp hz hw

lemma dominant_as_zero (p q r : ℝ) :
    dominantLaw p q r = orientedMixture p q r 0 := by
  unfold dominantLaw orientedMixture
  split_ifs <;> funext H w <;> simp [mixtureLaw]

/-- Every finite acquired startup has its exact distance from the dominant law. -/
theorem actual_startup_geometry {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (k l : Nat) :
    CoherentProfile (actualFutureWordWeight p q r (List.replicate (k+1) B)) ∧
    profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
      (actualFutureWordWeight p q r (List.replicate (l+1) B)) =
        |minority (theta p q r) k-minority (theta p q r) l| ∧
    profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
      (dominantLaw p q r) = minority (theta p q r) k := by
  have ht := theta_bounds hp hne
  have hk : minority (theta p q r) k ∈ Set.Icc (0:ℝ) 1 :=
    ⟨(minority_positive ht.1 k).le,(minority_le_half ht.1.le ht.2.le k).trans (by norm_num)⟩
  have hl : minority (theta p q r) l ∈ Set.Icc (0:ℝ) 1 :=
    ⟨(minority_positive ht.1 l).le,(minority_le_half ht.1.le ht.2.le l).trans (by norm_num)⟩
  have he (m : Nat) : actualFutureWordWeight p q r (List.replicate (m+1) B) =
      orientedMixture p q r (minority (theta p q r) m) := by
    funext H w; exact actual_oriented_startup hp hne m H w
  rw [he k,he l,dominant_as_zero]
  have hg := oriented_geometry hp hk hl
  refine ⟨hg.1,hg.2.2,?_⟩
  rw [(oriented_geometry hp hk (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)).2.2,sub_zero,
    abs_of_pos (minority_positive ht.1 k)]

/-- The equality stratum has one actual half-mixture at every startup length. -/
theorem equality_startup_geometry {p q r : ℝ} (hp : admissible p q r)
    (heq : r=p+q) (k : Nat) :
    (∀ H w, actualFutureWordWeight p q r (List.replicate (k+1) B) H w = mixtureLaw p q r (1/2) H w) ∧
    CoherentProfile (emptyLaw p q r) ∧
    profileDistance (mixtureLaw p q r (1/2)) (pureLaw p q r 2) = 1/2 ∧
    profileDistance (mixtureLaw p q r (1/2)) (pureLaw p q r 4) = 1/2 := by
  have hab : a p q=b r := by unfold a b; linarith
  have ha := pow_pos (holding_bounds hp).1 k
  have hx : startupCoordinate p q r k = 1/2 := by
    unfold startupCoordinate
    rw [← hab]
    field_simp [ha.ne']
    ring
  have h2 := mixture_profile_distance hp (x := 1/2) (z := 1)
    (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)
  have h4 := mixture_profile_distance hp (x := 1/2) (z := 0)
    (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1) (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
  refine ⟨?_,empty_coherent hp,?_,?_⟩
  · intro H w; rw [actual_startup_mixture hp,hx]
  · rw [(mixture_endpoints p q r).2] at h2
    norm_num at h2
    exact h2
  · rw [(mixture_endpoints p q r).1] at h4
    norm_num at h4
    exact h4

/-- Startup coordinates are injective exactly on the unequal stratum. -/
theorem startup_coordinate_injective {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) : Function.Injective (startupCoordinate p q r) := by
  have ht := theta_bounds hp hne
  intro k l hkl
  rw [oriented_startup_coordinate hp hne,oriented_startup_coordinate hp hne] at hkl
  have hm : minority (theta p q r) k=minority (theta p q r) l := by
    split_ifs at hkl <;> linarith
  exact (minority_strictAnti ht.1 ht.2).injective hm


lemma mixture_pure_distances {p q r x : ℝ} (hp : admissible p q r)
    (hx : x ∈ Set.Icc 0 1) :
    profileDistance (mixtureLaw p q r x) (pureLaw p q r 2) = 1-x ∧
    profileDistance (mixtureLaw p q r x) (pureLaw p q r 4) = x := by
  have h2 := mixture_profile_distance hp hx (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)
  have h4 := mixture_profile_distance hp hx (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)
  rw [(mixture_endpoints p q r).2,abs_of_nonpos (sub_nonpos.mpr hx.2)] at h2
  rw [(mixture_endpoints p q r).1,sub_zero,abs_of_nonneg hx.1] at h4
  exact ⟨by linarith,h4⟩

lemma profile_distance_eq_zero_of_eq {F G : LawProfile} (h : F=G) : profileDistance F G=0 := by
  subst G
  simp [profileDistance,totalVariation]

/-- Every interior mixture is distinct from all five pure laws and the empty law. -/
theorem interior_mixture_distinct {p q r x : ℝ} (hp : admissible p q r)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (∀ i : State, mixtureLaw p q r x ≠ pureLaw p q r i) ∧
      mixtureLaw p q r x ≠ emptyLaw p q r := by
  have hx : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0.le,hx1.le⟩
  have hd := mixture_pure_distances hp hx
  constructor
  · intro i he
    have hz := profile_distance_eq_zero_of_eq he
    fin_cases i
    all_goals dsimp only at he hz
    · change profileDistance (mixtureLaw p q r x) (pureLaw p q r 0)=0 at hz
      have hh := singleton_mixture_separation hp hx 0 (by simp)
      rw [profile_comm] at hh
      linarith [kappa_positive hp]
    · change profileDistance (mixtureLaw p q r x) (pureLaw p q r 1)=0 at hz
      have hh := singleton_mixture_separation hp hx 1 (by simp)
      rw [profile_comm] at hh
      linarith [kappa_positive hp]
    · change profileDistance (mixtureLaw p q r x) (pureLaw p q r 2)=0 at hz
      linarith [hd.1]
    · change profileDistance (mixtureLaw p q r x) (pureLaw p q r 3)=0 at hz
      have hh := singleton_mixture_separation hp hx 3 (by simp)
      rw [profile_comm] at hh
      linarith [kappa_positive hp]
    · change profileDistance (mixtureLaw p q r x) (pureLaw p q r 4)=0 at hz
      linarith [hd.2]
  · intro he
    have hz := profile_distance_eq_zero_of_eq he
    have hh := empty_mixture_separation hp hx
    rw [profile_comm] at hh
    linarith

/-- Distinct finite startup lengths give distinct actual complete laws when a≠b. -/
theorem actual_startup_injective {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) :
    Function.Injective (fun k : Nat => actualFutureWordWeight p q r (List.replicate (k+1) B)) := by
  intro k l he
  have hz := profile_distance_eq_zero_of_eq he
  dsimp only at he hz
  have hxk := startup_coordinate_bounds hp k
  have hxl := startup_coordinate_bounds hp l
  have hak (m : Nat) : actualFutureWordWeight p q r (List.replicate (m+1) B) =
      mixtureLaw p q r (startupCoordinate p q r m) := by
    funext H w; exact actual_startup_mixture hp m H w
  rw [hak k,hak l,mixture_profile_distance hp ⟨hxk.1.le,hxk.2.le⟩ ⟨hxl.1.le,hxl.2.le⟩] at hz
  exact startup_coordinate_injective hp hne (sub_eq_zero.mp (abs_eq_zero.mp hz))

/-- Positive source histories realize all the distinct pure and startup law classes. -/
theorem actual_predictive_class_distinctness {p q r : ℝ} (hp : admissible p q r) :
    Function.Injective (pureLaw p q r) ∧
    (∀ i : State, emptyLaw p q r ≠ pureLaw p q r i) ∧
    (∀ k : Nat, (∀ i : State, actualFutureWordWeight p q r (List.replicate (k+1) B) ≠ pureLaw p q r i) ∧
      actualFutureWordWeight p q r (List.replicate (k+1) B) ≠ emptyLaw p q r) := by
  refine ⟨?_,?_,?_⟩
  · intro i j he
    by_contra hn
    have hz := profile_distance_eq_zero_of_eq he
    linarith [pure_pair_separation hp i j hn,kappa_positive hp]
  · intro i he
    have hz := profile_distance_eq_zero_of_eq he
    linarith [empty_pure_separation hp i]
  · intro k
    have hx := startup_coordinate_bounds hp k
    have he : actualFutureWordWeight p q r (List.replicate (k+1) B) =
        mixtureLaw p q r (startupCoordinate p q r k) := by
      funext H w; exact actual_startup_mixture hp k H w
    rw [he]
    exact interior_mixture_distinct hp hx.1 hx.2

/-- The exact non-strict cutoff concerns actual laws, including all exact ties. -/
theorem actual_cutoff_geometry {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    0 < N2 p q r ε ∧
    N2 p q r ε = ⌈Real.log ((1-2*ε)/(2*ε))/|Real.log (theta p q r)|⌉₊ ∧
    (∀ k, profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
      (dominantLaw p q r) ≤ 2*ε ↔ N2 p q r ε ≤ k) ∧
    (∀ i < N2 p q r ε, 2*ε < profileDistance
      (actualFutureWordWeight p q r (List.replicate (i+1) B)) (dominantLaw p q r)) ∧
    (profileDistance (actualFutureWordWeight p q r (List.replicate (N2 p q r ε+1) B))
      (dominantLaw p q r) = 2*ε ↔
        Real.log ((1-2*ε)/(2*ε))/|Real.log (theta p q r)| = (N2 p q r ε : ℝ)) ∧
    Filter.Tendsto (fun k => profileDistance
      (actualFutureWordWeight p q r (List.replicate (k+1) B)) (dominantLaw p q r)) Filter.atTop (nhds 0) := by
  rcases actual_startup_cutoff hp hne hε hεk with ⟨hN,hval,hbefore,hiff,htie⟩
  have he (k : Nat) : profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
      (dominantLaw p q r) = minority (theta p q r) k := (actual_startup_geometry hp hne k k).2.2
  refine ⟨hN,rfl,?_,?_,?_,?_⟩
  · intro k; rw [he]; exact hiff k
  · intro i hi; rw [he]; exact hbefore i hi
  · rw [he]; exact htie
  · have ht := theta_bounds hp hne
    convert minority_tendsto_zero ht.1 ht.2 using 1
    funext k; exact he k

/-- The common midpoint profile bounds the entire actual saturated tail. -/
theorem startup_midpoint_tail_bound {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    let β := minority (theta p q r) (N2 p q r ε)/2
    CoherentProfile (orientedMixture p q r β) ∧
    profileDistance (dominantLaw p q r) (orientedMixture p q r β) ≤ ε ∧
    ∀ k, N2 p q r ε ≤ k →
      profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
        (orientedMixture p q r β) ≤ ε := by
  intro β
  have ht := theta_bounds hp hne
  have hcut := actual_startup_cutoff hp hne hε hεk
  have hb0 : 0 ≤ β := (div_pos (minority_positive ht.1 _) (by norm_num)).le
  have hb1 : β ≤ 1 := by dsimp [β]; linarith [minority_le_half ht.1.le ht.2.le (N2 p q r ε)]
  have hβε : β ≤ ε := by dsimp [β]; linarith [hcut.2.1]
  have hb : β ∈ Set.Icc (0:ℝ) 1 := ⟨hb0,hb1⟩
  refine ⟨(oriented_geometry hp hb hb).1,?_,?_⟩
  · rw [dominant_as_zero,(oriented_geometry hp (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) hb).2.2]
    simpa [abs_of_nonneg hb0] using hβε
  · intro k hk
    have hk0 := (minority_positive ht.1 k).le
    have hk1 := minority_le_half ht.1.le ht.2.le k
    have hmono : minority (theta p q r) k ≤ minority (theta p q r) (N2 p q r ε) :=
      (minority_strictAnti ht.1 ht.2).antitone hk
    have he : actualFutureWordWeight p q r (List.replicate (k+1) B) =
        orientedMixture p q r (minority (theta p q r) k) := by
      funext H w; exact actual_oriented_startup hp hne k H w
    rw [he,(oriented_geometry hp ⟨hk0,by linarith⟩ hb).2.2]
    apply abs_le.mpr
    constructor <;> dsimp [β] at * <;> linarith [hcut.2.1]


lemma pure_law_at_length {p q r : ℝ} (hp : admissible p q r) (L : Nat) (hL : 2 ≤ L) (i : State) :
    ∃ h : List Visible, h.length=L ∧ 0 < historyMass p q r h ∧
      actualFutureWordWeight p q r h = pureLaw p q r i := by
  let h := pureWitness i ++ List.replicate (L-(pureWitness i).length) (observation i)
  have hw : (pureWitness i).length ≤ 2 := by fin_cases i <;> simp [pureWitness]
  have hl : h.length=L := by dsimp [h]; simp only [List.length_append,List.length_replicate]; omega
  have hn : h ≠ [] := by intro he; have := congrArg List.length he; simp only [List.length_nil] at this; omega
  have hh := positive_pure_padding hp i (L-(pureWitness i).length)
  refine ⟨h,hl,hh.2.1,?_⟩
  funext H w
  simp only [actualFutureWordWeight,hn,if_false]
  rw [hh.2.2]
  rfl

lemma startup_history_positive {p q r : ℝ} (hp : admissible p q r) (k : Nat) :
    0 < historyMass p q r (List.replicate (k+1) B) := by
  have ha := pow_pos (holding_bounds hp).1 k
  have hb := pow_pos (holding_bounds hp).2.2.1 k
  simp [historyMass,acquired_all_B,startupVector,Fin.sum_univ_succ]
  positivity

noncomputable def cappedClassLaw (p q r : ℝ) (L : Nat) : State ⊕ Fin L → LawProfile
  | .inl i => pureLaw p q r i
  | .inr k => actualFutureWordWeight p q r (List.replicate (k.val+1) B)

/-- A length cap contains L startup classes and five pure classes, with no supplied clock. -/
theorem capped_predictive_classes {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (L : Nat) (hL : 2 ≤ L) :
    Function.Injective (cappedClassLaw p q r L) ∧
    (∀ t : State ⊕ Fin L, ∃ h : List Visible, h ≠ [] ∧ h.length ≤ L ∧
      0 < historyMass p q r h ∧ actualFutureWordWeight p q r h = cappedClassLaw p q r L t) ∧
    (∀ h : List Visible, h ≠ [] → h.length ≤ L → 0 < historyMass p q r h →
      ∃ t : State ⊕ Fin L, actualFutureWordWeight p q r h = cappedClassLaw p q r L t) ∧
    Fintype.card (State ⊕ Fin L) = L+5 := by
  have hdis := actual_predictive_class_distinctness hp
  refine ⟨?_,?_,?_,?_⟩
  · intro t u he
    cases t with
    | inl i =>
      cases u with
      | inl j => exact congrArg Sum.inl (hdis.1 he)
      | inr k => exact False.elim ((hdis.2.2 k.val).1 i he.symm)
    | inr k =>
      cases u with
      | inl i => exact False.elim ((hdis.2.2 k.val).1 i he)
      | inr l => exact congrArg Sum.inr (Fin.ext (actual_startup_injective hp hne he))
  · intro t
    cases t with
    | inl i =>
      obtain ⟨h,hl,hp',he⟩ := pure_law_at_length hp L hL i
      have hn : h ≠ [] := by intro hn; subst h; simp at hl; omega
      exact ⟨h,hn,hl.le,hp',he⟩
    | inr k =>
      refine ⟨List.replicate (k.val+1) B,by simp,?_,startup_history_positive hp k.val,rfl⟩
      simp only [List.length_replicate]
      omega
  · intro h hn hl hh
    rcases positive_history_classification p q r h hn hh with ⟨k,hk,hr,hw⟩ | ⟨i,hi,hpost⟩
    · have hkle : k < L := by rw [hk,List.length_replicate] at hl; omega
      exact ⟨.inr ⟨k,hkle⟩,by simp only [cappedClassLaw,hk]⟩
    · refine ⟨.inl i,?_⟩
      funext H w
      simp only [cappedClassLaw,actualFutureWordWeight,hn,if_false,hpost,pureLaw]
  · simp [State,Fintype.card_sum,add_comm]

noncomputable def fixedClassLaw (p q r : ℝ) (L : Nat) : State ⊕ Unit → LawProfile
  | .inl i => pureLaw p q r i
  | .inr _ => actualFutureWordWeight p q r (List.replicate L B)

/-- At one externally fixed length only its single startup law occurs; this is a domain statement. -/
theorem fixed_length_predictive_classes {p q r : ℝ} (hp : admissible p q r)
    (L : Nat) (hL : 2 ≤ L) :
    Function.Injective (fixedClassLaw p q r L) ∧
    (∀ t : State ⊕ Unit, ∃ h : List Visible, h.length=L ∧
      0 < historyMass p q r h ∧ actualFutureWordWeight p q r h = fixedClassLaw p q r L t) ∧
    (∀ h : List Visible, h.length=L → 0 < historyMass p q r h →
      ∃ t : State ⊕ Unit, actualFutureWordWeight p q r h = fixedClassLaw p q r L t) ∧
    Fintype.card (State ⊕ Unit) = 6 := by
  have hL1 : L-1+1=L := by omega
  have hdis := actual_predictive_class_distinctness hp
  refine ⟨?_,?_,?_,?_⟩
  · intro t u he
    cases t with
    | inl i =>
      cases u with
      | inl j => exact congrArg Sum.inl (hdis.1 he)
      | inr k =>
        have hh := (hdis.2.2 (L-1)).1 i
        rw [hL1] at hh
        exact False.elim (hh he.symm)
    | inr k =>
      cases u with
      | inl i =>
        have hh := (hdis.2.2 (L-1)).1 i
        rw [hL1] at hh
        exact False.elim (hh he)
      | inr l => exact congrArg Sum.inr (Subsingleton.elim k l)
  · intro t
    cases t with
    | inl i => exact pure_law_at_length hp L hL i
    | inr u =>
      have hh := startup_history_positive hp (L-1)
      rw [hL1] at hh
      exact ⟨List.replicate L B,by simp,hh,rfl⟩
  · intro h hl hh
    have hn : h ≠ [] := by intro he; subst h; simp at hl; omega
    rcases positive_history_classification p q r h hn hh with ⟨k,hk,hr,hw⟩ | ⟨i,hi,hpost⟩
    · have hkL : k+1=L := by rw [hk,List.length_replicate] at hl; exact hl
      exact ⟨.inr (),by simp only [fixedClassLaw,hk,hkL]⟩
    · refine ⟨.inl i,?_⟩
      funext H w
      simp only [fixedClassLaw,actualFutureWordWeight,hn,if_false,hpost,pureLaw]
  · simp [State,Fintype.card_sum]

/-- The capped initialized law family has one additional distinct empty boundary. -/
theorem initialized_capped_class_count {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (L : Nat) (hL : 2 ≤ L) :
    Function.Injective (fun t : Option (State ⊕ Fin L) =>
      match t with | none => emptyLaw p q r | some u => cappedClassLaw p q r L u) ∧
    Fintype.card (Option (State ⊕ Fin L)) = L+6 := by
  have hcap := (capped_predictive_classes hp hne L hL).1
  have hdis := actual_predictive_class_distinctness hp
  constructor
  · intro t u he
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some v =>
        cases v with
        | inl i => exact False.elim (hdis.2.1 i he)
        | inr k => exact False.elim ((hdis.2.2 k.val).2 he.symm)
    | some v =>
      cases u with
      | none =>
        cases v with
        | inl i => exact False.elim (hdis.2.1 i he.symm)
        | inr k => exact False.elim ((hdis.2.2 k.val).2 he)
      | some w => exact congrArg Option.some (hcap he)
  · simp [State,Fintype.card_sum,Fintype.card_option]
    omega


/-- Equality collapses startup ages to one class: six post-read and seven initialized laws. -/
theorem equality_predictive_classes {p q r : ℝ} (hp : admissible p q r) (heq : r=p+q) :
    Function.Injective (fixedClassLaw p q r 2) ∧
    (∀ t : State ⊕ Unit, ∃ h : List Visible, h ≠ [] ∧ 0 < historyMass p q r h ∧
      actualFutureWordWeight p q r h = fixedClassLaw p q r 2 t) ∧
    (∀ h : List Visible, h ≠ [] → 0 < historyMass p q r h →
      ∃ t : State ⊕ Unit, actualFutureWordWeight p q r h = fixedClassLaw p q r 2 t) ∧
    Function.Injective (fun t : Option (State ⊕ Unit) =>
      match t with | none => emptyLaw p q r | some u => fixedClassLaw p q r 2 u) ∧
    Fintype.card (State ⊕ Unit) = 6 ∧ Fintype.card (Option (State ⊕ Unit)) = 7 := by
  have hfixed := fixed_length_predictive_classes hp 2 (by norm_num)
  have hdis := actual_predictive_class_distinctness hp
  refine ⟨hfixed.1,?_,?_,?_,hfixed.2.2.2,by simp [State,Fintype.card_sum,Fintype.card_option]⟩
  · intro t
    obtain ⟨h,hl,hpos,he⟩ := hfixed.2.1 t
    have hn : h ≠ [] := by intro hn; subst h; simp at hl
    exact ⟨h,hn,hpos,he⟩
  · intro h hn hpos
    rcases positive_history_classification p q r h hn hpos with ⟨k,hk,hr,hw⟩ | ⟨i,hi,hpost⟩
    · refine ⟨.inr (),?_⟩
      funext H w
      simp only [fixedClassLaw,hk]
      rw [(equality_startup_geometry hp heq k).1 H w,
        (equality_startup_geometry hp heq 1).1 H w]
    · refine ⟨.inl i,?_⟩
      funext H w
      simp only [fixedClassLaw,actualFutureWordWeight,hn,if_false,hpost,pureLaw]
  · intro t u he
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some v =>
        cases v with
        | inl i => exact False.elim (hdis.2.1 i he)
        | inr v => exact False.elim ((hdis.2.2 1).2 he.symm)
    | some v =>
      cases u with
      | none =>
        cases v with
        | inl i => exact False.elim (hdis.2.1 i he.symm)
        | inr v => exact False.elim ((hdis.2.2 1).2 he)
      | some w => exact congrArg Option.some (hfixed.1 he)


/-- Every pre-cutoff actual startup law is separated from all synchronized and empty laws. -/
theorem startup_transient_separation {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (k : Nat) (hk : k < N2 p q r ε) :
    (∀ j : State, 2*ε < profileDistance
      (actualFutureWordWeight p q r (List.replicate (k+1) B)) (pureLaw p q r j)) ∧
    2*ε < profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B)) (emptyLaw p q r) := by
  have ht := theta_bounds hp hne
  have hδ := (actual_startup_cutoff hp hne hε hεk).2.2.1 k hk
  have hhalf := minority_le_half ht.1.le ht.2.le k
  have hεhalf : 2*ε < 1/2 := lt_of_lt_of_le hεk (by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2])
  have hx' := startup_coordinate_bounds hp k
  have hx : startupCoordinate p q r k ∈ Set.Icc (0:ℝ) 1 := ⟨hx'.1.le,hx'.2.le⟩
  have he : actualFutureWordWeight p q r (List.replicate (k+1) B) =
      mixtureLaw p q r (startupCoordinate p q r k) := by
    funext H w; exact actual_startup_mixture hp k H w
  rw [he]
  have hdist := mixture_pure_distances hp hx
  have h24 : 2*ε < profileDistance (mixtureLaw p q r (startupCoordinate p q r k)) (pureLaw p q r 2) ∧
      2*ε < profileDistance (mixtureLaw p q r (startupCoordinate p q r k)) (pureLaw p q r 4) := by
    rw [hdist.1,hdist.2,oriented_startup_coordinate hp hne]
    split_ifs <;> constructor <;> linarith
  constructor
  · intro j
    fin_cases j
    · change 2*ε < profileDistance (mixtureLaw p q r (startupCoordinate p q r k)) (pureLaw p q r 0)
      rw [profile_comm]
      exact lt_of_lt_of_le hεk (singleton_mixture_separation hp hx 0 (by simp))
    · change 2*ε < profileDistance (mixtureLaw p q r (startupCoordinate p q r k)) (pureLaw p q r 1)
      rw [profile_comm]
      exact lt_of_lt_of_le hεk (singleton_mixture_separation hp hx 1 (by simp))
    · exact h24.1
    · change 2*ε < profileDistance (mixtureLaw p q r (startupCoordinate p q r k)) (pureLaw p q r 3)
      rw [profile_comm]
      exact lt_of_lt_of_le hεk (singleton_mixture_separation hp hx 3 (by simp))
    · exact h24.2
  · rw [profile_comm]
    exact lt_of_lt_of_le (lt_of_lt_of_le hεk (kappa_bounds p q r).2.2.2.2.2.2.2)
      (empty_mixture_separation hp hx)

abbrev ActualPostreadHistory (p q r : ℝ) :=
  {h : List Visible // h ≠ [] ∧ 0 < historyMass p q r h}

abbrev ActualInitializedHistory (p q r : ℝ) :=
  {h : List Visible // 0 < historyMass p q r h}

noncomputable def postreadLawSet (p q r : ℝ) : Set LawProfile :=
  Set.range (fun h : ActualPostreadHistory p q r => actualFutureWordWeight p q r h.val)

noncomputable def initializedLawSet (p q r : ℝ) : Set LawProfile :=
  Set.range (fun h : ActualInitializedHistory p q r => actualFutureWordWeight p q r h.val)

/-- Both actual exact-law images are countably infinite on the unequal stratum. -/
theorem unequal_exact_classes_countably_infinite {p q r : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) :
    (postreadLawSet p q r).Countable ∧ Infinite (postreadLawSet p q r) ∧
    (initializedLawSet p q r).Countable ∧ Infinite (initializedLawSet p q r) := by
  have hc1 : (postreadLawSet p q r).Countable := Set.countable_range _
  have hc2 : (initializedLawSet p q r).Countable := Set.countable_range _
  let f : Nat → postreadLawSet p q r := fun k =>
    ⟨actualFutureWordWeight p q r (List.replicate (k+1) B),
      ⟨⟨List.replicate (k+1) B,by simp,startup_history_positive hp k⟩,rfl⟩⟩
  let g : Nat → initializedLawSet p q r := fun k =>
    ⟨actualFutureWordWeight p q r (List.replicate (k+1) B),
      ⟨⟨List.replicate (k+1) B,startup_history_positive hp k⟩,rfl⟩⟩
  have hf : Function.Injective f := by
    intro k l he
    exact actual_startup_injective hp hne (congrArg Subtype.val he)
  have hg : Function.Injective g := by
    intro k l he
    exact actual_startup_injective hp hne (congrArg Subtype.val he)
  exact ⟨hc1,Infinite.of_injective f hf,hc2,Infinite.of_injective g hg⟩

/-- Geometry of the actual finite-start source, with every parameter stratum retained. -/
structure PredictiveGeometry (p q r : ℝ) : Prop where
  branchSupport : ∀ H w,
    (0 < pureLaw p q r 2 H w ∧ 0 < pureLaw p q r 4 H w) ↔ w=(fun _ => B)
  holdingMasses : ∀ H, pureLaw p q r 2 H (fun _ => B)=(a p q)^H ∧
    pureLaw p q r 4 H (fun _ => B)=(b r)^H
  finiteGeometry : ∀ x z H, totalVariation (mixtureLaw p q r x H) (mixtureLaw p q r z H) =
    |x-z| *(1-(min (a p q) (b r))^H)
  completeGeometry : ∀ x z, x ∈ Set.Icc 0 1 → z ∈ Set.Icc 0 1 →
    profileDistance (mixtureLaw p q r x) (mixtureLaw p q r z)=|x-z|
  coherentMixtures : ∀ x, x ∈ Set.Icc 0 1 → CoherentProfile (mixtureLaw p q r x)
  positiveSeparation : 0 < kappa p q r
  pureSeparation : ∀ i j, i ≠ j → kappa p q r ≤ profileDistance (pureLaw p q r i) (pureLaw p q r j)
  singletonSeparation : ∀ x, x ∈ Set.Icc 0 1 → ∀ j, j=0 ∨ j=1 ∨ j=3 →
    kappa p q r ≤ profileDistance (pureLaw p q r j) (mixtureLaw p q r x)
  emptyMixtureSeparation : ∀ x, x ∈ Set.Icc 0 1 →
    (1/25:ℝ) ≤ profileDistance (emptyLaw p q r) (mixtureLaw p q r x)
  emptyPureSeparation : ∀ i, (1/5:ℝ) ≤ profileDistance (emptyLaw p q r) (pureLaw p q r i)
  finiteEmptyExitMasses : ∀ H,
    firstBExitMass (emptyLaw p q r) H true=(1-(b r)^H)/5 ∧
    firstBExitMass (emptyLaw p q r) H false=(1-(a p q)^H)/5
  startupLaws : ∀ (hne : a p q ≠ b r) k H w,
    actualFutureWordWeight p q r (List.replicate (k+1) B) H w =
      orientedMixture p q r (minority (theta p q r) k) H w
  cutoff : ∀ (hne : a p q ≠ b r) ε, 0 < 2*ε → 2*ε < kappa p q r →
    0 < N2 p q r ε ∧ minority (theta p q r) (N2 p q r ε) ≤ 2*ε ∧
    (∀ i < N2 p q r ε, 2*ε < minority (theta p q r) i) ∧
    (∀ k, minority (theta p q r) k ≤ 2*ε ↔ N2 p q r ε ≤ k) ∧
    (minority (theta p q r) (N2 p q r ε)=2*ε ↔
      Real.log ((1-2*ε)/(2*ε))/|Real.log (theta p q r)|=(N2 p q r ε:ℝ))
  midpointTail : ∀ (hne : a p q ≠ b r) ε, 0 < 2*ε → 2*ε < kappa p q r →
    let β := minority (theta p q r) (N2 p q r ε)/2
    CoherentProfile (orientedMixture p q r β) ∧
    profileDistance (dominantLaw p q r) (orientedMixture p q r β) ≤ ε ∧
    ∀ k, N2 p q r ε ≤ k →
      profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
        (orientedMixture p q r β) ≤ ε
  capped : ∀ (hne : a p q ≠ b r) L, 2 ≤ L →
    Function.Injective (cappedClassLaw p q r L)
  fixed : ∀ L, 2 ≤ L → Function.Injective (fixedClassLaw p q r L)
  initializedCapped : ∀ (hne : a p q ≠ b r) L, 2 ≤ L →
    Function.Injective (fun t : Option (State ⊕ Fin L) =>
      match t with | none => emptyLaw p q r | some u => cappedClassLaw p q r L u)
  equality : r=p+q → Function.Injective (fixedClassLaw p q r 2)
  unequalInfinite : a p q ≠ b r →
    (postreadLawSet p q r).Countable ∧ Infinite (postreadLawSet p q r) ∧
    (initializedLawSet p q r).Countable ∧ Infinite (initializedLawSet p q r)

/-- All geometry fields are derived from the literal source and admissibility alone. -/
theorem five_mode_predictive_geometry {p q r : ℝ} (hp : admissible p q r) : PredictiveGeometry p q r := by
  exact {
    branchSupport := branch_word_overlap hp
    holdingMasses := branch_all_B p q r
    finiteGeometry := mixture_finite_tv hp
    completeGeometry := fun x z hx hz => mixture_profile_distance hp hx hz
    coherentMixtures := fun x hx => (coherent_mixture_geometry hp hx hx).1
    positiveSeparation := kappa_positive hp
    pureSeparation := pure_pair_separation hp
    singletonSeparation := fun x hx j hj => singleton_mixture_separation hp hx j hj
    emptyMixtureSeparation := fun x hx => empty_mixture_separation hp hx
    emptyPureSeparation := empty_pure_separation hp
    finiteEmptyExitMasses := empty_first_B_exit_masses hp
    startupLaws := fun hne k H w => actual_oriented_startup hp hne k H w
    cutoff := fun hne ε hε hεk => actual_startup_cutoff hp hne hε hεk
    midpointTail := fun hne ε hε hεk => startup_midpoint_tail_bound hp hne hε hεk
    capped := fun hne L hL => (capped_predictive_classes hp hne L hL).1
    fixed := fun L hL => (fixed_length_predictive_classes hp L hL).1
    initializedCapped := fun hne L hL => (initialized_capped_class_count hp hne L hL).1
    equality := fun heq => (equality_predictive_classes hp heq).1
    unequalInfinite := unequal_exact_classes_countably_infinite hp }

end

end D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry

/- GID: D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeStrictStartup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict generated startup recurrence and initialized finite-carrier lower bounds. -/

import D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
import D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity

/-! The strict first startup cutoff and the exact recurrent selections share one total update. -/

namespace D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup
open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount
open D5.S3.ObserverMemory.Prediction.FiveModeSelfGeneratedLaws
open D5.S3.ObserverMemory.Prediction.FiveModePeriodicDiameter
open D5.S3.ObserverMemory.Prediction.FiveModeRecurrentPairRigidity
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators
noncomputable section

/-- A collision is strictly past the diameter threshold, including a later
collision outside every prescribed finite initial segment. -/
theorem startup_collision_strict {Z : Type*} (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hacc : O.toObserver.Accurate p q r ε true)
    (i j : Nat) (hij : i < j)
    (he : startupState O.toObserver i = startupState O.toObserver j) :
    minority (theta p q r) i < 2*ε := by
  classical
  have hle := startup_collision_forces_cutoff hp hne (generated_coherent O) hacc i j hij he
  apply lt_of_le_of_ne hle
  intro heq
  let z := startupState O.toObserver i
  have hper : (fun z => O.update z B)^[j-i] z = z := by
    change (fun z => O.toObserver.update z B)^[j-i] (startupState O.toObserver i) = _
    rw [← startup_shift, show i+(j-i) = j by omega]
    exact he.symm
  have ht := theta_bounds hp hne
  have hD := minority_positive ht.1 i
  have hD1 : minority (theta p q r) i < 1 :=
    (minority_le_half ht.1.le ht.2.le i).trans_lt (by norm_num)
  have h0 : profileDistance (dominantLaw p q r) (generatedLaw O.update O.row z) ≤
      minority (theta p q r) i/2 := by
    rw [heq]
    have hb := recurring_decoder_dominant_bound hp hne hacc i j hij he
    apply profile_le
    intro H
    have hc := hb H
    rw [total_variation_comm] at hc
    change totalVariation (dominantLaw p q r H) (generatedLaw O.update O.row z H) ≤ _ at hc
    linarith
  have h1 : profileDistance (orientedMixture p q r (minority (theta p q r) i))
      (generatedLaw O.update O.row z) ≤ minority (theta p q r) i/2 := by
    have hh := accurate_profile hacc (List.replicate (i+1) B)
      (startup_history_positive hp i) (Or.inl rfl)
    have hs : actualFutureWordWeight p q r (List.replicate (i+1) B) =
        orientedMixture p q r (minority (theta p q r) i) := by
      funext H w
      exact actual_oriented_startup hp hne i H w
    rw [hs] at hh
    change profileDistance _ (generatedLaw O.update O.row z) ≤ ε at hh
    calc
      _ ≤ ε := hh
      _ = minority (theta p q r) i/2 := by rw [heq]; ring
  exact periodic_diameter_obstruction O hp hne z (j-i) (by omega) hper hD hD1 h0 h1

/-- The strict cutoff increments the nonstrict cutoff exactly at a diameter tie. -/
def J (p q r ε : ℝ) : Nat :=
  if minority (theta p q r) (N2 p q r ε) = 2*ε then N2 p q r ε+1 else N2 p q r ε

private lemma J_first {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    0 < J p q r ε ∧ minority (theta p q r) (J p q r ε) < 2*ε ∧
    (∀ i < J p q r ε, 2*ε ≤ minority (theta p q r) i) ∧
    N2 p q r ε ≤ J p q r ε ∧ J p q r ε ≤ N2 p q r ε+1 ∧
    J p q r ε ≤ N1 p q r ε := by
  classical
  have ht := theta_bounds hp hne
  have he1 : 2*ε < 1/2 := by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
  have hn := cutoff_first_nonstrict ht.1 ht.2 hε he1
  change 0 < N2 p q r ε ∧ minority (theta p q r) (N2 p q r ε) ≤ 2*ε ∧
    (∀ i < N2 p q r ε, 2*ε < minority (theta p q r) i) ∧
    (∀ k, minority (theta p q r) k ≤ 2*ε ↔ N2 p q r ε ≤ k) ∧ _ at hn
  have hn1 := N1_threshold hp hne hε hεk
  have hnext := minority_strictAnti ht.1 ht.2 (show N2 p q r ε < N2 p q r ε+1 by omega)
  by_cases heq : minority (theta p q r) (N2 p q r ε) = 2*ε
  · simp only [J, if_pos heq]
    refine ⟨by omega, by linarith, ?_, by omega, by omega, ?_⟩
    · intro i hi
      by_cases hlt : i < N2 p q r ε
      · exact (hn.2.2.1 i hlt).le
      · have hi' : i = N2 p q r ε := by omega
        simpa [hi',heq]
    · have hepos : 0 < ε := by linarith
      have hd : N2 p q r ε < N1 p q r ε := by
        by_contra h
        have hh := (minority_strictAnti ht.1 ht.2).antitone (le_of_not_gt h)
        have hh1 := hn1.2.1
        rw [heq] at hh
        linarith
      omega
  · simp only [J, if_neg heq]
    refine ⟨hn.1, lt_of_le_of_ne hn.2.1 heq, fun i hi => (hn.2.2.1 i hi).le, le_rfl, by omega, ?_⟩
    exact (hn.2.2.2.1 _).mp (hn1.2.1.trans (by linarith))

/-- Every initial index before J differs from every later index, without any
upper bound on the later index. -/
theorem startup_never_recurs_before_J {Z : Type*} (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true)
    (i : Nat) (hi : i < J p q r ε) (j : Nat) (hij : i < j) :
    startupState O.toObserver i ≠ startupState O.toObserver j := by
  intro he
  exact (not_lt_of_ge ((J_first hp hne hε hεk).2.2.1 i hi))
    (startup_collision_strict O hp hne hacc i j hij he)


private lemma startup_pure_separation {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (k : Nat) (hk : k < N1 p q r ε) (i : State) :
    ε < profileDistance (actualFutureWordWeight p q r (List.replicate (k+1) B))
      (pureLaw p q r i) := by
  classical
  let x := minority (theta p q r) k
  have ht := theta_bounds hp hne
  have hx : x ∈ Set.Icc 0 1 :=
    ⟨(minority_positive ht.1 k).le, (minority_le_half ht.1.le ht.2.le k).trans (by norm_num)⟩
  have hxhalf : x ≤ 1/2 := minority_le_half ht.1.le ht.2.le k
  have hex : ε < x := (N1_threshold hp hne hε hεk).2.2.1 k hk
  have hek : ε < kappa p q r := by linarith
  have he : actualFutureWordWeight p q r (List.replicate (k+1) B) = orientedMixture p q r x := by
    funext H w; exact actual_oriented_startup hp hne k H w
  rw [he]
  have hgeneral (t : ℝ) (ht : t ∈ Set.Icc 0 1) (hxt : x ≤ t) (hxt' : x ≤ 1-t) :
      ε < profileDistance (mixtureLaw p q r t) (pureLaw p q r i) := by
    by_cases hi : i = 0 ∨ i = 1 ∨ i = 3
    · rw [profile_comm]
      exact hek.trans_le (singleton_mixture_separation hp ht i hi)
    · have hi' : i = 2 ∨ i = 4 := by fin_cases i <;> simp_all
      rcases hi' with rfl | rfl
      · rw [(mixture_pure_distances hp ht).1]
        exact hex.trans_le hxt'
      · rw [(mixture_pure_distances hp ht).2]
        exact hex.trans_le hxt
  unfold orientedMixture
  split_ifs
  · exact hgeneral (1-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩ (by linarith) (by linarith)
  · exact hgeneral x hx le_rfl (by linarith)

private lemma exact_initialized_injection {Z : Type*} [Fintype Z] (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (hacc : O.toObserver.Accurate p q r ε true) :
    ∃ f : SharpState (min (N1 p q r ε) (J p q r ε+1)) → Z, Function.Injective f := by
  classical
  have he1 : ε < 1 := by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
  obtain ⟨g,hg,hgexact⟩ := (recurrent_pair_rigidity hp O he1
    (fun h hh H _ => hacc h hh (Or.inl rfl) H)).2.2.2.2.2.2
  let M := min (N1 p q r ε) (J p q r ε+1)
  have hstartup : ∀ (k l : Fin M), startupState O.toObserver k.val =
      startupState O.toObserver l.val → k = l := by
    intro k l he
    apply Fin.ext
    rcases lt_trichotomy k.val l.val with hlt | heq | hlt
    · have hj : k.val < J p q r ε := by have := min_le_right (N1 p q r ε) (J p q r ε+1); omega
      exact (startup_never_recurs_before_J O hp hne hε hεk hacc _ hj _ hlt he).elim
    · exact heq
    · have hj : l.val < J p q r ε := by have := min_le_right (N1 p q r ε) (J p q r ε+1); omega
      exact (startup_never_recurs_before_J O hp hne hε hεk hacc _ hj _ hlt he.symm).elim
  have hcross (i : State) (k : Fin M) : g i ≠ startupState O.toObserver k.val := by
    intro he
    have ha := accurate_profile hacc (List.replicate (k.val+1) B)
      (startup_history_positive hp k.val) (Or.inl rfl)
    change profileDistance _ (generatedLaw O.update O.row (startupState O.toObserver k.val)) ≤ ε at ha
    rw [← he, (hgexact i).2] at ha
    have hk : k.val < N1 p q r ε := lt_of_lt_of_le k.isLt (min_le_left _ _)
    exact (not_lt_of_ge ha) (startup_pure_separation hp hne hε hεk k.val hk i)
  let charged : State ⊕ Fin M → Z := fun t => match t with
    | .inl i => g i
    | .inr k => startupState O.toObserver k.val
  have hcharged : Function.Injective charged := by
    intro x y he
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hg he)
      | inr k => exact (hcross i k he).elim
    | inr k =>
      cases y with
      | inl i => exact (hcross i k he.symm).elim
      | inr l => exact congrArg Sum.inr (hstartup k l he)
  have hnot (t : State ⊕ Fin M) : O.initial ≠ charged t := by
    have hr : charged t ∈ O.toObserver.Reached p q r := by
      cases t with
      | inl i => exact (hgexact i).1
      | inr k => exact ⟨List.replicate (k.val+1) B, by simp, startup_history_positive hp k.val, rfl⟩
    obtain ⟨h,hn,hh,he⟩ := hr
    rw [← he]
    exact postread_initialization_extra_state hp hne hεk (generated_coherent O) hacc h hn hh
  let f : SharpState M → Z := fun t => match t with
    | none => O.initial
    | some t => charged t
  refine ⟨f,?_⟩
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => exact (hnot y he).elim
  | some x =>
    cases y with
    | none => exact (hnot x he.symm).elim
    | some y => exact congrArg some (hcharged he)

/-- The whole finite carrier includes initialization and any generated-only
configurations. The five selected recurrent configurations are actually reached. -/
theorem generated_initialized_lower {Z : Type*} [Fintype Z] (O : GeneratedObserver Z)
    {p q r ε : ℝ} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r)
    (hacc : ∀ h : List Visible, 0 < historyMass p q r h → ∀ H : Nat, 0 < H →
      totalVariation (actualFutureWordWeight p q r h H)
        (generatedLaw O.update O.row (O.toObserver.run h) H) ≤ ε) :
    6+min (N1 p q r ε) (J p q r ε+1) ≤ Fintype.card Z := by
  obtain ⟨f,hf⟩ := exact_initialized_injection O hp hne hε hεk (guarantee_accurate hp O hacc)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, sharp_state_card] using hh

/-- The strict full-class lower bound is consumed by the existing attained
minimum, with the original off-tie and tie consequences and existing upper bound. -/
theorem initialized_generated_strict_minimum {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2*ε) (hεk : 2*ε < kappa p q r) :
    (∀ n, Attainable p q r ε n → 6+min (N1 p q r ε) (J p q r ε+1) ≤ n) ∧
    6+min (N1 p q r ε) (J p q r ε+1) ≤ minimum hp hne hε hεk ∧
    minimum hp hne hε hεk ≤ 6+N1 p q r ε ∧
    (N2 p q r ε < N1 p q r ε → 7+N2 p q r ε ≤ minimum hp hne hε hεk) ∧
    (minority (theta p q r) (N2 p q r ε) = 2*ε → N2 p q r ε+2 ≤ N1 p q r ε →
      8+N2 p q r ε ≤ minimum hp hne hε hεk) := by
  have hbound (n : Nat) (hn : Attainable p q r ε n) :
      6+min (N1 p q r ε) (J p q r ε+1) ≤ n := by
    obtain ⟨O,hO⟩ := hn
    simpa only [Fintype.card_fin] using generated_initialized_lower O hp hne hε hεk
      (fun h hh H _ => hO h hh (Or.inl rfl) H)
  have hl := hbound _ (minimum_attained hp hne hε hεk)
  have hu := (initialized_generated_minimum hp hne hε hεk).2.2.2.1
  have hj := J_first hp hne hε hεk
  refine ⟨hbound,hl,hu,?_,?_⟩
  · intro hn
    have hN : N2 p q r ε+1 ≤ min (N1 p q r ε) (J p q r ε+1) := by
      exact le_min (by omega) (by omega)
    omega
  · intro heq hn
    have hJ : J p q r ε = N2 p q r ε+1 := by simp only [J, if_pos heq]
    have hN : N2 p q r ε+2 ≤ min (N1 p q r ε) (J p q r ε+1) := by
      exact le_min hn (by omega)
    omega

end
end D5.S3.ObserverMemory.Prediction.FiveModeStrictStartup

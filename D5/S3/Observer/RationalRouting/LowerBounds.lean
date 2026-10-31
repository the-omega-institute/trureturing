/- GID: D5/S3/Observer/RationalRouting/LowerBounds
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/LowerBounds
   mirror-E: none(waiver:exact-symbolic-source)
   anchors: []
   utility: none
   digest: Every original-rational controller needs two actions and every preset controller needs four. -/

import D5.S3.Observer.RationalRouting.Source

/-! Universal lower bounds from finite-run replay and incompatible short prefixes. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

/-- The k-th actual letter is the k-th letter of one public schedule.
Read scales, pauses, local computation and stopping are unrestricted. -/
def Follows (schedule : ℕ → Bool) (w : List Bool) : Prop :=
  ∀ k : ℕ, k < w.length → w[k]? = some (schedule k)

/-- The action cap is required on every completed run on every prior member. -/
def ActionCap {State Output : Type} (code : State → Command State Output)
    (init : State) (h : ℕ) : Prop :=
  ∀ x, Prior x → ∀ out v reads, Run code x init [] out v reads → v.length ≤ h

/-- All terminal histories use prefixes of the same schedule. Finite schedules
are included by arbitrary extension after their last executable letter. -/
def Preset {State Output : Type} (code : State → Command State Output)
    (init : State) (schedule : ℕ → Bool) : Prop :=
  ∀ x, Prior x → ∀ out v reads, Run code x init [] out v reads → Follows schedule v

private theorem grid_den_dvd (w : List Bool) (s : ℕ) (x : ℚ) (hg : Grid w s x) :
    (attain w x).den ∣ 2^s := by
  obtain ⟨k,hk⟩ := hg
  have heq : attain w x = (k : ℚ)/(2^s : ℕ) := by
    apply (eq_div_iff (by positivity : (2^s : ℕ) ≠ (0 : ℚ))).mpr
    simpa [mul_comm] using hk
  rw [heq]
  have hh := Rat.den_dvd k (2^s : ℕ)
  have hh' : ((((k : ℚ)/(2^s : ℕ)).den : ℕ) : ℤ) ∣ (2^s : ℕ) := by
    simpa [Rat.divInt_eq_div] using hh
  exact_mod_cast hh'

private theorem not_dvd_two_power {d : ℕ} (p : ℕ) (hp : Nat.Prime p)
    (hpd : p ∣ d) (hpn : ¬ p ∣ 2) (s : ℕ) : ¬ d ∣ 2^s := by
  intro h
  exact hpn (hp.dvd_of_dvd_pow (hpd.trans h))

private theorem bad_denominator (s d : ℕ)
    (hd : d ∈ [3,5,6,7,9,11,12,13,15,19,20]) : ¬ d ∣ 2^s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_dvd_two_power 3 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 5 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 3 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 7 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 3 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 11 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 3 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 13 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 3 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 19 (by norm_num) (by norm_num) (by norm_num) s
  · exact not_dvd_two_power 5 (by norm_num) (by norm_num) (by norm_num) s

/-- Exact attained-prefix classification, with chronological orientation. -/
private theorem short_grid_routes (i : Bool) (w : List Bool) (s : ℕ)
    (hlen : w.length ≤ 3) (hg : Grid w s (endpoint i)) :
    (i = false ∧ (w = [false,false] ∨ w = [false,false,true])) ∨
    (i = true ∧ (w = [true,false] ∨ w = [true,false,true])) := by
  have hd := grid_den_dvd w s (endpoint i) hg
  rcases w with _ | ⟨a,w⟩
  · cases i <;> norm_num [attain, endpoint] at hd ⊢
    all_goals exfalso; apply bad_denominator s _ ?_ hd; simp
  rcases w with _ | ⟨b,w⟩
  · cases a <;> cases i <;> norm_num [attain,step,endpoint] at hd ⊢
    all_goals exfalso; apply bad_denominator s _ ?_ hd; simp
  rcases w with _ | ⟨c,w⟩
  · cases a <;> cases b <;> cases i <;> norm_num [attain,step,endpoint] at hd ⊢
    all_goals exfalso; apply bad_denominator s _ ?_ hd; simp
  rcases w with _ | ⟨d,w⟩
  · cases a <;> cases b <;> cases c <;> cases i <;>
      norm_num [attain,step,endpoint] at hd ⊢
    all_goals exfalso; apply bad_denominator s _ ?_ hd; simp
  · simp at hlen
    omega

private theorem run_word_prefix {State Output : Type} {code : State → Command State Output}
    {x : ℚ} {st : State} {w : List Bool} {out : Output} {v : List Bool}
    {reads : List (List Bool × ℕ)} (run : Run code x st w out v reads) : w <+: v := by
  induction run with
  | halt _ => exact ⟨[], by simp⟩
  | work _ _ ih => exact ih
  | move _ _ ih => exact (List.prefix_append _ _).trans ih
  | read _ _ ih => exact ih

private theorem run_read_prefix {State Output : Type} {code : State → Command State Output}
    {x : ℚ} {st : State} {w : List Bool} {out : Output} {v : List Bool}
    {reads : List (List Bool × ℕ)} (run : Run code x st w out v reads) :
    ∀ p ∈ reads, p.1 <+: v := by
  induction run with
  | halt _ => simp
  | work _ _ ih => exact ih
  | move _ _ ih => exact ih
  | read _ run ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact run_word_prefix run
    · exact ih p hp

private theorem endpoint_run_two {State Output : Type}
    {code : State → Command State Output} {init : State} {target : ℚ → Output}
    (correct : Correct code init target) (injective : Set.InjOn target {x | Prior x})
    (i : Bool) {out : Output} {v : List Bool} {reads : List (List Bool × ℕ)}
    (run : Run code (endpoint i) init [] out v reads) : 2 ≤ v.length := by
  by_contra h
  obtain ⟨⟨w,s⟩,hp,hg⟩ := endpoint_run_requires_grid correct injective i run
  have hlen : w.length ≤ v.length := (run_read_prefix run (w,s) hp).length_le
  have hshort : w.length ≤ 3 := by omega
  rcases short_grid_routes i w s hshort hg with ⟨_,rfl|rfl⟩ | ⟨_,rfl|rfl⟩ <;>
    simp at hlen <;> omega

private theorem endpoint_first_action {State Output : Type}
    {code : State → Command State Output} {init : State} {target : ℚ → Output}
    (correct : Correct code init target) (injective : Set.InjOn target {x | Prior x})
    (i : Bool) {out : Output} {v : List Bool} {reads : List (List Bool × ℕ)}
    (run : Run code (endpoint i) init [] out v reads) (hlen : v.length ≤ 3) :
    v[0]? = some i := by
  obtain ⟨⟨w,s⟩,hp,hg⟩ := endpoint_run_requires_grid correct injective i run
  have hpref := run_read_prefix run (w,s) hp
  have hshort : w.length ≤ 3 := hpref.length_le.trans hlen
  obtain ⟨suffix, hsuffix⟩ := hpref
  rcases short_grid_routes i w s hshort hg with ⟨rfl,rfl|rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    rw [← hsuffix] <;> rfl

/-- Against arbitrary deterministic controllers and arbitrary preset schedules,
correct original recovery forces uniform action caps at least two and four.
The targets may be any functions injective on the original rational prior. -/
theorem original_action_lower_bounds {State Output : Type}
    {code : State → Command State Output} {init : State} {target : ℚ → Output}
    (correct : Correct code init target) (injective : Set.InjOn target {x | Prior x}) :
    (∀ h, ActionCap code init h → 2 ≤ h) ∧
    (∀ schedule, Preset code init schedule → ∀ h, ActionCap code init h → 4 ≤ h) := by
  have hp : ∀ i, Prior (endpoint i) := fun i => ⟨i,Or.inl rfl⟩
  constructor
  · intro h cap
    obtain ⟨out,v,reads,run⟩ := (correct _ (hp false)).1
    exact (endpoint_run_two correct injective false run).trans (cap _ (hp false) _ _ _ run)
  · intro schedule preset h cap
    by_contra hh
    have h3 : h ≤ 3 := by omega
    obtain ⟨out0,v0,reads0,run0⟩ := (correct _ (hp false)).1
    obtain ⟨out1,v1,reads1,run1⟩ := (correct _ (hp true)).1
    have hlen0 := (cap _ (hp false) _ _ _ run0).trans h3
    have hlen1 := (cap _ (hp true) _ _ _ run1).trans h3
    have hfirst0 := endpoint_first_action correct injective false run0 hlen0
    have hfirst1 := endpoint_first_action correct injective true run1 hlen1
    have hpos0 : 0 < v0.length := by have := endpoint_run_two correct injective false run0; omega
    have hpos1 : 0 < v1.length := by have := endpoint_run_two correct injective true run1; omega
    have hs0 := preset _ (hp false) _ _ _ run0 0 hpos0
    have hs1 := preset _ (hp true) _ _ _ run1 0 hpos1
    rw [hfirst0] at hs0
    rw [hfirst1] at hs1
    have : (false : Bool) = true := Option.some.inj (hs0.trans hs1.symm)
    cases this

#print axioms original_action_lower_bounds

end D5.S3.Observer.RationalRouting

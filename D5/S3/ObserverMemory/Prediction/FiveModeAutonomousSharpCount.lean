/- GID: D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite autonomous common - law observers for the actual finite - start source. -/

import D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry

namespace D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount

open D5.S3.ObserverMemory.Prediction.FiniteStartFiveModeSource
open D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open scoped BigOperators

noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- One total update and one fixed complete - law decoder, without an age input. -/
structure Observer (Z : Type*) where
  initial : Z
  update : Z → Visible → Z
  decoder : Z → LawProfile

def Observer.run {Z : Type*} (O : Observer Z) (h : List Visible) : Z :=
  h.foldl O.update O.initial

def Observer.Coherent {Z : Type*} (O : Observer Z) : Prop :=
  ∀ z, CoherentProfile (O.decoder z)

def Observer.Accurate {Z : Type*} (O : Observer Z) (p q r ε : ℝ)
    (queryEmpty : Bool) : Prop :=
  ∀ h : List Visible, 0 < historyMass p q r h →
    (queryEmpty = true ∨ h ≠ []) →
    ∀ H : Nat, totalVariation (actualFutureWordWeight p q r h H)
      (O.decoder (O.run h) H) ≤ ε

def Observer.Reached {Z : Type*} (O : Observer Z) (p q r : ℝ) : Set Z :=
  {z | ∃ h : List Visible, h ≠ [] ∧ 0 < historyMass p q r h ∧ O.run h = z}

lemma run_snoc {Z : Type*} (O : Observer Z) (h : List Visible) (y : Visible) :
    O.run (h ++ [y]) = O.update (O.run h) y := by
  simp [Observer.run, List.foldl_append]

lemma actual_coherent {p q r : ℝ} (hp : admissible p q r)
    (h : List Visible) (hpos : 0 < historyMass p q r h) :
    CoherentProfile (actualFutureWordWeight p q r h) := by
  constructor
  · intro H
    exact ⟨fun w => (actual_law_probability_and_coherence hp h hpos H w).1,
      (actual_law_probability_and_coherence hp h hpos H (fun _ => B)).2.1⟩
  · intro H w
    exact (actual_law_probability_and_coherence hp h hpos H w).2.2

lemma accurate_profile {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hacc : O.Accurate p q r ε queryEmpty)
    (h : List Visible) (hpos : 0 < historyMass p q r h)
    (hq : queryEmpty = true ∨ h ≠ []) :
    profileDistance (actualFutureWordWeight p q r h) (O.decoder (O.run h)) ≤ ε :=
  profile_le (hacc h hpos hq)

/-- The triangle argument uses arbitrary probability profiles, not mixture decoders. -/
lemma common_state_distance {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hacc : O.Accurate p q r ε queryEmpty)
    (h t : List Visible) (hh : 0 < historyMass p q r h)
    (ht : 0 < historyMass p q r t)
    (hq : queryEmpty = true ∨ h ≠ []) (tq : queryEmpty = true ∨ t ≠ [])
    (he : O.run h = O.run t) :
    profileDistance (actualFutureWordWeight p q r h)
      (actualFutureWordWeight p q r t) ≤ 2 * ε := by
  apply profile_le
  intro H
  have h1 := hacc h hh hq H
  have h2 := hacc t ht tq H
  rw [← he] at h2
  have htri := total_variation_triangle (actualFutureWordWeight p q r h H)
    (O.decoder (O.run h) H) (actualFutureWordWeight p q r t H)
  rw [total_variation_comm (O.decoder (O.run h) H)] at htri
  linarith

abbrev SharpState (N : Nat) := Option (State ⊕ Fin N)

def dominantState (p q r : ℝ) : State := if b r < a p q then 2 else 4

def encodeSource (d : State) (N : Nat) : SourceTag → SharpState N
  | .start => none
  | .pure i => some (.inl i)
  | .startup k => if hk : k < N then some (.inr ⟨k,hk⟩) else some (.inl d)

def representative {N : Nat} : SharpState N → SourceTag
  | none => .start
  | some (.inl i) => .pure i
  | some (.inr k) => .startup k

/-- Singleton resets and the saturated B orbit are defined on every configuration. -/
def sharpUpdate (d : State) (N : Nat) (z : SharpState N) (y : Visible) : SharpState N :=
  encodeSource d N (sourceUpdate (representative z) y)

lemma dominant_successor (p q r : ℝ) :
    pureBSuccessor (dominantState p q r) = dominantState p q r := by
  unfold dominantState
  split_ifs <;> norm_num [pureBSuccessor, Fin.ext_iff]

lemma dominant_law (p q r : ℝ) :
    pureLaw p q r (dominantState p q r) = dominantLaw p q r := by
  unfold dominantState dominantLaw
  split_ifs <;> rfl

lemma sharp_source_step (d : State) (N : Nat) (hd : pureBSuccessor d = d)
    (z : SourceTag) (y : Visible) :
    sharpUpdate d N (encodeSource d N z) y = encodeSource d N (sourceUpdate z y) := by
  cases z with
  | start => rfl
  | pure i => rfl
  | startup k =>
    by_cases hk : k < N
    · simp [encodeSource, hk, sharpUpdate, representative]
    · have hk1 : ¬ k + 1 < N := by omega
      fin_cases y <;> simp [encodeSource, hk, hk1, sharpUpdate, representative, sourceUpdate]
      fin_cases d <;> simp [pureBSuccessor] at hd <;> simp_all [sourceUpdate]

lemma sharp_source_run (d : State) (N : Nat) (hd : pureBSuccessor d = d)
    (h : List Visible) :
    h.foldl (sharpUpdate d N) none = encodeSource d N (sourceRun h) := by
  exact List.foldl_hom (encodeSource d N) (l := h) (init := .start)
    (sharp_source_step d N hd)

def midpointDecoder (p q r ε : ℝ) : SharpState (N2 p q r ε) → LawProfile
  | none => emptyLaw p q r
  | some (.inl i) => if i = dominantState p q r then
      orientedMixture p q r (minority (theta p q r) (N2 p q r ε)/2)
      else pureLaw p q r i
  | some (.inr k) => actualFutureWordWeight p q r (List.replicate (k.val + 1) B)

def midpointObserver (p q r ε : ℝ) : Observer (SharpState (N2 p q r ε)) where
  initial := none
  update := sharpUpdate (dominantState p q r) (N2 p q r ε)
  decoder := midpointDecoder p q r ε

lemma midpoint_run (p q r ε : ℝ) (h : List Visible) :
    (midpointObserver p q r ε).run h =
      encodeSource (dominantState p q r) (N2 p q r ε) (sourceRun h) :=
  sharp_source_run _ _ (dominant_successor p q r) h

theorem midpoint_decoder_coherent {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r) :
    (midpointObserver p q r ε).Coherent := by
  intro z
  cases z with
  | none => exact empty_coherent hp
  | some z =>
    cases z with
    | inl i =>
      dsimp [midpointObserver, midpointDecoder]
      split_ifs
      · exact (startup_midpoint_tail_bound hp hne hε hεk).1
      · exact pure_coherent hp i
    | inr k => exact actual_coherent hp _ (startup_history_positive hp k.val)

lemma actual_pure_law {p q r : ℝ} (h : List Visible) (hne : h ≠ [])
    (i : State) (hi : acquiredPosterior p q r h = pureVector i) :
    actualFutureWordWeight p q r h = pureLaw p q r i := by
  funext H w
  simp [actualFutureWordWeight, hne, hi, pureLaw]

theorem midpoint_observer_accuracy {p q r ε : ℝ} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r) :
    (midpointObserver p q r ε).Accurate p q r ε true := by
  intro h hpos _ H
  have hε0 : 0 ≤ ε := by linarith
  by_cases hempty : h = []
  · subst h
    simp [Observer.run, midpointObserver, midpointDecoder, actualFutureWordWeight,
      emptyLaw, totalVariation, hε0]
  · rcases positive_history_classification p q r h hempty hpos with ⟨k,hk,hr,_⟩ | ⟨i,hr,hi⟩
    · subst h
      rw [midpoint_run, hr]
      by_cases hkn : k < N2 p q r ε
      · simp [encodeSource, hkn, midpointObserver, midpointDecoder, totalVariation, hε0]
      · have ht := (startup_midpoint_tail_bound hp hne hε hεk).2.2 k (by omega)
        have hc := (startup_midpoint_tail_bound hp hne hε hεk).1.1
        simpa [encodeSource, hkn, midpointObserver, midpointDecoder] using
          (finite_le_profile (actual_coherent hp _ hpos).1 hc H).trans ht
    · rw [midpoint_run, hr]
      have he := actual_pure_law h hempty i hi
      by_cases hid : i = dominantState p q r
      · subst i
        have ht := (startup_midpoint_tail_bound hp hne hε hεk).2.1
        have hc := (startup_midpoint_tail_bound hp hne hε hεk).1.1
        rw [he, dominant_law]
        simpa [encodeSource, midpointObserver, midpointDecoder] using
          (finite_le_profile (by rw [← dominant_law]; exact pure_probability hp _) hc H).trans ht
      · simp [he, encodeSource, midpointObserver, midpointDecoder, hid, totalVariation, hε0]

lemma sharp_state_card (N : Nat) : Fintype.card (SharpState N) = 6 + N := by
  simp [SharpState, Fintype.card_option, Fintype.card_sum]
  omega

lemma midpoint_reached_iff {p q r ε : ℝ} (hp : admissible p q r)
    (z : SharpState (N2 p q r ε)) :
    z ∈ (midpointObserver p q r ε).Reached p q r ↔ z ≠ none := by
  constructor
  · rintro ⟨h,hne,_,hr⟩
    rw [midpoint_run] at hr
    have hs := source_run_ne_start h hne
    cases he : sourceRun h with
    | start => exact (hs he).elim
    | pure i => rw [he] at hr; rw [← hr]; simp [encodeSource]
    | startup k =>
      rw [he] at hr
      simp only [encodeSource] at hr
      split_ifs at hr <;> simp [← hr]
  · intro hz
    cases z with
    | none => exact (hz rfl).elim
    | some z =>
      cases z with
      | inl i =>
        obtain ⟨h,hr,hpos,_,he⟩ := complete_source_tag_reachability hp (.pure i)
        refine ⟨h,?_,hpos,?_⟩
        · intro hn; have := he.mp hn; cases this
        · rw [midpoint_run,hr]; rfl
      | inr k =>
        refine ⟨List.replicate (k.val + 1) B,by simp, startup_history_positive hp k.val,?_⟩
        rw [midpoint_run]
        simp [sourceRun,startup_all_b,encodeSource,k.isLt]

theorem midpoint_observer_reachability {p q r ε : ℝ} (hp : admissible p q r) :
    (midpointObserver p q r ε).Reached p q r = {z | z ≠ none} ∧
    Nat.card ↥((midpointObserver p q r ε).Reached p q r) = 5 + N2 p q r ε ∧
    Fintype.card (SharpState (N2 p q r ε)) = 6 + N2 p q r ε := by
  have he : (midpointObserver p q r ε).Reached p q r = {z | z ≠ none} :=
    Set.ext (midpoint_reached_iff hp)
  refine ⟨he,?_,sharp_state_card _⟩
  let f : State ⊕ Fin (N2 p q r ε) → ↥((midpointObserver p q r ε).Reached p q r) :=
    fun z => ⟨some z,(midpoint_reached_iff hp _).mpr (by simp)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Option.some.inj (congrArg Subtype.val h)
    · rintro ⟨z,hz⟩
      cases z with
      | none => exact ((midpoint_reached_iff hp _).mp hz rfl).elim
      | some z => exact ⟨z,rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_eq_fintype_card]

def startupState {Z : Type*} (O : Observer Z) (k : Nat) : Z :=
  O.run (List.replicate (k + 1) B)

lemma fold_replicate {Z : Type*} (u : Z → Visible → Z) (z : Z) (n : Nat) :
    (List.replicate n B).foldl u z = (fun x => u x B)^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ,List.foldl_cons,Function.iterate_succ_apply] using ih (u z B)

lemma startup_shift {Z : Type*} (O : Observer Z) (i n : Nat) :
    startupState O (i + n) = (fun z => O.update z B)^[n] (startupState O i) := by
  simp only [startupState,Observer.run,fold_replicate]
  rw [show i + n + 1 = n + (i + 1) by omega,Function.iterate_add_apply]

/-- A collision recurs only through repetitions of the same total B update. -/
theorem startup_collision_recurrence {Z : Type*} (O : Observer Z)
    (i j : Nat) (hij : i < j) (he : startupState O i = startupState O j) :
    ∀ ℓ : Nat, startupState O (i + ℓ * (j - i)) = startupState O i := by
  have hstep : (fun z => O.update z B)^[j - i] (startupState O i) = startupState O i := by
    rw [← startup_shift,show i + (j - i) = j by omega]
    exact he.symm
  intro ℓ
  rw [startup_shift,Nat.mul_comm ℓ (j - i),Function.iterate_mul]
  exact Function.iterate_fixed hstep ℓ

/-- Finite - horizon triangles constrain the fixed decoder at a recurring actual startup state. -/
theorem recurring_decoder_dominant_bound {Z : Type*} {O : Observer Z}
    {p q r ε : ℝ} {queryEmpty : Bool} (hp : admissible p q r)
    (hne : a p q ≠ b r)
    (hacc : O.Accurate p q r ε queryEmpty)
    (i j : Nat) (hij : i < j) (he : startupState O i = startupState O j) :
    ∀ H, totalVariation (O.decoder (startupState O i) H) (dominantLaw p q r H) ≤ ε := by
  intro H
  have ht := theta_bounds hp hne
  have hindex : Filter.Tendsto (fun ℓ : Nat => i + ℓ * (j - i)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := fun ℓ : Nat => ℓ) _ Filter.tendsto_id
    intro ℓ
    have hm : ℓ ≤ ℓ * (j - i) := Nat.le_mul_of_pos_right ℓ (by omega)
    omega
  have hlim := ((minority_tendsto_zero ht.1 ht.2).comp hindex).const_add ε
  simp only [add_zero] at hlim
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro ℓ
  let k := i + ℓ * (j - i)
  have hr : startupState O k = startupState O i := startup_collision_recurrence O i j hij he ℓ
  have ha := hacc (List.replicate (k + 1) B) (startup_history_positive hp k) (Or.inr (by simp)) H
  change totalVariation (actualFutureWordWeight p q r (List.replicate (k + 1) B) H)
    (O.decoder (startupState O k) H) ≤ ε at ha
  rw [hr] at ha
  have hd : ProbabilityProfile (dominantLaw p q r) := by
    rw [← dominant_law]; exact pure_probability hp _
  have hb := (finite_le_profile (actual_startup_geometry hp hne k k).1.1 hd H)
  rw [(actual_startup_geometry hp hne k k).2.2] at hb
  have htri := total_variation_triangle (O.decoder (startupState O i) H)
    (actualFutureWordWeight p q r (List.replicate (k + 1) B) H) (dominantLaw p q r H)
  rw [total_variation_comm] at ha
  dsimp [k] at *
  linarith

theorem startup_collision_forces_cutoff {Z : Type*} {O : Observer Z}
    {p q r ε : ℝ} {queryEmpty : Bool} (hp : admissible p q r)
    (hne : a p q ≠ b r) (hc : O.Coherent)
    (hacc : O.Accurate p q r ε queryEmpty)
    (i j : Nat) (hij : i < j) (he : startupState O i = startupState O j) :
    minority (theta p q r) i ≤ 2 * ε := by
  have hb := recurring_decoder_dominant_bound hp hne hacc i j hij he
  have hi := accurate_profile hacc (List.replicate (i + 1) B)
    (startup_history_positive hp i) (Or.inr (by simp))
  have hd : profileDistance (actualFutureWordWeight p q r (List.replicate (i + 1) B))
      (dominantLaw p q r) ≤ 2 * ε := by
    apply profile_le
    intro H
    have htri := total_variation_triangle (actualFutureWordWeight p q r (List.replicate (i + 1) B) H)
      (O.decoder (startupState O i) H) (dominantLaw p q r H)
    have hh := (finite_le_profile (actual_startup_geometry hp hne i i).1.1
      (hc (startupState O i)).1 H).trans hi
    linarith [hb H]
  simpa only [(actual_startup_geometry hp hne i i).2.2] using hd

lemma pure_witness_actual {p q r : ℝ} (hp : admissible p q r) (i : State) :
    pureWitness i ≠ [] ∧ 0 < historyMass p q r (pureWitness i) ∧
      actualFutureWordWeight p q r (pureWitness i) = pureLaw p q r i := by
  have hne : pureWitness i ≠ [] := by fin_cases i <;> simp [pureWitness]
  have h := positive_pure_padding hp i 0
  simp only [List.replicate_zero,List.append_nil,pow_zero,mul_one] at h
  exact ⟨hne,h.2.1,actual_pure_law _ hne i h.2.2⟩

def chargedState {Z : Type*} (O : Observer Z) (N : Nat) : State ⊕ Fin N → Z
  | .inl i => O.run (pureWitness i)
  | .inr k => startupState O k.val

lemma charged_reached {Z : Type*} {O : Observer Z} {p q r : ℝ}
    (hp : admissible p q r) (N : Nat) (t : State ⊕ Fin N) :
    chargedState O N t ∈ O.Reached p q r := by
  cases t with
  | inl i => exact ⟨pureWitness i,(pure_witness_actual hp i).1,(pure_witness_actual hp i).2.1,rfl⟩
  | inr k => exact ⟨List.replicate (k.val + 1) B,by simp,startup_history_positive hp k.val,rfl⟩

/-- The pure witnesses and strict pre - cutoff startup witnesses form one disjoint injection. -/
theorem unequal_charged_injective {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r)
    (hc : O.Coherent) (hacc : O.Accurate p q r ε queryEmpty) :
    Function.Injective (chargedState O (N2 p q r ε)) := by
  have hpure : ∀ i j : State, O.run (pureWitness i) = O.run (pureWitness j) → i = j := by
    intro i j he
    by_contra hn
    have hd := common_state_distance hacc _ _ (pure_witness_actual hp i).2.1
      (pure_witness_actual hp j).2.1 (Or.inr (pure_witness_actual hp i).1)
      (Or.inr (pure_witness_actual hp j).1) he
    rw [(pure_witness_actual hp i).2.2,(pure_witness_actual hp j).2.2] at hd
    exact (not_le_of_gt (hεk.trans_le (pure_pair_separation hp i j hn))) hd
  have hcross : ∀ (i : State) (k : Fin (N2 p q r ε)),
      O.run (pureWitness i) ≠ startupState O k.val := by
    intro i k he
    have hd := common_state_distance hacc _ _ (startup_history_positive hp k.val)
      (pure_witness_actual hp i).2.1 (Or.inr (by simp))
      (Or.inr (pure_witness_actual hp i).1) he.symm
    rw [(pure_witness_actual hp i).2.2] at hd
    exact (not_le_of_gt ((startup_transient_separation hp hne hε hεk k.val k.isLt).1 i)) hd
  have hstartup : ∀ (i j : Fin (N2 p q r ε)), startupState O i.val = startupState O j.val → i = j := by
    intro i j he
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · have hd := startup_collision_forces_cutoff hp hne hc hacc i.val j.val hij he
      have hs := (actual_cutoff_geometry hp hne hε hεk).2.2.2.1 i.val i.isLt
      rw [(actual_startup_geometry hp hne i.val i.val).2.2] at hs
      exact (not_le_of_gt hs hd).elim
    · exact hij
    · have hd := startup_collision_forces_cutoff hp hne hc hacc j.val i.val hij he.symm
      have hs := (actual_cutoff_geometry hp hne hε hεk).2.2.2.1 j.val j.isLt
      rw [(actual_startup_geometry hp hne j.val j.val).2.2] at hs
      exact (not_le_of_gt hs hd).elim
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hpure i j he)
    | inr k => exact (hcross i k he).elim
  | inr k =>
    cases y with
    | inl i => exact (hcross i k he.symm).elim
    | inr l => exact congrArg Sum.inr (hstartup k l he)

lemma initial_B_half {p q r : ℝ} (hp : admissible p q r) :
    actualFutureWordWeight p q r [B] = mixtureLaw p q r (1/2) := by
  funext H w
  have h := actual_startup_mixture hp 0 H w
  norm_num [startupCoordinate] at h
  exact h

lemma half_pure_B_distance {p q r : ℝ} (hp : admissible p q r) (i : State) :
    profileDistance (mixtureLaw p q r (1/2)) (pureLaw p q r (pureBSuccessor i)) = 1/2 := by
  have hs : pureBSuccessor i = 2 ∨ pureBSuccessor i = 4 := by
    fin_cases i <;> norm_num [pureBSuccessor,Fin.ext_iff]
  rcases hs with hs | hs
  · rw [hs,(mixture_pure_distances hp (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)).1]
    norm_num
  · rw [hs,(mixture_pure_distances hp (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)).2]

/-- This initialization charge never queries the decoder at the initial configuration. -/
theorem postread_initialization_extra_state {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hεk : 2 * ε < kappa p q r) (hc : O.Coherent)
    (hacc : O.Accurate p q r ε queryEmpty)
    (h : List Visible) (hnot : h ≠ []) (hpos : 0 < historyMass p q r h) :
    O.initial ≠ O.run h := by
  have hsmall : 2 * ε < (1/2:ℝ) := by linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
  intro he
  rcases positive_history_classification p q r h hnot hpos with ⟨k,hk,_,_⟩ | ⟨i,_,hi⟩
  · subst h
    change O.initial = startupState O k at he
    have hcollision : startupState O 0 = startupState O (k + 1) := by
      calc
        startupState O 0 = O.update O.initial B := rfl
        _ = O.update (startupState O k) B := congrArg (fun z => O.update z B) he
        _ = startupState O (k + 1) := by simpa using (startup_shift O k 1).symm
    have hd := startup_collision_forces_cutoff hp hne hc hacc 0 (k + 1) (by omega) hcollision
    norm_num [minority] at hd
    linarith
  · have ht := actual_pure_B_transition hp h hnot hpos i hi
    have hnext := actual_pure_law (h++[B]) (by simp) (pureBSuccessor i) ht.2.2
    have hext : O.run [B] = O.run (h++[B]) := by
      rw [run_snoc]
      change O.update O.initial B = O.update (O.run h) B
      rw [he]
    have hd := common_state_distance hacc [B] (h++[B])
      (by simpa using startup_history_positive hp 0) ht.2.1
      (Or.inr (by simp)) (Or.inr (by simp)) hext
    rw [initial_B_half hp,hnext,half_pure_B_distance hp i] at hd
    linarith

def initializedCharged {Z : Type*} (O : Observer Z) (N : Nat) : SharpState N → Z
  | none => O.initial
  | some z => chargedState O N z

theorem unequal_initialized_injective {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r)
    (hc : O.Coherent) (hacc : O.Accurate p q r ε queryEmpty) :
    Function.Injective (initializedCharged O (N2 p q r ε)) := by
  have hi := unequal_charged_injective hp hne hε hεk hc hacc
  have hnot : ∀ t : State ⊕ Fin (N2 p q r ε), O.initial ≠ chargedState O (N2 p q r ε) t := by
    intro t
    obtain ⟨h,hne',hpos,hr⟩ := charged_reached hp (N2 p q r ε) t
    rw [← hr]
    exact postread_initialization_extra_state hp hne hεk hc hacc h hne' hpos
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => exact (hnot y he).elim
  | some x =>
    cases y with
    | none => exact (hnot x he.symm).elim
    | some y => exact congrArg some (hi he)

/-- The same reached injection is used before charging initialization. -/
theorem universal_unequal_lower_bound {Z : Type*} [Fintype Z] {O : Observer Z}
    {p q r ε : ℝ} {queryEmpty : Bool} (hp : admissible p q r) (hne : a p q ≠ b r)
    (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r)
    (hc : O.Coherent) (hacc : O.Accurate p q r ε queryEmpty) :
    6 + N2 p q r ε ≤ Fintype.card Z ∧ 5 + N2 p q r ε ≤ Nat.card ↥(O.Reached p q r) := by
  constructor
  · have hi := Nat.card_le_card_of_injective (initializedCharged O (N2 p q r ε))
      (unequal_initialized_injective hp hne hε hεk hc hacc)
    simpa only [Nat.card_eq_fintype_card,sharp_state_card] using hi
  · let f : State ⊕ Fin (N2 p q r ε) → ↥(O.Reached p q r) :=
      fun t => ⟨chargedState O (N2 p q r ε) t,charged_reached hp _ t⟩
    have hf : Function.Injective f := by
      intro x y he
      exact unequal_charged_injective hp hne hε hεk hc hacc (congrArg Subtype.val he)
    have hi := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_eq_fintype_card] using hi

abbrev EqualityState := State ⊕ Unit

def equalityProject : SourceTag → EqualityState
  | .pure i => .inl i
  | .start => .inr ()
  | .startup _ => .inr ()

def equalityRepresentative : EqualityState → SourceTag
  | .inl i => .pure i
  | .inr _ => .startup 0

def equalityUpdate (z : EqualityState) (y : Visible) : EqualityState :=
  equalityProject (sourceUpdate (equalityRepresentative z) y)

def equalityDecoder (p q r : ℝ) : EqualityState → LawProfile
  | .inl i => pureLaw p q r i
  | .inr _ => mixtureLaw p q r (1/2)

/-- Initialization directly in the half - mixture is legal only for post - read queries. -/
def equalityPostreadObserver (p q r : ℝ) : Observer EqualityState where
  initial := .inr ()
  update := equalityUpdate
  decoder := equalityDecoder p q r

def equalityInitializedProject : SourceTag → Option EqualityState
  | .start => none
  | .pure i => some (.inl i)
  | .startup _ => some (.inr ())

def equalityInitializedUpdate : Option EqualityState → Visible → Option EqualityState
  | none, y => equalityInitializedProject (sourceUpdate .start y)
  | some z, y => some (equalityUpdate z y)

def equalityInitializedDecoder (p q r : ℝ) : Option EqualityState → LawProfile
  | none => emptyLaw p q r
  | some z => equalityDecoder p q r z

def equalityInitializedObserver (p q r : ℝ) : Observer (Option EqualityState) where
  initial := none
  update := equalityInitializedUpdate
  decoder := equalityInitializedDecoder p q r

lemma equality_project_step (z : SourceTag) (y : Visible) :
    equalityUpdate (equalityProject z) y = equalityProject (sourceUpdate z y) := by
  cases z <;> fin_cases y <;> rfl

lemma equality_initialized_step (z : SourceTag) (y : Visible) :
    equalityInitializedUpdate (equalityInitializedProject z) y =
      equalityInitializedProject (sourceUpdate z y) := by
  cases z with
  | start => rfl
  | startup k => fin_cases y <;> rfl
  | pure i => fin_cases i <;> fin_cases y <;> rfl

theorem equality_run_invariants (p q r : ℝ) (h : List Visible) :
    (equalityPostreadObserver p q r).run h = equalityProject (sourceRun h) ∧
    (equalityInitializedObserver p q r).run h = equalityInitializedProject (sourceRun h) := by
  exact ⟨List.foldl_hom equalityProject (l := h) (init := .start) equality_project_step,
    List.foldl_hom equalityInitializedProject (l := h) (init := .start) equality_initialized_step⟩

lemma equality_decoder_coherent {p q r : ℝ} (hp : admissible p q r) :
    (equalityPostreadObserver p q r).Coherent ∧ (equalityInitializedObserver p q r).Coherent := by
  have hc : ∀ z, CoherentProfile (equalityDecoder p q r z) := by
    intro z
    cases z with
    | inl i => exact pure_coherent hp i
    | inr u => exact mixture_coherent hp (by norm_num)
  refine ⟨hc,?_⟩
  intro z
  cases z with
  | none => exact empty_coherent hp
  | some z => exact hc z

/-- At equality both machines reconstruct every queried actual law exactly. -/
theorem equality_observers_exact {p q r : ℝ} (hp : admissible p q r) (heq : r = p + q) :
    (∀ h, h ≠ [] → 0 < historyMass p q r h →
      (equalityPostreadObserver p q r).decoder ((equalityPostreadObserver p q r).run h) =
        actualFutureWordWeight p q r h) ∧
    (∀ h, 0 < historyMass p q r h →
      (equalityInitializedObserver p q r).decoder ((equalityInitializedObserver p q r).run h) =
        actualFutureWordWeight p q r h) := by
  have hnonempty : ∀ h, h ≠ [] → 0 < historyMass p q r h →
      equalityDecoder p q r (equalityProject (sourceRun h)) = actualFutureWordWeight p q r h ∧
      equalityInitializedDecoder p q r (equalityInitializedProject (sourceRun h)) =
        actualFutureWordWeight p q r h := by
    intro h hn hpos
    rcases positive_history_classification p q r h hn hpos with ⟨k,hk,hr,_⟩ | ⟨i,hr,hi⟩
    · subst h
      have hl : actualFutureWordWeight p q r (List.replicate (k + 1) B) = mixtureLaw p q r (1/2) := by
        funext H w; exact (equality_startup_geometry hp heq k).1 H w
      simp [hr,equalityProject,equalityInitializedProject,equalityDecoder,equalityInitializedDecoder,hl]
    · have hl := actual_pure_law h hn i hi
      simp [hr,equalityProject,equalityInitializedProject,equalityDecoder,equalityInitializedDecoder,hl]
  constructor
  · intro h hn hpos
    change equalityDecoder p q r ((equalityPostreadObserver p q r).run h) = _
    rw [(equality_run_invariants p q r h).1]
    exact (hnonempty h hn hpos).1
  · intro h hpos
    change equalityInitializedDecoder p q r ((equalityInitializedObserver p q r).run h) = _
    rw [(equality_run_invariants p q r h).2]
    by_cases hn : h=[]
    · subst h; rfl
    · exact (hnonempty h hn hpos).2

theorem equality_observer_accuracy {p q r ε : ℝ} (hp : admissible p q r)
    (heq : r = p + q) (hε : 0 ≤ ε) :
    (equalityPostreadObserver p q r).Accurate p q r ε false ∧
    (equalityInitializedObserver p q r).Accurate p q r ε true := by
  have he := equality_observers_exact hp heq
  constructor
  · intro h hp' hq H
    have hn : h ≠ [] := hq.resolve_left (by decide)
    rw [← he.1 h hn hp']
    simpa [totalVariation] using hε
  · intro h hp' _ H
    rw [← he.2 h hp']
    simpa [totalVariation] using hε

lemma equality_reached_all {p q r : ℝ} (hp : admissible p q r) :
    (equalityPostreadObserver p q r).Reached p q r = Set.univ ∧
    (equalityInitializedObserver p q r).Reached p q r = {z | z ≠ none} := by
  have hreach : ∀ z : EqualityState, ∃ h, h ≠ [] ∧ 0 < historyMass p q r h ∧
      equalityProject (sourceRun h) = z ∧ equalityInitializedProject (sourceRun h) = some z := by
    intro z
    cases z with
    | inl i =>
      refine ⟨pureWitness i,(pure_witness_actual hp i).1,(pure_witness_actual hp i).2.1,?_,?_⟩
      · rw [pure_witness_run]; rfl
      · rw [pure_witness_run]; rfl
    | inr u =>
      cases u
      refine ⟨[B],by simp,by simpa using startup_history_positive hp 0,?_,?_⟩ <;> rfl
  constructor
  · apply Set.eq_univ_of_forall
    intro z
    obtain ⟨h,hn,hp',hr,_⟩ := hreach z
    exact ⟨h,hn,hp',(equality_run_invariants p q r h).1.trans hr⟩
  · apply Set.ext
    intro z
    constructor
    · rintro ⟨h,hn,_,hr⟩
      have hs := source_run_ne_start h hn
      rw [(equality_run_invariants p q r h).2] at hr
      cases he : sourceRun h with
      | start => exact (hs he).elim
      | pure i => rw [he] at hr; rw [← hr]; simp [equalityInitializedProject]
      | startup k => rw [he] at hr; rw [← hr]; simp [equalityInitializedProject]
    · intro hn
      cases z with
      | none => exact (hn rfl).elim
      | some z =>
        obtain ⟨h,hn,hp',_,hr⟩ := hreach z
        exact ⟨h,hn,hp',(equality_run_invariants p q r h).2.trans hr⟩

lemma half_pure_separation {p q r : ℝ} (hp : admissible p q r) (i : State) :
    kappa p q r ≤ profileDistance (mixtureLaw p q r (1/2)) (pureLaw p q r i) := by
  have hx : (1/2:ℝ) ∈ Set.Icc 0 1 := by norm_num
  by_cases hi : i = 0 ∨ i = 1 ∨ i = 3
  · rw [profile_comm]
    exact singleton_mixture_separation hp hx i hi
  · have hh : i = 2 ∨ i = 4 := by fin_cases i <;> simp_all
    rcases hh with rfl | rfl
    · rw [(mixture_pure_distances hp hx).1]
      linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]
    · rw [(mixture_pure_distances hp hx).2]
      linarith [(kappa_bounds p q r).2.2.2.2.2.2.2]

def equalityCharged {Z : Type*} (O : Observer Z) : EqualityState → Z
  | .inl i => O.run (pureWitness i)
  | .inr _ => O.run [B]

lemma equality_charged_reached {Z : Type*} {O : Observer Z} {p q r : ℝ}
    (hp : admissible p q r) (z : EqualityState) : equalityCharged O z ∈ O.Reached p q r := by
  cases z with
  | inl i => exact ⟨pureWitness i,(pure_witness_actual hp i).1,(pure_witness_actual hp i).2.1,rfl⟩
  | inr u => exact ⟨[B],by simp,by simpa using startup_history_positive hp 0,rfl⟩

theorem equality_charged_injective {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    {queryEmpty : Bool} (hp : admissible p q r) (hεk : 2 * ε < kappa p q r)
    (hacc : O.Accurate p q r ε queryEmpty) : Function.Injective (equalityCharged O) := by
  have hpure : ∀ i j : State, O.run (pureWitness i) = O.run (pureWitness j) → i = j := by
    intro i j he
    by_contra hn
    have hd := common_state_distance hacc _ _ (pure_witness_actual hp i).2.1
      (pure_witness_actual hp j).2.1 (Or.inr (pure_witness_actual hp i).1)
      (Or.inr (pure_witness_actual hp j).1) he
    rw [(pure_witness_actual hp i).2.2,(pure_witness_actual hp j).2.2] at hd
    exact (not_le_of_gt (hεk.trans_le (pure_pair_separation hp i j hn))) hd
  have hcross : ∀ i : State, O.run [B] ≠ O.run (pureWitness i) := by
    intro i he
    have hd := common_state_distance hacc [B] (pureWitness i)
      (by simpa using startup_history_positive hp 0) (pure_witness_actual hp i).2.1
      (Or.inr (by simp)) (Or.inr (pure_witness_actual hp i).1) he
    rw [initial_B_half hp,(pure_witness_actual hp i).2.2] at hd
    exact (not_le_of_gt (hεk.trans_le (half_pure_separation hp i))) hd
  intro x y he
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl (hpure i j he)
    | inr u => exact (hcross i he.symm).elim
  | inr u =>
    cases y with
    | inl j => exact (hcross j he).elim
    | inr v => cases u; cases v; rfl

def equalityInitializedCharged {Z : Type*} (O : Observer Z) : Option EqualityState → Z
  | none => O.initial
  | some z => equalityCharged O z

theorem equality_initialized_injective {Z : Type*} {O : Observer Z} {p q r ε : ℝ}
    (hp : admissible p q r) (hεk : 2 * ε < kappa p q r)
    (hacc : O.Accurate p q r ε true) :
    Function.Injective (equalityInitializedCharged O) := by
  have hnot : ∀ z : EqualityState, O.initial ≠ equalityCharged O z := by
    intro z he
    cases z with
    | inl i =>
      have hd := common_state_distance hacc [] (pureWitness i) (by rw [empty_history_mass]; norm_num)
        (pure_witness_actual hp i).2.1 (Or.inl rfl) (Or.inl rfl) he
      change profileDistance (emptyLaw p q r) (actualFutureWordWeight p q r (pureWitness i)) ≤ 2 * ε at hd
      rw [(pure_witness_actual hp i).2.2] at hd
      linarith [empty_pure_separation hp i,(kappa_bounds p q r).2.2.2.2.2.2.2]
    | inr u =>
      have hd := common_state_distance hacc [] [B] (by rw [empty_history_mass]; norm_num)
        (by simpa using startup_history_positive hp 0) (Or.inl rfl) (Or.inl rfl) he
      change profileDistance (emptyLaw p q r) (actualFutureWordWeight p q r [B]) ≤ 2 * ε at hd
      rw [initial_B_half hp] at hd
      linarith [empty_mixture_separation hp (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1),
        (kappa_bounds p q r).2.2.2.2.2.2.2]
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some z => exact (hnot z he).elim
  | some z =>
    cases y with
    | none => exact (hnot z he.symm).elim
    | some t => exact congrArg some (equality_charged_injective hp hεk hacc he)

theorem universal_equality_lower_bounds {Z : Type*} [Fintype Z] {O : Observer Z}
    {p q r ε : ℝ} (hp : admissible p q r) (hεk : 2 * ε < kappa p q r) :
    (O.Accurate p q r ε false → 6 ≤ Fintype.card Z ∧ 6 ≤ Nat.card ↥(O.Reached p q r)) ∧
    (O.Accurate p q r ε true → 7 ≤ Fintype.card Z ∧ 6 ≤ Nat.card ↥(O.Reached p q r)) := by
  have hr : ∀ queryEmpty : Bool, O.Accurate p q r ε queryEmpty →
      6 ≤ Nat.card ↥(O.Reached p q r) := by
    intro queryEmpty hacc
    let f : EqualityState → ↥(O.Reached p q r) :=
      fun z => ⟨equalityCharged O z,equality_charged_reached hp z⟩
    have hf : Function.Injective f := by
      intro x y he
      exact equality_charged_injective hp hεk hacc (congrArg Subtype.val he)
    have hi := Nat.card_le_card_of_injective f hf
    simpa [EqualityState,Nat.card_eq_fintype_card] using hi
  constructor
  · intro hacc
    have hi := Nat.card_le_card_of_injective (equalityCharged O) (equality_charged_injective hp hεk hacc)
    exact ⟨by simpa [EqualityState,Nat.card_eq_fintype_card] using hi,hr false hacc⟩
  · intro hacc
    have hi := Nat.card_le_card_of_injective (equalityInitializedCharged O)
      (equality_initialized_injective hp hεk hacc)
    exact ⟨by simpa [EqualityState,Nat.card_eq_fintype_card] using hi,hr true hacc⟩

lemma equality_observer_cardinalities {p q r : ℝ} (hp : admissible p q r) :
    Fintype.card EqualityState = 6 ∧ Fintype.card (Option EqualityState) = 7 ∧
    Nat.card ↥((equalityPostreadObserver p q r).Reached p q r) = 6 ∧
    Nat.card ↥((equalityInitializedObserver p q r).Reached p q r) = 6 := by
  have hcard : Fintype.card EqualityState = 6 := by simp [EqualityState]
  refine ⟨hcard,by simp [EqualityState],?_,?_⟩
  · rw [(equality_reached_all hp).1]
    simp [Nat.card_eq_fintype_card,EqualityState]
  · let f : EqualityState → ↥((equalityInitializedObserver p q r).Reached p q r) :=
      fun z => ⟨some z,by rw [(equality_reached_all hp).2]; simp⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y he; exact Option.some.inj (congrArg Subtype.val he)
      · rintro ⟨z,hz⟩
        rw [(equality_reached_all hp).2] at hz
        cases z with
        | none => exact (hz rfl).elim
        | some z => exact ⟨z,rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf),Nat.card_eq_fintype_card]
    exact hcard

universe u

/-- Source Theorem 4.2: a single initialized observer attains both universal minima. -/
theorem sharp_initialized_common_decoder {p q r ε : ℝ} (hp : admissible p q r)
    (hne : r ≠ p + q) (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r) :
    (midpointObserver p q r ε).Coherent ∧
    (midpointObserver p q r ε).Accurate p q r ε true ∧
    Fintype.card (SharpState (N2 p q r ε)) = 6 + N2 p q r ε ∧
    Nat.card ↥((midpointObserver p q r ε).Reached p q r) = 5 + N2 p q r ε ∧
    ∀ (Z : Type u) [Fintype Z] (O : Observer Z), O.Coherent →
      O.Accurate p q r ε true →
        6 + N2 p q r ε ≤ Fintype.card Z ∧ 5 + N2 p q r ε ≤ Nat.card ↥(O.Reached p q r) := by
  have hab : a p q ≠ b r := by
    intro he; apply hne; dsimp [a,b] at he; linarith
  exact ⟨midpoint_decoder_coherent hp hab hε hεk,
    midpoint_observer_accuracy hp hab hε hεk,
    (midpoint_observer_reachability hp).2.2,(midpoint_observer_reachability hp).2.1,
    fun _ _ _ hc ha => universal_unequal_lower_bound hp hab hε hεk hc ha⟩

theorem sharp_postread_reached_common_decoder {p q r ε : ℝ} (hp : admissible p q r)
    (hne : r ≠ p + q) (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r) :
    (midpointObserver p q r ε).Coherent ∧
    (midpointObserver p q r ε).Accurate p q r ε false ∧
    Nat.card ↥((midpointObserver p q r ε).Reached p q r) = 5 + N2 p q r ε ∧
    ∀ (Z : Type u) [Fintype Z] (O : Observer Z), O.Coherent →
      O.Accurate p q r ε false → 5 + N2 p q r ε ≤ Nat.card ↥(O.Reached p q r) := by
  have hab : a p q ≠ b r := by
    intro he; apply hne; dsimp [a,b] at he; linarith
  refine ⟨midpoint_decoder_coherent hp hab hε hεk,?_,
    (midpoint_observer_reachability hp).2.1,?_⟩
  · intro h hpos _ H
    exact midpoint_observer_accuracy hp hab hε hεk h hpos (Or.inl rfl) H
  · intro Z _ O hc ha
    exact (universal_unequal_lower_bound hp hab hε hεk hc ha).2

/-- Source Theorem 4.3 on unequal holdings: after - read - only queries still charge initialization. -/
theorem postread_only_unequal_minimum {p q r ε : ℝ} (hp : admissible p q r)
    (hne : r ≠ p + q) (hε : 0 < 2 * ε) (hεk : 2 * ε < kappa p q r) :
    (midpointObserver p q r ε).Coherent ∧
    (midpointObserver p q r ε).Accurate p q r ε false ∧
    Fintype.card (SharpState (N2 p q r ε)) = 6 + N2 p q r ε ∧
    Nat.card ↥((midpointObserver p q r ε).Reached p q r) = 5 + N2 p q r ε ∧
    ∀ (Z : Type u) [Fintype Z] (O : Observer Z), O.Coherent →
      O.Accurate p q r ε false →
        6 + N2 p q r ε ≤ Fintype.card Z ∧ 5 + N2 p q r ε ≤ Nat.card ↥(O.Reached p q r) := by
  have hab : a p q ≠ b r := by
    intro he; apply hne; dsimp [a,b] at he; linarith
  have hr := sharp_postread_reached_common_decoder.{u} hp hne hε hεk
  exact ⟨hr.1,hr.2.1,sharp_state_card _,hr.2.2.1,
    fun Z _ O hc ha => ⟨(universal_unequal_lower_bound hp hab hε hεk hc ha).1,
      hr.2.2.2 Z O hc ha⟩⟩

/-- Equality is a separate six/seven - state construction, valid also at exact tolerance zero. -/
theorem equality_observer_minima {p q r ε : ℝ} (hp : admissible p q r)
    (heq : r = p + q) (hε : 0 ≤ ε) (hεk : 2 * ε < kappa p q r) :
    (equalityInitializedObserver p q r).Coherent ∧
    (equalityPostreadObserver p q r).Coherent ∧
    (equalityInitializedObserver p q r).Accurate p q r ε true ∧
    (equalityPostreadObserver p q r).Accurate p q r ε false ∧
    Fintype.card (Option EqualityState) = 7 ∧ Fintype.card EqualityState = 6 ∧
    Nat.card ↥((equalityInitializedObserver p q r).Reached p q r) = 6 ∧
    Nat.card ↥((equalityPostreadObserver p q r).Reached p q r) = 6 ∧
    (∀ h, 0 < historyMass p q r h →
      (equalityInitializedObserver p q r).decoder ((equalityInitializedObserver p q r).run h) =
        actualFutureWordWeight p q r h) ∧
    (∀ h, h ≠ [] → 0 < historyMass p q r h →
      (equalityPostreadObserver p q r).decoder ((equalityPostreadObserver p q r).run h) =
        actualFutureWordWeight p q r h) ∧
    ∀ (Z : Type u) [Fintype Z] (O : Observer Z),
      (O.Coherent → O.Accurate p q r ε true →
        7 ≤ Fintype.card Z ∧ 6 ≤ Nat.card ↥(O.Reached p q r)) ∧
      (O.Coherent → O.Accurate p q r ε false →
        6 ≤ Fintype.card Z ∧ 6 ≤ Nat.card ↥(O.Reached p q r)) := by
  have hc := equality_decoder_coherent hp
  have ha := equality_observer_accuracy hp heq hε
  have hn := equality_observer_cardinalities hp
  have he := equality_observers_exact hp heq
  refine ⟨hc.2,hc.1,ha.2,ha.1,hn.2.1,hn.1,hn.2.2.2,hn.2.2.1,he.2,he.1,?_⟩
  intro Z _ O
  exact ⟨fun _ ha => (universal_equality_lower_bounds hp hεk).2 ha,
    fun _ ha => (universal_equality_lower_bounds hp hεk).1 ha⟩

end
end D5.S3.ObserverMemory.Prediction.FiveModeAutonomousSharpCount

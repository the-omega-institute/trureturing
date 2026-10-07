/- GID: D5/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Decision/ExactRealMooreProbeStateBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed literal Moore tables need four query rows and six nominal rows. -/

import D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts

/-!
A fixed Moore row either queries one literal real parameter or halts with one
literal Boolean output. The read-only source ranges over the whole closed
unit interval times Bool. Correctness gives a finite first-Halt execution
separately for each source, without a common fuel bound.

Actual traces retain ordered issuing rows, literal parameters, responses and
the terminal row. Only finite actual runs are repetition-free; the control
table may contain cycles, duplicate literals and unreachable rows. All nominal
query rows count. Two opposite terminal outputs contribute two further rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open unitInterval
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts

namespace D5.S3.ConceptDynamics.Decision.ExactRealMooreProbeStateBounds
universe w
abbrev Source := I × Bool
abbrev Record := Sigma (fun _ : I => Bool)
abbrev History := Hist (fun _ : I => Bool)
abbrev Tagged (P : Type w) := P × Record

variable {P : Type w}
noncomputable section

def records (rs : List (Tagged P)) : History := rs.map Prod.snd

def rows (rs : List (Tagged P)) : List P := rs.map Prod.fst

/-- The original independently recursive fuel-indexed Moore execution. -/
def mooreRun (u : P → I ⊕ Bool) (v : P → Bool → P) (s : Source) :
    Nat → P → Option (History × Bool)
  | 0, _ => none
  | n + 1, p => match u p with
    | .inr b => some ([], b)
    | .inl a => (mooreRun u v s n (v p (response a s))).map
        (fun hb => (⟨a, response a s⟩ :: hb.1, hb.2))

/-- Each constructor retains the issuing row; the terminal row is separate. -/
inductive Actual (u : P → I ⊕ Bool) (v : P → Bool → P) (s : Source) :
    P → List (Tagged P) → P → Bool → Prop
  | halt {p : P} {b : Bool} : u p = .inr b → Actual u v s p [] p b
  | query {p : P} {a : I} {rs : List (Tagged P)} {q : P} {b : Bool} :
      u p = .inl a → Actual u v s (v p (response a s)) rs q b →
      Actual u v s p ((p, ⟨a, response a s⟩) :: rs) q b

/-- A finite actual prefix contains queries only and need not already halt. -/
inductive Prefix (u : P → I ⊕ Bool) (v : P → Bool → P) (s : Source) :
    P → List (Tagged P) → P → Prop
  | nil (p : P) : Prefix u v s p [] p
  | query {p : P} {a : I} {rs : List (Tagged P)} {q : P} :
      u p = .inl a → Prefix u v s (v p (response a s)) rs q →
      Prefix u v s p ((p, ⟨a, response a s⟩) :: rs) q

/-- Response-fold reconstruction is proof-side; Halt rows absorb. -/
def step (u : P → I ⊕ Bool) (v : P → Bool → P) (p : P) (r : Bool) : P :=
  match u p with
  | .inl _ => v p r
  | .inr _ => p

def replay (u : P → I ⊕ Bool) (v : P → Bool → P) (p : P) (h : History) : P :=
  h.foldl (fun p r => step u v p r.2) p

def policy (u : P → I ⊕ Bool) (v : P → Bool → P) (entry : P) : History → I ⊕ Bool :=
  fun h => u (replay u v entry h)

theorem replay_append (u : P → I ⊕ Bool) (v : P → Bool → P)
    (p : P) (h t : History) :
    replay u v p (h ++ t) = replay u v (replay u v p h) t :=
  List.foldl_append

theorem execute_eq_moore (u : P → I ⊕ Bool) (v : P → Bool → P)
    (entry : P) (s : Source) (n : Nat) (pre : History) :
    execute response (policy u v entry) n pre s =
      mooreRun u v s n (replay u v entry pre) := by
  induction n generalizing pre with
  | zero => rfl
  | succ n ih =>
    cases hu : u (replay u v entry pre) with
    | inr b => simp [execute, policy, mooreRun, hu]
    | inl a =>
      simp only [execute, policy, hu, mooreRun]
      rw [ih]
      have hs : replay u v entry (pre ++ [⟨a, response a s⟩]) =
          v (replay u v entry pre) (response a s) := by
        rw [replay_append]
        change step u v (replay u v entry pre) (response a s) = _
        simp [step, hu]
      rw [hs]

theorem Actual.to_fuel {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool}
    (h : Actual u v s p rs q b) :
    ∀ n, rs.length < n → mooreRun u v s n p = some (records rs, b) := by
  induction h with
  | halt hu =>
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n => simp [mooreRun, hu, records]
  | @query p a rs q b hu ht ih =>
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
      have hlt : rs.length < n := by simp only [List.length_cons] at hn; omega
      simp [mooreRun, hu, ih n hlt, records]

theorem fuel_to_actual (u : P → I ⊕ Bool) (v : P → Bool → P) (s : Source)
    (n : Nat) (p : P) (h : History) (b : Bool)
    (hr : mooreRun u v s n p = some (h, b)) :
    ∃ rs q, Actual u v s p rs q b ∧ records rs = h ∧ rs.length < n := by
  induction n generalizing p h b with
  | zero => simp [mooreRun] at hr
  | succ n ih =>
    cases hu : u p with
    | inr c =>
      have he : ([], c) = (h, b) := by simpa [mooreRun, hu] using hr
      rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      exact ⟨[], p, .halt hu, rfl, by simp⟩
    | inl a =>
      simp only [mooreRun, hu] at hr
      obtain ⟨⟨tail, c⟩, ht, he⟩ := Option.map_eq_some_iff.mp hr
      rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      obtain ⟨rs, q, ha, hh, hn⟩ := ih _ _ _ ht
      exact ⟨(p, ⟨a, response a s⟩) :: rs, q, .query hu ha,
        by change ⟨a, response a s⟩ :: records rs = _; rw [hh],
        by simp only [List.length_cons]; omega⟩





theorem Actual.terminal {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool} (h : Actual u v s p rs q b) :
    u q = .inr b := by
  induction h with
  | halt hu => exact hu
  | query _ _ ih => exact ih

theorem Actual.issued {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool} (h : Actual u v s p rs q b) :
    ∀ r ∈ rs, u r.1 = .inl r.2.1 ∧ response r.2.1 s = r.2.2 := by
  induction h with
  | halt _ => simp
  | @query p a rs q b hu ht ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hu, rfl⟩
    · exact ih r hr

theorem Actual.parameters_contained {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool} (h : Actual u v s p rs q b) :
    ∀ a ∈ (records rs).map Sigma.fst, ∃ k ∈ rows rs, u k = .inl a := by
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  obtain ⟨tag, htag, rfl⟩ := List.mem_map.mp hr
  exact ⟨tag.1, List.mem_map.mpr ⟨tag, htag, rfl⟩, (h.issued tag htag).1⟩





theorem Prefix.append_actual {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q t : P} {pre tail : List (Tagged P)} {b : Bool}
    (hp : Prefix u v s p pre q) (ht : Actual u v s q tail t b) :
    Actual u v s p (pre ++ tail) t b := by
  induction hp with
  | nil _ => exact ht
  | query hu hp ih => exact .query hu (ih ht)

theorem Prefix.suffix {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q t : P} {pre rs : List (Tagged P)} {b : Bool}
    (hp : Prefix u v s p pre q) (hr : Actual u v s p rs t b) :
    ∃ tail, rs = pre ++ tail ∧ Actual u v s q tail t b := by
  induction hp generalizing rs t b with
  | nil _ => exact ⟨rs, rfl, hr⟩
  | @query p a pre q hu hp ih =>
    cases hr with
    | halt hh => simp [hu] at hh
    | @query _ a' rs t b hh ht =>
      have he : a' = a := Sum.inl.inj (hh.symm.trans hu)
      subst a'
      obtain ⟨tail, he, ha⟩ := ih ht
      exact ⟨tail, by simp [he], ha⟩

theorem Actual.unique {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q q' : P} {rs rs' : List (Tagged P)} {b b' : Bool}
    (h : Actual u v s p rs q b) (h' : Actual u v s p rs' q' b') :
    rs = rs' ∧ q = q' ∧ b = b' := by
  induction h generalizing rs' q' b' with
  | halt hu =>
    cases h' with
    | halt hu' => exact ⟨rfl, rfl, Sum.inr.inj (hu.symm.trans hu')⟩
    | query hu' _ => simp [hu] at hu'
  | @query p a rs q b hu ht ih =>
    cases h' with
    | halt hu' => simp [hu] at hu'
    | @query _ a' rs' q' b' hu' ht' =>
      have he : a' = a := Sum.inl.inj (hu'.symm.trans hu)
      subst a'
      obtain ⟨rfl, rfl, rfl⟩ := ih ht'
      exact ⟨rfl, rfl, rfl⟩

theorem Actual.member_suffix {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q k : P} {rs : List (Tagged P)} {b : Bool}
    (h : Actual u v s p rs q b) (hk : k ∈ rows rs) :
    ∃ tail, Actual u v s k tail q b ∧ tail.length ≤ rs.length := by
  induction h with
  | halt _ => simp [rows] at hk
  | @query p a rs q b hu ht ih =>
    have hm : k = p ∨ k ∈ rows rs := by simpa [rows] using hk
    rcases hm with he | hm
    · subst k
      exact ⟨(p, ⟨a, response a s⟩) :: rs, .query hu ht, le_rfl⟩
    · obtain ⟨tail, ha, hn⟩ := ih hm
      exact ⟨tail, ha, by simp only [List.length_cons]; omega⟩

theorem Actual.rows_nodup {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool} (h : Actual u v s p rs q b) :
    (rows rs).Nodup := by
  induction h with
  | halt _ => simp [rows]
  | @query p a rs q b hu ht ih =>
    have hn : p ∉ rows rs := by
      intro hm
      obtain ⟨tail, ha, hlen⟩ := ht.member_suffix hm
      have he := (Actual.query hu ht).unique ha
      have hlength := congrArg List.length he.1
      simp only [List.length_cons] at hlength
      omega
    simpa [rows] using List.nodup_cons.mpr ⟨hn, ih⟩

def CorrectEntry (u : P → I ⊕ Bool) (v : P → Bool → P) (entry : P) : Prop :=
  ∀ s : Source, ∃ n h, mooreRun u v s n entry = some (h, s.2)

theorem correct_iff_policy (u : P → I ⊕ Bool) (v : P → Bool → P) (entry : P) :
    CorrectEntry u v entry ↔ ∀ s : Source, ∃ h n,
      execute response (policy u v entry) n [] s = some (h, s.2) := by
  simp only [CorrectEntry, execute_eq_moore, replay, List.foldl_nil]
  exact forall_congr' fun _ => exists_comm

theorem correct_actual_suffix {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} (hc : CorrectEntry u v entry) (s : Source)
    {pre : List (Tagged P)} {q : P} (hp : Prefix u v s entry pre q) :
    ∃ tail t, Actual u v s q tail t s.2 := by
  obtain ⟨n, h, hr⟩ := hc s
  obtain ⟨rs, t, ha, _, _⟩ := fuel_to_actual u v s n entry h s.2 hr
  obtain ⟨tail, _, ht⟩ := hp.suffix ha
  exact ⟨tail, t, ht⟩

theorem supplier_three_parameters {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} (hc : CorrectEntry u v entry) :
    ∃ (s : Source) (rs : List (Tagged P)) (q : P),
      Actual u v s entry rs q s.2 ∧ 3 ≤ ((records rs).map Sigma.fst).toFinset.card := by
  classical
  obtain ⟨s, h, ⟨n, hn⟩, hcost⟩ := result.2.1 (policy u v entry)
    ((correct_iff_policy u v entry).mp hc)
  rw [execute_eq_moore] at hn
  obtain ⟨rs, q, ha, hh, _⟩ := fuel_to_actual u v s n _ h s.2 hn
  exact ⟨s, rs, q, ha, by simpa [hh] using hcost⟩


def parameter (u : P → I ⊕ Bool) (p : P) : I :=
  match u p with
  | .inl a => a
  | .inr _ => 0

def queryRows [Fintype P] (u : P → I ⊕ Bool) : Finset P := by
  classical
  exact Finset.univ.filter (fun p => ∃ a, u p = .inl a)

theorem mem_queryRows [Fintype P] {u : P → I ⊕ Bool} {p : P} :
    p ∈ queryRows u ↔ ∃ a, u p = .inl a := by
  classical
  simp [queryRows]

theorem parameter_eq {u : P → I ⊕ Bool} {p : P} {a : I}
    (hu : u p = .inl a) : parameter u p = a := by
  simp [parameter, hu]

theorem actual_parameter_card_le {u : P → I ⊕ Bool} {v : P → Bool → P}
    {s : Source} {p t : P} {rs : List (Tagged P)} {b : Bool}
    (hr : Actual u v s p rs t b) (allowed : Finset P)
    (hs : ∀ k ∈ rows rs, k ∈ allowed) :
    ((records rs).map Sigma.fst).toFinset.card ≤ (allowed.image (parameter u)).card := by
  classical
  apply Finset.card_le_card
  intro a ha
  obtain ⟨k, hk, hu⟩ := hr.parameters_contained a (List.mem_toFinset.mp ha)
  exact Finset.mem_image.mpr ⟨k, hs k hk, parameter_eq hu⟩

theorem three_le_query_image [Fintype P] {u : P → I ⊕ Bool}
    {v : P → Bool → P} {entry : P} (hc : CorrectEntry u v entry) :
    3 ≤ ((queryRows u).image (parameter u)).card := by
  classical
  obtain ⟨s, rs, t, hr, hn⟩ := supplier_three_parameters hc
  apply hn.trans (actual_parameter_card_le hr (queryRows u) ?_)
  intro k hk
  obtain ⟨r, hrr, he⟩ := List.mem_map.mp hk
  exact mem_queryRows.mpr ⟨r.2.1, he ▸ (hr.issued r hrr).1⟩

theorem query_injective_of_le_three [Fintype P] {u : P → I ⊕ Bool}
    {v : P → Bool → P} {entry : P} (hc : CorrectEntry u v entry)
    (hle : (queryRows u).card ≤ 3) :
    Set.InjOn (parameter u) (queryRows u : Set P) := by
  classical
  have h3 := three_le_query_image hc
  have hleim := Finset.card_image_le (s := queryRows u) (f := parameter u)
  have he : ((queryRows u).image (parameter u)).card = (queryRows u).card := by omega
  exact Finset.card_image_iff.mp he

theorem correct_actual {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} (hc : CorrectEntry u v entry) (s : Source) :
    ∃ rs t, Actual u v s entry rs t s.2 := by
  obtain ⟨n, h, hr⟩ := hc s
  obtain ⟨rs, t, ha, _, _⟩ := fuel_to_actual u v s n entry h s.2 hr
  exact ⟨rs, t, ha⟩

theorem prefix_halt_output {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry q : P} {s : Source} {pre : List (Tagged P)} {b : Bool}
    (hc : CorrectEntry u v entry) (hp : Prefix u v s entry pre q)
    (hu : u q = .inr b) : b = s.2 := by
  obtain ⟨rs, t, hr⟩ := correct_actual_suffix hc s hp
  exact ((Actual.halt hu).unique hr).2.2

theorem prefix_fresh {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry q : P} {s : Source} {pre : List (Tagged P)} {a : I}
    (hc : CorrectEntry u v entry) (hp : Prefix u v s entry pre q)
    (hu : u q = .inl a) : q ∉ rows pre := by
  obtain ⟨rs, t, hr⟩ := correct_actual_suffix hc s hp
  cases hr with
  | halt hh => simp [hu] at hh
  | @query _ a' rs t b hh ht =>
    have hn := (hp.append_actual (.query hh ht)).rows_nodup
    have hn' : (rows pre ++ q :: rows rs).Nodup := by simpa [rows] using hn
    intro hm
    have hd := (List.nodup_append.mp hn').2.2
    exact hd q hm q (by simp) rfl


theorem Prefix.query_fixed {u : P → I ⊕ Bool} {v : P → Bool → P}
    {s : Source} {p q : P} {rs : List (Tagged P)} {a : I} {r : Bool}
    (hu : u p = .inl a) (he : response a s = r)
    (ht : Prefix u v s (v p r) rs q) :
    Prefix u v s p ((p, ⟨a, r⟩) :: rs) q := by
  subst r
  exact .query hu ht

theorem entry_query {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} (hc : CorrectEntry u v entry) : ∃ a, u entry = .inl a := by
  cases hu : u entry with
  | inl a => exact ⟨a, rfl⟩
  | inr b =>
    have h0 := prefix_halt_output hc (s := (0, false)) (.nil entry) hu
    have h1 := prefix_halt_output hc (s := (0, true)) (.nil entry) hu
    simp only at h0 h1
    exact Bool.false_ne_true (h0.symm.trans h1) |>.elim

theorem successor_query {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} {a : I} (hc : CorrectEntry u v entry)
    (hu : u entry = .inl a) (r : Bool) :
    ∃ c, u (v entry r) = .inl c := by
  obtain ⟨z, hz⟩ := exists_ne a
  have haz : a ≠ z := Ne.symm hz
  cases hq : u (v entry r) with
  | inl c => exact ⟨c, rfl⟩
  | inr b =>
    have hp0 : Prefix u v (a, !r) entry [(entry, ⟨a, r⟩)] (v entry r) :=
      Prefix.query_fixed hu (by simp [response]) (.nil _)
    have hp1 : Prefix u v (z, r) entry [(entry, ⟨a, r⟩)] (v entry r) :=
      Prefix.query_fixed hu (by simp [response, haz]) (.nil _)
    have h0 := prefix_halt_output hc hp0 hq
    have h1 := prefix_halt_output hc hp1 hq
    cases r <;> simp_all

theorem successor_ne_entry {u : P → I ⊕ Bool} {v : P → Bool → P}
    {entry : P} {a : I} (hc : CorrectEntry u v entry)
    (hu : u entry = .inl a) (r : Bool) : v entry r ≠ entry := by
  intro he
  have hp : Prefix u v (a, !r) entry [(entry, ⟨a, r⟩)] entry := by
    have hp' : Prefix u v (a, !r) entry [(entry, ⟨a, r⟩)] (v entry r) :=
      Prefix.query_fixed hu (by simp [response]) (.nil _)
    simpa only [he] using hp'
  exact prefix_fresh hc hp hu (by simp [rows])

theorem common_successor_impossible [Fintype P]
    {u : P → I ⊕ Bool} {v : P → Bool → P} {A B : P} {a : I}
    (hc : CorrectEntry u v A) (hA : u A = .inl a)
    (h0 : v A false = B) (h1 : v A true = B)
    (hle : (queryRows u).card ≤ 3) : False := by
  classical
  have hv : ∀ r, v A r = B := by intro r; cases r <;> assumption
  have correctB : CorrectEntry u v B := by
    intro s
    have hp : Prefix u v s A [(A, ⟨a, response a s⟩)] B := by
      simpa only [hv] using (Prefix.query hA (Prefix.nil (v A (response a s))))
    obtain ⟨rs, t, hr⟩ := correct_actual_suffix hc s hp
    exact ⟨rs.length + 1, records rs, hr.to_fuel _ (by omega)⟩
  obtain ⟨s, rs, t, hr, hn⟩ := supplier_three_parameters correctB
  have hwhole : Actual u v s A ((A, ⟨a, response a s⟩) :: rs) t s.2 :=
    Actual.query hA (by simpa only [hv] using hr)
  have hnot : A ∉ rows rs := (List.nodup_cons.mp (by simpa [rows] using hwhole.rows_nodup)).1
  have hbound := actual_parameter_card_le hr ((queryRows u).erase A) (by
    intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · intro he; subst k; exact hnot hk
    · obtain ⟨tag, hm, he⟩ := List.mem_map.mp hk
      exact mem_queryRows.mpr ⟨tag.2.1, he ▸ (hr.issued tag hm).1⟩)
  have him := Finset.card_image_le (s := (queryRows u).erase A) (f := parameter u)
  have hmem : A ∈ queryRows u := mem_queryRows.mpr ⟨a, hA⟩
  have herase := Finset.card_erase_add_one hmem
  omega

theorem query_exhaustion [Fintype P] {u : P → I ⊕ Bool} {A B C : P}
    (hA : A ∈ queryRows u) (hB : B ∈ queryRows u) (hC : C ∈ queryRows u)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hle : (queryRows u).card ≤ 3) :
    ∀ q ∈ queryRows u, q = A ∨ q = B ∨ q = C := by
  classical
  intro q hq
  by_contra hn
  have hqA : q ≠ A := by tauto
  have hqB : q ≠ B := by tauto
  have hqC : q ≠ C := by tauto
  have hsub : {q, A, B, C} ⊆ queryRows u := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  have hfour : ({q, A, B, C} : Finset P).card = 4 := by
    simp [hqA, hqB, hqC, hAB, hAC, hBC]
  omega

theorem distinct_successors_impossible
    {u : P → I ⊕ Bool} {v : P → Bool → P} {A B C : P} {a c d : I}
    (hc : CorrectEntry u v A)
    (hA : u A = .inl a) (hB : u B = .inl c) (hC : u C = .inl d)
    (h0 : v A false = B) (h1 : v A true = C)
    (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (hex : ∀ q, (∃ e, u q = .inl e) → q = A ∨ q = B ∨ q = C) : False := by
  have pref0 : Prefix u v (c, false) A
      [(A, ⟨a, false⟩), (B, ⟨c, true⟩)] (v B true) := by
    apply Prefix.query_fixed hA (by simp [response, hac])
    rw [h0]
    exact Prefix.query_fixed hB (by simp [response]) (.nil _)
  have pref1 : Prefix u v (a, true) A
      [(A, ⟨a, false⟩), (B, ⟨c, true⟩)] (v B true) := by
    apply Prefix.query_fixed hA (by simp [response])
    rw [h0]
    exact Prefix.query_fixed hB (by simp [response, Ne.symm hac]) (.nil _)
  have hB1 : v B true = C := by
    cases hq : u (v B true) with
    | inr b =>
      have hb0 := prefix_halt_output hc pref0 hq
      have hb1 := prefix_halt_output hc pref1 hq
      exact (Bool.false_ne_true (hb0.symm.trans hb1)).elim
    | inl e =>
      rcases hex (v B true) ⟨e, hq⟩ with he | he | he
      · have hf := prefix_fresh hc pref0 hq
        exact (hf (by simp [rows, he])).elim
      · have hf := prefix_fresh hc pref0 hq
        exact (hf (by simp [rows, he])).elim
      · exact he
  have prefC0 : Prefix u v (c, false) A
      [(A, ⟨a, false⟩), (B, ⟨c, true⟩), (C, ⟨d, false⟩)] (v C false) := by
    apply Prefix.query_fixed hA (by simp [response, hac])
    rw [h0]
    apply Prefix.query_fixed hB (by simp [response])
    rw [hB1]
    exact Prefix.query_fixed hC (by simp [response, Ne.symm hcd]) (.nil _)
  have prefC1 : Prefix u v (d, true) A
      [(A, ⟨a, true⟩), (C, ⟨d, false⟩)] (v C false) := by
    apply Prefix.query_fixed hA (by simp [response, had])
    rw [h1]
    exact Prefix.query_fixed hC (by simp [response]) (.nil _)
  cases hq : u (v C false) with
  | inr b =>
    have hb0 := prefix_halt_output hc prefC0 hq
    have hb1 := prefix_halt_output hc prefC1 hq
    exact Bool.false_ne_true (hb0.symm.trans hb1)
  | inl e =>
    have hf := prefix_fresh hc prefC0 hq
    rcases hex (v C false) ⟨e, hq⟩ with he | he | he <;>
      exact hf (by simp [rows, he])

theorem four_le_queryRows [Fintype P] {u : P → I ⊕ Bool}
    {v : P → Bool → P} {entry : P} (hc : CorrectEntry u v entry) :
    4 ≤ (queryRows u).card := by
  classical
  by_contra hn
  have hle : (queryRows u).card ≤ 3 := by omega
  obtain ⟨a, hA⟩ := entry_query hc
  let B := v entry false
  let C := v entry true
  obtain ⟨c, hB⟩ := successor_query hc hA false
  obtain ⟨d, hC⟩ := successor_query hc hA true
  change u B = .inl c at hB
  change u C = .inl d at hC
  have h0 : v entry false = B := rfl
  have h1 : v entry true = C := rfl
  by_cases hBC : B = C
  · exact common_successor_impossible hc hA h0 (h1.trans hBC.symm) hle
  have hAB : entry ≠ B := (successor_ne_entry hc hA false).symm
  have hAC : entry ≠ C := (successor_ne_entry hc hA true).symm
  have hmA : entry ∈ queryRows u := mem_queryRows.mpr ⟨a, hA⟩
  have hmB : B ∈ queryRows u := mem_queryRows.mpr ⟨c, hB⟩
  have hmC : C ∈ queryRows u := mem_queryRows.mpr ⟨d, hC⟩
  have hinj := query_injective_of_le_three hc hle
  have hac : a ≠ c := by
    intro he
    exact hAB (hinj hmA hmB (by simpa [parameter, hA, hB] using he))
  have had : a ≠ d := by
    intro he
    exact hAC (hinj hmA hmC (by simpa [parameter, hA, hC] using he))
  have hcd : c ≠ d := by
    intro he
    exact hBC (hinj hmB hmC (by simpa [parameter, hB, hC] using he))
  have hex := query_exhaustion hmA hmB hmC hAB hAC hBC hle
  exact distinct_successors_impossible hc hA hB hC h0 h1 hac had hcd
    (fun q hq => hex q (mem_queryRows.mpr hq))


theorem nominal_lower_bounds [Finite P] (u : P → I ⊕ Bool)
    (v : P → Bool → P) (entry : P) (hc : CorrectEntry u v entry) :
    4 ≤ Nat.card {p : P // ∃ a, u p = .inl a} ∧ 6 ≤ Nat.card P := by
  classical
  let _ := Fintype.ofFinite P
  have hfour := four_le_queryRows hc
  have hqcard : Nat.card {p : P // ∃ a, u p = .inl a} = (queryRows u).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  obtain ⟨rs0, t0, hr0⟩ := correct_actual hc (0, false)
  obtain ⟨rs1, t1, hr1⟩ := correct_actual hc (0, true)
  have ht0 : u t0 = .inr false := hr0.terminal
  have ht1 : u t1 = .inr true := hr1.terminal
  have hne : t0 ≠ t1 := by
    intro he
    rw [he, ht1] at ht0
    cases ht0
  have hdis : Disjoint (queryRows u) {t0, t1} := by
    apply Finset.disjoint_left.mpr
    intro q hq ht
    obtain ⟨a, ha⟩ := mem_queryRows.mp hq
    rcases Finset.mem_insert.mp ht with he | he
    · subst q; rw [ht0] at ha; cases ha
    · have he' : q = t1 := Finset.mem_singleton.mp he
      subst q; rw [ht1] at ha; cases ha
  have hcunion := Finset.card_union_of_disjoint hdis
  have htwo : ({t0, t1} : Finset P).card = 2 := by simp [hne]
  have hnom := Finset.card_le_univ ((queryRows u) ∪ {t0, t1})
  constructor
  · rw [hqcard]
    exact hfour
  · rw [Nat.card_eq_fintype_card]
    omega


 theorem Prefix.replay {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} (h : Prefix u v s p rs q) :
    replay u v p (records rs) = q := by
  induction h with
  | nil p => rfl
  | query hu ht ih => simpa [ExactRealMooreProbeStateBounds.replay, records, step, hu] using ih


theorem response_joint_measurable :
    Measurable (fun z : I × Source => response z.1 z.2) := by
  rcases result with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  exact hm

theorem Actual.cost_eq {u : P → I ⊕ Bool} {v : P → Bool → P} {s : Source}
    {p q : P} {rs : List (Tagged P)} {b : Bool} (ha : Actual u v s p rs q b) :
    cost (policy u v p) s = (((records rs).map Sigma.fst).toFinset.card : ENNReal) := by
  classical
  have hr : ∃ n hb, execute response (policy u v p) n [] s = some hb := by
    refine ⟨rs.length + 1, (records rs, b), ?_⟩
    simpa only [execute_eq_moore, replay, List.foldl_nil] using
      ha.to_fuel (rs.length + 1) (by omega)
  rw [cost, dif_pos hr]
  have chosen := Classical.choose_spec (Classical.choose_spec hr)
  have chosen' : mooreRun u v s (Classical.choose hr) p =
      some (Classical.choose (Classical.choose_spec hr)) := by
    simpa only [execute_eq_moore, replay, List.foldl_nil] using chosen
  obtain ⟨rs', q', ha', he, _⟩ := fuel_to_actual u v s _ p _ _ chosen'
  have ht := ha.unique ha'
  exact congrArg (fun h : History => ((h.map Sigma.fst).toFinset.card : ENNReal))
    (he.symm.trans (congrArg records ht.1).symm)

/-- A fixed table's readout pattern; the source and literal query domain stay intact. -/
def signature (u : P → I ⊕ Bool) (s : Source) : P → Bool := fun p =>
  match u p with
  | .inl a => response a s
  | .inr _ => false

theorem signature_measurable (u : P → I ⊕ Bool) : Measurable (signature u) := by
  apply measurable_pi_lambda
  intro p
  cases hu : u p with
  | inr b => simpa only [signature, hu] using (measurable_const : Measurable (fun _ : Source => false))
  | inl a =>
    simpa only [signature, hu, Function.comp_def] using
      response_joint_measurable.comp (measurable_const.prodMk measurable_id :
        Measurable (fun s : Source => (a, s)))

theorem moore_signature_eq (u : P → I ⊕ Bool) (v : P → Bool → P)
    (s s' : Source) (hs : signature u s = signature u s') (n : Nat) (p : P) :
    mooreRun u v s n p = mooreRun u v s' n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases hu : u p with
    | inr b => simp only [mooreRun, hu]
    | inl a =>
      have he := congrFun hs p
      simp only [signature, hu] at he
      simp only [mooreRun, hu]
      rw [he, ih]

theorem cost_signature_eq (u : P → I ⊕ Bool) (v : P → Bool → P)
    (entry : P) (s s' : Source) (hs : signature u s = signature u s') :
    cost (policy u v entry) s = cost (policy u v entry) s' := by
  classical
  have hexe : ∀ n, execute response (policy u v entry) n [] s =
      execute response (policy u v entry) n [] s' := by
    intro n
    rw [execute_eq_moore, execute_eq_moore, moore_signature_eq u v s s' hs]
  by_cases hr : ∃ n hb, execute response (policy u v entry) n [] s = some hb
  · obtain ⟨n, ⟨h, b⟩, hn⟩ := hr
    have hn' := (hexe n).symm.trans hn
    have hm : mooreRun u v s n entry = some (h, b) := by
      simpa only [execute_eq_moore, replay, List.foldl_nil] using hn
    have hm' : mooreRun u v s' n entry = some (h, b) := by
      simpa only [execute_eq_moore, replay, List.foldl_nil] using hn'
    obtain ⟨rs, q, ha, he, _⟩ := fuel_to_actual u v s n entry h b hm
    obtain ⟨rs', q', ha', he', _⟩ := fuel_to_actual u v s' n entry h b hm'
    rw [ha.cost_eq, ha'.cost_eq, he, he']
  · have hr' : ¬ ∃ n hb, execute response (policy u v entry) n [] s' = some hb := by
      rintro ⟨n, hb, hn⟩
      exact hr ⟨n, hb, (hexe n).trans hn⟩
    simp only [cost, dif_neg hr, dif_neg hr']

/-- Proof-side Borel factorization through the fixed finite table's response pattern. -/
theorem signature_factor_borel [Finite P] {A : Type*} [MeasurableSpace A]
    (u : P → I ⊕ Bool) (f : Source → A)
    (hf : ∀ s s', signature u s = signature u s' → f s = f s') : Measurable f := by
  classical
  let g : (P → Bool) → A := fun r =>
    if hr : ∃ s, signature u s = r then f (Classical.choose hr) else f (0, false)
  have hg : Measurable g := measurable_of_finite _
  have he : f = g ∘ signature u := by
    funext s
    have hr : ∃ s', signature u s' = signature u s := ⟨s, rfl⟩
    simp only [Function.comp_def, g, dif_pos hr]
    exact hf s (Classical.choose hr) (Classical.choose_spec hr).symm
  rw [he]
  exact hg.comp (signature_measurable u)

theorem cost_source_borel [Finite P] (u : P → I ⊕ Bool) (v : P → Bool → P)
    (entry : P) : Measurable (fun s : Source => cost (policy u v entry) s) :=
  signature_factor_borel u _ (cost_signature_eq u v entry)

theorem terminal_event_source_borel [Finite P] (u : P → I ⊕ Bool)
    (v : P → Bool → P) (entry : P) (E : Set (History × Bool)) :
    MeasurableSet {s : Source | ∃ n hb, mooreRun u v s n entry = some hb ∧ hb ∈ E} := by
  classical
  let f : Source → Bool := fun s => decide (∃ n hb, mooreRun u v s n entry = some hb ∧ hb ∈ E)
  have hm : Measurable f := signature_factor_borel u f (by
    intro s s' hs
    simp only [f, moore_signature_eq u v s s' hs])
  have he : {s : Source | ∃ n hb, mooreRun u v s n entry = some hb ∧ hb ∈ E} =
      f ⁻¹' {true} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, f, decide_eq_true_eq]
  rw [he]
  exact (measurableSet_singleton true).preimage hm



end
end D5.S3.ConceptDynamics.Decision.ExactRealMooreProbeStateBounds

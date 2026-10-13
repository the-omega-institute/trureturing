/- GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryStoppedSplice
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NativeBernoulliFactoryStoppedSplice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual stopped execution splicing and marked seed-section products. -/

import D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryCriticalMoment

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryStoppedSplice
open SeededBernoulliFactoryExecution NativeBernoulliFactoryCriticalMoment

local notation "History" => List (Bool × Bool)
local notation "Action" => Bool ⊕ (Bool × Bool)
local notation "Cell" => Bool × Bool
variable {GateSeed CoreSeed Tape : Type}
local instance : MeasurableSpace (Option (ℕ × Cell)) := ⊤
local instance : MeasurableSpace (Option Bool) := ⊤

/-- Search the prefixes in increasing order, including the empty prefix. -/
def scanReturn (G : GateSeed → Bool → History → Action) (g : GateSeed)
    (S : Bool) (h : History) : ℕ → Option (ℕ × Cell)
  | 0 => match G g S [] with
    | .inl _ => none
    | .inr c => some (0, c)
  | m + 1 => match scanReturn G g S h m with
    | some cut => some cut
    | none => match G g S (h.take (m + 1)) with
      | .inl _ => none
      | .inr c => some (m + 1, c)

/-- A returned gate is replaced immediately by its selected continuation.
The gate only reads its own seed coordinate. -/
def stoppedSplice (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (seed : GateSeed × CoreSeed) (S : Bool) (h : History) : Action :=
  match scanReturn G seed.1 S h h.length with
  | none => G seed.1 S h
  | some (n, c) => C c seed.2 S (h.drop n)

/-- All labelled calls of a finite record, followed by the indicated action. -/
def seedSection {Seed : Type} (π : Seed → Bool → History → Action)
    (S : Bool) (h : History) (a : Action) : Set Seed :=
  {seed | (∀ i : Fin h.length,
    π seed S (h.take i) = .inl (h.get i).1) ∧ π seed S h = a}

private theorem scan_return_none_iff (G : GateSeed → Bool → History → Action)
    (g : GateSeed) (S : Bool) (h : History) (m : ℕ) :
    scanReturn G g S h m = none ↔
      ∀ i ≤ m, ∃ source, G g S (h.take i) = .inl source := by
  induction m with
  | zero =>
    cases hg : G g S [] <;> simp [scanReturn, hg]
  | succ m ih =>
    cases he : scanReturn G g S h m with
    | some cut =>
      simp only [scanReturn, he, reduceCtorEq, false_iff]
      intro hall
      have := ih.mpr (fun i hi => hall i (Nat.le_succ_of_le hi))
      rw [he] at this
      contradiction
    | none =>
      have hprev := ih.mp he
      cases hg : G g S (h.take (m + 1)) with
      | inl source =>
        simp only [scanReturn, he, hg, true_iff]
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hi
        · exact ⟨source, hg⟩
        · exact hprev i (by omega)
      | inr c =>
        simp only [scanReturn, he, hg, reduceCtorEq, false_iff]
        intro hall
        obtain ⟨source, hs⟩ := hall (m + 1) le_rfl
        rw [hg] at hs
        contradiction

private theorem scan_return_first (G : GateSeed → Bool → History → Action)
    (g : GateSeed) (S : Bool) (h : History) (n m : ℕ) (c : Cell)
    (hnm : n ≤ m)
    (hpre : ∀ i < n, ∃ source, G g S (h.take i) = .inl source)
    (hend : G g S (h.take n) = .inr c) :
    scanReturn G g S h m = some (n, c) := by
  have hbase : scanReturn G g S h n = some (n, c) := by
    cases n with
    | zero =>
      simp only [List.take_zero] at hend
      simp [scanReturn, hend]
    | succ n =>
      have hn : scanReturn G g S h n = none :=
        (scan_return_none_iff G g S h n).mpr (fun i hi => hpre i (by omega))
      simp [scanReturn, hn, hend]
  induction m, hnm using Nat.le_induction with
  | base => exact hbase
  | succ m hnm ih => simp [scanReturn, ih]

/-- A genuine first returned prefix is unchanged by every suffix extension. -/
theorem scan_return_append (G : GateSeed → Bool → History → Action)
    (g : GateSeed) (S : Bool) (γ t : History) (c : Cell)
    (hg : g ∈ seedSection G S γ (.inr c)) :
    scanReturn G g S (γ ++ t) (γ ++ t).length = some (γ.length, c) := by
  apply scan_return_first
  · simp
  · intro i hi
    refine ⟨(γ.get ⟨i, hi⟩).1, ?_⟩
    rw [List.take_append_of_le_length hi.le]
    exact hg.1 ⟨i, hi⟩
  · simpa using hg.2

private theorem splice_after_cut (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (g : GateSeed) (s : CoreSeed) (S : Bool) (γ t : History) (c : Cell)
    (hg : g ∈ seedSection G S γ (.inr c)) :
    stoppedSplice G C (g, s) S (γ ++ t) = C c s S t := by
  simp only [stoppedSplice, scan_return_append G g S γ t c hg]
  simp

private theorem splice_before_cut (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (g : GateSeed) (s : CoreSeed) (S : Bool) (γ : History) (c : Cell)
    (hg : g ∈ seedSection G S γ (.inr c)) (i : ℕ) (hi : i < γ.length) :
    stoppedSplice G C (g, s) S (γ.take i) = G g S (γ.take i) := by
  have hn : scanReturn G g S (γ.take i) (γ.take i).length = none := by
    apply (scan_return_none_iff ..).mpr
    intro j hj
    have hji : j ≤ i := hj.trans (List.length_take_le ..)
    have hjγ : j < γ.length := hji.trans_lt hi
    refine ⟨(γ.get ⟨j, hjγ⟩).1, ?_⟩
    simpa [List.take_take, Nat.min_eq_left hji] using hg.1 ⟨j, hjγ⟩
  simp only [stoppedSplice, hn]

/-- The recorded tape answers use the global call indices. -/
def tapeSection (answer : Bool → ℕ → Tape → Bool) (γ : History) : Set Tape :=
  {tape | ∀ i : Fin γ.length, answer (γ.get i).1 i tape = (γ.get i).2}

private theorem history_of_sections {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool)
    (answer : Bool → ℕ → Tape → Bool) (seed : Seed) (tape : Tape)
    (γ : History)
    (hseed : ∀ i : Fin γ.length, π seed S (γ.take i) = .inl (γ.get i).1)
    (htape : tape ∈ tapeSection answer γ) :
    ∀ n ≤ γ.length, acquiredHistory π S answer n (seed, tape) = γ.take n := by
  intro n
  induction n with
  | zero => simp [acquiredHistory]
  | succ n ih =>
    intro hn
    have hi : n < γ.length := by omega
    rw [acquiredHistory, ih (by omega)]
    rw [hseed ⟨n, hi⟩]
    change γ.take n ++ [((γ.get ⟨n, hi⟩).1, answer (γ.get ⟨n, hi⟩).1 n tape)] = _
    rw [htape ⟨n, hi⟩]
    exact (List.take_succ_eq_append_getElem hi).symm

/-- The actual wrapper record and next action agree with the actual core at
every elapsed core time. A returned core stays returned without extra calls. -/
theorem acquired_history_stopped_splice
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (g : GateSeed) (s : CoreSeed) (S : Bool)
    (answer : Bool → ℕ → Tape → Bool) (tape : Tape)
    (γ : History) (c : Cell)
    (hg : g ∈ seedSection G S γ (.inr c))
    (htape : tape ∈ tapeSection answer γ) (k : ℕ) :
    let core := acquiredHistory (C c) S (fun source j t => answer source (γ.length + j) t)
      k (s, tape)
    acquiredHistory (stoppedSplice G C) S answer (γ.length + k) ((g, s), tape) =
      γ ++ core ∧
    stoppedSplice G C (g, s) S
      (acquiredHistory (stoppedSplice G C) S answer (γ.length + k) ((g, s), tape)) =
      C c s S core := by
  have hbase : acquiredHistory (stoppedSplice G C) S answer γ.length ((g, s), tape) = γ := by
    have h := history_of_sections (stoppedSplice G C) S answer (g, s) tape γ
      (fun i => (splice_before_cut G C g s S γ c hg i i.isLt).trans (hg.1 i))
      htape γ.length le_rfl
    simpa using h
  have hh : acquiredHistory (stoppedSplice G C) S answer (γ.length + k) ((g, s), tape) =
      γ ++ acquiredHistory (C c) S (fun source j t => answer source (γ.length + j) t)
        k (s, tape) := by
    induction k with
    | zero => simpa [acquiredHistory] using hbase
    | succ k ih =>
      rw [Nat.add_succ, acquiredHistory, ih, splice_after_cut G C g s S γ _ c hg]
      simp only [acquiredHistory]
      split <;> simp [List.append_assoc]
  exact ⟨hh, by rw [hh]; exact splice_after_cut G C g s S γ _ c hg⟩

private theorem history_prefix {Seed : Type} (π : Seed → Bool → History → Action)
    (S : Bool) (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape)
    (i n : ℕ) (hin : i ≤ n) :
    acquiredHistory π S answer i ω <+: acquiredHistory π S answer n ω := by
  induction n, hin using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n hin ih =>
    simp only [acquiredHistory]
    split
    · exact ih.trans (List.prefix_append _ _)
    · exact ih

private theorem sections_of_actual_return {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool)
    (answer : Bool → ℕ → Tape → Bool) (ω : Seed × Tape) (n : ℕ) (c : Cell)
    (hstop : hittingAfter (fun i z => π z.1 S (acquiredHistory π S answer i z))
      (Set.range (fun cell : Cell => (Sum.inr cell : Action))) 0 ω = (n : WithTop ℕ))
    (hret : π ω.1 S (acquiredHistory π S answer n ω) = .inr c) :
    ω.1 ∈ seedSection π S (acquiredHistory π S answer n ω) (.inr c) ∧
      ω.2 ∈ tapeSection answer (acquiredHistory π S answer n ω) := by
  let γ := acquiredHistory π S answer n ω
  have hlen : γ.length = n := acquired_history_length_at_return π S answer ω n hstop
  have hp (i : ℕ) (hi : i ≤ n) : γ.take i = acquiredHistory π S answer i ω := by
    have hl : (acquiredHistory π S answer i ω).length = i :=
      acquired_history_length_before_return π S answer ω i (by rw [hstop]; exact_mod_cast hi)
    simpa only [hl] using (List.prefix_iff_eq_take.mp (history_prefix π S answer ω i n hi)).symm
  have hstep (i : Fin γ.length) :
      π ω.1 S (γ.take i) = .inl (γ.get i).1 ∧
        answer (γ.get i).1 i ω.2 = (γ.get i).2 := by
    have hin : i.val < n := by simpa [hlen] using i.isLt
    obtain ⟨source, hs⟩ := call_before_return π S answer ω i
      (by rw [hstop]; exact_mod_cast hin)
    change π ω.1 S (acquiredHistory π S answer i ω) = .inl source at hs
    have he := hp (i + 1) (by omega)
    rw [acquiredHistory, hs, ← hp i hin.le, List.take_succ_eq_append_getElem i.isLt] at he
    have helem : γ.get i = (source, answer source i ω.2) := by
      simpa [List.get_eq_getElem] using List.append_cancel_left he
    rw [helem, hp i hin.le]
    exact ⟨hs, rfl⟩
  exact ⟨⟨fun i => (hstep i).1, hret⟩, fun i => (hstep i).2⟩

/-- A finite return of the original execution supplies the cut automatically;
the wrapper then uses global innovations `n + k` for every core step. -/
theorem acquired_history_at_actual_stop
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (g : GateSeed) (s : CoreSeed) (S : Bool)
    (answer : Bool → ℕ → Tape → Bool) (tape : Tape) (n : ℕ) (c : Cell)
    (hstop : hittingAfter (fun i z => G z.1 S (acquiredHistory G S answer i z))
      (Set.range (fun cell : Cell => (Sum.inr cell : Action))) 0 (g, tape) = (n : WithTop ℕ))
    (hret : G g S (acquiredHistory G S answer n (g, tape)) = .inr c) (k : ℕ) :
    let γ := acquiredHistory G S answer n (g, tape)
    let core := acquiredHistory (C c) S (fun source j t => answer source (n + j) t) k (s, tape)
    acquiredHistory (stoppedSplice G C) S answer (n + k) ((g, s), tape) = γ ++ core ∧
      stoppedSplice G C (g, s) S
        (acquiredHistory (stoppedSplice G C) S answer (n + k) ((g, s), tape)) = C c s S core := by
  obtain ⟨hg, ht⟩ := sections_of_actual_return G S answer (g, tape) n c hstop hret
  have hl := acquired_history_length_at_return G S answer (g, tape) n hstop
  have hx := acquired_history_stopped_splice G C g s S answer tape
    (acquiredHistory G S answer n (g, tape)) c hg ht k
  exact ⟨by simpa only [hl] using hx.1, by simpa only [hl] using hx.2⟩

private theorem take_append_at (γ t : History) (j : ℕ) :
    (γ ++ t).take (γ.length + j) = γ ++ t.take j := by
  simp [List.take_append, List.take_of_length_le (Nat.le_add_right γ.length j)]

private theorem splice_seed_section_iff
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (g : GateSeed) (s : CoreSeed) (S : Bool) (γ t : History) (c : Cell) (a : Action)
    (hg : g ∈ seedSection G S γ (.inr c)) :
    (g, s) ∈ seedSection (stoppedSplice G C) S (γ ++ t) a ↔
      s ∈ seedSection (C c) S t a := by
  constructor
  · rintro ⟨hcall, hend⟩
    constructor
    · intro j
      have hj : γ.length + j.val < (γ ++ t).length := by simp
      have he := hcall ⟨γ.length + j.val, hj⟩
      rw [take_append_at, splice_after_cut G C g s S γ _ c hg] at he
      simpa [List.get_eq_getElem, List.getElem_append_right] using he
    · rwa [splice_after_cut G C g s S γ t c hg] at hend
  · rintro ⟨hcall, hend⟩
    constructor
    · intro i
      by_cases hi : i.val < γ.length
      · rw [List.take_append_of_le_length hi.le,
          splice_before_cut G C g s S γ c hg i hi]
        simpa [List.get_eq_getElem, List.getElem_append_left hi] using hg.1 ⟨i, hi⟩
      · have hi' : γ.length ≤ i.val := by omega
        have hj : i.val - γ.length < t.length := by have := i.isLt; simp at this; omega
        have he : i.val = γ.length + (i.val - γ.length) := by omega
        change stoppedSplice G C (g, s) S ((γ ++ t).take i.val) = _
        rw [he, take_append_at, splice_after_cut G C g s S γ _ c hg]
        simpa [List.get_eq_getElem, List.getElem_append_right hi'] using hcall ⟨_, hj⟩
    · rw [splice_after_cut G C g s S γ t c hg]
      exact hend

/-- Marking the actual first returned gate record separates the seed section
exactly. No core seed coordinate is constrained by the gate. -/
theorem stopped_seed_section_product
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (S : Bool) (γ t : History) (c : Cell) (a : Action) :
    (Prod.fst ⁻¹' seedSection G S γ (.inr c)) ∩
        seedSection (stoppedSplice G C) S (γ ++ t) a =
      (seedSection G S γ (.inr c)) ×ˢ (seedSection (C c) S t a) := by
  ext ⟨g, s⟩
  change (g ∈ seedSection G S γ (.inr c) ∧
    (g, s) ∈ seedSection (stoppedSplice G C) S (γ ++ t) a) ↔ _
  constructor
  · rintro ⟨hg, hc⟩
    exact ⟨hg, (splice_seed_section_iff G C g s S γ t c a hg).mp hc⟩
  · rintro ⟨hg, hc⟩
    exact ⟨hg, (splice_seed_section_iff G C g s S γ t c a hg).mpr hc⟩

private theorem scan_return_measurable [MeasurableSpace GateSeed]
    (G : GateSeed → Bool → History → Action)
    (hG : ∀ S h, Measurable (fun g => G g S h)) (S : Bool) (h : History) (m : ℕ) :
    Measurable (fun g => scanReturn G g S h m) := by
  let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
  induction m with
  | zero =>
    exact (Measurable.of_discrete (f := fun a : Action => match a with
      | .inl _ => (none : Option (ℕ × Cell))
      | .inr c => some (0, c))).comp (hG S [])
  | succ m ih =>
    exact (Measurable.of_discrete (f := fun z : Option (ℕ × Cell) × Action =>
      match z.1 with
      | some cut => some cut
      | none => match z.2 with
        | .inl _ => none
        | .inr c => some (m + 1, c))).comp (ih.prodMk (hG S (h.take (m + 1))))

/-- Finite prefix replay preserves measurability for arbitrary seed spaces. -/
theorem stopped_splice_measurable [MeasurableSpace GateSeed] [MeasurableSpace CoreSeed]
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (hG : ∀ S h, Measurable (fun g => G g S h))
    (hC : ∀ c S h, Measurable (fun s => C c s S h)) (S : Bool) (h : History) :
    Measurable (fun seed => stoppedSplice G C seed S h) := by
  have hf : Measurable (fun z : (GateSeed × CoreSeed) × Option (ℕ × Cell) =>
      match z.2 with
      | none => G z.1.1 S h
      | some (n, c) => C c z.1.2 S (h.drop n)) := by
    apply measurable_from_prod_countable_left
    intro cut
    cases cut with
    | none => exact (hG S h).comp measurable_fst
    | some cut => exact (hC cut.2 S (h.drop cut.1)).comp measurable_snd
  exact hf.comp (measurable_id.prodMk
    ((scan_return_measurable G hG S h h.length).comp measurable_fst))

private theorem seed_section_measurable {Seed : Type} [MeasurableSpace Seed]
    (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h))
    (S : Bool) (h : History) (a : Action) : MeasurableSet (seedSection π S h a) := by
  apply MeasurableSet.inter
  · change MeasurableSet {seed | ∀ i : Fin h.length,
      π seed S (h.take i) = .inl (h.get i).1}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i : Fin h.length =>
      (hπ S (h.take i)) (action_singleton_measurable (.inl (h.get i).1)))
  · exact (hπ S h) (action_singleton_measurable a)

local notation "Coin" => fun (p : unitInterval) (u : ℝ) => decide (u ≤ (p : ℝ))
local notation "Read" => fun (p q : unitInterval) (source : Bool) (n : ℕ) (tape : ℕ → ℝ) =>
  Coin (if source then q else p) (tape n)
local notation "RawLaw" => fun {Seed : Type} [MeasurableSpace Seed] (ν : Measure Seed) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => (volume.restrict (Icc (0 : ℝ) 1) : Measure ℝ)))

private def recordStream (h : History) (i : ℕ) : Cell := h[i]?.getD (false, false)

private theorem prefix_record_stream (h : History) (n : ℕ) (hn : n ≤ h.length) :
    List.ofFn (fun i : Fin n => recordStream h i) = h.take n := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hih : i < h.length := hin.trans_le hn
    simp [recordStream, List.getElem?_eq_getElem hih]

/-- A labelled native leaf includes every actual call and its next action. -/
def nativeLeaf {Seed : Type} (π : Seed → Bool → History → Action)
    (S : Bool) (p q : unitInterval) (h : History) (a : Action) : Set (Seed × (ℕ → ℝ)) :=
  {ω | (∀ i < h.length,
    π ω.1 S (acquiredHistory π S (Read p q) i ω) = .inl (recordStream h i).1 ∧
      Read p q (recordStream h i).1 i ω.2 = (recordStream h i).2) ∧
    π ω.1 S (acquiredHistory π S (Read p q) h.length ω) = a}

private def sourceLikelihood (p q : unitInterval) (h : History) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range h.length,
    (bernoulliMeasure true false (if (recordStream h i).1 then q else p))
      {(recordStream h i).2}

private theorem native_leaf_sections {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool) (p q : unitInterval)
    (h : History) (a : Action) :
    nativeLeaf π S p q h a = seedSection π S h a ×ˢ tapeSection (Read p q) h := by
  simp only [nativeLeaf, Set.ofPred_and]
  rw [trace_action_seed_event π S p q (recordStream h) h.length a,
    trace_event_sections π S p q (recordStream h) h.length]
  ext ⟨s, tape⟩
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [prefix_record_stream h h.length le_rfl, List.take_length]
  constructor
  · rintro ⟨⟨hp, ht⟩, ha⟩
    refine ⟨⟨?_, ha⟩, ?_⟩
    · intro i
      have hi := hp i i.isLt
      rw [prefix_record_stream h i i.isLt.le] at hi
      simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem i.isLt] using hi
    · intro i
      have hi := ht i (Finset.mem_range.mpr i.isLt)
      simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem i.isLt] using hi
  · rintro ⟨⟨hp, ha⟩, ht⟩
    refine ⟨⟨?_, ?_⟩, ha⟩
    · intro i hi
      rw [prefix_record_stream h i hi.le]
      simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem hi] using hp ⟨i, hi⟩
    · intro i hi
      have hil := Finset.mem_range.mp hi
      simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem hil] using ht ⟨i, hil⟩

private theorem tape_section_append (answer : Bool → ℕ → Tape → Bool)
    (γ t : History) (tape : Tape) :
    tape ∈ tapeSection answer (γ ++ t) ↔
      tape ∈ tapeSection answer γ ∧
        tape ∈ tapeSection (fun source j r => answer source (γ.length + j) r) t := by
  constructor
  · intro h
    constructor
    · intro i
      have hi : i.val < (γ ++ t).length := by simp only [List.length_append]; omega
      simpa [List.get_eq_getElem, List.getElem_append_left i.isLt] using h ⟨i, hi⟩
    · intro j
      have hj : γ.length + j.val < (γ ++ t).length := by simp
      simpa [List.get_eq_getElem, List.getElem_append_right] using h ⟨_, hj⟩
  · rintro ⟨hg, ht⟩ i
    by_cases hi : i.val < γ.length
    · simpa [List.get_eq_getElem, List.getElem_append_left hi] using hg ⟨i, hi⟩
    · have hil : γ.length ≤ i.val := by omega
      have hj : i.val - γ.length < t.length := by have := i.isLt; simp at this; omega
      have he : γ.length + (i.val - γ.length) = i.val := by omega
      simpa [List.get_eq_getElem, List.getElem_append_right hil, he] using ht ⟨_, hj⟩

/-- The marked wrapper leaf is exactly the gate leaf and the original core
leaf on the shifted tape. Its cut is the actual first return of the gate. -/
theorem native_stopped_leaf_cut
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (S : Bool) (p q : unitInterval) (γ t : History) (c : Cell) (a : Action) :
    (nativeLeaf (stoppedSplice G C) S p q (γ ++ t) a ∩
        (fun ω => ω.1.1) ⁻¹' seedSection G S γ (.inr c) =
      {ω : (GateSeed × CoreSeed) × (ℕ → ℝ) |
        (ω.1.1, ω.2) ∈ nativeLeaf G S p q γ (.inr c) ∧
        (ω.1.2, fun i => ω.2 (γ.length + i)) ∈ nativeLeaf (C c) S p q t a}) ∧
    (∀ ω ∈ nativeLeaf G S p q γ (.inr c),
      hittingAfter (fun n z => G z.1 S (acquiredHistory G S (Read p q) n z))
        (Set.range (fun cell : Cell => (Sum.inr cell : Action))) 0 ω =
          (γ.length : WithTop ℕ)) := by
  constructor
  · simp only [native_leaf_sections]
    ext ⟨⟨g, s⟩, tape⟩
    change (((g, s) ∈ seedSection (stoppedSplice G C) S (γ ++ t) a ∧
        tape ∈ tapeSection (Read p q) (γ ++ t)) ∧ g ∈ seedSection G S γ (.inr c)) ↔ _
    rw [tape_section_append]
    by_cases hg : g ∈ seedSection G S γ (.inr c)
    · rw [splice_seed_section_iff G C g s S γ t c a hg]
      change ((_ ∧ _ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
      tauto
    · simp [hg]
  · intro ω hω
    exact trace_return_call_count G S p q (recordStream γ) γ.length c ω hω.1 hω.2

private theorem native_leaf_with_seed_law {Seed : Type} [MeasurableSpace Seed]
    (π : Seed → Bool → History → Action)
    (hπ : ∀ S h, Measurable (fun seed => π seed S h)) (S : Bool)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p q : unitInterval)
    (h : History) (a : Action) (D : Set Seed) (hD : MeasurableSet D) :
    (RawLaw ν) (nativeLeaf π S p q h a ∩ Prod.fst ⁻¹' D) =
      ν (seedSection π S h a ∩ D) * sourceLikelihood p q h := by
  let E : Set Seed := {s | π s S (List.ofFn (fun i : Fin h.length => recordStream h i)) = a} ∩ D
  have hE : MeasurableSet E :=
    ((hπ S _) (action_singleton_measurable a)).inter hD
  have he := trace_action_seed_event π S p q (recordStream h) h.length a
  change ({ω | ∀ i < h.length,
      π ω.1 S (acquiredHistory π S (Read p q) i ω) = .inl (recordStream h i).1 ∧
        Read p q (recordStream h i).1 i ω.2 = (recordStream h i).2} ∩
    {ω | π ω.1 S (acquiredHistory π S (Read p q) h.length ω) = a}) = _ at he
  simp only [nativeLeaf, Set.ofPred_and]
  rw [he, Set.inter_assoc, ← Set.preimage_inter]
  rw [(native_source_trace_law π hπ S ν p q (recordStream h) h.length E hE).2]
  congr 1
  apply congrArg ν
  ext s
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, E]
  rw [prefix_record_stream h h.length le_rfl, List.take_length]
  change ((∀ i < h.length, π s S (List.ofFn (fun j : Fin i => recordStream h j)) =
    .inl (recordStream h i).1) ∧ π s S h = a ∧ s ∈ D) ↔ _
  constructor
  · rintro ⟨hp, ha, hd⟩
    refine ⟨⟨?_, ha⟩, hd⟩
    intro i
    have hi := hp i i.isLt
    rw [prefix_record_stream h i i.isLt.le] at hi
    simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem i.isLt] using hi
  · rintro ⟨⟨hp, ha⟩, hd⟩
    refine ⟨?_, ha, hd⟩
    intro i hi
    rw [prefix_record_stream h i hi.le]
    simpa [recordStream, List.get_eq_getElem, List.getElem?_eq_getElem hi] using hp ⟨i, hi⟩

private theorem source_likelihood_append (p q : unitInterval) (γ t : History) :
    sourceLikelihood p q (γ ++ t) = sourceLikelihood p q γ * sourceLikelihood p q t := by
  unfold sourceLikelihood
  rw [List.length_append, Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [recordStream, List.getElem?_append_left (Finset.mem_range.mp hi)]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [recordStream, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]

/-- The probability of a marked stopped wrapper leaf factors without dividing
by the gate probability. Both sources use the same innovation at each index. -/
theorem native_stopped_record_factorization
    [MeasurableSpace GateSeed] [MeasurableSpace CoreSeed]
    (G : GateSeed → Bool → History → Action)
    (C : Cell → CoreSeed → Bool → History → Action)
    (hG : ∀ S h, Measurable (fun g => G g S h))
    (hC : ∀ c S h, Measurable (fun s => C c s S h))
    (νg : Measure GateSeed) (νc : Measure CoreSeed)
    [IsProbabilityMeasure νg] [IsProbabilityMeasure νc]
    (S : Bool) (p q : unitInterval) (γ t : History) (c : Cell) (a : Action) :
    (RawLaw (νg.prod νc))
      {ω : (GateSeed × CoreSeed) × (ℕ → ℝ) |
        (ω.1.1, ω.2) ∈ nativeLeaf G S p q γ (.inr c) ∧
        (ω.1.2, fun i => ω.2 (γ.length + i)) ∈ nativeLeaf (C c) S p q t a} =
      (RawLaw νg) (nativeLeaf G S p q γ (.inr c)) *
        (RawLaw νc) (nativeLeaf (C c) S p q t a) := by
  have hm : MeasurableSet (Prod.fst ⁻¹' seedSection G S γ (.inr c) :
      Set (GateSeed × CoreSeed)) := measurable_fst (seed_section_measurable G hG S γ (.inr c))
  have hw := native_leaf_with_seed_law (stoppedSplice G C)
    (stopped_splice_measurable G C hG hC) S (νg.prod νc) p q (γ ++ t) a
    (Prod.fst ⁻¹' seedSection G S γ (.inr c)) hm
  change (RawLaw (νg.prod νc))
    (nativeLeaf (stoppedSplice G C) S p q (γ ++ t) a ∩
      (fun ω => ω.1.1) ⁻¹' seedSection G S γ (.inr c)) = _ at hw
  have hg := native_leaf_with_seed_law G hG S νg p q γ (.inr c) univ MeasurableSet.univ
  have hc := native_leaf_with_seed_law (C c) (hC c) S νc p q t a univ MeasurableSet.univ
  simp only [Set.preimage_univ, Set.inter_univ] at hg hc
  rw [← (native_stopped_leaf_cut G C S p q γ t c a).1]
  rw [hw, hg, hc, Set.inter_comm, stopped_seed_section_product,
    Measure.prod_prod, source_likelihood_append]
  ac_rfl

/-- A one-source gate uses `none` to request another answer and `some v`
to return. The first actual answer is retained separately from the gate bit. -/
def firstXGate (G : GateSeed → Bool → History → Option Bool)
    (g : GateSeed) (S : Bool) : History → Action
  | [] => .inl S
  | (source, b) :: t =>
    if source = S then
      match G g b t with
      | none => .inl S
      | some v => .inr (b, v)
    else .inl S

/-- The core success bit is mapped to agreement with the actual first answer. -/
def firstXAction (b : Bool) : Action → Action
  | .inl source => .inl source
  | .inr c => .inr (b, if c.1 then b else !b)

/-- The fair-bit coordinate is read only when the gate does not trigger. -/
def firstXContinuation (C : CoreSeed → Bool → History → Action)
    (c : Cell) (s : CoreSeed × Bool) (S : Bool) (h : History) : Action :=
  if c.2 then firstXAction c.1 (C s.1 S h) else .inr (c.1, s.2)

/-- The private gate seed, core seed and fair bit occupy disjoint coordinates. -/
def firstXWrapper (G : GateSeed → Bool → History → Option Bool)
    (C : CoreSeed → Bool → History → Action) :
    GateSeed × (CoreSeed × Bool) → Bool → History → Action :=
  stoppedSplice (firstXGate G) (firstXContinuation C)

private theorem first_x_wrong_source (G : GateSeed → Bool → History → Option Bool)
    (C : CoreSeed → Bool → History → Action) (seed : GateSeed × (CoreSeed × Bool))
    (S source b : Bool) (h : History) (hbad : source ≠ S) :
    firstXWrapper G C seed S ((source, b) :: h) = .inl S := by
  have hn : scanReturn (firstXGate G) seed.1 S ((source, b) :: h)
      ((source, b) :: h).length = none := by
    apply (scan_return_none_iff ..).mpr
    intro i hi
    refine ⟨S, ?_⟩
    cases i <;> simp [firstXGate, hbad]
  simp only [firstXWrapper, stoppedSplice, hn]
  simp [firstXGate, hbad]

private theorem first_x_gate_section (G : GateSeed → Bool → History → Option Bool)
    (g : GateSeed) (S b v : Bool) (h : History)
    (hc : ∀ i : Fin h.length, (h.get i).1 = S ∧ G g b (h.take i) = none)
    (he : G g b h = some v) :
    g ∈ seedSection (firstXGate G) S ((S, b) :: h) (.inr (b, v)) := by
  constructor
  · intro i
    cases hn : i.val with
    | zero => simp [firstXGate, hn]
    | succ j =>
      have hj : j < h.length := by have := i.isLt; simp at this; omega
      have hcall := hc ⟨j, hj⟩
      simpa [firstXGate, hn, hcall.2, List.get_eq_getElem] using
        congrArg (fun source => (Sum.inl source : Action)) hcall.1.symm
  · simp [firstXGate, he]

private theorem first_x_continuation_history
    (C : CoreSeed → Bool → History → Action) (b fair S : Bool)
    (answer : Bool → ℕ → Tape → Bool) (s : CoreSeed) (tape : Tape) (k : ℕ) :
    acquiredHistory (firstXContinuation C (b, true)) S answer k ((s, fair), tape) =
      acquiredHistory C S answer k (s, tape) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [acquiredHistory, ih, firstXContinuation, ↓reduceIte]
    cases C s S (acquiredHistory C S answer k (s, tape)) <;> rfl

private theorem first_x_gate_measurable [MeasurableSpace GateSeed]
    (G : GateSeed → Bool → History → Option Bool)
    (hG : ∀ b h, Measurable (fun g => G g b h)) (S : Bool) (h : History) :
    Measurable (fun g => firstXGate G g S h) := by
  cases h with
  | nil => exact measurable_const
  | cons x h =>
    by_cases hx : x.1 = S
    · convert (Measurable.of_discrete (f := fun v : Option Bool =>
        match v with | none => (Sum.inl S : Action) | some v => .inr (x.2, v))).comp
        (hG x.2 h) using 1
      funext g
      simp [firstXGate, hx]
    · simp only [firstXGate, hx, ↓reduceIte]
      exact measurable_const

private theorem first_x_continuation_measurable [MeasurableSpace CoreSeed]
    (C : CoreSeed → Bool → History → Action)
    (hC : ∀ S h, Measurable (fun s => C s S h)) (c : Cell) (S : Bool) (h : History) :
    Measurable (fun s => firstXContinuation C c s S h) := by
  let : MeasurableSingletonClass Action := ⟨action_singleton_measurable⟩
  rcases c with ⟨b, v⟩
  cases v
  · exact (Measurable.of_discrete (f := fun fair : Bool => (Sum.inr (b, fair) : Action))).comp
      (measurable_snd : Measurable (fun s : CoreSeed × Bool => s.2))
  · exact (Measurable.of_discrete (f := firstXAction b)).comp ((hC S h).comp measurable_fst)

/-- The first-X wrapper is measurable and starts with exactly the requested
source. At every triggered finite gate record it runs the original core on
the shifted native tape, including a core that returns without making a call. -/
theorem first_x_stopped_execution
    [MeasurableSpace GateSeed] [MeasurableSpace CoreSeed]
    (G : GateSeed → Bool → History → Option Bool)
    (C : CoreSeed → Bool → History → Action)
    (hG : ∀ b h, Measurable (fun g => G g b h))
    (hC : ∀ S h, Measurable (fun s => C s S h)) :
    (∀ S h, Measurable (fun seed => firstXWrapper G C seed S h)) ∧
    (∀ seed S, firstXWrapper G C seed S [] = .inl S) ∧
    (∀ seed S source b h, source ≠ S →
      firstXWrapper G C seed S ((source, b) :: h) = .inl S) ∧
    ∀ (g : GateSeed) (s : CoreSeed) (fair S b v : Bool) (p q : unitInterval)
      (tape : ℕ → ℝ) (h : History),
      (∀ i : Fin h.length, (h.get i).1 = S ∧ G g b (h.take i) = none) →
      G g b h = some v →
      tape ∈ tapeSection (Read p q) ((S, b) :: h) →
      ∀ k : ℕ,
      let n := 1 + h.length
      let core := if v then acquiredHistory C S (Read p q) k (s, fun i => tape (n + i)) else []
      acquiredHistory (firstXWrapper G C) S (Read p q) (n + k) ((g, (s, fair)), tape) =
        ((S, b) :: h) ++ core ∧
      firstXWrapper G C (g, (s, fair)) S
        (acquiredHistory (firstXWrapper G C) S (Read p q) (n + k) ((g, (s, fair)), tape)) =
        (if v then firstXAction b (C s S core) else .inr (b, fair)) := by
  refine ⟨stopped_splice_measurable (firstXGate G) (firstXContinuation C)
    (first_x_gate_measurable G hG) (first_x_continuation_measurable C hC), ?_,
    first_x_wrong_source G C, ?_⟩
  · intro seed S
    simp [firstXWrapper, stoppedSplice, scanReturn, firstXGate]
  · intro g s fair S b v p q tape h hc he ht k
    have hg := first_x_gate_section G g S b v h hc he
    have hs := acquired_history_stopped_splice (firstXGate G) (firstXContinuation C)
      g (s, fair) S (Read p q) tape ((S, b) :: h) (b, v) hg ht k
    dsimp only at hs ⊢
    cases v with
    | false =>
      have hz : ∀ j, acquiredHistory (firstXContinuation C (b, false)) S
          (fun source j t => Read p q source (((S, b) :: h).length + j) t)
          j ((s, fair), tape) = [] := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => simpa [acquiredHistory, firstXContinuation] using ih
      rw [hz k] at hs
      simpa [firstXWrapper, firstXContinuation, Nat.add_comm] using hs
    | true =>
      rw [first_x_continuation_history] at hs
      have hshift : acquiredHistory C S
        (fun source j t => Read p q source (((S, b) :: h).length + j) t) k (s, tape) =
        acquiredHistory C S (Read p q) k (s, fun i => tape (1 + h.length + i)) := by
        clear hs
        induction k with
        | zero => rfl
        | succ k ih =>
          simp only [acquiredHistory, ih]
          split <;> simp [Nat.add_comm]
      rw [hshift] at hs
      simpa [firstXWrapper, firstXContinuation, Nat.add_comm] using hs

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernoulliFactoryStoppedSplice

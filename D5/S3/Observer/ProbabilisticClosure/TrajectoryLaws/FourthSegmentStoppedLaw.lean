/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-segment first-completion words have their Bernoulli atomic law. -/

import D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators Classical
open D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation (trace FirstStop Nonstop)

abbrev Letter := Fin 2
abbrev Stream := ℕ → Letter
abbrev RawTail := Option (List Letter)

instance : MeasurableSpace (List Letter) := ⊤
instance : MeasurableSingletonClass (List Letter) := ⟨fun _ => trivial⟩
instance : MeasurableSpace RawTail := ⊤
instance : MeasurableSingletonClass RawTail := ⟨fun _ => trivial⟩

inductive ActivePhase where
  | p | beta
  deriving DecidableEq

inductive FourthControl where
  | active (s : ActivePhase)
  | pending (b : Letter)
  | delivered
  deriving DecidableEq

/-- Partial Read table; terminal states have no Read transition. -/
def legalRead : FourthControl → Letter → Option FourthControl
  | .active .p, x => some (if x = 0 then .pending 0 else .active .beta)
  | .active .beta, x => some (if x = 0 then .active .p else .pending 1)
  | .pending _, _ => none
  | .delivered, _ => none

/-- The sole operation at pending b is Stop b, followed by delivery. -/
def legalStop : FourthControl → Letter → Option FourthControl
  | .pending b, x => if x = b then some .delivered else none
  | _, _ => none

/-- Totalization for the mathematical trace only; it grants no extra Read. -/
def totalRead (c : FourthControl) (x : Letter) : FourthControl :=
  (legalRead c x).getD c

def pendingColor : FourthControl → Option Letter
  | .pending b => some b
  | _ => none

def readPrefix (ω : Stream) (n : ℕ) : List Letter :=
  List.ofFn (fun i : Fin n => ω i.val)

def Prefix (ω : Stream) (w : List Letter) : Prop := readPrefix ω w.length = w

/-- Finite parsing follows the Read table and terminates at its first pending state. -/
def Parses : FourthControl → List Letter → Letter → Prop
  | c, [], b => pendingColor c = some b
  | c, x :: w, b => pendingColor c = none ∧ Parses (totalRead c x) w b

/-- The output is selected by actual first completion, independently of word families. -/
def stoppedReadWord (s : ActivePhase) (ω : Stream) : RawTail := by
  classical
  exact if h : ∃ n, pendingColor (trace totalRead (.active s) ω n) ≠ none then
    some (readPrefix ω (Nat.find h)) else none

def loopWord (j : ℕ) : List Letter := (List.replicate j [1, 0]).flatten

def pWord (j : ℕ) (b : Letter) : List Letter :=
  loopWord j ++ if b = 0 then [0] else [1, 1]

def WordFamily : ActivePhase → Letter → List Letter → Prop
  | .p, b, w => ∃ j, w = pWord j b
  | .beta, b, w => (b = 1 ∧ w = [1]) ∨ ∃ j, w = 0 :: pWord j b

theorem prefix_length (ω : Stream) (n : ℕ) : (readPrefix ω n).length = n := by
  simp [readPrefix]

private theorem prefix_succ (ω : Stream) (n : ℕ) :
    readPrefix ω (n + 1) = ω 0 :: readPrefix (fun i => ω (i + 1)) n := by
  simp [readPrefix, List.ofFn_succ]

private theorem trace_head (c : FourthControl) (ω : Stream) (n : ℕ) :
    trace totalRead c ω (n + 1) =
      trace totalRead (totalRead c (ω 0)) (fun i => ω (i + 1)) n := by
  change (readPrefix ω (n + 1)).foldl totalRead c = _
  rw [prefix_succ]
  rfl

private theorem first_stop_head (c : FourthControl) (ω : Stream) (b : Letter) (n : ℕ) :
    FirstStop totalRead pendingColor c ω b (n + 1) ↔
      pendingColor c = none ∧
        FirstStop totalRead pendingColor (totalRead c (ω 0)) (fun i => ω (i + 1)) b n := by
  simp only [FirstStop, trace_head]
  constructor
  · rintro ⟨h, hs⟩
    refine ⟨hs 0 (by omega), h, ?_⟩
    intro j hj
    simpa only [trace_head] using hs (j + 1) (by omega)
  · rintro ⟨hc, h, hs⟩
    refine ⟨h, ?_⟩
    intro j hj
    cases j with
    | zero => exact hc
    | succ j => simpa only [trace_head] using hs j (by omega)

private theorem first_stop_parses (c : FourthControl) (ω : Stream) (b : Letter) (n : ℕ) :
    FirstStop totalRead pendingColor c ω b n ↔ Parses c (readPrefix ω n) b := by
  induction n generalizing c ω with
  | zero => simp [FirstStop, trace, readPrefix, Parses]
  | succ n ih => rw [first_stop_head, prefix_succ]; exact and_congr_right (fun _ => ih _ _)

theorem loop_succ (j : ℕ) : loopWord (j + 1) = 1 :: 0 :: loopWord j := by
  simp [loopWord, List.replicate_succ]

theorem p_word_succ (j : ℕ) (b : Letter) :
    pWord (j + 1) b = 1 :: 0 :: pWord j b := by
  simp [pWord, loop_succ]

private theorem parses_pending (a b : Letter) (w : List Letter) :
    Parses (.pending a) w b ↔ w = [] ∧ a = b := by
  cases w <;> simp [Parses, pendingColor]

private theorem family_nil (s : ActivePhase) (b : Letter) : ¬WordFamily s b [] := by
  have hp (j : ℕ) : pWord j b ≠ [] := by
    simp [pWord]
    split_ifs <;> simp
  cases s <;> simp [WordFamily, hp, Ne.symm]

private theorem family_head (s : ActivePhase) (x b : Letter) (w : List Letter) :
    WordFamily s b (x :: w) ↔
      match totalRead (.active s) x with
      | .active t => WordFamily t b w
      | .pending a => w = [] ∧ a = b
      | .delivered => False := by
  cases s <;> fin_cases x
  · constructor
    · rintro ⟨j, hj⟩
      cases j with
      | zero => fin_cases b <;> simp [pWord, loopWord] at hj ⊢ <;> tauto
      | succ j => simp [p_word_succ] at hj
    · rintro ⟨rfl, rfl⟩; exact ⟨0, rfl⟩
  · change WordFamily .p b (1 :: w) ↔ WordFamily .beta b w
    constructor
    · rintro ⟨j, hj⟩
      cases j with
      | zero =>
          fin_cases b
          · simp [pWord, loopWord] at hj
          · exact Or.inl ⟨rfl, by simpa [pWord, loopWord] using hj⟩
      | succ j => exact Or.inr ⟨j, by simpa [p_word_succ] using hj⟩
    · rintro (⟨rfl, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨0, rfl⟩
      · exact ⟨j + 1, (p_word_succ j b).symm⟩
  · simp [WordFamily, totalRead, legalRead]
  · simp [WordFamily, totalRead, legalRead, and_comm, eq_comm]

/-- The exact first-completion language is derived from the independent Read parser. -/
theorem parses_normal_form (s : ActivePhase) (w : List Letter) (b : Letter) :
    Parses (.active s) w b ↔ WordFamily s b w := by
  induction w generalizing s with
  | nil => simp [Parses, pendingColor, family_nil]
  | cons x w ih =>
      rw [family_head]
      simp only [Parses, pendingColor, true_and]
      cases s <;> fin_cases x <;>
        simp only [totalRead, legalRead, Fin.reduceEq, ↓reduceIte, Option.getD_some] <;>
        first | exact ih _ | exact parses_pending _ _ _

/-- Both directions preserve the entire readPrefix and exclude every earlier completion. -/
theorem first_completion_normal_form (s : ActivePhase) (ω : Stream) (b : Letter) (n : ℕ) :
    FirstStop totalRead pendingColor (.active s) ω b n ↔
      ∃ w : List Letter, w.length = n ∧ Prefix ω w ∧ WordFamily s b w := by
  rw [first_stop_parses, parses_normal_form]
  constructor
  · intro h
    exact ⟨readPrefix ω n, prefix_length ω n, by simp [Prefix, prefix_length], h⟩
  · rintro ⟨w, hn, hw, hf⟩
    have he : readPrefix ω n = w := by simpa [Prefix, hn] using hw
    simpa [he] using hf

private theorem stopped_some_first (s : ActivePhase) (ω : Stream) (w : List Letter) :
    stoppedReadWord s ω = some w ↔
      ∃ b, FirstStop totalRead pendingColor (.active s) ω b w.length ∧ Prefix ω w := by
  classical
  constructor
  · intro hw
    unfold stoppedReadWord at hw
    split_ifs at hw with h
    · have he : readPrefix ω (Nat.find h) = w := Option.some.inj hw
      have hn : Nat.find h = w.length := by rw [← he, prefix_length]
      have hs := Nat.find_spec h
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hs
      refine ⟨b, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · simpa [hn] using hb
        · intro j hj
          exact not_ne_iff.mp (Nat.find_min h (by omega))
      · simpa [Prefix, hn] using he
  · rintro ⟨b, hs, hw⟩
    have h : ∃ n, pendingColor (trace totalRead (.active s) ω n) ≠ none :=
      ⟨w.length, by rw [hs.1]; simp⟩
    have hn : Nat.find h = w.length := by
      apply Nat.le_antisymm (Nat.find_min' h (by rw [hs.1]; simp))
      by_contra hh
      have hlt : Nat.find h < w.length := by omega
      exact Nat.find_spec h (hs.2 _ hlt)
    simpa [stoppedReadWord, h, hn, Prefix] using congrArg some hw

private theorem stopped_none (s : ActivePhase) (ω : Stream) :
    stoppedReadWord s ω = none ↔ Nonstop totalRead pendingColor (.active s) ω := by
  classical
  unfold stoppedReadWord Nonstop
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff]
    rintro hh
    obtain ⟨n, hn⟩ := h
    exact hn (hh n)
  · simp only [true_iff]
    intro n
    exact not_ne_iff.mp (fun hn => h ⟨n, hn⟩)

/-- Finite output fibers are full prefix cylinders, with invalid words excluded. -/
theorem stopped_word_fiber (s : ActivePhase) (ω : Stream) (w : List Letter) :
    stoppedReadWord s ω = some w ↔ Prefix ω w ∧ ∃ b, WordFamily s b w := by
  rw [stopped_some_first]
  constructor
  · rintro ⟨b, hb, hw⟩
    obtain ⟨v, hn, hv, hf⟩ := (first_completion_normal_form s ω b w.length).mp hb
    have he : v = w := by
      have hv' : readPrefix ω w.length = v := by simpa [Prefix, hn] using hv
      exact hv'.symm.trans hw
    exact ⟨hw, b, he ▸ hf⟩
  · rintro ⟨hw, b, hf⟩
    exact ⟨b, (first_completion_normal_form s ω b w.length).mpr
      ⟨w, rfl, hw, hf⟩, hw⟩

def prefixCylinder (w : List Letter) : Set Stream := {ω | Prefix ω w}

private theorem measurable_prefix (n : ℕ) : Measurable (fun ω : Stream => readPrefix ω n) := by
  exact (measurable_of_countable (fun v : Fin n → Letter => List.ofFn v)).comp
    (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

theorem measurable_cylinder (w : List Letter) : MeasurableSet (prefixCylinder w) :=
  (measurable_prefix w.length) (measurableSet_singleton w)

/-- Measurability uses countably many measurable fibers, not a countable stream domain. -/
theorem measurable_stopped_read_word (s : ActivePhase) : Measurable (stoppedReadWord s) := by
  classical
  have hf (w : List Letter) : MeasurableSet {ω | stoppedReadWord s ω = some w} := by
    have he : {ω | stoppedReadWord s ω = some w} =
        if ∃ b, WordFamily s b w then prefixCylinder w else ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, stopped_word_fiber]
      split_ifs with h <;> simp [prefixCylinder, h]
    rw [he]
    split_ifs
    · exact measurable_cylinder w
    · exact MeasurableSet.empty
  apply measurable_to_countable'
  intro t
  cases t with
  | some w => exact hf w
  | none =>
      have he : {ω | stoppedReadWord s ω = none} =
          (⋃ w : List Letter, {ω | stoppedReadWord s ω = some w})ᶜ := by
        ext ω
        cases ht : stoppedReadWord s ω <;> simp [ht]
      change MeasurableSet {ω | stoppedReadWord s ω = none}
      rw [he]
      exact (MeasurableSet.iUnion hf).compl

/-- The raw stream is a homogeneous trajectory with a constant Bernoulli kernel. -/
def rawReadLaw (r : unitInterval) : Measure Stream :=
  Kernel.trajMeasure (bernoulliMeasure (0 : Letter) 1 r)
    (fun n => (Kernel.const Letter (bernoulliMeasure (0 : Letter) 1 r)).comap
      (fun u : ↥(Iic n) → Letter => u ⟨n, mem_Iic.mpr le_rfl⟩)
      (measurable_pi_apply _))

instance (r : unitInterval) : IsProbabilityMeasure (rawReadLaw r) := by
  unfold rawReadLaw
  infer_instance

def alphaMass (r : unitInterval) : ℝ≥0∞ := unitInterval.toNNReal r

def betaMass (r : unitInterval) : ℝ≥0∞ := unitInterval.toNNReal (unitInterval.symm r)

def wordMass (r : unitInterval) (w : List Letter) : ℝ≥0∞ :=
  (w.map (fun x => (bernoulliMeasure (0 : Letter) 1 r) {x})).prod

/-- An independent countable atomic law, with no atom at infinite noncompletion. -/
def explicitStoppedWordLaw (s : ActivePhase) (r : unitInterval) : Measure RawTail :=
  let R := alphaMass r
  let S := betaMass r
  let A := R * S
  match s with
  | .p => Measure.sum (fun j : ℕ =>
      (R * A ^ j) • Measure.dirac (some (pWord j 0)) +
      (S ^ 2 * A ^ j) • Measure.dirac (some (pWord j 1)))
  | .beta => S • Measure.dirac (some [1]) + Measure.sum (fun j : ℕ =>
      (R ^ 2 * A ^ j) • Measure.dirac (some (0 :: pWord j 0)) +
      (R * S ^ 2 * A ^ j) • Measure.dirac (some (0 :: pWord j 1)))

theorem cylinder_mass (r : unitInterval) (w : List Letter) :
    rawReadLaw r (prefixCylinder w) = wordMass r w := by
  classical
  cases w with
  | nil => simp [prefixCylinder, Prefix, readPrefix, wordMass]
  | cons x w =>
      let v : Fin (w.length + 1) → Letter := (x :: w).get
      have h := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
        (bernoulliMeasure (0 : Letter) 1 r)
        (Kernel.const Letter (bernoulliMeasure (0 : Letter) 1 r)) w.length v
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton v)] at h
      have he : (fun (ω : Stream) (i : Fin (w.length + 1)) => ω i.val) ⁻¹' {v} =
          prefixCylinder (x :: w) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, prefixCylinder,
          Set.mem_ofPred_eq, Prefix, readPrefix, List.length_cons]
        rw [← List.ofFn_get (x :: w), List.ofFn_inj]
      rw [he] at h
      have hm : wordMass r (x :: w) =
          ∏ i : Fin (w.length + 1), (bernoulliMeasure (0 : Letter) 1 r) {v i} := by
        rw [wordMass, ← List.ofFn_get (x :: w), List.map_ofFn, List.prod_ofFn]
        rfl
      rw [hm, Fin.prod_univ_succ]
      simpa only [rawReadLaw, Kernel.const_apply] using h

private theorem bernoulli_alpha (r : unitInterval) :
    (bernoulliMeasure (0 : Letter) 1 r) {0} = alphaMass r := by
  simp [bernoulliMeasure, alphaMass]

private theorem word_mass_append (r : unitInterval) (v w : List Letter) :
    wordMass r (v ++ w) = wordMass r v * wordMass r w := by
  simp [wordMass]

private theorem loop_mass (r : unitInterval) (j : ℕ) :
    wordMass r (loopWord j) = (alphaMass r * betaMass r) ^ j := by
  simp [wordMass, loopWord, List.map_flatten, List.prod_flatten,
    bernoulli_alpha, alphaMass, betaMass, mul_comm]

theorem p_word_mass (r : unitInterval) (j : ℕ) (b : Letter) :
    wordMass r (pWord j b) =
      (if b = 0 then alphaMass r else betaMass r ^ 2) *
        (alphaMass r * betaMass r) ^ j := by
  unfold pWord
  rw [word_mass_append, loop_mass]
  fin_cases b <;> simp [wordMass, bernoulli_alpha, alphaMass, betaMass] <;> ring

private theorem nonstop_head (c : FourthControl) (ω : Stream) :
    Nonstop totalRead pendingColor c ω ↔ pendingColor c = none ∧
      Nonstop totalRead pendingColor (totalRead c (ω 0)) (fun i => ω (i + 1)) := by
  constructor
  · intro h
    exact ⟨h 0, fun n => by simpa [trace_head] using h (n + 1)⟩
  · rintro ⟨h, ht⟩ n
    cases n with
    | zero => exact h
    | succ n => simpa [trace_head] using ht n

private theorem nonstop_p_return (ω : Stream)
    (h : Nonstop totalRead pendingColor (.active .p) ω) :
    ω 0 = 1 ∧ ω 1 = 0 ∧
      Nonstop totalRead pendingColor (.active .p) (fun i => ω (i + 2)) := by
  have h1 := (nonstop_head _ _).mp h
  have h0 : ω 0 = 1 := by
    rcases (show ω 0 = 0 ∨ ω 0 = 1 by
      have hx := (ω 0).isLt
      have hz : (ω 0).val = 0 ∨ (ω 0).val = 1 := by omega
      exact hz.imp (fun h => Fin.ext h) (fun h => Fin.ext h)) with hx | hx
    · have hh := h1.2 0
      simp [trace, totalRead, legalRead, pendingColor, hx] at hh
    · exact hx
  have hb : Nonstop totalRead pendingColor (.active .beta) (fun i => ω (i + 1)) := by
    simpa [totalRead, legalRead, h0] using h1.2
  have h2 := (nonstop_head _ _).mp hb
  have hβ : ω 1 = 0 := by
    rcases (show ω 1 = 0 ∨ ω 1 = 1 by
      have hx := (ω 1).isLt
      have hz : (ω 1).val = 0 ∨ (ω 1).val = 1 := by omega
      exact hz.imp (fun h => Fin.ext h) (fun h => Fin.ext h)) with hx | hx
    · exact hx
    · have hh := h2.2 0
      simp [trace, totalRead, legalRead, pendingColor, hx] at hh
  exact ⟨h0, hβ, by simpa [totalRead, legalRead, hβ, Nat.add_assoc] using h2.2⟩

private theorem nonstop_p_prefix (ω : Stream)
    (h : Nonstop totalRead pendingColor (.active .p) ω) (j : ℕ) :
    Prefix ω (loopWord j) := by
  induction j generalizing ω with
  | zero => simp [Prefix, loopWord, readPrefix]
  | succ j ih =>
      obtain ⟨h0, h1, ht⟩ := nonstop_p_return ω h
      have hp := ih _ ht
      unfold Prefix at hp ⊢
      rw [loop_succ]
      simp only [List.length_cons, prefix_succ]
      simpa [h0, h1, Nat.add_assoc] using congrArg (fun w => (1 : Letter) :: 0 :: w) hp

private theorem nonstop_beta_return (ω : Stream)
    (h : Nonstop totalRead pendingColor (.active .beta) ω) :
    ω 0 = 0 ∧ Nonstop totalRead pendingColor (.active .p) (fun i => ω (i + 1)) := by
  have ht := (nonstop_head _ _).mp h
  have h0 : ω 0 = 0 := by
    rcases (show ω 0 = 0 ∨ ω 0 = 1 by
      have hx := (ω 0).isLt
      have hz : (ω 0).val = 0 ∨ (ω 0).val = 1 := by omega
      exact hz.imp (fun h => Fin.ext h) (fun h => Fin.ext h)) with hx | hx
    · exact hx
    · have hh := ht.2 0
      simp [trace, totalRead, legalRead, pendingColor, hx] at hh
  exact ⟨h0, by simpa [totalRead, legalRead, h0] using ht.2⟩

/-- The unique phase-specific infinite legal sequence of noncompleting Reads. -/
def infiniteTail (s : ActivePhase) (n : ℕ) : Letter :=
  match s with
  | .p => if n % 2 = 0 then 1 else 0
  | .beta => if n % 2 = 0 then 0 else 1

theorem loop_as_prefix (j : ℕ) :
    loopWord j = readPrefix (infiniteTail .p) (2 * j) := by
  let a : Fin 2 → Letter := fun i => if i.val = 0 then 1 else 0
  have ha : List.ofFn a = [1, 0] := rfl
  have hn := List.ofFn_fin_repeat a j
  rw [ha] at hn
  have he : List.ofFn (Fin.repeat j a) = readPrefix (infiniteTail .p) (2 * j) := by
    unfold readPrefix
    rw [Nat.mul_comm 2 j]
    apply congrArg List.ofFn
    funext i
    simp [Fin.repeat, Fin.modNat, infiniteTail, a]
  exact hn.symm.trans he

private theorem infinite_tail_nonstop (s : ActivePhase) :
    Nonstop totalRead pendingColor (.active s) (infiniteTail s) := by
  have ht : ∀ n, trace totalRead (.active s) (infiniteTail s) n =
      .active (if n % 2 = 0 then s else match s with | .p => .beta | .beta => .p) := by
    intro n
    induction n with
    | zero => simp [trace]
    | succ n ih =>
        simp only [trace, List.ofFn_succ', List.concat_eq_append, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        change totalRead (trace totalRead (.active s) (infiniteTail s) n)
          (infiniteTail s n) = _
        rw [ih]
        rcases Nat.mod_two_eq_zero_or_one n with hn | hn
        · have hn' : (n + 1) % 2 = 1 := by omega
          cases s <;> simp [infiniteTail, hn, hn', totalRead, legalRead]
        · have hn' : (n + 1) % 2 = 0 := by omega
          cases s <;> simp [infiniteTail, hn, hn', totalRead, legalRead]
  intro n
  rw [ht]
  rfl

private theorem stream_eq_infinite_p (ω : Stream) (h : ∀ j, Prefix ω (loopWord j)) :
    ω = infiniteTail .p := by
  funext n
  have hp := h (n + 1)
  have hl : (loopWord (n + 1)).length = 2 * (n + 1) := by
    rw [loop_as_prefix, prefix_length]
  unfold Prefix at hp
  rw [hl, loop_as_prefix] at hp
  have hf := List.ofFn_injective hp
  exact congrFun hf ⟨n, by omega⟩

/-- None corresponds to the original unique infinite path, not to an omitted sample point. -/
theorem noncompletion_fiber (s : ActivePhase) (ω : Stream) :
    stoppedReadWord s ω = none ↔ ω = infiniteTail s := by
  constructor
  · intro h
    have hn := (stopped_none s ω).mp h
    cases s with
    | p => exact stream_eq_infinite_p ω (fun j => nonstop_p_prefix ω hn j)
    | beta =>
        obtain ⟨h0, hp⟩ := nonstop_beta_return ω hn
        have he := stream_eq_infinite_p _ (fun j => nonstop_p_prefix _ hp j)
        funext n
        cases n with
        | zero => simpa [infiniteTail] using h0
        | succ n =>
            have he' := congrFun he n
            have hm := Nat.mod_two_eq_zero_or_one n
            have hrel : infiniteTail .p n = infiniteTail .beta (n + 1) := by
              rcases hm with hm | hm
              · have hm' : (n + 1) % 2 = 1 := by omega
                simp [infiniteTail, hm, hm']
              · have hm' : (n + 1) % 2 = 0 := by omega
                simp [infiniteTail, hm, hm']
            exact he'.trans hrel
  · rintro rfl
    exact (stopped_none _ _).mpr (infinite_tail_nonstop s)

/-- Infinite noncompletion remains an outcome, but has actual mass zero at every parameter. -/
theorem actual_noncompletion_mass_zero (r : unitInterval) (s : ActivePhase) :
    rawReadLaw r {ω | stoppedReadWord s ω = none} = 0 := by
  have hratio : alphaMass r * betaMass r < 1 := by
    rw [alphaMass, betaMass, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
    change unitInterval.toNNReal r * unitInterval.toNNReal (unitInterval.symm r) < 1
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_mul, NNReal.coe_one, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq]
    have hr := r.property
    nlinarith [sq_nonneg ((r : ℝ) - 1 / 2)]
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  apply le_antisymm _ (by positivity)
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro j
  cases s with
  | p =>
      calc
        rawReadLaw r {ω | stoppedReadWord .p ω = none} ≤
            rawReadLaw r (prefixCylinder (loopWord j)) := by
          apply measure_mono
          intro ω hω
          rw [(noncompletion_fiber _ _).mp hω]
          change Prefix (infiniteTail .p) (loopWord j)
          unfold Prefix
          rw [loop_as_prefix, prefix_length]
        _ = (alphaMass r * betaMass r) ^ j := by rw [cylinder_mass, loop_mass]
  | beta =>
      calc
        rawReadLaw r {ω | stoppedReadWord .beta ω = none} ≤
            rawReadLaw r (prefixCylinder (0 :: loopWord j)) := by
          apply measure_mono
          intro ω hω
          have hpath := (noncompletion_fiber _ _).mp hω
          obtain ⟨h0, hh⟩ := nonstop_beta_return ω
            (hpath.symm ▸ infinite_tail_nonstop .beta)
          have hp := nonstop_p_prefix _ hh j
          simpa [prefixCylinder, Prefix, prefix_succ, h0] using
            congrArg (fun w => (0 : Letter) :: w) hp
        _ = alphaMass r * (alphaMass r * betaMass r) ^ j := by
          rw [cylinder_mass]
          simp only [wordMass, List.map_cons, List.prod_cons, bernoulli_alpha]
          rw [← wordMass, loop_mass]
        _ ≤ (alphaMass r * betaMass r) ^ j := by
          exact mul_le_of_le_one_left (by positivity) (by simpa [alphaMass] using
            (show (unitInterval.toNNReal r : ℝ≥0∞) ≤ 1 from by
              exact_mod_cast r.property.2))

theorem p_word_length (j : ℕ) (b : Letter) :
    (pWord j b).length = 2 * j + if b = 0 then 1 else 2 := by
  have hl : (loopWord j).length = 2 * j := by
    rw [loop_as_prefix, prefix_length]
  simp [pWord, hl]
  split_ifs <;> simp

private theorem p_word_injective (i j : ℕ) (a b : Letter) :
    pWord i a = pWord j b ↔ i = j ∧ a = b := by
  constructor
  · intro h
    have hl := congrArg List.length h
    rw [p_word_length, p_word_length] at hl
    fin_cases a <;> fin_cases b <;> simp at hl ⊢ <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem explicit_finite_mass (s : ActivePhase) (r : unitInterval) (w : List Letter) :
    explicitStoppedWordLaw s r {some w} =
      if ∃ b, WordFamily s b w then wordMass r w else 0 := by
  classical
  by_cases h : ∃ b, WordFamily s b w
  · rw [if_pos h]
    obtain ⟨b, hb⟩ := h
    cases s with
    | p =>
        obtain ⟨j, rfl⟩ := hb
        rw [p_word_mass]
        fin_cases b <;>
          simp [explicitStoppedWordLaw, Measure.sum_apply, Pi.single_apply, p_word_injective]
    | beta =>
        rcases hb with ⟨rfl, rfl⟩ | ⟨j, rfl⟩
        · simp [explicitStoppedWordLaw, Measure.sum_apply, wordMass, betaMass]
        · simp only [wordMass, List.map_cons, List.prod_cons, bernoulli_alpha]
          rw [← wordMass, p_word_mass]
          fin_cases b <;>
            simp [explicitStoppedWordLaw, Measure.sum_apply, Pi.single_apply, p_word_injective] <;> ring
  · rw [if_neg h]
    cases s with
    | p =>
        have h0 (j : ℕ) : pWord j 0 ≠ w := fun he => h ⟨0, j, he.symm⟩
        have h1 (j : ℕ) : pWord j 1 ≠ w := fun he => h ⟨1, j, he.symm⟩
        simp [explicitStoppedWordLaw, Measure.sum_apply, h0, h1]
    | beta =>
        have hβ : [1] ≠ w := fun he => h ⟨1, Or.inl ⟨rfl, he.symm⟩⟩
        have h0 (j : ℕ) : (0 : Letter) :: pWord j 0 ≠ w :=
          fun he => h ⟨0, Or.inr ⟨j, he.symm⟩⟩
        have h1 (j : ℕ) : (0 : Letter) :: pWord j 1 ≠ w :=
          fun he => h ⟨1, Or.inr ⟨j, he.symm⟩⟩
        simp [explicitStoppedWordLaw, Measure.sum_apply, hβ, h0, h1]

/-- The independently executed first-completion word has exactly the explicit atomic law. -/
theorem actual_fourth_segment_stopped_word_law (r : unitInterval) (s : ActivePhase) :
    Measurable (stoppedReadWord s) ∧
      (rawReadLaw r).map (stoppedReadWord s) = explicitStoppedWordLaw s r := by
  classical
  refine ⟨measurable_stopped_read_word s, Measure.ext_of_singleton (fun t => ?_)⟩
  rw [Measure.map_apply (measurable_stopped_read_word s) (measurableSet_singleton t)]
  cases t with
  | none =>
      change rawReadLaw r {ω | stoppedReadWord s ω = none} = _
      rw [actual_noncompletion_mass_zero]
      cases s <;> simp [explicitStoppedWordLaw, Measure.sum_apply]
  | some w =>
      rw [explicit_finite_mass]
      have he : (stoppedReadWord s) ⁻¹' {some w} =
          if ∃ b, WordFamily s b w then prefixCylinder w else ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, stopped_word_fiber]
        split_ifs with h <;> simp [prefixCylinder, h]
      rw [he]
      split_ifs
      · exact cylinder_mass r w
      · simp

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw

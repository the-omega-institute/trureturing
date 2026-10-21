/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Measurable next-event rules admit unpadded normalization preserving every capped execution. -/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.TakeDrop
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

abbrev Spins := ℤ → Bool
abbrev SourcePoint := Bool × Spins

inductive Hidden where
  | a (spin : Bool)
  | b (spin : Bool)
  deriving DecidableEq, Fintype

/-- Both phases use the original integer read clock. -/
def visible (φ : Bool) (S : Spins) (t : ℤ) : Bool :=
  if (t - φ.toInt) % 2 = 0 then
    Bool.xor (S ((t - φ.toInt) / 2)) (S ((t - φ.toInt) / 2 + 1))
  else false

def hidden (φ : Bool) (S : Spins) (t : ℤ) : Hidden :=
  if (t - φ.toInt) % 2 = 0 then .a (S ((t - φ.toInt) / 2))
  else .b (S ((t - φ.toInt) / 2 + 1))

/-- The target spin index at endpoint zero or one, in either phase. -/
def targetIndex (j φ : Bool) : ℤ := if φ then 0 else j.toInt

def targetClass (j φ : Bool) (s : Bool) : Hidden :=
  if j = φ then .a s else .b s

theorem active_visible (φ : Bool) (S : Spins) (e : ℤ) :
    visible φ S (2 * e + φ.toInt) = Bool.xor (S e) (S (e + 1)) := by
  have hd : (2 * e + φ.toInt - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt - φ.toInt) % 2 = 0 := by omega
  simp [visible, hm, hd]

private theorem separator_visible (φ : Bool) (S : Spins) (e : ℤ) :
    visible φ S (2 * e + φ.toInt + 1) = false := by
  have hm : (2 * e + φ.toInt + 1 - φ.toInt) % 2 ≠ 0 := by omega
  simp [visible, hm]

private theorem active_hidden (φ : Bool) (S : Spins) (e : ℤ) :
    hidden φ S (2 * e + φ.toInt) = .a (S e) := by
  have hd : (2 * e + φ.toInt - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt - φ.toInt) % 2 = 0 := by omega
  simp [hidden, hm, hd]

private theorem separator_hidden (φ : Bool) (S : Spins) (e : ℤ) :
    hidden φ S (2 * e + φ.toInt + 1) = .b (S (e + 1)) := by
  have hd : (2 * e + φ.toInt + 1 - φ.toInt) / 2 = e := by omega
  have hm : (2 * e + φ.toInt + 1 - φ.toInt) % 2 ≠ 0 := by omega
  simp [hidden, hm, hd]

private theorem negative_seam (S : Spins) : hidden true S 0 = .b (S 0) := by
  simpa using separator_hidden true S (-1)

theorem actual_endpoint (j φ : Bool) (S : Spins) :
    hidden φ S j.toInt = targetClass j φ (S (targetIndex j φ)) := by
  cases j <;> cases φ
  · simpa [targetClass, targetIndex] using active_hidden false S 0
  · simpa [targetClass, targetIndex] using negative_seam S
  · simpa [targetClass, targetIndex] using separator_hidden false S 0
  · simpa [targetClass, targetIndex] using active_hidden true S 0

theorem opposite_phase_visible (φ : Bool) (S : Spins) (t : ℤ)
    (h : (t - φ.toInt) % 2 = 0) : visible (!φ) S t = false := by
  have ht : 2 * ((t - (!φ).toInt - 1) / 2) + (!φ).toInt + 1 = t := by
    cases φ <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
      Bool.toInt_true] at * <;> omega
  simpa only [ht] using separator_visible (!φ) S ((t - (!φ).toInt - 1) / 2)

theorem constant_visible (φ s : Bool) (t : ℤ) : visible φ (fun _ => s) t = false := by
  simp [visible]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A none leaf means permanent internal continuation after the reads already made. -/
inductive ReadTree where
  | leaf (output : Option Hidden)
  | read (address : ℤ) (zero one : ReadTree)
  deriving DecidableEq

abbrev Record := List (ℤ × Bool)

structure Execution where
  output : Option Hidden
  record : Record
  deriving DecidableEq

namespace Execution

def paid (v : Execution) : ℕ := v.record.length

def returned (v : Execution) : Bool := v.output.isSome

def prepend (t : ℤ) (b : Bool) (v : Execution) : Execution :=
  ⟨v.output, (t,b) :: v.record⟩

@[simp] theorem paid_prepend (t : ℤ) (b : Bool) (v : Execution) :
    (v.prepend t b).paid = v.paid + 1 := by simp [paid, prepend]


end Execution

namespace ReadTree

def height : ReadTree → ℕ
  | .leaf _ => 0
  | .read _ z o => max z.height o.height + 1

/-- Repeated and separator reads are recorded and charged separately. -/
def run : ReadTree → (ℤ → Bool) → Execution
  | .leaf a, _ => ⟨a, []⟩
  | .read t z o, x => (if x t then o.run x else z.run x).prepend t (x t)

/-- All formal reply branches, including branches inconsistent with repeated addresses. -/
def formalRuns : ReadTree → List Execution
  | .leaf a => [⟨a, []⟩]
  | .read t z o => (z.formalRuns.map (Execution.prepend t false)) ++
      (o.formalRuns.map (Execution.prepend t true))

/-- Every potential queried address, including nodes not visited in this execution. -/
def addresses : ReadTree → Finset ℤ
  | .leaf _ => ∅
  | .read t z o => insert t (z.addresses ∪ o.addresses)

/-- Every spin coordinate used by a potential read in either source phase. -/
def support : ReadTree → Finset ℤ
  | .leaf _ => ∅
  | .read t z o => {t / 2, t / 2 + 1, (t - 1) / 2, (t - 1) / 2 + 1} ∪
      (z.support ∪ o.support)


private theorem paid_le_height (T : ReadTree) (x : ℤ → Bool) : (T.run x).paid ≤ T.height := by
  induction T with
  | leaf a => exact le_rfl
  | read t z o hz ho =>
    simp only [run, height]
    split
    · simpa using Nat.add_le_add_right (ho.trans (le_max_right _ _)) 1
    · simpa using Nat.add_le_add_right (hz.trans (le_max_left _ _)) 1

theorem paid_cap (T : ReadTree) {k : ℕ} (h : T.height ≤ k) (x : ℤ → Bool) :
    (T.run x).paid ≤ k := (T.paid_le_height x).trans h

theorem record_addresses (T : ReadTree) (x : ℤ → Bool) :
    ∀ a ∈ (T.run x).record, a.1 ∈ T.addresses := by
  induction T with
  | leaf a => simp [run]
  | read t z o hz ho =>
    simp only [run, Execution.prepend, addresses]
    split <;> intro a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ho a ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hz a ha))

private theorem run_eq_of_agree (T : ReadTree) (x y : ℤ → Bool)
    (h : ∀ t ∈ T.addresses, x t = y t) : T.run x = T.run y := by
  induction T with
  | leaf a => rfl
  | read t z o hz ho =>
    have ht := h t (Finset.mem_insert_self _ _)
    have hz' : z.run x = z.run y := hz fun a ha =>
      h a (Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
    have ho' : o.run x = o.run y := ho fun a ha =>
      h a (Finset.mem_insert_of_mem (Finset.mem_union_right _ ha))
    simp only [run, ht, hz', ho']

theorem source_run_eq_of_agree (T : ReadTree) (φ : Bool) (S R : Spins)
    (h : ∀ i ∈ T.support, S i = R i) :
    T.run (visible φ S) = T.run (visible φ R) := by
  have hs : ∀ t ∈ T.addresses,
      ({t / 2, t / 2 + 1, (t - 1) / 2, (t - 1) / 2 + 1} : Finset ℤ) ⊆ T.support := by
    clear h
    induction T with
    | leaf a => simp [addresses]
    | read a z o hz ho =>
      intro t ht i hi
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Finset.mem_union_left _ hi
      · rcases Finset.mem_union.mp ht with ht | ht
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hz t ht hi))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (ho t ht hi))
  apply T.run_eq_of_agree
  intro t ht
  have he (i : ℤ) (hi : i ∈ ({t / 2, t / 2 + 1,
      (t - 1) / 2, (t - 1) / 2 + 1} : Finset ℤ)) : S i = R i := h i (hs t ht hi)
  cases φ <;> simp only [visible, Bool.toInt_false, Bool.toInt_true, sub_zero]
  · rw [he _ (by simp), he _ (by simp)]
  · rw [he _ (by simp), he _ (by simp)]

/-- A zero paid count forces an actual leaf, including for a nonreturning execution. -/
theorem leaf_of_paid_zero (T : ReadTree) (x : ℤ → Bool) (h : (T.run x).paid = 0) :
    T = .leaf (T.run x).output := by
  cases T with
  | leaf a => rfl
  | read t z o =>
    simp only [run] at h
    split at h <;> simp at h

def stopComb : List ℤ → ReadTree
  | [] => .leaf (some (.a false))
  | t :: ts => .read t (stopComb ts) (.leaf (some (.a true)))

@[simp] private theorem height_stopComb (ts : List ℤ) : (stopComb ts).height = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [stopComb, height, ih]

theorem stopComb_all_zero (ts : List ℤ) (x : ℤ → Bool)
    (h : ∀ t ∈ ts, x t = false) :
    (stopComb ts).run x = ⟨some (.a false), ts.map (fun t => (t, false))⟩ := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [stopComb, run, h t (by simp), Bool.false_eq_true, ↓reduceIte]
    rw [ih (fun a ha => h a (by simp [ha]))]
    rfl

/-- Every formal comb branch returns at its own depth, without padding early leaves. -/
theorem stopComb_formal_outcomes (ts : List ℤ) :
    ∀ v ∈ (stopComb ts).formalRuns,
      v.output = some (.a false) ∧ v.paid = ts.length ∨
      v.output = some (.a true) ∧ 1 ≤ v.paid ∧ v.paid ≤ ts.length := by
  induction ts with
  | nil =>
    intro v hv
    have hv' : v = ⟨some (.a false), []⟩ := by simpa [stopComb, formalRuns] using hv
    subst v
    exact Or.inl ⟨rfl, rfl⟩
  | cons t ts ih =>
    intro v hv
    simp only [stopComb, formalRuns, List.mem_append, List.mem_map] at hv
    rcases hv with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · rcases ih w hw with ⟨ho, hn⟩ | ⟨ho, hn, hb⟩
      · refine Or.inl ⟨ho, ?_⟩
        simp only [Execution.paid_prepend, List.length_cons]
        omega
      · refine Or.inr ⟨ho, ?_, ?_⟩
        · simp only [Execution.paid_prepend]; omega
        · simp only [Execution.paid_prepend, List.length_cons]; omega
    · have hw' : w = ⟨some (.a true), []⟩ := by simpa only [List.mem_singleton] using hw
      subst w
      exact Or.inr ⟨rfl, by simp [Execution.paid, Execution.prepend], by
        simp [Execution.paid, Execution.prepend]⟩

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory
open scoped NNReal ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- The next finite read, finite return, or permanent internal continuation. -/
inductive EventKind where
  | read (address : ℤ)
  | terminal (output : Option Hidden)
  deriving DecidableEq, Countable

instance : Nonempty EventKind := ⟨.terminal none⟩

deriving instance Countable for ReadTree

instance : MeasurableSpace Record := ⊤
instance : MeasurableSingletonClass Record := ⟨fun _ => trivial⟩
instance : MeasurableSpace Hidden := ⊤
instance : MeasurableSingletonClass Hidden := ⟨fun _ => trivial⟩
instance : MeasurableSpace EventKind := ⊤
instance : MeasurableSingletonClass EventKind := ⟨fun _ => trivial⟩
instance : MeasurableSpace ReadTree := ⊤
instance : MeasurableSingletonClass ReadTree := ⟨fun _ => trivial⟩

universe u

/-- No source, phase, hidden-state, or unacquired reply is an argument of the rule.
The waiting time is finite and nonnegative; it does not affect the paid record. -/
structure RawRule (U : Type u) [MeasurableSpace U] where
  next : U → Record → EventKind
  wait : U → Record → ℝ≥0

namespace RawRule
variable {U : Type u} [MeasurableSpace U]

/-- Ordinary measurable versions of all next events and finite waiting times. -/
structure Lawful (Q : RawRule U) : Prop where
  measurable_next : ∀ r, Measurable (fun u => Q.next u r)
  measurable_wait : ∀ r, Measurable (fun u => Q.wait u r)

/-- Completion-measurable versions on the unchanged seed probability space. -/
structure CompletionLawful (Q : RawRule U) (ν : Measure U) : Prop where
  measurable_next : ∀ r, @Measurable (NullMeasurableSpace U ν) EventKind inferInstance _
    (fun u => Q.next u r)
  measurable_wait : ∀ r, @Measurable (NullMeasurableSpace U ν) ℝ≥0 inferInstance _
    (fun u => Q.wait u r)

private theorem CompletionLawful.aemeasurable_next {Q : RawRule U} {ν : Measure U}
    (hQ : Q.CompletionLawful ν) (r : Record) : AEMeasurable (fun u => Q.next u r) ν :=
  (show NullMeasurable (fun u => Q.next u r) ν from hQ.measurable_next r).aemeasurable

private theorem CompletionLawful.aemeasurable_wait {Q : RawRule U} {ν : Measure U}
    (hQ : Q.CompletionLawful ν) (r : Record) : AEMeasurable (fun u => Q.wait u r) ν :=
  (show NullMeasurable (fun u => Q.wait u r) ν from hQ.measurable_wait r).aemeasurable

/-- The record after exactly n actual reads, absent if a terminal event preceded it. -/
def readPrefix (Q : RawRule U) (u : U) (x : ℤ → Bool) : ℕ → Option Record
  | 0 => some []
  | n + 1 => (Q.readPrefix u x n).bind fun r =>
      match Q.next u r with
      | .read t => some (r ++ [(t, x t)])
      | .terminal _ => none

/-- The uncapped count includes infinite-read nonreturn and all repeated calls. -/
def paidCount (Q : RawRule U) (u : U) (x : ℤ → Bool) : ℕ∞ :=
  ⨆ n : ℕ, if (Q.readPrefix u x n).isSome then (n : ℕ∞) else 0

/-- The cap is on every actual source and seed, including nonreturn and null paths. -/
def TotalCap (Q : RawRule U) (k : ℕ) : Prop :=
  ∀ (φ : Bool) (S : Spins) (u : U), Q.paidCount u (visible φ S) ≤ k

def Completes (Q : RawRule U) (u : U) (x : ℤ → Bool) (v : Execution) : Prop :=
  Q.readPrefix u x v.paid = some v.record ∧ Q.next u v.record = .terminal v.output

/-- Existence of a finite return, distinct from permanent internal continuation. -/
def Returns (Q : RawRule U) (u : U) (x : ℤ → Bool) (a : Hidden) : Prop :=
  ∃ n r, Q.readPrefix u x n = some r ∧ Q.next u r = .terminal (some a)

/-- Infinite reads and internal permanent continuation both have output none. -/
def output (Q : RawRule U) (u : U) (x : ℤ → Bool) : Option Hidden :=
  if h : ∃ a, Q.Returns u x a then some h.choose else none

/-- The elapsed finite waits include the wait preceding the terminal return. -/
def elapsed (Q : RawRule U) (u : U) (r : Record) : ℝ≥0 :=
  ∑ i ∈ Finset.range (r.length + 1), Q.wait u (r.take i)

/-- Every nonreturn has infinite return time, even at a finite paid count. -/
def returnTime (Q : RawRule U) (u : U) (x : ℤ → Bool) : ℝ≥0∞ :=
  if h : ∃ a, Q.Returns u x a then
    (Q.elapsed u ((h.choose_spec.choose_spec).choose) : ℝ≥0∞) else ⊤

/-- A finite sequence of finite waits returns finitely exactly when its output exists. -/
theorem finite_return_iff (Q : RawRule U) (u : U) (x : ℤ → Bool) :
    Q.returnTime u x < ⊤ ↔ (Q.output u x).isSome = true := by
  by_cases h : ∃ a, Q.Returns u x a
  · simp [returnTime, output, h]
  · simp [returnTime, output, h]

/-- Expansion truncates only a further read at exhausted fuel, without charging it. -/
def unfold (Q : RawRule U) : ℕ → U → Record → ReadTree
  | 0, u, r => match Q.next u r with
      | .read _ => .leaf none
      | .terminal a => .leaf a
  | n + 1, u, r => match Q.next u r with
      | .read t => .read t (Q.unfold n u (r ++ [(t, false)]))
          (Q.unfold n u (r ++ [(t, true)]))
      | .terminal a => .leaf a

def normalize (Q : RawRule U) (k : ℕ) (u : U) : ReadTree := Q.unfold k u []

private theorem readPrefix_length (Q : RawRule U) (u : U) (x : ℤ → Bool) (n : ℕ) (r : Record)
    (h : Q.readPrefix u x n = some r) : r.length = n := by
  induction n generalizing r with
  | zero => simpa [readPrefix] using h.symm
  | succ n ih =>
    simp only [readPrefix] at h
    cases hp : Q.readPrefix u x n with
    | none => simp [hp] at h
    | some s =>
      cases he : Q.next u s with
      | terminal a => simp [hp, he] at h
      | read t =>
        simp only [hp, Option.bind_some, he, Option.some.injEq] at h
        subst r
        simp [ih s hp]

private theorem readPrefix_bound (Q : RawRule U) (u : U) (x : ℤ → Bool) (n : ℕ) (r : Record)
    (h : Q.readPrefix u x n = some r) : (n : ℕ∞) ≤ Q.paidCount u x := by
  exact le_iSup_of_le n (by simp [h])

private theorem readPrefix_none_mono (Q : RawRule U) (u : U) (x : ℤ → Bool) {n m : ℕ}
    (h : Q.readPrefix u x n = none) (hnm : n ≤ m) : Q.readPrefix u x m = none := by
  induction m with
  | zero => have hn : n = 0 := by omega
            simpa only [hn] using h
  | succ m ih =>
    by_cases hm : n ≤ m
    · simp [readPrefix, ih hm]
    · have he : n = m + 1 := by omega
      simpa only [he] using h

private theorem terminal_readPrefix_bound (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {n m : ℕ} {r s : Record} {a : Option Hidden}
    (hr : Q.readPrefix u x n = some r) (ha : Q.next u r = .terminal a)
    (hs : Q.readPrefix u x m = some s) : m ≤ n := by
  by_contra h
  have hn : Q.readPrefix u x (n + 1) = none := by simp [readPrefix, hr, ha]
  have := Q.readPrefix_none_mono u x hn (by omega : n + 1 ≤ m)
  rw [hs] at this
  contradiction

private theorem completes_unique (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {v w : Execution} (hv : Q.Completes u x v) (hw : Q.Completes u x w) : v = w := by
  have hlen : v.paid = w.paid := Nat.le_antisymm
    (Q.terminal_readPrefix_bound u x hw.1 hw.2 hv.1)
    (Q.terminal_readPrefix_bound u x hv.1 hv.2 hw.1)
  have hr : v.record = w.record := Option.some.inj (hv.1.symm.trans (hlen ▸ hw.1))
  have ho : v.output = w.output := by
    have := hv.2.symm.trans (hr ▸ hw.2)
    exact EventKind.terminal.inj this
  cases v; cases w; simp_all

/-- The actual uncapped output and total paid count of a finite semantic completion. -/
private theorem completes_observables (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {v : Execution} (hv : Q.Completes u x v) :
    Q.output u x = v.output ∧ Q.paidCount u x = v.paid := by
  have hn : Q.paidCount u x ≤ v.paid := by
    apply iSup_le
    intro n
    cases hp : Q.readPrefix u x n with
    | none => simp [hp]
    | some r =>
      simp only [hp, Option.isSome_some, ↓reduceIte]
      exact_mod_cast Q.terminal_readPrefix_bound u x hv.1 hv.2 hp
  constructor
  · have hret (a : Hidden) : Q.Returns u x a ↔ v.output = some a := by
      constructor
      · rintro ⟨n, r, hr, ha⟩
        have hlen := Q.readPrefix_length u x n r hr
        have hw : Q.Completes u x ⟨some a, r⟩ := by
          constructor
          · simpa [Execution.paid, hlen] using hr
          · exact ha
        have := Q.completes_unique u x hv hw
        exact congrArg Execution.output this
      · intro ha
        exact ⟨v.paid, v.record, hv.1, ha ▸ hv.2⟩
    unfold output
    split
    · rename_i h
      exact (hret h.choose).mp h.choose_spec |>.symm
    · rename_i h
      cases ho : v.output with
      | none => rfl
      | some a => exact (h ⟨a, (hret a).mpr ho⟩).elim
  · exact le_antisymm hn (Q.readPrefix_bound u x _ _ hv.1)

theorem unfold_height (Q : RawRule U) (k : ℕ) (u : U) (r : Record) :
    (Q.unfold k u r).height ≤ k := by
  induction k generalizing r with
  | zero => cases h : Q.next u r <;> simp [unfold, h, ReadTree.height]
  | succ k ih =>
    cases h : Q.next u r <;> simp only [unfold, h, ReadTree.height]
    · exact Nat.succ_le_succ (max_le (ih _) (ih _))
    · omega

/-- Every actual capped path reaches its original terminal event at its original record. -/
theorem unfold_correct (Q : RawRule U) (u : U) (x : ℤ → Bool) (k n : ℕ) (r : Record)
    (hr : Q.readPrefix u x n = some r)
    (hc : ∀ m s, Q.readPrefix u x m = some s → m ≤ n + k) :
    let v := (Q.unfold k u r).run x
    Q.readPrefix u x (n + v.paid) = some (r ++ v.record) ∧
      Q.next u (r ++ v.record) = .terminal v.output := by
  induction k generalizing n r with
  | zero =>
    cases he : Q.next u r with
    | terminal a => simpa [unfold, he, ReadTree.run, Execution.paid] using And.intro hr he
    | read t =>
      have hp : Q.readPrefix u x (n + 1) = some (r ++ [(t, x t)]) := by
        simp [readPrefix, hr, he]
      have := hc _ _ hp
      omega
  | succ k ih =>
    cases he : Q.next u r with
    | terminal a => simpa [unfold, he, ReadTree.run, Execution.paid] using And.intro hr he
    | read t =>
      have hp : Q.readPrefix u x (n + 1) = some (r ++ [(t, x t)]) := by
        simp [readPrefix, hr, he]
      have hh := ih (n + 1) (r ++ [(t, x t)]) hp (by
        intro m s hs; have := hc m s hs; omega)
      cases hx : x t <;>
        simpa [unfold, he, ReadTree.run, hx, Execution.prepend, Execution.paid,
          List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- Every earlier acquired record is a literal prefix of every later one. -/
private theorem readPrefix_extension (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {n m : ℕ} {r s : Record} (hr : Q.readPrefix u x n = some r)
    (hs : Q.readPrefix u x m = some s) (hnm : n ≤ m) : ∃ tail, s = r ++ tail := by
  induction m generalizing s with
  | zero =>
    have hn : n = 0 := by omega
    rw [hn, readPrefix] at hr
    simp only [readPrefix, Option.some.injEq] at hs
    simp only [Option.some.injEq] at hr
    subst r; subst s; exact ⟨[], rfl⟩
  | succ m ih =>
    by_cases hnm' : n ≤ m
    · simp only [readPrefix] at hs
      cases hp : Q.readPrefix u x m with
      | none => simp [hp] at hs
      | some q =>
        cases he : Q.next u q with
        | terminal a => simp [hp, he] at hs
        | read t =>
          simp only [hp, Option.bind_some, he, Option.some.injEq] at hs
          obtain ⟨tail, htail⟩ := ih hp hnm'
          exact ⟨tail ++ [(t, x t)], by rw [← List.append_assoc, ← htail]; exact hs.symm⟩
    · have hn : n = m + 1 := by omega
      have he : r = s := Option.some.inj (hr.symm.trans (hn ▸ hs))
      exact ⟨[], by simp [he]⟩

/-- A finite terminal record contains every read actually made by the raw rule. -/
theorem completes_record_subset (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {v : Execution} (hv : Q.Completes u x v) {n : ℕ} {r : Record}
    (hr : Q.readPrefix u x n = some r) : ∀ a ∈ r, a ∈ v.record := by
  have hn := Q.terminal_readPrefix_bound u x hv.1 hv.2 hr
  obtain ⟨tail, ht⟩ := Q.readPrefix_extension u x hr hv.1 hn
  intro a ha
  rw [ht]
  exact List.mem_append_left _ ha

/-- A cap on one execution suffices for exact normalization on that execution. -/
private theorem normalization_execution (Q : RawRule U) (k : ℕ) (u : U) (x : ℤ → Bool)
    (hc : Q.paidCount u x ≤ k) :
    let v := (Q.normalize k u).run x
    Q.Completes u x v ∧ Q.output u x = v.output ∧ Q.paidCount u x = v.paid := by
  have h := Q.unfold_correct u x k 0 [] rfl (by
    intro m r hr
    have hm := (Q.readPrefix_bound u x m r hr).trans hc
    simpa using (show m ≤ k by exact_mod_cast hm))
  have hv : Q.Completes u x ((Q.normalize k u).run x) := by
    simpa [normalize, Completes] using h
  exact ⟨hv, Q.completes_observables u x hv⟩

/-- Pointwise normalization on every original source/seed path, including nonreturns. -/
theorem normalization_pointwise (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k)
    (φ : Bool) (S : Spins) (u : U) :
    let v := (Q.normalize k u).run (visible φ S)
    Q.Completes u (visible φ S) v ∧
      Q.output u (visible φ S) = v.output ∧
      Q.paidCount u (visible φ S) = v.paid :=
  Q.normalization_execution k u (visible φ S) (hc φ S u)

theorem normalization_return_indicator (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k)
    (φ : Bool) (S : Spins) (u : U) :
    decide (Q.returnTime u (visible φ S) < ⊤) =
      ((Q.normalize k u).run (visible φ S)).returned := by
  have ho := (Q.normalization_pointwise k hc φ S u).2.1
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq, Execution.returned, ho] using
    Q.finite_return_iff u (visible φ S)

private theorem measurable_unfold (Q : RawRule U) (hQ : Q.Lawful) (k : ℕ) :
    ∀ r : Record, Measurable (fun u => Q.unfold k u r) := by
  induction k with
  | zero =>
    intro r
    exact (measurable_of_countable (fun e : EventKind => match e with
      | .read _ => ReadTree.leaf none
      | .terminal a => ReadTree.leaf a)).comp (hQ.measurable_next r)
  | succ k ih =>
    intro r
    have hchildren : ∀ t : ℤ, Measurable (fun u =>
        ReadTree.read t (Q.unfold k u (r ++ [(t, false)]))
          (Q.unfold k u (r ++ [(t, true)]))) := by
      intro t
      exact (measurable_of_countable (fun p : ReadTree × ReadTree =>
        ReadTree.read t p.1 p.2)).comp ((ih _).prodMk (ih _))
    have h : Measurable (fun p : U × EventKind => match p.2 with
        | .read t => ReadTree.read t (Q.unfold k p.1 (r ++ [(t, false)]))
            (Q.unfold k p.1 (r ++ [(t, true)]))
        | .terminal a => ReadTree.leaf a) := by
      apply measurable_from_prod_countable_left
      intro e
      cases e with
      | read t => exact hchildren t
      | terminal a => exact measurable_const
    exact h.comp (measurable_id.prodMk (hQ.measurable_next r))

theorem measurable_normalize (Q : RawRule U) (hQ : Q.Lawful) (k : ℕ) : Measurable (Q.normalize k) :=
  Q.measurable_unfold hQ k []

/-- A single ordinary version is chosen simultaneously over every countable record. -/
def ordinaryVersion (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) : RawRule U where
  next u r := (hQ.aemeasurable_next r).mk (fun u => Q.next u r) u
  wait u r := (hQ.aemeasurable_wait r).mk (fun u => Q.wait u r) u

private theorem ordinaryVersion_lawful (Q : RawRule U) (ν : Measure U) (hQ : Q.CompletionLawful ν) :
    (Q.ordinaryVersion ν hQ).Lawful :=
  ⟨fun r => (hQ.aemeasurable_next r).measurable_mk,
    fun r => (hQ.aemeasurable_wait r).measurable_mk⟩

private theorem ordinaryVersion_common_set (Q : RawRule U) (ν : Measure U)
    (hQ : Q.CompletionLawful ν) :
    ∀ᵐ u ∂ν, ∀ r, Q.next u r = (Q.ordinaryVersion ν hQ).next u r ∧
      Q.wait u r = (Q.ordinaryVersion ν hQ).wait u r := by
  apply ae_all_iff.2
  intro r
  exact (hQ.aemeasurable_next r).ae_eq_mk.and (hQ.aemeasurable_wait r).ae_eq_mk

private theorem unfold_congr (Q R : RawRule U) (u : U)
    (h : ∀ r, Q.next u r = R.next u r) (k : ℕ) (r : Record) :
    Q.unfold k u r = R.unfold k u r := by
  induction k generalizing r with
  | zero => simp only [unfold, h]
  | succ k ih =>
    simp only [unfold, h]
    cases R.next u r with
    | terminal a => rfl
    | read t => simp only [ih]

/-- Version transport is almost everywhere; pointwise normalization remains separate. -/
theorem completion_normalization_version (Q : RawRule U) (ν : Measure U)
    (hQ : Q.CompletionLawful ν) (k : ℕ) :
    ∃ T₀ : U → {T : ReadTree // T.height ≤ k}, Measurable T₀ ∧
      ∀ᵐ u ∂ν, Q.normalize k u = (T₀ u).val := by
  let R := Q.ordinaryVersion ν hQ
  refine ⟨fun u => ⟨R.normalize k u, R.unfold_height k u []⟩, ?_, ?_⟩
  · exact (R.measurable_normalize (Q.ordinaryVersion_lawful ν hQ) k).subtype_mk
  · filter_upwards [Q.ordinaryVersion_common_set ν hQ] with u hu
    exact Q.unfold_congr R u (fun r => (hu r).1) k []

/-- A common ordinary version preserves every actual execution at almost every seed. -/
theorem completion_normalization_bridge (Q : RawRule U) (ν : Measure U)
    (hQ : Q.CompletionLawful ν) (k : ℕ) (hc : Q.TotalCap k) :
    ∃ T₀ : U → {T : ReadTree // T.height ≤ k}, Measurable T₀ ∧
      (∀ᵐ u ∂ν, Q.normalize k u = (T₀ u).val) ∧
      ∀ᵐ u ∂ν, ∀ (φ : Bool) (S : Spins),
        let v := (T₀ u).val.run (visible φ S)
        Q.Completes u (visible φ S) v ∧ Q.output u (visible φ S) = v.output ∧
          Q.paidCount u (visible φ S) = v.paid := by
  obtain ⟨T₀, hm, he⟩ := Q.completion_normalization_version ν hQ k
  refine ⟨T₀, hm, he, ?_⟩
  filter_upwards [he] with u hu
  intro φ S
  simpa only [hu] using Q.normalization_pointwise k hc φ S u

end RawRule

namespace ReadTree

/-- Follow the ordered acquired record, rejecting inconsistent addresses. -/
def follow : ReadTree → Record → Option ReadTree
  | T, [] => some T
  | .leaf _, _ :: _ => none
  | .read t z o, (a,b) :: r => if a = t then (if b then o else z).follow r else none

def eventAfter (T : ReadTree) (r : Record) : EventKind :=
  match T.follow r with
  | none => .terminal none
  | some (.leaf a) => .terminal a
  | some (.read t _ _) => .read t

private theorem follow_append (T : ReadTree) (r s : Record) :
    T.follow (r ++ s) = (T.follow r).bind (fun V => V.follow s) := by
  induction r generalizing T with
  | nil => rfl
  | cons a r ih =>
    cases T with
    | leaf b => rfl
    | read t z o =>
      simp only [List.cons_append, follow]
      split_ifs with h hb
      · exact ih o
      · exact ih z
      · rfl

private theorem follow_height (T : ReadTree) (r : Record) (V : ReadTree)
    (h : T.follow r = some V) : r.length + V.height ≤ T.height := by
  induction r generalizing T with
  | nil => simp only [follow, Option.some.injEq] at h; subst V; simp
  | cons a r ih =>
    cases T with
    | leaf b => simp [follow] at h
    | read t z o =>
      simp only [follow] at h
      split_ifs at h with ha hb
      · have hh := ih o h
        simp only [List.length_cons, height]
        omega
      · have hh := ih z h
        simp only [List.length_cons, height]
        omega

end ReadTree

namespace RawRule
variable {U : Type u} [MeasurableSpace U]

/-- Realization uses exactly the same seed and no new randomness. -/
def realize (T : U → ReadTree) : RawRule U where
  next u r := (T u).eventAfter r
  wait _ _ := 0

theorem realize_lawful (T : U → ReadTree) (hT : Measurable T) : (realize T).Lawful := by
  constructor
  · intro r
    exact (measurable_of_countable (fun V : ReadTree => V.eventAfter r)).comp hT
  · intro _; exact measurable_const

private theorem realize_prefix (T : U → ReadTree) (u : U) (x : ℤ → Bool) (n : ℕ)
    (r : Record) (hr : (realize T).readPrefix u x n = some r) :
    ∃ V, (T u).follow r = some V := by
  induction n generalizing r with
  | zero => simp only [readPrefix, Option.some.injEq] at hr; subst r; exact ⟨T u, rfl⟩
  | succ n ih =>
    simp only [readPrefix] at hr
    cases hp : (realize T).readPrefix u x n with
    | none => simp [hp] at hr
    | some s =>
      rw [hp, Option.bind_some] at hr
      change (match (T u).eventAfter s with
        | .read t => some (s ++ [(t, x t)])
        | .terminal _ => none) = some r at hr
      obtain ⟨V, hV⟩ := ih s hp
      cases V with
      | leaf a => simp [ReadTree.eventAfter, hV] at hr
      | read t z o =>
        simp only [ReadTree.eventAfter, hV, Option.some.injEq] at hr
        subst r
        rw [ReadTree.follow_append, hV]
        cases hx : x t <;> simp [ReadTree.follow, hx]

theorem realize_cap (T : U → ReadTree) (k : ℕ) (hT : ∀ u, (T u).height ≤ k) :
    (realize T).TotalCap k := by
  intro φ S u
  apply iSup_le
  intro n
  cases hp : (realize T).readPrefix u (visible φ S) n with
  | none => simp [hp]
  | some r =>
    simp only [hp, Option.isSome_some, ↓reduceIte]
    obtain ⟨V, hV⟩ := realize_prefix T u (visible φ S) n r hp
    have hh := (T u).follow_height r V hV
    have hlen := (realize T).readPrefix_length u (visible φ S) n r hp
    have hn : n ≤ k := by have := hT u; omega
    exact_mod_cast hn

private theorem unfold_realize (T : U → ReadTree) (u : U) (n : ℕ) (r : Record) (V : ReadTree)
    (hr : (T u).follow r = some V) (hV : V.height ≤ n) :
    (realize T).unfold n u r = V := by
  induction n generalizing r V with
  | zero =>
    cases V with
    | leaf a => simp [unfold, realize, ReadTree.eventAfter, hr]
    | read t z o => simp [ReadTree.height] at hV
  | succ n ih =>
    cases V with
    | leaf a => simp [unfold, realize, ReadTree.eventAfter, hr]
    | read t z o =>
      have hz : (T u).follow (r ++ [(t, false)]) = some z := by
        simp [ReadTree.follow_append, hr, ReadTree.follow]
      have ho : (T u).follow (r ++ [(t, true)]) = some o := by
        simp [ReadTree.follow_append, hr, ReadTree.follow]
      have hz' : z.height ≤ n := by simp only [ReadTree.height] at hV; omega
      have ho' : o.height ≤ n := by simp only [ReadTree.height] at hV; omega
      simp only [unfold, realize, ReadTree.eventAfter, hr]
      change ReadTree.read t ((realize T).unfold n u (r ++ [(t, false)]))
        ((realize T).unfold n u (r ++ [(t, true)])) = ReadTree.read t z o
      rw [ih _ _ hz hz', ih _ _ ho ho']

theorem normalize_realize (T : U → ReadTree) (k : ℕ) (u : U)
    (hT : (T u).height ≤ k) : (realize T).normalize k u = T u :=
  unfold_realize T u k [] (T u) rfl hT

end RawRule
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

end


noncomputable section
open Classical MeasureTheory
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open scoped NNReal
universe u v w

/-- Measurability in the available observation field completed by ambient null sets. -/
def CompletionAvailable {Ω : Type v} {U : Type u} {Y : Type w}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace Y]
    (μ : Measure Ω) (seed : Ω → U) (f : Ω → Y) : Prop :=
  ∀ E : Set Y, MeasurableSet E → ∃ B : Set U, MeasurableSet B ∧
    f ⁻¹' E =ᵐ[μ] seed ⁻¹' B

/-- Countable event fibers admit one ordinary version without assumptions on the seed space. -/
private theorem completion_available_countable_version {Ω : Type v} {U : Type u} {Y : Type w}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace Y]
    [Countable Y] [Nonempty Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) (seed : Ω → U) (f : Ω → Y)
    (hf : CompletionAvailable μ seed f) :
    ∃ g : U → Y, Measurable g ∧ f =ᵐ[μ] (fun ω => g (seed ω)) := by
  letI : Encodable Y := Encodable.ofCountable Y
  letI : Inhabited Y := ⟨Classical.choice inferInstance⟩
  let e : ℕ → Y := fun n => (Encodable.decode n).getD default
  have he : Function.Surjective e := fun a => ⟨Encodable.encode a, by simp [e]⟩
  choose B hB hEq using fun a : Y => hf {a} (measurableSet_singleton a)
  let p : U → ℕ → Prop := fun u n => u ∈ B (e n) ∨ (∀ a, u ∉ B a) ∧ n = 0
  have hp : ∀ u, ∃ n, p u n := by
    intro u
    by_cases h : ∃ a, u ∈ B a
    · obtain ⟨a, ha⟩ := h
      obtain ⟨n, rfl⟩ := he a
      exact ⟨n, Or.inl ha⟩
    · exact ⟨0, Or.inr ⟨by simpa only [not_exists] using h, rfl⟩⟩
  have hm : ∀ n, MeasurableSet {u | p u n} := by
    intro n
    by_cases hn : n = 0
    · have hs : MeasurableSet {u | ∀ a, u ∉ B a} := by
        have ht : {u | ∀ a, u ∉ B a} = ⋂ a, (B a)ᶜ := by ext u; simp
        rw [ht]
        exact MeasurableSet.iInter (fun a => (hB a).compl)
      have ht : {u | p u n} = B (e n) ∪ {u | ∀ a, u ∉ B a} := by
        ext u; simp only [p, hn, and_true, Set.mem_union, Set.mem_setOf_eq]
      rw [ht]
      exact (hB (e n)).union hs
    · simpa only [p, hn, and_false, or_false, Set.setOf_mem_eq] using hB (e n)
  refine ⟨fun u => e (Nat.find (hp u)),
    (measurable_of_countable e).comp (measurable_find hp hm), ?_⟩
  have hAll : ∀ᵐ ω ∂μ, ∀ a : Y, f ω = a ↔ seed ω ∈ B a := by
    apply ae_all_iff.2
    intro a
    filter_upwards [hEq a] with ω hω
    exact Iff.of_eq hω
  filter_upwards [hAll] with ω hω
  rcases Nat.find_spec (hp (seed ω)) with h | h
  · exact (hω _).mpr h
  · exact (h.1 (f ω) ((hω _).mp rfl)).elim

/-- Ambient completion versions have no source information beyond null modifications
of the seed-and-record observation field. -/
structure CompletedRule (U : Type u) [MeasurableSpace U] where
  next : SourcePoint × U → Record → EventKind
  wait : SourcePoint × U → Record → ℝ≥0

namespace CompletedRule
variable {U : Type u} [MeasurableSpace U]

def fromRaw (R : RawRule U) : CompletedRule U where
  next p r := R.next p.2 r
  wait p r := R.wait p.2 r

structure Lawful (Q : CompletedRule U) (μ : Measure (SourcePoint × U)) : Prop where
  next_available : ∀ r, CompletionAvailable μ Prod.snd (fun p => Q.next p r)
  wait_available : ∀ r, CompletionAvailable μ Prod.snd (fun p => Q.wait p r)

theorem fromRaw_lawful (R : RawRule U) (hR : R.Lawful)
    (μ : Measure (SourcePoint × U)) : (fromRaw R).Lawful μ := by
  constructor
  · intro r E hE
    exact ⟨(fun u => R.next u r) ⁻¹' E, hR.measurable_next r hE,
      Filter.EventuallyEq.rfl⟩
  · intro r E hE
    exact ⟨(fun u => R.wait u r) ⁻¹' E, hR.measurable_wait r hE,
      Filter.EventuallyEq.rfl⟩

/-- Seed-completed rules embed into the ambient observation completion without new randomness. -/
theorem fromRaw_completion_lawful (R : RawRule U) (ν : Measure U)
    (hR : R.CompletionLawful ν) (μ : Measure (SourcePoint × U))
    (hp : QuasiMeasurePreserving Prod.snd μ ν) : (fromRaw R).Lawful μ := by
  let R₀ := R.ordinaryVersion ν hR
  have h₀ := fromRaw_lawful R₀ (R.ordinaryVersion_lawful ν hR) μ
  have he := hp.ae (R.ordinaryVersion_common_set ν hR)
  constructor
  · intro r E hE
    obtain ⟨B, hB, hb⟩ := h₀.next_available r E hE
    refine ⟨B, hB, ?_⟩
    filter_upwards [he, hb] with p hpr hpb
    exact (congrArg (fun e => e ∈ E) (hpr r).1).trans hpb
  · intro r E hE
    obtain ⟨B, hB, hb⟩ := h₀.wait_available r E hE
    refine ⟨B, hB, ?_⟩
    filter_upwards [he, hb] with p hpr hpb
    exact (congrArg (fun e => e ∈ E) (hpr r).2).trans hpb

def atSource (Q : CompletedRule U) (s : SourcePoint) : RawRule U where
  next u r := Q.next (s,u) r
  wait u r := Q.wait (s,u) r

def TotalCap (Q : CompletedRule U) (k : ℕ) : Prop :=
  ∀ (s : SourcePoint) (u : U), (Q.atSource s).paidCount u (visible s.1 s.2) ≤ k

def normalize (Q : CompletedRule U) (k : ℕ) (p : SourcePoint × U) : ReadTree :=
  (Q.atSource p.1).normalize k p.2

/-- Finite waits can be replaced by zero; all event kinds share one ambient full-measure set. -/
private theorem ordinary_version (Q : CompletedRule U) (μ : Measure (SourcePoint × U))
    (hQ : Q.Lawful μ) :
    ∃ R : RawRule U, R.Lawful ∧ ∀ᵐ p ∂μ, ∀ r, Q.next p r = R.next p.2 r := by
  have h (r : Record) := completion_available_countable_version μ Prod.snd
    (fun p => Q.next p r) (hQ.next_available r)
  choose g hg he using h
  refine ⟨⟨fun u r => g r u, fun _ _ => 0⟩,
    ⟨hg, fun _ => measurable_const⟩, ?_⟩
  exact ae_all_iff.2 he

/-- Ambient versions give an a.e. tree identity, separately from the all-path cap. -/
theorem normalization_version (Q : CompletedRule U) (μ : Measure (SourcePoint × U))
    (hQ : Q.Lawful μ) (k : ℕ) :
    ∃ T : U → {t : ReadTree // t.height ≤ k}, Measurable T ∧
      Q.normalize k =ᵐ[μ] (fun p => (T p.2).val) := by
  obtain ⟨R, hR, he⟩ := Q.ordinary_version μ hQ
  refine ⟨fun u => ⟨R.normalize k u, R.unfold_height k u []⟩,
    (R.measurable_normalize hR k).subtype_mk, ?_⟩
  filter_upwards [he] with p hp
  exact (Q.atSource p.1).unfold_congr R p.2 hp k []

/-- Actual records and nonreturn counts are preserved on every capped ambient execution. -/
theorem completed_normalization_execution (Q : CompletedRule U) (k : ℕ) (hc : Q.TotalCap k)
    (p : SourcePoint × U) :
    let v := (Q.normalize k p).run (visible p.1.1 p.1.2)
    (Q.atSource p.1).Completes p.2 (visible p.1.1 p.1.2) v ∧
      (Q.atSource p.1).output p.2 (visible p.1.1 p.1.2) = v.output ∧
      (Q.atSource p.1).paidCount p.2 (visible p.1.1 p.1.2) = v.paid :=
  (Q.atSource p.1).normalization_execution k p.2 (visible p.1.1 p.1.2) (hc p.1 p.2)

end CompletedRule
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
end

/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Measurable next-event rules admit unpadded normalization preserving every capped execution. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.ReadTree
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory
open scoped NNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- The next finite read, finite return, or permanent internal continuation. -/
inductive EventKind where
  | read (address : ℤ)
  | terminal (output : Option Hidden)
  deriving DecidableEq, Countable

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
  measurable_next : ∀ r, Measurable (fun u => next u r)
  measurable_wait : ∀ r, Measurable (fun u => wait u r)

namespace RawRule
variable {U : Type u} [MeasurableSpace U]

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

theorem readPrefix_length (Q : RawRule U) (u : U) (x : ℤ → Bool) (n : ℕ) (r : Record)
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

theorem readPrefix_bound (Q : RawRule U) (u : U) (x : ℤ → Bool) (n : ℕ) (r : Record)
    (h : Q.readPrefix u x n = some r) : (n : ℕ∞) ≤ Q.paidCount u x := by
  exact le_iSup_of_le n (by simp [h])

theorem readPrefix_none_mono (Q : RawRule U) (u : U) (x : ℤ → Bool) {n m : ℕ}
    (h : Q.readPrefix u x n = none) (hnm : n ≤ m) : Q.readPrefix u x m = none := by
  induction m with
  | zero => have hn : n = 0 := by omega
            simpa only [hn] using h
  | succ m ih =>
    by_cases hm : n ≤ m
    · simp [readPrefix, ih hm]
    · have he : n = m + 1 := by omega
      simpa only [he] using h

theorem terminal_readPrefix_bound (Q : RawRule U) (u : U) (x : ℤ → Bool)
    {n m : ℕ} {r s : Record} {a : Option Hidden}
    (hr : Q.readPrefix u x n = some r) (ha : Q.next u r = .terminal a)
    (hs : Q.readPrefix u x m = some s) : m ≤ n := by
  by_contra h
  have hn : Q.readPrefix u x (n + 1) = none := by simp [readPrefix, hr, ha]
  have := Q.readPrefix_none_mono u x hn (by omega : n + 1 ≤ m)
  rw [hs] at this
  contradiction

theorem completes_unique (Q : RawRule U) (u : U) (x : ℤ → Bool)
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
theorem completes_observables (Q : RawRule U) (u : U) (x : ℤ → Bool)
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

/-- Pointwise normalization on every original source/seed path, including nonreturns. -/
theorem normalization_pointwise (Q : RawRule U) (k : ℕ) (hc : Q.TotalCap k)
    (φ : Bool) (S : Spins) (u : U) :
    let v := (Q.normalize k u).run (visible φ S)
    Q.Completes u (visible φ S) v ∧
      Q.output u (visible φ S) = v.output ∧
      Q.paidCount u (visible φ S) = v.paid := by
  have h := Q.unfold_correct u (visible φ S) k 0 [] rfl (by
    intro m r hr
    have hm := (Q.readPrefix_bound u (visible φ S) m r hr).trans (hc φ S u)
    simpa using (show m ≤ k by exact_mod_cast hm))
  have hv : Q.Completes u (visible φ S) ((Q.normalize k u).run (visible φ S)) := by
    simpa [normalize, Completes] using h
  exact ⟨hv, Q.completes_observables u (visible φ S) hv⟩

/-- Countability permits evaluation at a measurable, varying acquired record. -/
theorem measurable_next_record (Q : RawRule U) {r : U → Record} (hr : Measurable r) :
    Measurable (fun u => Q.next u (r u)) :=
  (measurable_from_prod_countable_left (f := fun p : U × Record => Q.next p.1 p.2)
    Q.measurable_next).comp (measurable_id.prodMk hr)

theorem measurable_unfold (Q : RawRule U) (k : ℕ) :
    ∀ r : Record, Measurable (fun u => Q.unfold k u r) := by
  induction k with
  | zero =>
    intro r
    exact (measurable_of_countable (fun e : EventKind => match e with
      | .read _ => ReadTree.leaf none
      | .terminal a => ReadTree.leaf a)).comp (Q.measurable_next r)
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
    exact h.comp (measurable_id.prodMk (Q.measurable_next r))

theorem measurable_normalize (Q : RawRule U) (k : ℕ) : Measurable (Q.normalize k) :=
  Q.measurable_unfold k []

end RawRule
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

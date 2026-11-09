/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip.finite_certificate
   digest: Barker's generating function for the literal eight-colour two-column strip. -/

/-
admission_basis: open-problem-resolution (#28399; Proved)
escape_witness: none; every declaration is bind-only. The all-height reduction v_eq_w
instantiates Function.Semiconj.iterate_right at the boundary-class map after the
finite one-step premises are normalized.
Direct frozen dependencies: none.
Closed, unfrozen dependency: TransferMatrix.scalarRelationShift.
The six-colour scanner and width transfer fix Fin 6 and two flags; they cannot
instantiate Fin 8 with three flags. The eight-colour scanner is public and
consumed by the literal row-major normalization and continuation transfer.
The pair map uses Fin.ofNat and Nat.min, retaining the literal colour convention.
Seen: proof_shape=bind-only; consumers=allowed
allowed: proof_shape=bind-only; consumers=good
instDecidableAllowed: proof_shape=bind-only; consumers=widthInstDecidableGood
advance: proof_shape=bind-only; consumers=good
good: proof_shape=bind-only; consumers=good_iff
finish: proof_shape=bind-only; consumers=normal_cons
finish_fst: proof_shape=bind-only; consumers=normal_cons
finish_snd: proof_shape=bind-only; consumers=normal_cons
finish_third: proof_shape=bind-only; consumers=normal_cons
good_iff: proof_shape=bind-only; consumers=normal_cons
beta: proof_shape=bind-only; consumers=pairs
colour_bond_iff: proof_shape=bind-only; consumers=bonds_iff
WidthRow: proof_shape=bind-only; consumers=widthNormal
prior: proof_shape=bind-only; consumers=widthNormal
instDecidablePrior: proof_shape=bind-only; consumers=widthInstDecidableNormal
widthNormal: proof_shape=bind-only; consumers=Legal
prior_zero: proof_shape=bind-only; consumers=normal_cons
prior_succ: proof_shape=bind-only; consumers=normal_cons
normal_cons: proof_shape=bind-only; consumers=tail_iff
widthLegal: proof_shape=bind-only; consumers=width_counting_bridge
widthInstDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
widthInstDecidableGood: proof_shape=bind-only; consumers=widthStep
widthInstDecidableLegal: proof_shape=bind-only; consumers=width_counting_bridge
TailGood: proof_shape=bind-only; consumers=tail_iff
instDecidableTailGood: proof_shape=bind-only; consumers=count
tail_iff: proof_shape=bind-only; consumers=width_counting_bridge
widthStep: proof_shape=bind-only; consumers=widthV
widthV: proof_shape=bind-only; consumers=v2
count: proof_shape=bind-only; consumers=count_eq_v
count_eq_v: proof_shape=bind-only; consumers=width_counting_bridge
widthTotal: proof_shape=bind-only; consumers=total2
width_counting_bridge: proof_shape=bind-only; consumers=counting_bridge
Row: proof_shape=bind-only; consumers=rowLegal
rowLegal: proof_shape=bind-only; consumers=Legal
bonds: proof_shape=bind-only; consumers=Legal
instDecidableRowLegal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableBonds: proof_shape=bind-only; consumers=instDecidableLegal
Legal: proof_shape=bind-only; consumers=a
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=result
pairs: proof_shape=bind-only; consumers=v2
compatible: proof_shape=bind-only; consumers=v2
instDecidableCompatible: proof_shape=bind-only; consumers=v2
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v2: proof_shape=bind-only; consumers=v_eq_w
total2: proof_shape=bind-only; consumers=a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next
instDecidableValid: proof_shape=bind-only; consumers=row_counts
seenClass: proof_shape=bind-only; consumers=classCount
T: proof_shape=bind-only; consumers=finite_certificate
classCount: proof_shape=bind-only; consumers=finite_certificate
firstCount: proof_shape=bind-only; consumers=finite_certificate
valid_next: proof_shape=bind-only; consumers=v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_counts: proof_shape=bind-only; consumers=finite_certificate
vector_relation: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=result
w: proof_shape=bind-only; consumers=a_eq_w
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.RingTheory.PowerSeries.Basic

/-! Eight-colour exclusion and a row-major scanner shared by strip widths. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip

abbrev Seen := Bool × Bool × Bool

def allowed (s : Seen) (c : Fin 8) : Prop :=
  ((c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6) → s.1 = true) ∧
    ((c = 3 ∨ c = 4 ∨ c = 5) → s.2.1 = true) ∧ (c = 4 → s.2.2 = true)

instance instDecidableAllowed (s : Seen) (c : Fin 8) : Decidable (allowed s c) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _) ∧ (_ → _)))

def advance (s : Seen) (c : Fin 8) : Seen :=
  (s.1 || decide (c = 1), s.2.1 || decide (c = 2), s.2.2 || decide (c = 3))

def good : {n : ℕ} → Seen → (Fin n → Fin 8) → Prop
  | 0, _, _ => True
  | _n + 1, s, f => allowed s (f 0) ∧ good (advance s (f 0)) (Fin.tail f)

def finish : {n : ℕ} → Seen → (Fin n → Fin 8) → Seen
  | 0, s, _ => s
  | _n + 1, s, f => finish (advance s (f 0)) (Fin.tail f)

theorem finish_fst {n : ℕ} (s : Seen) (f : Fin n → Fin 8) :
    (finish s f).1 = true ↔ s.1 = true ∨ ∃ i, f i = 1 := by
  induction n generalizing s with
  | zero => simp [finish]
  | succ n ih =>
    rw [finish, ih]
    simp [advance, Fin.exists_fin_succ, Fin.tail, or_assoc]

theorem finish_snd {n : ℕ} (s : Seen) (f : Fin n → Fin 8) :
    (finish s f).2.1 = true ↔ s.2.1 = true ∨ ∃ i, f i = 2 := by
  induction n generalizing s with
  | zero => simp [finish]
  | succ n ih =>
    rw [finish, ih]
    simp [advance, Fin.exists_fin_succ, Fin.tail, or_assoc]

theorem finish_third {n : ℕ} (s : Seen) (f : Fin n → Fin 8) :
    (finish s f).2.2 = true ↔ s.2.2 = true ∨ ∃ i, f i = 3 := by
  induction n generalizing s with
  | zero => simp [finish]
  | succ n ih =>
    rw [finish, ih]
    simp [advance, Fin.exists_fin_succ, Fin.tail, or_assoc]

theorem good_iff {n : ℕ} (s : Seen) (f : Fin n → Fin 8) :
    good s f ↔ ∀ i,
      ((f i = 2 ∨ f i = 3 ∨ f i = 4 ∨ f i = 5 ∨ f i = 6) →
        s.1 = true ∨ ∃ j, j < i ∧ f j = 1) ∧
      ((f i = 3 ∨ f i = 4 ∨ f i = 5) →
        s.2.1 = true ∨ ∃ j, j < i ∧ f j = 2) ∧
      (f i = 4 → s.2.2 = true ∨ ∃ j, j < i ∧ f j = 3) := by
  induction n generalizing s with
  | zero => simp [good]
  | succ n ih =>
    simp only [good, ih, Fin.forall_fin_succ]
    have hp : ∀ i : Fin n, (0 : Fin (n + 1)) < i.succ := fun i => Nat.zero_lt_succ _
    simp [Fin.tail, Fin.exists_fin_succ, advance, allowed, or_assoc, hp]

/-- The four complementary pairs are {0,7}, {1,6}, {2,5}, {3,4}. -/
def beta (c : Fin 8) : Fin 4 :=
  Fin.ofNat 4 (Nat.min c.val (7 - c.val))

theorem colour_bond_iff (x y : Fin 8) :
    (x ≠ y ∧ x.val + y.val ≠ 7) ↔ beta x ≠ beta y := by
  revert x y
  decide +kernel

section

variable {k : ℕ} [NeZero k] {B : Type}
abbrev WidthRow (k : ℕ) := Fin k → Fin 8

def prior {n : ℕ} (f : Fin n → WidthRow k)
    (i : Fin n) (j : Fin k) (d : Fin 8) : Prop :=
  ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ f r k = d

instance instDecidablePrior {n : ℕ} (f : Fin n → WidthRow k)
    (i : Fin n) (j : Fin k) (d : Fin 8) :
    Decidable (prior f i j d) := inferInstanceAs (Decidable (∃ _ _, _ ∧ _))

def widthNormal {n : ℕ} (s : Seen) (f : Fin n → WidthRow k) : Prop :=
  ∀ i j, ((f i j = 2 ∨ f i j = 3 ∨ f i j = 4 ∨ f i j = 5 ∨ f i j = 6) →
    s.1 = true ∨ prior f i j 1) ∧
    ((f i j = 3 ∨ f i j = 4 ∨ f i j = 5) → s.2.1 = true ∨ prior f i j 2) ∧
    (f i j = 4 → s.2.2 = true ∨ prior f i j 3)

theorem prior_zero {n : ℕ} (c : WidthRow k) (f : Fin n → WidthRow k)
    (j : Fin k) (d : Fin 8) :
    prior (Fin.cons c f) 0 j d ↔ ∃ k, k < j ∧ c k = d := by
  simp [prior, Fin.exists_fin_succ]

omit [NeZero k] in
theorem prior_succ {n : ℕ} (c : WidthRow k) (f : Fin n → WidthRow k)
    (i : Fin n) (j : Fin k) (d : Fin 8) :
    prior (Fin.cons c f) i.succ j d ↔ (∃ k, c k = d) ∨ prior f i j d := by
  simp [prior, Fin.exists_fin_succ]

theorem normal_cons {n : ℕ} (s : Seen) (c : WidthRow k) (f : Fin n → WidthRow k) :
    widthNormal s (Fin.cons c f) ↔ good s c ∧ widthNormal (finish s c) f := by
  simp only [widthNormal, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    prior_zero, prior_succ, good_iff, finish_fst, finish_snd, finish_third, or_assoc]

def widthLegal (R : WidthRow k → Prop) (E : WidthRow k → WidthRow k → Prop)
    {n : ℕ} (A : Fin n × Fin k → Fin 8) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, R (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), E (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    widthNormal (false, false, false) (fun i j => A (i, j))

instance widthInstDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → WidthRow k) :
    Decidable (widthNormal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _) ∧ (_ → _)))

omit [NeZero k] in
instance widthInstDecidableGood (s : Seen) (c : WidthRow k) : Decidable (good s c) := by
  induction k generalizing s with
  | zero => exact isTrue trivial
  | succ k ih =>
    change Decidable (allowed s (c 0) ∧ good (advance s (c 0)) (Fin.tail c))
    haveI := ih (advance s (c 0)) (Fin.tail c)
    infer_instance


variable (R : WidthRow k → Prop) (P : WidthRow k → B) (C : B → WidthRow k → Prop)
variable [DecidablePred R] [DecidableRel C]
variable (E : WidthRow k → WidthRow k → Prop) [DecidableRel E]
variable (edge : ∀ c d, E c d ↔ C (P c) d)

instance widthInstDecidableLegal {n : ℕ} (A : Fin n × Fin k → Fin 8) :
    Decidable (widthLegal R E A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def TailGood : {n : ℕ} → Seen → (B) → (Fin n → WidthRow k) → Prop
  | 0, _, _, _ => True
  | _ + 1, s, p, f => R (f 0) ∧ C p (f 0) ∧ good s (f 0) ∧
      TailGood (finish s (f 0)) (P (f 0)) (Fin.tail f)


instance instDecidableTailGood {n : ℕ} (s : Seen) (p : B) (f : Fin n → WidthRow k) :
    Decidable (TailGood R P C s p f) := by
  induction n generalizing s p with
  | zero => exact isTrue trivial
  | succ n ih =>
    change Decidable (R (f 0) ∧ C p (f 0) ∧ good s (f 0) ∧
      TailGood R P C (finish s (f 0)) (P (f 0)) (Fin.tail f))
    haveI := ih (finish s (f 0)) (P (f 0)) (Fin.tail f)
    infer_instance

omit [DecidablePred R] [DecidableRel C] [DecidableRel E] in
include edge in
theorem tail_iff {n : ℕ} (s : Seen) (p : B) (f : Fin n → WidthRow k) :
    TailGood R P C s p f ↔ widthNormal s f ∧
      (∀ i, R (f i)) ∧
      (∀ (i : Fin n) (h : i.val + 1 < n), E (f i) (f ⟨i.val + 1, h⟩)) ∧
      (∀ (h : 0 < n), C p (f ⟨0, h⟩)) := by
  induction n generalizing s p with
  | zero => simp [TailGood, widthNormal]
  | succ n ih =>
    have hn : widthNormal s f ↔ good s (f 0) ∧ widthNormal (finish s (f 0)) (Fin.tail f) := by
      simpa only [Fin.cons_self_tail] using normal_cons s (f 0) (Fin.tail f)
    rw [TailGood, ih, hn]
    have hb : (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1),
        E (f i) (f ⟨i.val + 1, h⟩)) ↔
        (∀ (h : 0 < n), C (P (f 0)) (Fin.tail f ⟨0, h⟩)) ∧
        (∀ (i : Fin n) (h : i.val + 1 < n),
          E (Fin.tail f i) (Fin.tail f ⟨i.val + 1, h⟩)) := by
      simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ]
      constructor
      · intro h
        constructor
        · intro hn
          simpa only [edge, Fin.tail, Fin.succ] using h.1 (by omega)
        · intro i hi
          exact h.2 i (by omega)
      · rintro ⟨h0, ht⟩
        constructor
        · intro hn
          simpa only [edge, Fin.tail, Fin.succ] using h0 (by omega)
        · intro i hi
          exact ht i (by omega)
    rw [hb]
    simp only [Fin.forall_fin_succ, Fin.tail, Fin.mk_zero, Nat.zero_lt_succ, forall_const]
    tauto

def widthStep (w : Seen → (B) → ℤ) (s : Seen) (p : B) : ℤ :=
  ∑ c : WidthRow k, if R c ∧ C p c ∧ good s c then
    w (finish s c) (P c) else 0

def widthV : ℕ → Seen → (B) → ℤ
  | 0, _, _ => 1
  | n + 1, s, p => widthStep R P C (widthV n) s p

def count (n : ℕ) (s : Seen) (p : B) : ℤ :=
  ∑ f : Fin n → WidthRow k, if TailGood R P C s p f then 1 else 0

omit [NeZero k] in
theorem count_eq_v (n : ℕ) : count R P C n = widthV R P C n := by
  induction n with
  | zero => funext s p; simp [count, TailGood, widthV]
  | succ n ih =>
    funext s p
    rw [count, ← (Fin.consEquiv (fun _ : Fin (n + 1) => WidthRow k)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ c : WidthRow k, ∑ f : Fin n → WidthRow k,
      if TailGood R P C s p (Fin.cons c f) then (1 : ℤ) else 0) = _
    change _ = widthStep R P C (widthV R P C n) s p
    rw [← ih]
    unfold widthStep count
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : R c ∧ C p c ∧ good s c
    · simp [TailGood, h.1, h.2.1, h.2.2]
    · have hn : ∀ f : Fin n → WidthRow k, ¬ TailGood R P C s p (Fin.cons c f) := by
        intro f hf
        exact h ⟨hf.1, hf.2.1, hf.2.2.1⟩
      simp [hn, h]

def widthTotal (w : Seen → (B) → ℤ) : ℤ :=
  ∑ c : WidthRow k, if c 0 = 0 ∧ R c ∧ good (false, false, false) c then
    w (finish (false, false, false) c) (P c) else 0

include edge in
theorem width_counting_bridge (n : ℕ) :
    ((Finset.univ.filter (fun A : Fin (n + 1) × Fin k → Fin 8 =>
      (∃ i : Fin (n + 1), i.val = 0 ∧ A (i, 0) = 0) ∧
      (∀ i, R (fun j => A (i, j))) ∧
      (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1), E (fun j => A (i, j))
        (fun j => A (⟨i.val + 1, h⟩, j))) ∧
      widthNormal (false, false, false) (fun i j => A (i, j)))).card : ℤ) =
      widthTotal R P (widthV R P C n) := by
  change ((Finset.univ.filter (fun A => widthLegal R E A)).card : ℤ) = _
  rw [Finset.natCast_card_filter]
  let e : (Fin (n + 1) × Fin k → Fin 8) ≃ (Fin (n + 1) → WidthRow k) :=
    { toFun := fun A i j => A (i, j)
      invFun := fun f p => f p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => WidthRow k)).sum_comp, Fintype.sum_prod_type]
  unfold widthTotal
  apply Finset.sum_congr rfl
  intro c _
  rw [← count_eq_v R P C]
  unfold count
  have hl : ∀ f : Fin n → WidthRow k,
      widthLegal R E (fun p => (Fin.cons c f : Fin (n + 1) → WidthRow k) p.1 p.2) ↔
        (c 0 = 0 ∧ R c ∧ good (false, false, false) c) ∧
          TailGood R P C (finish (false, false, false) c) (P c) f := by
    intro f
    rw [tail_iff R P C E edge, widthLegal, normal_cons]
    have hz : (∃ i : Fin (n + 1), i.val = 0 ∧
        (Fin.cons c f : Fin (n + 1) → WidthRow k) i 0 = 0) ↔ c 0 = 0 := by
      constructor
      · rintro ⟨i, hi, h⟩
        simpa only [show i = 0 from Fin.ext hi, Fin.cons_zero] using h
      · exact fun h => ⟨0, rfl, h⟩
    rw [hz]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.val_zero, Fin.val_succ]
    constructor
    · rintro ⟨hc, hr, hb, hg⟩
      refine ⟨⟨hc, hr.1, hg.1⟩, hg.2, hr.2, ?_, ?_⟩
      · intro i hi
        exact hb.2 i (by omega)
      · intro hn
        have he : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).succ :=
          Fin.ext rfl
        simpa only [edge, he, Fin.cons_succ] using hb.1 (by omega)
    · rintro ⟨⟨hc, hr, hg⟩, hn, ht, hb, hp⟩
      refine ⟨hc, ⟨hr, ht⟩, ⟨?_, ?_⟩, hg, hn⟩
      · intro h
        have he : (⟨0 + 1, h⟩ : Fin (n + 1)) = (⟨0, by omega⟩ : Fin n).succ :=
          Fin.ext rfl
        simpa only [edge, he, Fin.cons_succ] using hp (by omega)
      · intro i hi
        exact hb i (by omega)
  change (∑ f : Fin n → WidthRow k,
    if widthLegal R E (fun p => (Fin.cons c f : Fin (n + 1) → WidthRow k) p.1 p.2)
      then (1 : ℤ) else 0) = _
  simp_rw [hl]
  by_cases h : c 0 = 0 ∧ R c ∧ good (false, false, false) c <;> simp [h]

end


abbrev Row := Fin 2 → Fin 8

def rowLegal (c : Row) : Prop := c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 7

def bonds (c d : Row) : Prop :=
  (∀ j : Fin 2, c j ≠ d j ∧ (c j).val + (d j).val ≠ 7) ∧
    (c 1 ≠ d 0 ∧ (c 1).val + (d 0).val ≠ 7)

private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (_ ∧ _))
private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable ((∀ _, _ ∧ _) ∧ (_ ∧ _)))

def Legal {n : ℕ} (A : Fin n × Fin 2 → Fin 8) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), bonds (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    widthNormal (false, false, false) (fun i j => A (i, j))

private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 2 → Fin 8) :
    Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The literal filtered finite count. The first-cell existential sets `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 2 → Fin 8 => Legal A)).card

def pairs (c : Row) : Fin 4 × Fin 4 := (beta (c 0), beta (c 1))

def compatible (p : Fin 4 × Fin 4) (c : Row) : Prop :=
  p.1 ≠ beta (c 0) ∧ p.2 ≠ beta (c 1) ∧ p.2 ≠ beta (c 0)

private instance instDecidableCompatible (p : Fin 4 × Fin 4) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  simp only [bonds, Fin.forall_fin_two, colour_bond_iff, compatible, pairs]
  tauto

private abbrev v2 := widthV rowLegal pairs compatible
private abbrev total2 := widthTotal rowLegal pairs

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total2 (v2 n) := by
  exact width_counting_bridge rowLegal pairs compatible bonds bonds_iff n

def Valid (s : Seen) (p : Fin 4 × Fin 4) : Prop :=
  s.1 = true ∧ p.1 ≠ p.2 ∧
    (s.2.1 = false → p.1.val < 2 ∧ p.2.val < 2) ∧
    (s.2.2 = false → p.1.val < 3 ∧ p.2.val < 3) ∧ (s.2.2 = true → s.2.1 = true)

private instance instDecidableValid (s : Seen) (p : Fin 4 × Fin 4) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ → _ ∧ _) ∧ (_ → _ ∧ _) ∧ (_ → _)))

def seenClass (s : Seen) : Fin 3 := if s.2.2 then 2 else if s.2.1 then 1 else 0

def T : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, 1], ![0, 4, 6], ![0, 0, 16]]

/-- Legal one-row continuations counted by the final seen-colour class. -/
def classCount (s : Seen) (p : Fin 4 × Fin 4) (b : Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    seenClass (finish s c) = b then 1 else 0

/-- First rows counted by their final seen-colour class. -/
def firstCount (b : Fin 3) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c ∧
    seenClass (finish (false, false, false) c) = b then 1 else 0

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c →
      Valid (finish (false, false, false) c) (pairs c) := by
  decide +kernel

private theorem row_counts : ∀ s p, Valid s p → ∀ b,
    classCount s p b = T (seenClass s) b := by
  decide +kernel

private theorem initial_counts : ∀ b, firstCount b = if b = 0 then 1 else 0 := by
  decide +kernel

private theorem vector_relation :
    (T ^ (1 + 2)).mulVec (1 : Fin 3 → ℤ) =
      ∑ j : Fin 2, (![-64, 20] : Fin 2 → ℤ) j •
        (T ^ (1 + j.val)).mulVec (1 : Fin 3 → ℤ) := by
  decide +kernel

/-- Single-row class counts and the quadratic relation after the transient first step. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ b, classCount s p b = T (seenClass s) b) ∧
    (∀ b, firstCount b = if b = 0 then 1 else 0) ∧
    (T ^ (1 + 2)).mulVec (1 : Fin 3 → ℤ) =
      ∑ j : Fin 2, (![-64, 20] : Fin 2 → ℤ) j •
        (T ^ (1 + j.val)).mulVec (1 : Fin 3 → ℤ) :=
  ⟨row_counts, initial_counts, vector_relation⟩

private def w (n : ℕ) : Fin 3 → ℤ := (T ^ n).mulVec 1

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 4 × Fin 4) (h : Valid s p) :
    v2 n s p = w n (seenClass s) := by
  induction n generalizing s p with
  | zero => simp [v2, widthV, w, Matrix.one_mulVec]
  | succ n ih =>
    rw [v2, widthV, widthStep]
    change (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
      v2 n (finish s c) (pairs c) else 0) = _
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v2 n (finish s c) (pairs c) else 0) =
        ∑ b : Fin 3, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          seenClass (finish s c) = b then (1 : ℤ) else 0) * w n b := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ b : Fin 3, classCount s p b * w n b) = _
    simp_rw [finite_certificate.1 s p h]
    change _ = (T ^ (n + 1)).mulVec (1 : Fin 3 → ℤ) (seenClass s)
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    rfl

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = w n 0 := by
  rw [counting_bridge, total2, widthTotal]
  change (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
    v2 n (finish (false, false, false) c) (pairs c) else 0) = _
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c then
      v2 n (finish (false, false, false) c) (pairs c) else 0) =
      ∑ b : Fin 3, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c ∧
        seenClass (finish (false, false, false) c) = b then (1 : ℤ) else 0) * w n b := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ b : Fin 3, firstCount b * w n b) = _
  simp [finite_certificate.2.1]

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 20 * a (n + 3) - 64 * a (n + 2) := by
  have hh := TransferMatrix.scalarRelationShift T (Pi.single 0 1) 2 1 ![-64, 20]
    finite_certificate.2.2 n
  simp only [single_dotProduct, one_mul] at hh
  norm_num [Fin.sum_univ_succ, Nat.add_assoc] at hh
  rw [show n + 4 = (n + 1 + 2) + 1 by omega,
    show n + 3 = (n + 1 + 1) + 1 by omega,
    show n + 2 = (n + 1 + 0) + 1 by omega, a_eq_w, a_eq_w, a_eq_w]
  dsimp [w]
  linarith

private theorem zero_count : a 0 = 0 := by simp [a, Legal]

open PowerSeries in
/-- Barker's generating-function identity, with coefficient zero at index zero. -/
theorem result :
    (1 - 4 * X) * (1 - 16 * X) * (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (1 - 17 * X + 40 * X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 4 * X) * (1 - 16 * X) * F =
      F - 20 * (F * X ^ 1) + 64 * (F * X ^ 2) := by ring
  have hr : (X * (1 - 17 * X + 40 * X ^ 2) : PowerSeries ℤ) =
      X - 17 * X ^ 2 + 40 * X ^ 3 := by ring
  change (1 - 4 * X) * (1 - 16 * X) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence (n - 4)
    have h4 : n - 4 + 4 = n := by omega
    have h3 : n - 4 + 3 = n - 1 := by omega
    have h2 : n - 4 + 2 = n - 2 := by omega
    rw [h4, h3, h2] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    have hw0 : w 0 0 = 1 := by decide +kernel
    have hw1 : w 1 0 = 3 := by decide +kernel
    have hw2 : w 2 0 = 36 := by decide +kernel
    rw [hw0] at h1
    rw [hw1] at h2
    rw [hw2] at h3
    norm_num only at h1 h2 h3
    interval_cases n <;> norm_num only [zero_count, h1, h2, h3,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip

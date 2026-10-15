/- GID: D5/S1/Recurrence/AntiRecurrenceAutomaticity
   generality: G
   mirror-B: D5/B/S1/Recurrence/AntiRecurrenceAutomaticity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary positive linear recurrences and their finite-state discrepancy. -/

import D5.S0.Automata.DFAOStateLowerBound
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Recurrence.AntiRecurrenceAutomaticity
open Finset
open D5.S0.Automata.DFAOStateLowerBound
/-- The zero entries are auxiliary. Positive indices partition the positive
integers and satisfy the source block recurrence. -/
structure Source (k : ℕ) (a : Fin k → ℕ) (A B : ℕ → ℕ) : Prop where
  zeroA : A 0 = 0
  zeroB : B 0 = 0
  monoA : StrictMono A
  monoB : StrictMono B
  partition : ∀ x, 0 < x → ((∃ n, 0 < n ∧ A n = x) ↔ ¬ ∃ m, 0 < m ∧ B m = x)
  recurrence : ∀ n, A (n + 1) = ∑ j : Fin k, a j * B (k * n + j.val + 1)
private def available (s : Finset ℕ) (x : ℕ) : Prop := 0 < x ∧ x ∉ s
private theorem available_infinite (s : Finset ℕ) : {x | available s x}.Infinite := by
  convert (Set.Ioi_infinite (0 : ℕ)).sdiff s.finite_toSet using 1
  ext x
  simp [available]
private noncomputable def complement (s : Finset ℕ) : ℕ → ℕ := Nat.nth (available s)
private theorem complement_pos (s : Finset ℕ) (m : ℕ) : 0 < complement s m := (Nat.nth_mem_of_infinite (available_infinite s) m).1
private theorem complement_mono (s : Finset ℕ) : StrictMono (complement s) := Nat.nth_strictMono (available_infinite s)

private theorem complement_avoid (s : Finset ℕ) (m : ℕ) : complement s m ∉ s := (Nat.nth_mem_of_infinite (available_infinite s) m).2
private theorem complement_subset {s t : Finset ℕ} (hst : s ⊆ t) (m : ℕ) : complement s m ≤ complement t m := by
  apply Nat.nth_le_of_strictMonoOn_of_mapsTo (complement t)
  · intro i _
    exact ⟨complement_pos t i, fun hi => complement_avoid t i (hst hi)⟩
  · exact (complement_mono t).strictMonoOn _

private theorem nth_agree_below {p q : ℕ → Prop} (hp : {x | p x}.Infinite) (m : ℕ) (h : ∀ x ≤ Nat.nth p m, p x ↔ q x) :
    Nat.nth q m = Nat.nth p m := by
  classical
  have hc : Nat.count q (Nat.nth p m) = Nat.count p (Nat.nth p m) := by
    apply le_antisymm
    · exact Nat.count_mono_left (fun x hx => (h x hx.le).mpr)
    · exact Nat.count_mono_left (fun x hx => (h x hx.le).mp)
  rw [Nat.count_nth_of_infinite hp] at hc
  have hmem : q (Nat.nth p m) := (h _ le_rfl).mp (Nat.nth_mem_of_infinite hp m)
  simpa only [hc] using (Nat.nth_count hmem)
private theorem complement_insert {s : Finset ℕ} {v m : ℕ} (h : complement s m < v) : complement (insert v s) m = complement s m := by
  classical
  apply nth_agree_below (available_infinite s)
  intro x hx
  simp only [available, Finset.mem_insert, not_or]
  have hv : x ≠ v := by
    change x ≤ complement s m at hx
    omega
  tauto

private noncomputable def next (k : ℕ) (a : Fin k → ℕ) (s : Finset ℕ) (n : ℕ) : ℕ := ∑ j : Fin k, a j * complement s (k * n + j.val)
private noncomputable def history (k : ℕ) (a : Fin k → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (next k a (history k a n) n) (history k a n)

private noncomputable def positiveA (k : ℕ) (a : Fin k → ℕ) (n : ℕ) : ℕ := next k a (history k a n) n
private theorem prefix_succ (k : ℕ) (a : Fin k → ℕ) (n : ℕ) : history k a (n + 1) = insert (positiveA k a n) (history k a n) := rfl

private theorem prefix_mono (k : ℕ) (a : Fin k → ℕ) : Monotone (history k a) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  exact subset_insert _ _
private theorem prefix_mem (k : ℕ) (a : Fin k → ℕ) (n v : ℕ) : v ∈ history k a n ↔ ∃ i < n, positiveA k a i = v := by
  classical
  induction n with
  | zero => simp [history]
  | succ n ih =>
    rw [prefix_succ, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨i, hi, hv⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨i, by omega, hv⟩
    · rintro ⟨i, hi, hv⟩
      by_cases hin : i = n
      · subst i
        exact Or.inl hv.symm
      · exact Or.inr ⟨i, by omega, hv⟩

private theorem complement_shift (s : Finset ℕ) (m d : ℕ) : complement s m + d ≤ complement s (m + d) := by
  simpa only [Nat.add_comm] using (complement_mono s).add_le_nat d m
private theorem positiveA_gap (k : ℕ) (a : Fin k → ℕ) (n : ℕ) : positiveA k a n + k * ∑ j, a j ≤ positiveA k a (n + 1) := by
  unfold positiveA next
  calc
    (∑ j : Fin k, a j * complement (history k a n) (k * n + j.val)) + k * ∑ j : Fin k, a j = ∑ j : Fin k, a j *
        (complement (history k a n) (k * n + j.val) + k) := by
          simp only [mul_add, sum_add_distrib, mul_sum]
          congr 1
          exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)
    _ ≤ ∑ j : Fin k, a j * complement (history k a (n + 1)) (k * (n + 1) + j.val) := by
      apply Finset.sum_le_sum
      intro j _
      apply Nat.mul_le_mul_left
      calc
        complement (history k a n) (k * n + j.val) + k ≤ complement (history k a n) (k * n + j.val + k) := complement_shift _ _ _
        _ ≤ complement (history k a (n + 1)) (k * (n + 1) + j.val) := by
          simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using complement_subset (prefix_mono k a (Nat.le_succ n)) (k * n + j.val + k)

private theorem weighted_above_block (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (f : ℕ → ℕ) (hf : StrictMono f) (hpos : ∀ m, 0 < f m) (n : ℕ) (j : Fin k) :
    f (k * n + j.val) < ∑ i : Fin k, a i * f (k * n + i.val) := by
  classical
  let last : Fin k := ⟨k - 1, by omega⟩
  let first : Fin k := ⟨0, by omega⟩
  have hne : first ≠ last := by
    intro h
    have := congrArg Fin.val h
    dsimp [first, last] at this
    omega
  have hlast : f (k * n + j.val) ≤ a last * f (k * n + last.val) := by
    calc
      _ ≤ f (k * n + last.val) := hf.monotone (by dsimp [last]; omega)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (ha last)
  have hfirst : 0 < a first * f (k * n + first.val) := Nat.mul_pos (ha first) (hpos _)
  have hsum : a first * f (k * n + first.val) + a last * f (k * n + last.val) ≤ ∑ i : Fin k, a i * f (k * n + i.val) :=
    Finset.add_le_sum (fun i _ => Nat.zero_le (a i * f (k * n + i.val))) (mem_univ first) (mem_univ last) hne
  omega
private theorem next_above_block (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (s : Finset ℕ) (n : ℕ) (j : Fin k) :
    complement s (k * n + j.val) < next k a s n :=
  weighted_above_block k a hk ha (complement s) (complement_mono s) (complement_pos s) n j

private theorem complement_stable_step (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (n m : ℕ) (hm : m < k * (n + 1)) :
    complement (history k a (n + 1)) m = complement (history k a n) m := by
  rw [prefix_succ]
  apply complement_insert
  calc
    complement (history k a n) m ≤ complement (history k a n) (k * n + (k - 1)) := (complement_mono _).monotone (by
          simp only [Nat.mul_add, Nat.mul_one] at hm
          omega)
    _ < positiveA k a n := next_above_block k a hk ha _ n ⟨k - 1, by omega⟩

private theorem complement_stable (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (n p m : ℕ)
    (hnp : n ≤ p) (hm : m < k * (n + 1)) : complement (history k a p) m = complement (history k a n) m := by
  induction p, hnp using Nat.le_induction with
  | base => rfl
  | succ p hnp ih =>
    rw [complement_stable_step k a hk ha p m (lt_of_lt_of_le hm (Nat.mul_le_mul_left k (by omega))), ih]
private noncomputable def positiveB (k : ℕ) (a : Fin k → ℕ) (m : ℕ) : ℕ := complement (history k a (m + 1)) m

private theorem positiveB_eq (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (n m : ℕ) (hm : m < k * (n + 1)) :
    positiveB k a m = complement (history k a n) m := by
  have hm' : m < k * (m + 1 + 1) := by nlinarith
  rcases le_total n (m + 1) with h | h
  · exact complement_stable k a hk ha n (m + 1) m h hm
  · exact (complement_stable k a hk ha (m + 1) n m h hm').symm
private theorem positiveB_strict (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) : StrictMono (positiveB k a) := by
  intro m l hml
  rw [positiveB_eq k a hk ha (l + 1) m (by nlinarith)]
  exact complement_mono _ hml

private theorem trace_pos (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) : 0 < ∑ j, a j := by
  let j : Fin k := ⟨0, by omega⟩
  exact lt_of_lt_of_le (ha j) (Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (mem_univ j))
private theorem positiveA_strict (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) : StrictMono (positiveA k a) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := Nat.mul_pos (by omega : 0 < k) (trace_pos k a hk ha)
  have hg := positiveA_gap k a n
  omega

private noncomputable def constructedA (k : ℕ) (a : Fin k → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => positiveA k a n
private noncomputable def constructedB (k : ℕ) (a : Fin k → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => positiveB k a n

private theorem positiveA_positive (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (n : ℕ) : 0 < positiveA k a n := by
  exact lt_trans (complement_pos _ _) (next_above_block k a hk ha _ n ⟨0, by omega⟩)
private theorem constructed_disjoint (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (n m : ℕ) :
    positiveA k a n ≠ positiveB k a m := by
  intro h
  have hb := positiveB_eq k a hk ha (n + m + 1) m (by nlinarith)
  have hm : positiveA k a n ∈ history k a (n + m + 1) := (prefix_mem k a _ _).mpr ⟨n, by omega, rfl⟩
  rw [h, hb] at hm
  exact complement_avoid _ _ hm

private theorem constructed_exhaustive (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (x : ℕ) (hx : 0 < x)
    (hA : ¬ ∃ n, positiveA k a n = x) : ∃ m, positiveB k a m = x := by
  classical
  have hav : available (history k a x) x := by
    refine ⟨hx, ?_⟩
    intro h
    obtain ⟨i, _, hi⟩ := (prefix_mem k a x x).mp h
    exact hA ⟨i, hi⟩
  let m := Nat.count (available (history k a x)) x
  have hm : m ≤ x := Nat.count_le _
  have hB := positiveB_eq k a hk ha x m (by nlinarith)
  refine ⟨m, hB.trans ?_⟩
  exact Nat.nth_count hav
private theorem constructed_source (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) :
    Source k a (constructedA k a) (constructedB k a) := by
  classical
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero => exact positiveA_positive k a hk ha 0
    | succ n => exact positiveA_strict k a hk ha (Nat.lt_succ_self n)
  · apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero => exact complement_pos _ _
    | succ n => exact positiveB_strict k a hk ha (Nat.lt_succ_self n)
  · intro x hx
    constructor
    · rintro ⟨n, hn, hAn⟩ ⟨m, hm, hBm⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact constructed_disjoint k a hk ha n m (hAn.trans hBm.symm)
    · intro hB
      by_contra hA
      have hA' : ¬ ∃ n, positiveA k a n = x := by
        rintro ⟨n, hn⟩
        exact hA ⟨n + 1, by omega, hn⟩
      obtain ⟨m, hm⟩ := constructed_exhaustive k a hk ha x hx hA'
      exact hB ⟨m + 1, by omega, hm⟩
  · intro n
    change next k a (history k a n) n = ∑ j : Fin k, a j * positiveB k a (k * n + j.val)
    unfold next
    apply sum_congr rfl
    intro j _
    rw [positiveB_eq k a hk ha n (k * n + j.val)]
    simp only [Nat.mul_add, Nat.mul_one]
    omega

private theorem nth_range (f : ℕ → ℕ) (hf : StrictMono f) (m : ℕ) : Nat.nth (fun x => ∃ n, f n = x) m = f m := by
  have hinf : {x | ∃ n, f n = x}.Infinite := Set.infinite_range_of_injective hf.injective
  have hindex (n : ℕ) : ∀ hfin : (Set.ofPred (fun x => ∃ n, f n = x)).Finite, n < hfin.toFinset.card := by
    intro hfin
    exact (hinf hfin).elim
  symm
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f
  · rintro x ⟨n, rfl⟩
    exact ⟨n, hindex n, rfl⟩
  · intro n _
    exact ⟨n, rfl⟩
  · exact hf.strictMonoOn _
  · exact hindex m

private theorem source_pos {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (n : ℕ) : 0 < A (n + 1) ∧ 0 < B (n + 1) := by
  constructor
  · simpa only [h.zeroA] using h.monoA (Nat.zero_lt_succ n)
  · simpa only [h.zeroB] using h.monoB (Nat.zero_lt_succ n)
private theorem source_above_block {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (n : ℕ) (j : Fin k) : B (k * n + j.val + 1) < A (n + 1) := by
  rw [h.recurrence n]
  exact weighted_above_block k a hk ha (fun m => B (m + 1)) (h.monoB.comp (strictMono_id.add_const 1)) (fun m => (source_pos h m).2) n j

private theorem source_B_range {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (x : ℕ) :
    (∃ m, B (m + 1) = x) ↔ 0 < x ∧ ¬ ∃ n, 0 < n ∧ A n = x := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨(source_pos h m).2, ?_⟩
    intro hA
    exact (h.partition _ (source_pos h m).2).mp hA ⟨m + 1, by omega, rfl⟩
  · rintro ⟨hx, hA⟩
    have hB : ∃ m, 0 < m ∧ B m = x := by
      by_contra hn
      exact hA ((h.partition x hx).mpr hn)
    obtain ⟨m, hm, hv⟩ := hB
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact ⟨m, hv⟩
private theorem source_unique (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) (A B : ℕ → ℕ) (h : Source k a A B) :
    constructedA k a = A ∧ constructedB k a = B := by
  classical
  have hA (n : ℕ) : positiveA k a n = A (n + 1) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hB (j : Fin k) : complement (history k a n) (k * n + j.val) = B (k * n + j.val + 1) := by
        let p : ℕ → Prop := fun x => ∃ m, B (m + 1) = x
        have hf : StrictMono (fun m => B (m + 1)) := h.monoB.comp (strictMono_id.add_const 1)
        have hp : {x | p x}.Infinite := Set.infinite_range_of_injective hf.injective
        have hval := nth_range (fun m => B (m + 1)) hf (k * n + j.val)
        have heq := nth_agree_below hp (k * n + j.val) (q := available (history k a n))
        apply Eq.trans (heq ?_) hval
        intro x hx
        rw [hval] at hx
        rw [show p x ↔ 0 < x ∧ ¬ ∃ i, 0 < i ∧ A i = x from source_B_range h x]
        constructor
        · rintro ⟨hx0, hnot⟩
          refine ⟨hx0, ?_⟩
          intro hxmem
          obtain ⟨i, hi, hiv⟩ := (prefix_mem k a n x).mp hxmem
          exact hnot ⟨i + 1, by omega, (ih i hi).symm.trans hiv⟩
        · rintro ⟨hx0, hnot⟩
          refine ⟨hx0, ?_⟩
          rintro ⟨i, hi, hiv⟩
          rcases lt_or_ge i (n + 1) with hin | hin
          · have hi' : i - 1 < n := by omega
            apply hnot
            apply (prefix_mem k a n x).mpr
            refine ⟨i - 1, hi', ?_⟩
            rw [ih (i - 1) hi', Nat.sub_add_cancel (by omega : 1 ≤ i)]
            exact hiv
          · have hle := h.monoA.monotone hin
            have hstrict := source_above_block h hk ha n j
            omega
      change next k a (history k a n) n = A (n + 1)
      rw [h.recurrence n]
      unfold next
      exact sum_congr rfl (fun j _ => congrArg (a j * ·) (hB j))
  have hAf : constructedA k a = A := by
    funext n
    cases n with
    | zero => exact h.zeroA.symm
    | succ n => exact hA n
  refine ⟨hAf, ?_⟩
  have hc := constructed_source k a hk ha
  funext m
  cases m with
  | zero => exact h.zeroB.symm
  | succ m =>
    have hf : StrictMono (fun m => B (m + 1)) := h.monoB.comp (strictMono_id.add_const 1)
    have hfc : StrictMono (fun m => constructedB k a (m + 1)) := hc.monoB.comp (strictMono_id.add_const 1)
    rw [← nth_range _ hf m, ← nth_range _ hfc m]
    congr 1
    funext x
    apply propext
    rw [source_B_range hc x, source_B_range h x, hAf]

/-- Sum of the positive integral coefficients. -/
def trace (k : ℕ) (a : Fin k → ℕ) : ℕ := ∑ j, a j

/-- The source linear slope. -/
def slope (k : ℕ) (a : Fin k → ℕ) : ℕ := k * trace k a + 1
/-- Integer discrepancy, including the auxiliary zero term. -/
def discrepancy (k : ℕ) (a : Fin k → ℕ) (A : ℕ → ℕ) (n : ℕ) : ℤ := (A n : ℤ) - (slope k a : ℤ) * n

private theorem trace_ge (k : ℕ) (a : Fin k → ℕ) (ha : ∀ j, 0 < a j) : k ≤ trace k a := by
  calc
    k = ∑ _j : Fin k, 1 := by simp
    _ ≤ ∑ j : Fin k, a j := sum_le_sum (fun j _ => ha j)
    _ = trace k a := rfl
private theorem positive_index (f : ℕ → ℕ) (x : ℕ) : (∃ n, 0 < n ∧ f n = x) ↔ ∃ n, f (n + 1) = x := by
  constructor
  · rintro ⟨n, hn, hx⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨n, hx⟩
  · rintro ⟨n, hx⟩
    exact ⟨n + 1, by omega, hx⟩

private theorem source_partition {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (x : ℕ) (hx : 0 < x) :
    (∃ n, A (n + 1) = x) ↔ ¬ ∃ m, B (m + 1) = x := by
  simpa only [positive_index] using h.partition x hx
private noncomputable def rank (A : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical exact Nat.count (fun y => ∃ n, A (n + 1) = y) x

private theorem source_rank {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (m : ℕ) : B (m + 1) = m + 1 + rank A (B (m + 1)) ∧
      A (rank A (B (m + 1))) < B (m + 1) ∧ B (m + 1) < A (rank A (B (m + 1)) + 1) := by
  classical
  let p : ℕ → Prop := fun x => ∃ n, A (n + 1) = x
  let q : ℕ → Prop := fun x => ∃ n, B (n + 1) = x
  have hp0 : ¬p 0 := by rintro ⟨n, hn⟩; have := (source_pos h n).1; omega
  have hq0 : ¬q 0 := by rintro ⟨n, hn⟩; have := (source_pos h n).2; omega
  have hcount (x : ℕ) : Nat.count p (x + 1) + Nat.count q (x + 1) = x := by
    induction x with
    | zero => simp [Nat.count_succ, hp0, hq0]
    | succ x ih =>
      have hpart : p (x + 1) ↔ ¬ q (x + 1) := source_partition h _ (by omega)
      by_cases hp : p (x + 1)
      · have hq : ¬q (x + 1) := hpart.mp hp
        rw [Nat.count_succ p (x + 1), Nat.count_succ q (x + 1), if_pos hp, if_neg hq]
        omega
      · have hq : q (x + 1) := by tauto
        rw [Nat.count_succ p (x + 1), Nat.count_succ q (x + 1), if_neg hp, if_pos hq]
        omega
  have hfa : StrictMono (fun n => A (n + 1)) := h.monoA.comp (strictMono_id.add_const 1)
  have hfb : StrictMono (fun n => B (n + 1)) := h.monoB.comp (strictMono_id.add_const 1)
  have hpa : {x | p x}.Infinite := Set.infinite_range_of_injective hfa.injective
  have hqb : {x | q x}.Infinite := Set.infinite_range_of_injective hfb.injective
  have hcb : Nat.count q (B (m + 1)) = m := by
    rw [← nth_range _ hfb m]
    exact Nat.count_nth_of_infinite hqb m
  have htotal : Nat.count p (B (m + 1)) + Nat.count q (B (m + 1)) + 1 = B (m + 1) := by
    have hbpos := (source_pos h m).2
    obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B (m + 1) ≠ 0)
    rw [hv]
    simpa only [Nat.succ_eq_add_one] using congrArg (fun t => t + 1) (hcount v)
  have ht : rank A (B (m + 1)) = Nat.count p (B (m + 1)) := rfl
  refine ⟨by omega, ?_, ?_⟩
  · by_cases ht0 : rank A (B (m + 1)) = 0
    · rw [ht0, h.zeroA]
      exact (source_pos h m).2
    · have hlt : rank A (B (m + 1)) - 1 < Nat.count p (B (m + 1)) := by omega
      have hn := Nat.nth_lt_of_lt_count hlt
      rw [nth_range _ hfa, Nat.sub_add_cancel (by omega : 1 ≤ rank A (B (m + 1)))] at hn
      exact hn
  · have hle : B (m + 1) ≤ Nat.nth p (rank A (B (m + 1))) :=
      (Nat.count_le_iff_le_nth hpa).mp ht.ge
    rw [nth_range _ hfa] at hle
    have hnot : ¬p (B (m + 1)) := by
      have hpart := source_partition h _ (source_pos h m).2
      exact fun hp => hpart.mp hp ⟨m, rfl⟩
    have hne : B (m + 1) ≠ A (rank A (B (m + 1)) + 1) := by
      intro heq
      exact hnot ⟨_, heq.symm⟩
    omega
private theorem source_gap {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (n : ℕ) : A (n + 1) + k * trace k a ≤ A (n + 2) := by
  rw [h.recurrence n, h.recurrence (n + 1)]
  calc
    (∑ j : Fin k, a j * B (k * n + j.val + 1)) + k * trace k a = ∑ j : Fin k, a j * (B (k * n + j.val + 1) + k) := by
        simp only [trace, mul_add, sum_add_distrib, mul_sum]
        congr 1
        exact sum_congr rfl (fun _ _ => Nat.mul_comm _ _)
    _ ≤ ∑ j : Fin k, a j * B (k * (n + 1) + j.val + 1) := by
      apply sum_le_sum
      intro j _
      apply Nat.mul_le_mul_left
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.monoB.add_le_nat k (k * n + j.val + 1)

private theorem source_growth {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (n : ℕ) : 1 + n * (k * trace k a) ≤ A (n + 1) := by
  induction n with
  | zero => have := (source_pos h 0).1; omega
  | succ n ih =>
    have := source_gap h n
    nlinarith
private theorem source_rank_block {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (n : ℕ) (j : Fin k) : rank A (B (k * n + j.val + 1)) ≤ n := by
  have hr := (source_rank h (k * n + j.val)).2.1
  have hb := source_above_block h hk ha n j
  have he := h.monoA.lt_iff_lt.mp (lt_trans hr hb)
  omega

private theorem earlier_rank {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (n : ℕ) (hn : 4 * (k * trace k a) + 4 ≤ n) (j : Fin k) : rank A (B (k * (n - 1) + j.val + 1)) + 1 < n := by
  have ht := trace_ge k a ha
  have hh : k + 2 ≤ k * trace k a := by nlinarith
  have hn2 : 2 ≤ n := by omega
  have hg := source_growth h (n - 2)
  have hB := source_rank h (k * (n - 1) + (k - 1))
  have htB := source_rank_block h hk ha (n - 1) ⟨k - 1, by omega⟩
  have heq : k * (n - 1) + (k - 1) + 1 = k * n := by
    have : n - 1 + 1 = n := by omega
    have : k - 1 + 1 = k := by omega
    nlinarith
  rw [heq] at hB htB
  have hBbound : B (k * n) ≤ k * n + n - 1 := by omega
  have hgap : B (k * n) < A (n - 1) := by
    have hn2' : n - 2 + 1 = n - 1 := by omega
    rw [hn2'] at hg
    have hprod : (k + 2) * (n - 2) ≤ k * trace k a * (n - 2) := Nat.mul_le_mul_right _ hh
    have : n - 2 + 2 = n := by omega
    nlinarith
  have hbj : B (k * (n - 1) + j.val + 1) ≤ B (k * n) := by
    apply h.monoB.monotone
    have : n - 1 + 1 = n := by omega
    nlinarith [j.isLt]
  have hr := (source_rank h (k * (n - 1) + j.val)).2.1
  have hrlt := h.monoA.lt_iff_lt.mp (lt_trans hr (lt_of_le_of_lt hbj hgap))
  omega

private def constantTerm (k : ℕ) (a : Fin k → ℕ) : ℤ := ∑ j : Fin k, (a j : ℤ) * ((j.val : ℤ) + 1 - k)
private theorem weighted_indices (k : ℕ) (a : Fin k → ℕ) (n : ℕ) : (∑ j : Fin k, (a j : ℤ) * ((k : ℤ) * n + j.val + 1)) =
      (k * trace k a : ℕ) * ((n : ℤ) + 1) + constantTerm k a := by
  calc
    _ = ∑ j : Fin k, (((k : ℤ) * ((n : ℤ) + 1)) * a j + (a j : ℤ) * ((j.val : ℤ) + 1 - k)) := sum_congr rfl (fun _ _ => by ring)
    _ = ((k : ℤ) * ((n : ℤ) + 1)) * (∑ j : Fin k, (a j : ℤ)) + constantTerm k a := by rw [sum_add_distrib, ← mul_sum]; rfl
    _ = _ := by simp only [trace, Nat.cast_mul, Nat.cast_sum]; ring

private theorem discrepancy_formula {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (n : ℕ) :
    discrepancy k a A (n + 1) = constantTerm k a + (∑ j : Fin k, (a j : ℤ) * rank A (B (k * n + j.val + 1))) - (n + 1) := by
  have hb (j : Fin k) : (B (k * n + j.val + 1) : ℤ) = ((k : ℤ) * n + j.val + 1) + rank A (B (k * n + j.val + 1)) := by
    exact_mod_cast (source_rank h (k * n + j.val)).1
  have he : (A (n + 1) : ℤ) = (k * trace k a : ℕ) * ((n : ℤ) + 1) + constantTerm k a +
        ∑ j : Fin k, (a j : ℤ) * rank A (B (k * n + j.val + 1)) := by
    calc
      (A (n + 1) : ℤ) = ∑ j : Fin k, (a j : ℤ) * (B (k * n + j.val + 1) : ℤ) := by
        exact_mod_cast h.recurrence n
      _ = ∑ j : Fin k, ((a j : ℤ) * ((k : ℤ) * n + j.val + 1) + (a j : ℤ) * rank A (B (k * n + j.val + 1))) := by
        apply sum_congr rfl
        intro j _
        rw [hb j]
        ring
      _ = _ := by rw [sum_add_distrib, weighted_indices]
  unfold discrepancy slope
  push_cast
  push_cast at he
  linarith
private theorem discrepancy_balance {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (n : ℕ) :
    (k * trace k a : ℕ) * discrepancy k a A (n + 1) = (k * trace k a : ℕ) * constantTerm k a + constantTerm k a + ∑ j : Fin k, (a j : ℤ) *
          ((k * trace k a : ℕ) * rank A (B (k * n + j.val + 1)) - ((k : ℤ) * n + j.val + 1)) := by
  have hs : (∑ j : Fin k, (a j : ℤ) * ((k * trace k a : ℕ) * rank A (B (k * n + j.val + 1)) - ((k : ℤ) * n + j.val + 1))) =
        (k * trace k a : ℕ) * (∑ j : Fin k, (a j : ℤ) * rank A (B (k * n + j.val + 1))) -
          ∑ j : Fin k, (a j : ℤ) * ((k : ℤ) * n + j.val + 1) := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [hs, weighted_indices, discrepancy_formula h n]
  ring

private theorem inverse_residual {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (m : ℕ) : let t := rank A (B (m + 1))
    (k * trace k a : ℕ) * (t : ℤ) + discrepancy k a A t < (m + 1 : ℕ) ∧ (m + 1 : ℕ) < (k * trace k a : ℕ) * (t : ℤ) +
        (slope k a : ℕ) + discrepancy k a A (t + 1) := by
  dsimp only
  have hr := source_rank h m
  have hB : (B (m + 1) : ℤ) = (m : ℤ) + 1 + rank A (B (m + 1)) := by exact_mod_cast hr.1
  have hl : (A (rank A (B (m + 1))) : ℤ) < B (m + 1) := by
    exact_mod_cast hr.2.1
  have hu : (B (m + 1) : ℤ) < A (rank A (B (m + 1)) + 1) := by
    exact_mod_cast hr.2.2
  unfold discrepancy slope
  push_cast
  constructor <;> nlinarith

private theorem discrepancy_bounded {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j) :
    ∃ D : ℕ, ∀ n, |discrepancy k a A n| ≤ (D : ℤ) := by
  classical
  let H := k * trace k a
  let N := 4 * H + 4
  let c := constantTerm k a
  let E : ℤ := ∑ i ∈ Finset.range N, |discrepancy k a A i|
  let D : ℤ := E + ((k : ℤ) + 1) * |c| + ((H : ℤ) + 1)
  have hE : 0 ≤ E := sum_nonneg (fun i _ => abs_nonneg _)
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have htNat := trace_ge k a ha
  have ht : (1 : ℤ) ≤ trace k a := by exact_mod_cast (by omega : 1 ≤ trace k a)
  have hH : (0 : ℤ) < H := by
    dsimp [H]
    exact_mod_cast Nat.mul_pos (by omega : 0 < k) (by omega : 0 < trace k a)
  have hHcast : (H : ℤ) = (k : ℤ) * trace k a := by simp [H]
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbudget0 : ((k : ℤ) + 1) * |c| + ((H : ℤ) + 1) ≤ D := by
    dsimp [D]
    linarith
  have hbudget1 : ((k : ℤ) + 1) * |c| + ((H : ℤ) + 1) + D ≤ (k : ℤ) * D := by
    have hc := mul_nonneg (by omega : 0 ≤ (k : ℤ) - 2) hD
    nlinarith
  have hbudget : (H : ℤ) * |c| + |c| + (trace k a : ℤ) * ((H : ℤ) + 1 + D) ≤ (H : ℤ) * D := by
    have hsmall := mul_nonneg (by omega : 0 ≤ (trace k a : ℤ) - 1) (abs_nonneg c)
    have hcost : (H : ℤ) * |c| + |c| ≤ (trace k a : ℤ) * ((k : ℤ) + 1) * |c| := by
      rw [hHcast]
      nlinarith
    calc
      _ ≤ (trace k a : ℤ) * (((k : ℤ) + 1) * |c| + ((H : ℤ) + 1) + D) := by
        nlinarith [hcost]
      _ ≤ (trace k a : ℤ) * ((k : ℤ) * D) := mul_le_mul_of_nonneg_left hbudget1 (by omega)
      _ = (H : ℤ) * D := by rw [hHcast]; ring
  have hbound (n : ℕ) : |discrepancy k a A n| ≤ D := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N
      · have hs : |discrepancy k a A n| ≤ E :=
          single_le_sum (fun i _ => abs_nonneg (discrepancy k a A i)) (mem_range.mpr hn)
        apply hs.trans
        dsimp [D]
        have hnon := mul_nonneg (by omega : 0 ≤ (k : ℤ) + 1) (abs_nonneg c)
        linarith
      · have hnlarge : 4 * (k * trace k a) + 4 ≤ n := by
          change ¬n < 4 * (k * trace k a) + 4 at hn
          omega
        let b := n - 1
        have hbn : b + 1 = n := by dsimp [b]; omega
        let t : Fin k → ℕ := fun j => rank A (B (k * b + j.val + 1))
        let z : Fin k → ℤ := fun j =>
          (H : ℤ) * (t j : ℤ) - ((k * b + j.val + 1 : ℕ) : ℤ)
        have hz (j : Fin k) : -((H : ℤ) + 1 + D) ≤ z j ∧ z j ≤ (H : ℤ) + 1 + D := by
          have hprev : t j + 1 < n := earlier_rank h hk ha n hnlarge j
          have ht1 := abs_le.mp (ih (t j + 1) hprev)
          have ht0 := abs_le.mp (ih (t j) (by omega))
          have hinv := inverse_residual h (k * b + j.val)
          change (H : ℤ) * (t j : ℤ) + discrepancy k a A (t j) < ((k * b + j.val + 1 : ℕ) : ℤ) ∧ ((k * b + j.val + 1 : ℕ) : ℤ) <
              (H : ℤ) * (t j : ℤ) + ((H : ℤ) + 1) + discrepancy k a A (t j + 1) at hinv
          dsimp only [z]
          push_cast at hinv ⊢
          constructor <;> linarith
        have htcast : (∑ j : Fin k, (a j : ℤ)) = (trace k a : ℤ) := by
          simp [trace]
        have hlo : -(trace k a : ℤ) * ((H : ℤ) + 1 + D) ≤ ∑ j : Fin k, (a j : ℤ) * z j := by
          calc
            _ = ∑ j : Fin k, (a j : ℤ) * (-((H : ℤ) + 1 + D)) := by
              rw [← sum_mul, htcast]; ring
            _ ≤ _ := sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hz j).1 (by positivity))
        have hhi : (∑ j : Fin k, (a j : ℤ) * z j) ≤ (trace k a : ℤ) * ((H : ℤ) + 1 + D) := by
          calc
            _ ≤ ∑ j : Fin k, (a j : ℤ) * ((H : ℤ) + 1 + D) := sum_le_sum (fun j _ =>
                mul_le_mul_of_nonneg_left (hz j).2 (by positivity))
            _ = _ := by rw [← sum_mul, htcast]
        have hb := discrepancy_balance h b
        rw [hbn] at hb
        have hb' : (H : ℤ) * discrepancy k a A n = (H : ℤ) * c + c + ∑ j : Fin k, (a j : ℤ) * z j := by
          simpa only [H, c, t, z, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hb
        have hcl := mul_le_mul_of_nonneg_left (neg_abs_le c) hH.le
        have hcu := mul_le_mul_of_nonneg_left (le_abs_self c) hH.le
        have hc0 := neg_abs_le c
        have hc1 := le_abs_self c
        apply abs_le.mpr
        constructor <;> nlinarith
  refine ⟨D.toNat, ?_⟩
  intro n
  rw [Int.toNat_of_nonneg hD]
  exact hbound n

/-- Standard base-b digits, most significant first. The remainder operation is
only a total coercion into Fin b; standard digits already lie below b. -/
def msfDigits (b : ℕ) (hb : 0 < b) (n : ℕ) : List (Fin b) := (Nat.digits b n).reverse.map (fun d => ⟨d % b, Nat.mod_lt d hb⟩)
private def value (b : ℕ) (w : List (Fin b)) : ℕ := w.foldl (fun n r => b * n + r.val) 0

private theorem value_ofDigits (b : ℕ) (w : List (Fin b)) : value b w = Nat.ofDigits b (w.map Fin.val).reverse := by
  unfold value
  rw [List.foldl_eq_foldr_reverse, Nat.ofDigits_eq_foldr, ← List.map_reverse, List.foldr_map]
  congr 1
  funext r n
  simp only [Function.comp_def, Nat.cast_id]
  omega
private theorem value_msfDigits (b : ℕ) (hb : 1 < b) (n : ℕ) : value b (msfDigits b (by omega) n) = n := by
  have hm : (msfDigits b (by omega) n).map Fin.val = (Nat.digits b n).reverse := by
    calc
      _ = (Nat.digits b n).reverse.map (fun d => d % b) := by
        simp only [msfDigits, List.map_map, Function.comp_def]
      _ = (Nat.digits b n).reverse.map id := by
        apply List.map_congr_left
        intro d hd
        exact Nat.mod_eq_of_lt (Nat.digits_lt_base hb (List.mem_reverse.mp hd))
      _ = _ := List.map_id _
  rw [value_ofDigits, hm, List.reverse_reverse, Nat.ofDigits_digits]

/-- A finite native output automaton computes the entire sequence on standard
MSF digits. At zero the empty standard expansion reads the auxiliary term. -/
def Automatic (b : ℕ) (hb : 1 < b) (f : ℕ → ℤ) : Prop := ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : DFAO (Fin b) ℤ Q,
    ∀ n, M.evalOutput (msfDigits b (by omega) n) = f n
private theorem automatic_of_finite_features {b : ℕ} (hb : 1 < b) {V : Type} [Finite V] (s : ℕ → V) (out : V → ℤ) (f : ℕ → ℤ)
    (hout : ∀ n, out (s n) = f n) (hstep : ∀ n m (r : Fin b), s n = s m → s (b * n + r.val) = s (b * m + r.val)) : Automatic b hb f := by
  classical
  let Q := Set.range s
  letI : Fintype Q := Fintype.ofFinite Q
  let st (n : ℕ) : Q := ⟨s n, n, rfl⟩
  let repr (q : Q) := Classical.choose q.property
  have hrepr (q : Q) : s (repr q) = q.val := Classical.choose_spec q.property
  let M : DFAO (Fin b) ℤ Q := {
    step := fun q r => st (b * repr q + r.val)
    start := st 0
    accept := ∅
    output := fun q => out q.val }
  have htrans (n : ℕ) (r : Fin b) : M.step (st n) r = st (b * n + r.val) := by
    apply Subtype.ext
    exact hstep (repr (st n)) n r (hrepr (st n))
  have heval (w : List (Fin b)) (n : ℕ) : M.toDFA.evalFrom (st n) w = st (w.foldl (fun m r => b * m + r.val) n) := by
    induction w generalizing n with
    | nil => rfl
    | cons r w ih =>
      change M.toDFA.evalFrom (M.step (st n) r) w = _
      rw [htrans]
      exact ih _
  refine ⟨Q, inferInstance, M, ?_⟩
  intro n
  change out (M.toDFA.evalFrom (st 0) (msfDigits b (by omega) n)).val = f n
  rw [heval]
  change out (s (value b (msfDigits b (by omega) n))) = f n
  rw [value_msfDigits b hb n, hout n]

private def padded (f : ℕ → ℤ) (n : ℤ) : ℤ := if 0 ≤ n then f n.toNat else 0
private theorem padded_nat (f : ℕ → ℤ) (n : ℕ) : padded f n = f n := by simp [padded]

private theorem inverse_monotone (A : ℕ → ℕ) (hA : StrictMono A) : Monotone (fun n : ℕ => (A n : ℤ) - n) := by
  apply monotone_nat_of_le_succ
  intro n
  have hh : (A n : ℤ) < A (n + 1) := by exact_mod_cast hA (Nat.lt_succ_self n)
  push_cast
  omega
private theorem inverse_unique (A : ℕ → ℕ) (hA : StrictMono A) (t u : ℕ) (m : ℤ) (ht : (A t : ℤ) - t < m ∧ m ≤ (A (t + 1) : ℤ) - (t + 1))
    (hu : (A u : ℤ) - u < m ∧ m ≤ (A (u + 1) : ℤ) - (u + 1)) : t = u := by
  have hmono := inverse_monotone A hA
  rcases lt_trichotomy t u with h | h | h
  · have hh := hmono (show t + 1 ≤ u by omega)
    push_cast at hh
    omega
  · exact h
  · have hh := hmono (show u + 1 ≤ t by omega)
    push_cast at hh
    omega

private theorem automatic_of_local_window (b : ℕ) (hb : 1 < b) (f : ℕ → ℤ) (D Q R : ℕ) (hbound : ∀ n, |f n| ≤ (D : ℤ))
    (hlocal : ∀ q p : ℕ, Q ≤ q → Q ≤ p → ∀ r : Fin b, (∀ z : ℤ, |z| ≤ (R : ℤ) → padded f ((q : ℤ) + z) = padded f ((p : ℤ) + z)) →
      f (b * q + r.val) = f (b * p + r.val)) : Automatic b hb f := by
  classical
  let L : ℕ := 2 * b * (R + 2)
  let M : ℕ := Q + L + 2
  let J := Set.Icc (-(L : ℤ)) (L : ℤ)
  let V := Set.Icc (-(D : ℤ)) (D : ℤ)
  letI : Fintype J := (Set.finite_Icc (-(L : ℤ)) (L : ℤ)).fintype
  letI : Fintype V := (Set.finite_Icc (-(D : ℤ)) (D : ℤ)).fintype
  have hpadded (x : ℤ) : -(D : ℤ) ≤ padded f x ∧ padded f x ≤ D := by
    unfold padded
    split_ifs with hx
    · exact abs_le.mp (hbound x.toNat)
    · constructor <;> omega
  let s (n : ℕ) : Fin (M + 1) × (J → V) := (⟨min n M, by omega⟩, fun z => ⟨padded f ((n : ℤ) + z.val), hpadded _⟩)
  let zeroJ : J := ⟨0, by dsimp [J]; constructor <;> omega⟩
  let out (v : Fin (M + 1) × (J → V)) : ℤ := (v.2 zeroJ).val
  apply automatic_of_finite_features hb s out f
  · intro n
    dsimp [out, s, zeroJ]
    simpa only [add_zero] using padded_nat f n
  · intro n m r heq
    have hcap : min n M = min m M := congrArg (fun v => v.1.val) heq
    by_cases hn : n < M
    · have hm : m < M := by omega
      have hnm : n = m := by
        simpa only [min_eq_left hn.le, min_eq_left hm.le] using hcap
      subst m
      rfl
    have hnm : M ≤ n ∧ M ≤ m := by omega
    have hwin (z : ℤ) (hz : |z| ≤ (L : ℤ)) : padded f ((n : ℤ) + z) = padded f ((m : ℤ) + z) :=
      congrArg (fun v => (v.2 (⟨z, abs_le.mp hz⟩ : J)).val) heq
    apply Prod.ext
    · apply Fin.ext
      have hnchild : M ≤ b * n + r.val := by
        have := Nat.le_mul_of_pos_left n (by omega : 0 < b)
        omega
      have hmchild : M ≤ b * m + r.val := by
        have := Nat.le_mul_of_pos_left m (by omega : 0 < b)
        omega
      exact (min_eq_right hnchild).trans (min_eq_right hmchild).symm
    · funext z
      apply Subtype.ext
      change padded f (((b * n + r.val : ℕ) : ℤ) + z.val) = padded f (((b * m + r.val : ℕ) : ℤ) + z.val)
      let x : ℤ := (r.val : ℤ) + z.val
      let t : ℤ := x / (b : ℤ)
      have hbZ : (0 : ℤ) < b := by exact_mod_cast (by omega : 0 < b)
      have hrem0 : 0 ≤ x % (b : ℤ) := Int.emod_nonneg _ (by omega)
      have hrem1 : x % (b : ℤ) < b := Int.emod_lt_of_pos _ hbZ
      let d : Fin b := ⟨(x % (b : ℤ)).toNat, by omega⟩
      have hdcast : (d.val : ℤ) = x % (b : ℤ) := Int.toNat_of_nonneg hrem0
      have hL : (2 : ℤ) * R ≤ L := by
        dsimp [L]
        push_cast
        nlinarith
      have hC : (0 : ℤ) ≤ L - (R : ℤ) := by omega
      have hbc : (L : ℤ) ≤ (b : ℤ) * ((L : ℤ) - R) := by
        calc
          (L : ℤ) ≤ 2 * ((L : ℤ) - R) := by omega
          _ ≤ (b : ℤ) * ((L : ℤ) - R) := mul_le_mul_of_nonneg_right (by exact_mod_cast hb) hC
      have hx : -(L : ℤ) ≤ x ∧ x ≤ (L : ℤ) + b - 1 := by
        have hz : -(L : ℤ) ≤ z.val ∧ z.val ≤ L := z.property
        have hr := r.isLt
        dsimp [x]
        constructor <;> omega
      have ht : -(L : ℤ) + R ≤ t ∧ t ≤ (L : ℤ) - R := by
        constructor
        · apply (Int.le_ediv_iff_mul_le hbZ).mpr
          nlinarith [hx.1]
        · apply (Int.ediv_le_iff_le_mul hbZ).mpr
          nlinarith [hx.2]
      have hnZ : (Q : ℤ) + L + 2 ≤ n := by exact_mod_cast hnm.1
      have hmZ : (Q : ℤ) + L + 2 ≤ m := by exact_mod_cast hnm.2
      let q : ℕ := ((n : ℤ) + t).toNat
      let p : ℕ := ((m : ℤ) + t).toNat
      have hqcast : (q : ℤ) = (n : ℤ) + t := Int.toNat_of_nonneg (by omega)
      have hpcast : (p : ℤ) = (m : ℤ) + t := Int.toNat_of_nonneg (by omega)
      have hq : Q ≤ q := by omega
      have hp : Q ≤ p := by omega
      have hdiv : (b : ℤ) * t + x % (b : ℤ) = x := Int.mul_ediv_add_emod x b
      have hidxn : ((b * n + r.val : ℕ) : ℤ) + z.val = (b * q + d.val : ℕ) := by
        push_cast
        rw [hqcast, hdcast]
        dsimp [x] at hdiv
        nlinarith
      have hidxm : ((b * m + r.val : ℕ) : ℤ) + z.val = (b * p + d.val : ℕ) := by
        push_cast
        rw [hpcast, hdcast]
        dsimp [x] at hdiv
        nlinarith
      rw [hidxn, hidxm, padded_nat, padded_nat]
      apply hlocal q p hq hp d
      intro w hw
      have htw : |t + w| ≤ (L : ℤ) := by
        have hw' := abs_le.mp hw
        apply abs_le.mpr
        constructor <;> omega
      have hh := hwin (t + w) htw
      rw [hqcast, hpcast]
      simpa only [add_assoc] using hh


private theorem block_index_value {k : ℕ} {a : Fin k → ℕ} (hk : 1 < k) (ha : ∀ j, 0 < a j) (q : ℕ) (hq : 1 ≤ q)
    (r : Fin (trace k a)) (j : Fin k) : ((k * (trace k a * q + r.val - 1) + j.val + 1 : ℕ) : ℤ) = (k * trace k a : ℕ) * (q : ℤ) +
        ((k : ℤ) * ((r.val : ℤ) - 1) + j.val + 1) := by
  have ht := trace_ge k a ha
  have hn : 1 ≤ trace k a * q + r.val := by nlinarith
  have hs : ((trace k a * q + r.val - 1 : ℕ) : ℤ) = ((trace k a * q + r.val : ℕ) : ℤ) - 1 := by
    have hnat := Nat.sub_add_cancel hn
    have hv : ((trace k a * q + r.val - 1 : ℕ) : ℤ) + 1 = ((trace k a * q + r.val : ℕ) : ℤ) := by exact_mod_cast hnat
    omega
  push_cast
  rw [hs]
  push_cast
  ring

private def windowRadius (k : ℕ) (a : Fin k → ℕ) (D : ℕ) : ℕ := D + 2 * slope k a + k + 2

private theorem rank_offset_bound {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (D : ℕ) (hD : ∀ n, |discrepancy k a A n| ≤ (D : ℤ)) (q : ℕ) (hq : 1 ≤ q) (r : Fin (trace k a)) (j : Fin k) :
    |(rank A (B (k * (trace k a * q + r.val - 1) + j.val + 1)) : ℤ) - q| ≤ (windowRadius k a D : ℤ) := by
  let H := k * trace k a
  let t := rank A (B (k * (trace k a * q + r.val - 1) + j.val + 1))
  let u : ℤ := (k : ℤ) * ((r.val : ℤ) - 1) + j.val + 1
  let s : ℤ := (t : ℤ) - q
  have ht := trace_ge k a ha
  have hH : (1 : ℤ) ≤ H := by
    dsimp [H]
    exact_mod_cast (show 1 ≤ k * trace k a by nlinarith)
  have hHcast : (H : ℤ) = (k : ℤ) * trace k a := by simp [H]
  have hr : (r.val : ℤ) < trace k a := by exact_mod_cast r.isLt
  have hj : (j.val : ℤ) < k := by exact_mod_cast j.isLt
  have hupper := mul_le_mul_of_nonneg_left (show (r.val : ℤ) ≤ (trace k a : ℤ) - 1 by omega) (show (0 : ℤ) ≤ k by positivity)
  have hlower : (0 : ℤ) ≤ (k : ℤ) * r.val := by positivity
  have hu : -(H : ℤ) ≤ u ∧ u ≤ H := by
    dsimp [u]
    rw [hHcast]
    constructor <;> nlinarith
  have hinv := inverse_residual h (k * (trace k a * q + r.val - 1) + j.val)
  have hd0 := abs_le.mp (hD t)
  have hd1 := abs_le.mp (hD (t + 1))
  have hindex := block_index_value hk ha q hq r j
  change (H : ℤ) * (t : ℤ) + discrepancy k a A t < ((k * (trace k a * q + r.val - 1) + j.val + 1 : ℕ) : ℤ) ∧
    ((k * (trace k a * q + r.val - 1) + j.val + 1 : ℕ) : ℤ) < (H : ℤ) * (t : ℤ) + ((H : ℤ) + 1) + discrepancy k a A (t + 1) at hinv
  change ((k * (trace k a * q + r.val - 1) + j.val + 1 : ℕ) : ℤ) = (H : ℤ) * (q : ℤ) + u at hindex
  have hres : -((H : ℤ) + 1 + D) + u ≤ (H : ℤ) * s ∧ (H : ℤ) * s ≤ u + D := by
    dsimp [s]
    constructor <;> linarith
  have hS : (windowRadius k a D : ℤ) = (D : ℤ) + 2 * ((H : ℤ) + 1) + k + 2 := by
    simp only [windowRadius, slope, H, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  change |s| ≤ (windowRadius k a D : ℤ)
  apply abs_le.mpr
  constructor
  · by_cases hs : 0 ≤ s
    · omega
    · have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (H : ℤ) - 1 by omega)
        (show s ≤ 0 by omega)
      nlinarith
  · by_cases hs : s ≤ 0
    · omega
    · have hmul := mul_nonneg (show 0 ≤ (H : ℤ) - 1 by omega) (show 0 ≤ s by omega)
      nlinarith

private theorem rank_interval {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (m : ℕ) : let t := rank A (B (m + 1))
    (A t : ℤ) - t < (m + 1 : ℕ) ∧ (m + 1 : ℕ) ≤ (A (t + 1) : ℤ) - (t + 1) := by
  dsimp only
  have hr := source_rank h m
  have hB : (B (m + 1) : ℤ) = (m : ℤ) + 1 + rank A (B (m + 1)) := by
    exact_mod_cast hr.1
  have hl : (A (rank A (B (m + 1))) : ℤ) < B (m + 1) := by
    exact_mod_cast hr.2.1
  have hu : (B (m + 1) : ℤ) < A (rank A (B (m + 1)) + 1) := by
    exact_mod_cast hr.2.2
  push_cast
  constructor <;> omega

private theorem discrepancy_inverse (k : ℕ) (a : Fin k → ℕ) (A : ℕ → ℕ) (t : ℕ) :
    (A t : ℤ) - t = (k * trace k a : ℕ) * (t : ℤ) + discrepancy k a A t := by
  unfold discrepancy slope
  push_cast
  ring


private theorem local_rank_offset {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (D : ℕ) (hD : ∀ n, |discrepancy k a A n| ≤ (D : ℤ)) (q p : ℕ) (hq : windowRadius k a D + 1 ≤ q)
    (hp : windowRadius k a D + 1 ≤ p) (r : Fin (trace k a)) (hwin : ∀ z : ℤ, |z| ≤ (windowRadius k a D + 1 : ℕ) →
      padded (discrepancy k a A) ((q : ℤ) + z) = padded (discrepancy k a A) ((p : ℤ) + z)) (j : Fin k) :
    (rank A (B (k * (trace k a * q + r.val - 1) + j.val + 1)) : ℤ) - q =
      (rank A (B (k * (trace k a * p + r.val - 1) + j.val + 1)) : ℤ) - p := by
  let H := k * trace k a
  let m1 := k * (trace k a * q + r.val - 1) + j.val + 1
  let m2 := k * (trace k a * p + r.val - 1) + j.val + 1
  let t1 := rank A (B m1)
  let t2 := rank A (B m2)
  let s : ℤ := (t1 : ℤ) - q
  have hs : |s| ≤ (windowRadius k a D : ℤ) := rank_offset_bound h hk ha D hD q (by omega) r j
  have hs' := abs_le.mp hs
  have hpZ : (windowRadius k a D : ℤ) + 1 ≤ p := by exact_mod_cast hp
  have hnonneg : 0 ≤ (p : ℤ) + s := by omega
  let t : ℕ := ((p : ℤ) + s).toNat
  have htcast : (t : ℤ) = (p : ℤ) + s := Int.toNat_of_nonneg hnonneg
  have hqcast : (q : ℤ) + s = (t1 : ℤ) := by dsimp [s]; ring
  have hs1 : |s + 1| ≤ (windowRadius k a D + 1 : ℕ) := by
    push_cast
    apply abs_le.mpr
    constructor <;> omega
  have he0 : discrepancy k a A t1 = discrepancy k a A t := by
    have hh := hwin s (by push_cast; omega)
    rw [hqcast, ← htcast, padded_nat, padded_nat] at hh
    exact hh
  have he1 : discrepancy k a A (t1 + 1) = discrepancy k a A (t + 1) := by
    have hh := hwin (s + 1) hs1
    have hq1 : (q : ℤ) + (s + 1) = (t1 + 1 : ℕ) := by
      push_cast
      omega
    have hp1 : (p : ℤ) + (s + 1) = (t + 1 : ℕ) := by
      push_cast
      omega
    rw [hq1, hp1, padded_nat, padded_nat] at hh
    exact hh
  have hshift : (t : ℤ) - p = (t1 : ℤ) - q := by
    rw [htcast]
    dsimp [s]
    ring
  have hmult := congrArg (fun z : ℤ => (H : ℤ) * z) hshift
  have hi1 := block_index_value hk ha q (by omega) r j
  have hi2 := block_index_value hk ha p (by omega) r j
  change (m1 : ℤ) = (H : ℤ) * (q : ℤ) + _ at hi1
  change (m2 : ℤ) = (H : ℤ) * (p : ℤ) + _ at hi2
  have hdelt0 : (A t : ℤ) - t - m2 = (A t1 : ℤ) - t1 - m1 := by
    rw [discrepancy_inverse, discrepancy_inverse, ← he0]
    linarith only [hmult, hi1, hi2]
  have hdelt1 : (A (t + 1) : ℤ) - (t + 1) - m2 = (A (t1 + 1) : ℤ) - (t1 + 1) - m1 := by
    have hd1 := discrepancy_inverse k a A (t + 1)
    have hd2 := discrepancy_inverse k a A (t1 + 1)
    push_cast at hd1 hd2
    change _ = (H : ℤ) * ((t : ℤ) + 1) + _ at hd1
    change _ = (H : ℤ) * ((t1 : ℤ) + 1) + _ at hd2
    linarith only [hmult, hi1, hi2, hd1, hd2, he1]
  have hI1 := rank_interval h (k * (trace k a * q + r.val - 1) + j.val)
  have hI2 := rank_interval h (k * (trace k a * p + r.val - 1) + j.val)
  change (A t1 : ℤ) - t1 < (m1 : ℤ) ∧ (m1 : ℤ) ≤ (A (t1 + 1) : ℤ) - (t1 + 1) at hI1
  change (A t2 : ℤ) - t2 < (m2 : ℤ) ∧ (m2 : ℤ) ≤ (A (t2 + 1) : ℤ) - (t2 + 1) at hI2
  have hIt : (A t : ℤ) - t < (m2 : ℤ) ∧ (m2 : ℤ) ≤ (A (t + 1) : ℤ) - (t + 1) := by
    constructor <;> linarith only [hI1.1, hI1.2, hdelt0, hdelt1]
  have hteq : t = t2 := inverse_unique A h.monoA t t2 (m2 : ℤ) hIt hI2
  rw [hteq] at hshift
  exact hshift.symm

private theorem source_local {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j)
    (D : ℕ) (hD : ∀ n, |discrepancy k a A n| ≤ (D : ℤ)) (q p : ℕ) (hq : windowRadius k a D + 1 ≤ q)
    (hp : windowRadius k a D + 1 ≤ p) (r : Fin (trace k a)) (hwin : ∀ z : ℤ, |z| ≤ (windowRadius k a D + 1 : ℕ) →
      padded (discrepancy k a A) ((q : ℤ) + z) = padded (discrepancy k a A) ((p : ℤ) + z)) : discrepancy k a A (trace k a * q + r.val) =
      discrepancy k a A (trace k a * p + r.val) := by
  let n1 := trace k a * q + r.val
  let n2 := trace k a * p + r.val
  let t1 : Fin k → ℕ := fun j => rank A (B (k * (n1 - 1) + j.val + 1))
  let t2 : Fin k → ℕ := fun j => rank A (B (k * (n2 - 1) + j.val + 1))
  have hsum : (∑ j : Fin k, (a j : ℤ) * (t1 j : ℤ)) - (∑ j : Fin k, (a j : ℤ) * (t2 j : ℤ)) = (trace k a : ℤ) * ((q : ℤ) - p) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ j : Fin k, (a j : ℤ) * ((q : ℤ) - p) := by
        apply sum_congr rfl
        intro j _
        have ho := local_rank_offset h hk ha D hD q p hq hp r hwin j
        change (t1 j : ℤ) - q = (t2 j : ℤ) - p at ho
        have hm := congrArg (fun z : ℤ => (a j : ℤ) * z) ho
        linarith only [hm]
      _ = _ := by rw [← sum_mul]; simp only [trace, Nat.cast_sum]
  have ht := trace_ge k a ha
  have hn1 : 1 ≤ n1 := by dsimp [n1]; nlinarith
  have hn2 : 1 ≤ n2 := by dsimp [n2]; nlinarith
  have hf1 := discrepancy_formula h (n1 - 1)
  have hf2 := discrepancy_formula h (n2 - 1)
  rw [Nat.sub_add_cancel hn1] at hf1
  rw [Nat.sub_add_cancel hn2] at hf2
  change discrepancy k a A n1 = constantTerm k a + (∑ j : Fin k, (a j : ℤ) * (t1 j : ℤ)) - (((n1 - 1 : ℕ) : ℤ) + 1) at hf1
  change discrepancy k a A n2 = constantTerm k a + (∑ j : Fin k, (a j : ℤ) * (t2 j : ℤ)) - (((n2 - 1 : ℕ) : ℤ) + 1) at hf2
  have hsub1 : ((n1 - 1 : ℕ) : ℤ) + 1 = n1 := by exact_mod_cast Nat.sub_add_cancel hn1
  have hsub2 : ((n2 - 1 : ℕ) : ℤ) + 1 = n2 := by exact_mod_cast Nat.sub_add_cancel hn2
  rw [hsub1] at hf1
  rw [hsub2] at hf2
  have hn1cast : (n1 : ℤ) = (trace k a : ℤ) * q + r.val := by
    simp only [n1, Nat.cast_add, Nat.cast_mul]
  have hn2cast : (n2 : ℤ) = (trace k a : ℤ) * p + r.val := by
    simp only [n2, Nat.cast_add, Nat.cast_mul]
  change discrepancy k a A n1 = discrepancy k a A n2
  linarith only [hf1, hf2, hsum, hn1cast, hn2cast]

private theorem source_automatic {k : ℕ} {a : Fin k → ℕ} {A B : ℕ → ℕ} (h : Source k a A B) (hk : 1 < k) (ha : ∀ j, 0 < a j) :
    Automatic (trace k a) (by have := trace_ge k a ha; omega) (discrepancy k a A) := by
  obtain ⟨D, hD⟩ := discrepancy_bounded h hk ha
  apply automatic_of_local_window (trace k a) (by have := trace_ge k a ha; omega)
    (discrepancy k a A) D (windowRadius k a D + 1) (windowRadius k a D + 1) hD
  exact source_local h hk ha D hD

/-- The entire positive-coefficient anti-recurrence family has a unique
complementary source and a finite automaton for its exact discrepancy. -/
theorem result (k : ℕ) (a : Fin k → ℕ) (hk : 1 < k) (ha : ∀ j, 0 < a j) : ∃ A B : ℕ → ℕ, Source k a A B ∧
      (∀ A' B', Source k a A' B' → A' = A ∧ B' = B) ∧ Automatic (trace k a) (by have := trace_ge k a ha; omega) (discrepancy k a A) := by
  let A := constructedA k a
  let B := constructedB k a
  have h := constructed_source k a hk ha
  refine ⟨A, B, h, ?_, source_automatic h hk ha⟩
  intro A' B' h'
  have hu := source_unique k a hk ha A' B' h'
  exact ⟨hu.1.symm, hu.2.symm⟩

#print axioms result
#check result

end D5.S1.Recurrence.AntiRecurrenceAutomaticity

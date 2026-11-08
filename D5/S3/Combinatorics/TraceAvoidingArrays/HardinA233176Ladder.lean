/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Barker's integer generating function for the normalized three-row exclusion ladder. -/

/-
admission_basis: open-problem-resolution (#28235; Proved)
escape_witness: none
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-! Three rows with horizontal and diagonal complementary-pair exclusion. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder

open HardinA233175PairStrip
  (Seen allowed advance good finish finish_fst finish_snd good_iff edge_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

private abbrev Col := Fin 3 → Fin 6
private abbrev Labels := Fin 3 → Fin 3

private def seen (s : Fin 3) : Seen := (decide (0 < s.val), decide (1 < s.val))

private def next (s : Fin 3) (x : Fin 6) : Fin 3 :=
  max s (if x = 1 then 1 else if x = 2 then 2 else 0)

private instance instDecidableAllowed (s : Seen) (x : Fin 6) : Decidable (allowed s x) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → _)))

private instance instDecidableGood {n : ℕ} (s : Seen) (f : Fin n → Fin 6) :
    Decidable (good s f) := by
  induction n generalizing s with
  | zero => exact isTrue trivial
  | succ n ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)

private theorem advance_seen : ∀ s x, allowed (seen s) x →
    advance (seen s) x = seen (next s x) := by
  decide +kernel

private theorem next_mono (s : Fin 3) (x : Fin 6) : s ≤ next s x := le_max_left _ _

private theorem label_next : ∀ s x, allowed (seen s) x → beta x ≤ next s x := by
  decide +kernel

private def endLevel : {n : ℕ} → Fin 3 → (Fin n → Fin 6) → Fin 3
  | 0, s, _ => s
  | _ + 1, s, f => endLevel (next s (f 0)) (Fin.tail f)

private theorem endLevel_mono {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6) :
    s ≤ endLevel s f := by
  induction n generalizing s with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (next_mono s (f 0)) (ih _ _)

private theorem finish_seen {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6)
    (h : good (seen s) f) : finish (seen s) f = seen (endLevel s f) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change allowed (seen s) (f 0) ∧
      good (advance (seen s) (f 0)) (Fin.tail f) at h
    rw [finish, advance_seen s (f 0) h.1]
    exact ih _ _ (by simpa only [advance_seen s (f 0) h.1] using h.2)

private def normal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)

private theorem earlier_iff {n : ℕ} (A : Fin 3 × Fin n → Fin 6)
    (r : Fin 3) (j : Fin n) (d : Fin 6) :
    (∃ q, q.1.val * n + q.2.val < r.val * n + j.val ∧ A q = d) ↔
      (∃ s k, s < r ∧ A (s, k) = d) ∨ ∃ k, k < j ∧ A (r, k) = d := by
  have he (s : Fin 3) (k : Fin n) :
      s.val * n + k.val < r.val * n + j.val ↔ s < r ∨ s = r ∧ k < j := by
    fin_cases s <;> fin_cases r <;> simp only [Fin.lt_def, Fin.ext_iff] <;>
      simp only [Fin.reduceFinMk] <;> omega
  simp only [Prod.exists, he]
  constructor
  · rintro ⟨s, k, (hs | ⟨rfl, hk⟩), hd⟩
    · exact Or.inl ⟨s, k, hs, hd⟩
    · exact Or.inr ⟨k, hk, hd⟩
  · rintro (⟨s, k, hs, hd⟩ | ⟨k, hk, hd⟩)
    · exact ⟨s, k, Or.inl hs, hd⟩
    · exact ⟨r, k, Or.inr ⟨rfl, hk⟩, hd⟩

private theorem normal_iff {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    normal A ↔ good (false, false) (fun j => A (0, j)) ∧
      good (finish (false, false) (fun j => A (0, j))) (fun j => A (1, j)) ∧
      good (finish (finish (false, false) (fun j => A (0, j)))
        (fun j => A (1, j))) (fun j => A (2, j)) := by
  simp only [normal, good_iff, earlier_iff, finish_fst, finish_snd]
  simp only [Bool.false_eq_true, false_or]
  have hr (r : Fin 3) (d : Fin 6) :
      (∃ s k, s < r ∧ A (s, k) = d) ↔
        (r = 1 ∧ ∃ k, A (0, k) = d) ∨
        (r = 2 ∧ (∃ k, A (0, k) = d) ∨ ∃ k, A (1, k) = d) := by
    fin_cases r <;> simp [Fin.exists_fin_succ]
  simp_rw [hr]
  constructor
  · intro h
    exact ⟨by simpa using fun j => h (0, j),
      by simpa [or_assoc] using fun j => h (1, j),
      by simpa [or_assoc] using fun j => h (2, j)⟩
  · rintro ⟨ht, hm, hb⟩ ⟨r, j⟩
    fin_cases r
    · simpa using ht j
    · simpa [or_assoc] using hm j
    · simpa [or_assoc] using hb j

private def Legal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
    (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 3),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      A (r, j) ≠ A (s, ⟨j.val + 1, h⟩) ∧
        (A (r, j)).val + (A (s, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A

private instance instDecidableNormal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    Decidable (normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _)))

private instance instDecidableLegal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Literal filtered count; the first-cell existential sets the empty coefficient to zero. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 3 × Fin n → Fin 6 => Legal A)).card

private def pairs (c : Col) : Labels := fun i => beta (c i)

private def compatible (p : Labels) (c : Col) : Prop :=
  ∀ r s : Fin 3, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) → beta (c s) ≠ p r

private instance instDecidableCompatible (p : Labels) (c : Col) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _ _, _ → _))

private theorem bonds_iff (c d : Col) :
    (∀ r s : Fin 3, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      c r ≠ d s ∧ (c r).val + (d s).val ≠ 5) ↔ compatible (pairs c) d := by
  have he (x y : Fin 6) : (x ≠ y ∧ x.val + y.val ≠ 5) ↔ beta y ≠ beta x := by
    have hh := edge_iff (fun _ => x) (fun _ => y)
    change (∀ _r _s : Fin 2, x ≠ y ∧ x.val + y.val ≠ 5) ↔
      (∀ _r : Fin 2, beta y ≠ beta x ∧ beta y ≠ beta x) at hh
    simpa only [Fin.forall_fin_two, and_self] using hh
  simp only [he, compatible, pairs]

private def chain : {n : ℕ} → Labels → (Fin n → Col) → Prop
  | 0, _, _ => True
  | _ + 1, p, f => compatible p (f 0) ∧ chain (pairs (f 0)) (Fin.tail f)

private theorem chain_tail {n : ℕ} (f : Fin (n + 1) → Col) :
    chain (pairs (f 0)) (Fin.tail f) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simpa [chain, Fin.tail, Fin.forall_fin_succ] using
      (and_congr_right (fun _ => ih (Fin.tail f)))

private theorem legal_iff {n : ℕ} (f : Fin (n + 1) → Col) :
    Legal (fun p => f p.2 p.1) ↔ f 0 0 = 0 ∧
      good (false, false) (fun j => f j 0) ∧
      good (finish (false, false) (fun j => f j 0)) (fun j => f j 1) ∧
      good (finish (finish (false, false) (fun j => f j 0))
        (fun j => f j 1)) (fun j => f j 2) ∧
      chain (pairs (f 0)) (Fin.tail f) := by
  have hf : (∃ j : Fin (n + 1), j.val = 0 ∧ f j 0 = 0) ↔ f 0 0 = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = 0 from Fin.ext hj] using h
    · exact fun h => ⟨0, rfl, h⟩
  have he : (∀ (j : Fin (n + 1)) (h : j.val + 1 < n + 1) (r s : Fin 3),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      f j r ≠ f ⟨j.val + 1, h⟩ s ∧
        (f j r).val + (f ⟨j.val + 1, h⟩ s).val ≠ 5) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
    simp only [bonds_iff]
    constructor
    · intro h i
      exact h i.castSucc (by simp)
    · intro h j hj
      exact h ⟨j.val, by omega⟩
  rw [Legal, hf, he, normal_iff, ← chain_tail]
  tauto

private def TailGood {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (f : Fin n → Col) : Prop :=
  chain p f ∧ good (seen t) (fun i => f i 0) ∧ good (seen b) (fun i => f i 1) ∧
    good (seen c) (fun i => f i 2) ∧
    endLevel t (fun i => f i 0) = q ∧ endLevel b (fun i => f i 1) = r

private instance instDecidableChain {n : ℕ} (p : Labels) (f : Fin n → Col) :
    Decidable (chain p f) := by
  induction n generalizing p with
  | zero => exact isTrue trivial
  | succ n ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)

private instance instDecidableTailGood {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (f : Fin n → Col) : Decidable (TailGood q r t b c p f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private def admissible (q r t b c : Fin 3) (p : Labels) (d : Col) : Prop :=
  compatible p d ∧ allowed (seen t) (d 0) ∧ allowed (seen b) (d 1) ∧
    allowed (seen c) (d 2) ∧ next t (d 0) ≤ q ∧ next b (d 1) ≤ r

private instance instDecidableAdmissible (q r t b c : Fin 3) (p : Labels) (d : Col) :
    Decidable (admissible q r t b c p d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem tailGood_cons {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (d : Col) (f : Fin n → Col) :
    TailGood q r t b c p (Fin.cons d f) ↔
      admissible q r t b c p d ∧
        TailGood q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) f := by
  simp only [TailGood, chain, good, endLevel, Fin.cons_zero, Fin.tail_cons]
  by_cases ht : allowed (seen t) (d 0)
  · by_cases hb : allowed (seen b) (d 1)
    · by_cases hc : allowed (seen c) (d 2)
      · rw [advance_seen t (d 0) ht, advance_seen b (d 1) hb,
          advance_seen c (d 2) hc]
        have hq := endLevel_mono (next t (d 0)) (fun i => f i 0)
        have hr := endLevel_mono (next b (d 1)) (fun i => f i 1)
        simp only [admissible, ht, hb, hc, true_and]
        constructor
        · rintro ⟨⟨hp, hh⟩, h0, h1, h2, h3, h4⟩
          exact ⟨⟨hp, h3 ▸ hq, h4 ▸ hr⟩, hh, h0.2, h1.2, h2.2, h3, h4⟩
        · rintro ⟨⟨hp, _, _⟩, hh, h0, h1, h2, h3, h4⟩
          exact ⟨⟨hp, hh⟩, ⟨ht, h0⟩, ⟨hb, h1⟩, ⟨hc, h2⟩, h3, h4⟩
      · simp [admissible, hc]
    · simp [admissible, hb]
  · simp [admissible, ht]

private def step (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ)
    (q r t b c : Fin 3) (p : Labels) : ℤ :=
  ∑ d : Col, if admissible q r t b c p d then
    w q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) else 0

private def v : ℕ → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ
  | 0, q, r, t, b, _, _ => if t = q ∧ b = r then 1 else 0
  | k + 1, q, r, t, b, c, p => step (v k) q r t b c p

private def count (n : ℕ) (q r t b c : Fin 3) (p : Labels) : ℤ :=
  ∑ f : Fin n → Col, if TailGood q r t b c p f then 1 else 0

private theorem count_eq_v (n : ℕ) : count n = v n := by
  induction n with
  | zero => funext q r t b c p; simp [count, TailGood, v, good, endLevel, chain]
  | succ n ih =>
    funext q r t b c p
    rw [count, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Col)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ d : Col, ∑ f : Fin n → Col,
      if TailGood q r t b c p (Fin.cons d f) then (1 : ℤ) else 0) = _
    change _ = step (v n) q r t b c p
    rw [← ih]
    unfold step count
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : admissible q r t b c p d <;> simp [tailGood_cons, h]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder

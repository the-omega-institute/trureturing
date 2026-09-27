/- GID: D5/S3/Arith/GreedyFibonacciAverageClosedForm
   generality: G
   mirror-B: D5/B/S3/Arith/GreedyFibonacciAverageClosedForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The greedy sequence whose running averages are Fibonacci takes the conjectured closed form from index ten onwards. -/

import D5.S3.Arith.FriedFibonacciShiftNonFibonacci
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Arith.GreedyFibonacciAverageClosedForm

/-
proof_shape: result: content
escape_witness: the active path carries several intermediate facts, none of them an
  instantiation, projection or normalisation of a pinned upstream statement or of the one
  frozen prerequisite:
  (i) `good_exists`, which produces an admissible value at every step and so makes the
      greedy sequence total;
  (ii) `sum_even` and `sum_odd`, the closed values `(10+2k)F(k+8)` and `(11+2k)F(k+8)` of the
      partial sums;
  (iii) `bound_odd` and `bound_even`, the two inequalities that exclude every smaller
      Fibonacci average;
  (iv) `mem_split` together with `fib_not_mem` and `X_not_mem`, which rule out repetition;
  (v) `step_odd`, `step_even` and `hist_pair`, the two greedy steps and their induction.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result
  (statement_id sha256:43a2c0de0117a748741cfdb8806fe92886cf2e8ac3bcbe66415ac7f171549a05)
-/

/-- `k` is a Fibonacci number. -/
def IsFib (k : ℕ) : Prop := ∃ m, Nat.fib m = k

instance : DecidablePred IsFib := fun k =>
  decidable_of_iff ((List.range (k + 2)).any (fun m => Nat.fib m == k) = true)
    (by
      simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
      constructor
      · rintro ⟨m, -, hm⟩
        exact ⟨m, hm⟩
      · rintro ⟨m, hm⟩
        refine ⟨m, ?_, hm⟩
        have h := Nat.le_fib_add_one m
        rw [hm] at h
        omega)

/-- After the history `L`, the value `v` is admissible at step `n`: it is positive, unused, and
makes the average of the first `n` terms a Fibonacci number. -/
def Good (L : List ℕ) (n v : ℕ) : Prop :=
  0 < v ∧ v ∉ L ∧ n ∣ (L.sum + v) ∧ IsFib ((L.sum + v) / n)

instance (L : List ℕ) (n v : ℕ) : Decidable (Good L n v) := by
  unfold Good
  infer_instance

/-- Every step admits some value, so the greedy rule never stalls. -/
theorem good_exists (L : List ℕ) (n : ℕ) (hn : 0 < n) : ∃ v, Good L n v := by
  have mem_le_sum : ∀ (K : List ℕ) (x : ℕ), x ∈ K → x ≤ K.sum := by
    intro K
    induction K with
    | nil => intro x hx; cases hx
    | cons b t ih =>
      intro x hx
      rw [List.sum_cons]
      rcases List.mem_cons.mp hx with h | h
      · omega
      · have := ih x h
        omega
  set M := L.sum with hM
  have hfib : 2 * M + 1 ≤ Nat.fib (2 * M + 2) := by
    have h := Nat.le_fib_add_one (2 * M + 2)
    omega
  have hbig : 2 * M + 1 ≤ n * Nat.fib (2 * M + 2) :=
    le_trans hfib (Nat.le_mul_of_pos_left _ hn)
  refine ⟨n * Nat.fib (2 * M + 2) - M, ?_, ?_, ?_, ?_⟩
  · omega
  · intro hmem
    have : (n * Nat.fib (2 * M + 2) - M) ≤ M := by
      rw [hM]
      exact mem_le_sum L _ hmem
    omega
  · have : M + (n * Nat.fib (2 * M + 2) - M) = n * Nat.fib (2 * M + 2) := by omega
    rw [this]
    exact Dvd.intro _ rfl
  · have he : M + (n * Nat.fib (2 * M + 2) - M) = n * Nat.fib (2 * M + 2) := by omega
    rw [he, Nat.mul_div_cancel_left _ hn]
    exact ⟨2 * M + 2, rfl⟩

/-- The greedy value at step `n` after history `L`. -/
def nextVal (L : List ℕ) (n : ℕ) : ℕ :=
  if hn : 0 < n then Nat.find (good_exists L n hn) else 0

/-- The first `n` terms of the sequence, in order. -/
def hist : ℕ → List ℕ
  | 0 => []
  | (n + 1) => hist n ++ [nextVal (hist n) (n + 1)]

/-- The sequence of distinct least positive numbers whose running averages are Fibonacci. -/
def a (n : ℕ) : ℕ := nextVal (hist (n - 1)) n

/-- The value taken at an even index, written without subtraction. -/
def X (j : ℕ) : ℕ := Nat.fib (j + 2) + 2 * j * Nat.fib (j + 1)

/-- The first ten terms, as a list. -/
def base10 : List ℕ := [1, 3, 2, 6, 13, 5, 26, 8, 53, 93]

/-- The terms from index eleven onwards, in pairs. -/
def tailList : ℕ → List ℕ
  | 0 => []
  | (k + 1) => tailList k ++ [Nat.fib (k + 8), X (k + 6)]

/-- The closed form conjectured at the end of Section 6 of the source, and with it the two
standing conjectures recorded at the sequence entry.  The even case is written additively so
that no truncated subtraction occurs. -/
def claim : Prop :=
  ∀ n : ℕ, 10 ≤ n →
    (n % 2 = 0 → a n + (n - 1) * Nat.fib (n / 2 + 2) = n * Nat.fib (n / 2 + 3)) ∧
    (n % 2 = 1 → a n = Nat.fib ((n + 1) / 2 + 2))

theorem result : claim := by
  have nve : ∀ {L : List ℕ} {n v : ℕ}, 0 < n → Good L n v →
      (∀ w, w < v → ¬ Good L n w) → nextVal L n = v := by
    intro L n v hn h1 h2
    rw [nextVal, dif_pos hn]
    exact (Nat.find_eq_iff _).mpr ⟨h1, h2⟩
  have fle : ∀ {m t : ℕ}, Nat.fib m < Nat.fib (t + 1) → Nat.fib m ≤ Nat.fib t := by
    intro m t hlt
    by_contra hc
    have hmt : t < m := by
      by_contra hc2
      exact absurd (Nat.fib_mono (show m ≤ t by omega)) (by omega)
    exact absurd (Nat.fib_mono (show t + 1 ≤ m by omega)) (by omega)
  have xmono : ∀ {i j : ℕ}, i < j → X i < X j := by
    intro i j h
    have step : ∀ p : ℕ, X p < X (p + 1) := by
      intro p
      have e0 : X p = Nat.fib (p + 2) + 2 * p * Nat.fib (p + 1) := rfl
      have e1 : X (p + 1) = Nat.fib (p + 3) + 2 * (p + 1) * Nat.fib (p + 2) := by
        unfold X
        rw [show p + 1 + 2 = p + 3 from by omega, show p + 1 + 1 = p + 2 from by omega]
      have h1 : Nat.fib (p + 2) < Nat.fib (p + 3) := by
        have hh := Nat.fib_lt_fib_succ (n := p + 2) (by omega)
        rw [show p + 2 + 1 = p + 3 from by omega] at hh
        exact hh
      have h2 : 2 * p * Nat.fib (p + 1) ≤ 2 * (p + 1) * Nat.fib (p + 2) :=
        Nat.mul_le_mul (by omega) (Nat.fib_mono (by omega))
      omega
    induction j with
    | zero => omega
    | succ p ih =>
      rcases Nat.lt_or_ge i p with hp | hp
      · exact lt_trans (ih hp) (step p)
      · have hip : i = p := by omega
        subst hip
        exact step i

  have keyEven : ∀ k : ℕ, (11 + 2 * k) * Nat.fib (k + 8) + X (k + 6)
      = (12 + 2 * k) * Nat.fib (k + 9) := by
    intro k
    have h9 : Nat.fib (k + 9) = Nat.fib (k + 7) + Nat.fib (k + 8) := by
      rw [show k + 9 = (k + 7) + 2 from by omega, Nat.fib_add_two,
        show (k + 7) + 1 = k + 8 from by omega]
    have hX : X (k + 6) = Nat.fib (k + 8) + 2 * (k + 6) * Nat.fib (k + 7) := by
      unfold X
      rw [show k + 6 + 2 = k + 8 from by omega, show k + 6 + 1 = k + 7 from by omega]
    rw [h9, hX]
    ring

  have memSplit : ∀ (k v : ℕ), v ∈ base10 ++ tailList k →
      v ∈ base10 ∨ (∃ i, i < k ∧ v = Nat.fib (i + 8)) ∨ (∃ i, i < k ∧ v = X (i + 6)) := by
    intro k
    induction k with
    | zero =>
      intro v h
      rcases List.mem_append.mp h with h' | h'
      · exact Or.inl h'
      · simp [tailList] at h'
    | succ p ih =>
      intro v h
      rcases List.mem_append.mp h with h' | h'
      · exact Or.inl h'
      · rw [show tailList (p + 1) = tailList p ++ [Nat.fib (p + 8), X (p + 6)] from rfl] at h'
        rcases List.mem_append.mp h' with h'' | h''
        · rcases ih v (List.mem_append.mpr (Or.inr h'')) with c | c | c
          · exact Or.inl c
          · obtain ⟨i, hi, hv⟩ := c
            exact Or.inr (Or.inl ⟨i, by omega, hv⟩)
          · obtain ⟨i, hi, hv⟩ := c
            exact Or.inr (Or.inr ⟨i, by omega, hv⟩)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h''
          rcases h'' with hv | hv
          · exact Or.inr (Or.inl ⟨p, by omega, hv⟩)
          · exact Or.inr (Or.inr ⟨p, by omega, hv⟩)

  have sumEven : ∀ k : ℕ, (base10 ++ tailList k).sum = (10 + 2 * k) * Nat.fib (k + 8) := by
    intro k
    induction k with
    | zero => decide
    | succ p ih =>
      rw [show tailList (p + 1) = tailList p ++ [Nat.fib (p + 8), X (p + 6)] from rfl,
        ← List.append_assoc, List.sum_append, ih]
      have hk := keyEven p
      have hsplit : (11 + 2 * p) * Nat.fib (p + 8)
          = (10 + 2 * p) * Nat.fib (p + 8) + Nat.fib (p + 8) := by ring
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [show 10 + 2 * (p + 1) = 12 + 2 * p from by ring, show p + 1 + 8 = p + 9 from by omega]
      omega

  have sumOdd : ∀ k : ℕ, (base10 ++ tailList k ++ [Nat.fib (k + 8)]).sum
      = (11 + 2 * k) * Nat.fib (k + 8) := by
    intro k
    rw [List.sum_append, sumEven]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    ring

  have fibNotMem : ∀ k : ℕ, Nat.fib (k + 8) ∉ base10 ++ tailList k := by
    intro k hmem
    have n26 : ¬ IsFib 26 := by decide
    have n53 : ¬ IsFib 53 := by decide
    have n93 : ¬ IsFib 93 := by decide
    have h21 : 21 ≤ Nat.fib (k + 8) := by
      have h := Nat.fib_mono (show 8 ≤ k + 8 by omega)
      have e : Nat.fib 8 = 21 := by decide
      omega
    rcases memSplit k _ hmem with h | h | h
    · have hc : Nat.fib (k + 8) = 26 ∨ Nat.fib (k + 8) = 53 ∨ Nat.fib (k + 8) = 93 := by
        simp only [base10, List.mem_cons, List.not_mem_nil, or_false] at h
        omega
      rcases hc with h' | h' | h'
      · exact n26 ⟨k + 8, h'⟩
      · exact n53 ⟨k + 8, h'⟩
      · exact n93 ⟨k + 8, h'⟩
    · obtain ⟨i, hi, hv⟩ := h
      have hlt : Nat.fib (i + 8) < Nat.fib (k + 8) := by
        have h1 : Nat.fib ((i + 6) + 2) < Nat.fib ((k + 6) + 2) :=
          Nat.fib_add_two_strictMono (by omega)
        rw [show (i + 6) + 2 = i + 8 from by omega, show (k + 6) + 2 = k + 8 from by omega] at h1
        exact h1
      omega
    · obtain ⟨i, hi, hv⟩ := h
      exact _root_.D5.S3.Arith.FriedFibonacciShiftNonFibonacci.result (i + 6) (by omega) (k + 8) hv

  have xGe : ∀ k : ℕ, 177 ≤ X (k + 6) := by
    intro k
    have e : X (k + 6) = Nat.fib (k + 8) + 2 * (k + 6) * Nat.fib (k + 7) := by
      unfold X
      rw [show k + 6 + 2 = k + 8 from by omega, show k + 6 + 1 = k + 7 from by omega]
    have h1 : Nat.fib 8 ≤ Nat.fib (k + 8) := Nat.fib_mono (by omega)
    have h2 : Nat.fib 7 ≤ Nat.fib (k + 7) := Nat.fib_mono (by omega)
    have h3 : 12 * Nat.fib 7 ≤ 2 * (k + 6) * Nat.fib (k + 7) := Nat.mul_le_mul (by omega) h2
    have e7 : Nat.fib 7 = 13 := by decide
    have e8 : Nat.fib 8 = 21 := by decide
    omega

  have xNotMem : ∀ k : ℕ, X (k + 6) ∉ base10 ++ tailList k ++ [Nat.fib (k + 8)] := by
    intro k hmem
    have h177 := xGe k
    rcases List.mem_append.mp hmem with h | h
    · rcases memSplit k _ h with h' | h' | h'
      · simp only [base10, List.mem_cons, List.not_mem_nil, or_false] at h'
        omega
      · obtain ⟨i, hi, hv⟩ := h'
        exact _root_.D5.S3.Arith.FriedFibonacciShiftNonFibonacci.result (k + 6) (by omega) (i + 8)
          hv.symm
      · obtain ⟨i, hi, hv⟩ := h'
        have := xmono (show i + 6 < k + 6 by omega)
        omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact _root_.D5.S3.Arith.FriedFibonacciShiftNonFibonacci.result (k + 6) (by omega) (k + 8)
        h.symm

  have boundOdd : ∀ k : ℕ, (11 + 2 * k) * Nat.fib (k + 7)
      ≤ (10 + 2 * k) * Nat.fib (k + 8) := by
    intro k
    have e8 : Nat.fib (k + 8) = Nat.fib (k + 6) + Nat.fib (k + 7) := by
      rw [show k + 8 = (k + 6) + 2 from by omega, Nat.fib_add_two,
        show (k + 6) + 1 = k + 7 from by omega]
    have e7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := by
      rw [show k + 7 = (k + 5) + 2 from by omega, Nat.fib_add_two,
        show (k + 5) + 1 = k + 6 from by omega]
    have h56 : Nat.fib (k + 5) ≤ Nat.fib (k + 6) := Nat.fib_mono (by omega)
    have hmul : 2 * Nat.fib (k + 6) ≤ (10 + 2 * k) * Nat.fib (k + 6) :=
      Nat.mul_le_mul (by omega) (le_refl _)
    calc (11 + 2 * k) * Nat.fib (k + 7)
        = (10 + 2 * k) * Nat.fib (k + 7) + Nat.fib (k + 7) := by ring
      _ ≤ (10 + 2 * k) * Nat.fib (k + 7) + (10 + 2 * k) * Nat.fib (k + 6) := by omega
      _ = (10 + 2 * k) * (Nat.fib (k + 6) + Nat.fib (k + 7)) := by ring
      _ = (10 + 2 * k) * Nat.fib (k + 8) := by rw [e8]

  have boundEven : ∀ k : ℕ, (12 + 2 * k) * Nat.fib (k + 7)
      ≤ (11 + 2 * k) * Nat.fib (k + 8) := by
    intro k
    have e8 : Nat.fib (k + 8) = Nat.fib (k + 6) + Nat.fib (k + 7) := by
      rw [show k + 8 = (k + 6) + 2 from by omega, Nat.fib_add_two,
        show (k + 6) + 1 = k + 7 from by omega]
    have e7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := by
      rw [show k + 7 = (k + 5) + 2 from by omega, Nat.fib_add_two,
        show (k + 5) + 1 = k + 6 from by omega]
    have h56 : Nat.fib (k + 5) ≤ Nat.fib (k + 6) := Nat.fib_mono (by omega)
    have hmul : 2 * Nat.fib (k + 6) ≤ (11 + 2 * k) * Nat.fib (k + 6) :=
      Nat.mul_le_mul (by omega) (le_refl _)
    calc (12 + 2 * k) * Nat.fib (k + 7)
        = (11 + 2 * k) * Nat.fib (k + 7) + Nat.fib (k + 7) := by ring
      _ ≤ (11 + 2 * k) * Nat.fib (k + 7) + (11 + 2 * k) * Nat.fib (k + 6) := by omega
      _ = (11 + 2 * k) * (Nat.fib (k + 6) + Nat.fib (k + 7)) := by ring
      _ = (11 + 2 * k) * Nat.fib (k + 8) := by rw [e8]

  have histNine : hist 9 = [1, 3, 2, 6, 13, 5, 26, 8, 53] := by
    have h1 : hist 1 = [1] := by
      show hist 0 ++ [nextVal (hist 0) 1] = _
      rw [nve (L := hist 0) (n := 1) (v := 1) (by omega) (by decide) (by decide)]
      rfl
    have h2 : hist 2 = [1, 3] := by
      show hist 1 ++ [nextVal (hist 1) 2] = _
      rw [h1, nve (L := [1]) (n := 2) (v := 3) (by omega) (by decide) (by decide)]
      rfl
    have h3 : hist 3 = [1, 3, 2] := by
      show hist 2 ++ [nextVal (hist 2) 3] = _
      rw [h2, nve (L := [1, 3]) (n := 3) (v := 2) (by omega) (by decide) (by decide)]
      rfl
    have h4 : hist 4 = [1, 3, 2, 6] := by
      show hist 3 ++ [nextVal (hist 3) 4] = _
      rw [h3, nve (L := [1, 3, 2]) (n := 4) (v := 6) (by omega) (by decide) (by decide)]
      rfl
    have h5 : hist 5 = [1, 3, 2, 6, 13] := by
      show hist 4 ++ [nextVal (hist 4) 5] = _
      rw [h4, nve (L := [1, 3, 2, 6]) (n := 5) (v := 13) (by omega) (by decide) (by decide)]
      rfl
    have h6 : hist 6 = [1, 3, 2, 6, 13, 5] := by
      show hist 5 ++ [nextVal (hist 5) 6] = _
      rw [h5, nve (L := [1, 3, 2, 6, 13]) (n := 6) (v := 5) (by omega) (by decide) (by decide)]
      rfl
    have h7 : hist 7 = [1, 3, 2, 6, 13, 5, 26] := by
      show hist 6 ++ [nextVal (hist 6) 7] = _
      rw [h6, nve (L := [1, 3, 2, 6, 13, 5]) (n := 7) (v := 26) (by omega) (by decide) (by decide)]
      rfl
    have h8 : hist 8 = [1, 3, 2, 6, 13, 5, 26, 8] := by
      show hist 7 ++ [nextVal (hist 7) 8] = _
      rw [h7, nve (L := [1, 3, 2, 6, 13, 5, 26]) (n := 8) (v := 8) (by omega) (by decide) (by decide)]
      rfl
    have h9 : hist 9 = [1, 3, 2, 6, 13, 5, 26, 8, 53] := by
      show hist 8 ++ [nextVal (hist 8) 9] = _
      rw [h8, nve (L := [1, 3, 2, 6, 13, 5, 26, 8]) (n := 9) (v := 53) (by omega) (by decide) (by decide)]
      rfl
    exact h9

  have aTen : a 10 = 93 := by
    rw [a, show (10 : ℕ) - 1 = 9 from rfl, histNine]
    exact nve (by omega) (by decide) (by decide)

  have histTen : hist 10 = [1, 3, 2, 6, 13, 5, 26, 8, 53, 93] := by
    show hist 9 ++ [nextVal (hist 9) 10] = _
    rw [histNine, nve (L := [1, 3, 2, 6, 13, 5, 26, 8, 53]) (n := 10) (v := 93)
      (by omega) (by decide) (by decide)]
    rfl

  have stepOdd : ∀ k : ℕ, nextVal (base10 ++ tailList k) (11 + 2 * k)
      = Nat.fib (k + 8) := by
    intro k
    have hS : (base10 ++ tailList k).sum = (10 + 2 * k) * Nat.fib (k + 8) := sumEven k
    have htot : (base10 ++ tailList k).sum + Nat.fib (k + 8)
        = (11 + 2 * k) * Nat.fib (k + 8) := by rw [hS]; ring
    refine nve (by omega) ⟨Nat.fib_pos.mpr (by omega), fibNotMem k, ?_, ?_⟩ ?_
    · rw [htot]; exact Dvd.intro _ rfl
    · rw [htot, Nat.mul_div_cancel_left _ (show 0 < 11 + 2 * k by omega)]
      exact ⟨k + 8, rfl⟩
    · rintro w hw ⟨hpos, hnm, hdvd, m, hm⟩
      have heq : (base10 ++ tailList k).sum + w = (11 + 2 * k) * Nat.fib m := by
        rw [hm, Nat.mul_comm]
        exact (Nat.div_mul_cancel hdvd).symm
      have hupper : (11 + 2 * k) * Nat.fib m < (11 + 2 * k) * Nat.fib (k + 8) := by omega
      have hmlt : Nat.fib m < Nat.fib (k + 8) := Nat.lt_of_mul_lt_mul_left hupper
      have hle : Nat.fib m ≤ Nat.fib (k + 7) := by
        have h := fle (m := m) (t := k + 7)
        rw [show k + 7 + 1 = k + 8 from by omega] at h
        exact h hmlt
      have hb := boundOdd k
      have hmul : (11 + 2 * k) * Nat.fib m ≤ (11 + 2 * k) * Nat.fib (k + 7) :=
        Nat.mul_le_mul (le_refl _) hle
      omega

  have stepEven : ∀ k : ℕ,
      nextVal (base10 ++ tailList k ++ [Nat.fib (k + 8)]) (12 + 2 * k) = X (k + 6) := by
    intro k
    have hS : (base10 ++ tailList k ++ [Nat.fib (k + 8)]).sum
        = (11 + 2 * k) * Nat.fib (k + 8) := sumOdd k
    have htot : (base10 ++ tailList k ++ [Nat.fib (k + 8)]).sum + X (k + 6)
        = (12 + 2 * k) * Nat.fib (k + 9) := by rw [hS]; exact keyEven k
    refine nve (by omega) ⟨?_, xNotMem k, ?_, ?_⟩ ?_
    · have := xGe k; omega
    · rw [htot]; exact Dvd.intro _ rfl
    · rw [htot, Nat.mul_div_cancel_left _ (show 0 < 12 + 2 * k by omega)]
      exact ⟨k + 9, rfl⟩
    · rintro w hw ⟨hpos, hnm, hdvd, m, hm⟩
      have heq : (base10 ++ tailList k ++ [Nat.fib (k + 8)]).sum + w
          = (12 + 2 * k) * Nat.fib m := by
        rw [hm, Nat.mul_comm]
        exact (Nat.div_mul_cancel hdvd).symm
      have hupper : (12 + 2 * k) * Nat.fib m < (12 + 2 * k) * Nat.fib (k + 9) := by omega
      have hmlt : Nat.fib m < Nat.fib (k + 9) := Nat.lt_of_mul_lt_mul_left hupper
      rcases Nat.lt_or_ge (Nat.fib m) (Nat.fib (k + 8)) with hlt | hge
      · have hle7 : Nat.fib m ≤ Nat.fib (k + 7) := by
          have h := fle (m := m) (t := k + 7)
          rw [show k + 7 + 1 = k + 8 from by omega] at h
          exact h hlt
        have hb := boundEven k
        have hmul : (12 + 2 * k) * Nat.fib m ≤ (12 + 2 * k) * Nat.fib (k + 7) :=
          Nat.mul_le_mul (le_refl _) hle7
        omega
      · have hle8 : Nat.fib m ≤ Nat.fib (k + 8) := by
          have h := fle (m := m) (t := k + 8)
          rw [show k + 8 + 1 = k + 9 from by omega] at h
          exact h hmlt
        have heqf : Nat.fib m = Nat.fib (k + 8) := by omega
        have hsplit : (12 + 2 * k) * Nat.fib (k + 8)
            = (11 + 2 * k) * Nat.fib (k + 8) + Nat.fib (k + 8) := by ring
        have hw8 : w = Nat.fib (k + 8) := by rw [heqf] at heq; omega
        exact hnm (by
          rw [hw8]
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

  have histPair : ∀ k : ℕ, hist (10 + 2 * k) = base10 ++ tailList k ∧
      hist (11 + 2 * k) = base10 ++ tailList k ++ [Nat.fib (k + 8)] := by
    intro k
    induction k with
    | zero =>
      have h10 : hist (10 + 2 * 0) = base10 ++ tailList 0 := by
        show hist 10 = base10 ++ []
        rw [List.append_nil, histTen]
        rfl
      refine ⟨h10, ?_⟩
      show hist 11 = _
      rw [show hist 11 = hist 10 ++ [nextVal (hist 10) 11] from rfl]
      rw [show hist 10 = base10 ++ tailList 0 from h10]
      rw [show (11 : ℕ) = 11 + 2 * 0 from rfl, stepOdd 0]
    | succ p ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hA : hist (10 + 2 * (p + 1)) = base10 ++ tailList (p + 1) := by
        rw [show 10 + 2 * (p + 1) = (11 + 2 * p) + 1 from by ring,
          show hist ((11 + 2 * p) + 1)
            = hist (11 + 2 * p) ++ [nextVal (hist (11 + 2 * p)) ((11 + 2 * p) + 1)] from rfl,
          ih2, show (11 + 2 * p) + 1 = 12 + 2 * p from by ring, stepEven p,
          show tailList (p + 1) = tailList p ++ [Nat.fib (p + 8), X (p + 6)] from rfl]
        simp
      refine ⟨hA, ?_⟩
      rw [show 11 + 2 * (p + 1) = (10 + 2 * (p + 1)) + 1 from by ring,
        show hist ((10 + 2 * (p + 1)) + 1)
          = hist (10 + 2 * (p + 1))
              ++ [nextVal (hist (10 + 2 * (p + 1))) ((10 + 2 * (p + 1)) + 1)] from rfl,
        hA, show (10 + 2 * (p + 1)) + 1 = 11 + 2 * (p + 1) from by ring, stepOdd (p + 1)]

  have xIdentity : ∀ j : ℕ, 1 ≤ j →
      X j + (2 * j - 1) * Nat.fib (j + 2) = 2 * j * Nat.fib (j + 3) := by
    intro j hj
    have e3 : Nat.fib (j + 3) = Nat.fib (j + 1) + Nat.fib (j + 2) := by
      rw [show j + 3 = (j + 1) + 2 from by omega, Nat.fib_add_two,
        show (j + 1) + 1 = j + 2 from by omega]
    have e : X j = Nat.fib (j + 2) + 2 * j * Nat.fib (j + 1) := rfl
    have hd : (2 * j - 1) * Nat.fib (j + 2) + Nat.fib (j + 2) = 2 * j * Nat.fib (j + 2) := by
      have hs : 2 * j - 1 + 1 = 2 * j := by omega
      calc (2 * j - 1) * Nat.fib (j + 2) + Nat.fib (j + 2)
          = (2 * j - 1 + 1) * Nat.fib (j + 2) := by ring
        _ = 2 * j * Nat.fib (j + 2) := by rw [hs]
    have hdist : 2 * j * (Nat.fib (j + 1) + Nat.fib (j + 2))
        = 2 * j * Nat.fib (j + 1) + 2 * j * Nat.fib (j + 2) := by ring
    rw [e3]
    omega

  have aodd : ∀ k : ℕ, a (11 + 2 * k) = Nat.fib (k + 8) := by
    intro k
    rw [a, show 11 + 2 * k - 1 = 10 + 2 * k from by omega, (histPair k).1]
    exact stepOdd k
  have aeven : ∀ k : ℕ, a (12 + 2 * k) = X (k + 6) := by
    intro k
    rw [a, show 12 + 2 * k - 1 = 11 + 2 * k from by omega, (histPair k).2]
    exact stepEven k
  intro n hn
  constructor
  · intro hev
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j := ⟨n / 2, by omega⟩
    have hj : 5 ≤ j := by omega
    have hX : a (2 * j) = X j := by
      rcases Nat.eq_or_lt_of_le hj with h | h
      · rw [← h]
        exact aTen
      · have hb := aeven (j - 6)
        rw [show 12 + 2 * (j - 6) = 2 * j from by omega,
          show (j - 6) + 6 = j from by omega] at hb
        exact hb
    rw [hX, show 2 * j / 2 = j from by omega]
    exact xIdentity j (by omega)
  · intro hodd
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 1 := ⟨n / 2, by omega⟩
    have hj : 5 ≤ j := by omega
    have hb := aodd (j - 5)
    rw [show 11 + 2 * (j - 5) = 2 * j + 1 from by omega,
      show (j - 5) + 8 = j + 3 from by omega] at hb
    rw [hb, show (2 * j + 1 + 1) / 2 = j + 1 from by omega,
      show j + 1 + 2 = j + 3 from by omega]


end D5.S3.Arith.GreedyFibonacciAverageClosedForm

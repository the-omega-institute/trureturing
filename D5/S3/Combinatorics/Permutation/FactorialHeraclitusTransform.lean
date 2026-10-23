/- GID: D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/FactorialHeraclitusTransform
   mirror-E: none(waiver:theorem-has-no-separate-numeric-evidence)
   anchors: []
   utility: none
   digest: The factorial Heraclitus transform hits every integer by complete interval blocks. -/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.FactorialHeraclitusTransform

/-- The integers in the order `0, 1, -1, 2, -2, …`:
smaller absolute value first, positive first on ties. -/
def unrank (r : ℕ) : ℤ := if r % 2 = 1 then (((r + 1) / 2 : ℕ) : ℤ) else -((r / 2 : ℕ) : ℤ)

/-- `d` is a factorial number `k!` with `k ≥ 1`. -/
def IsFactorial (d : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ d = Nat.factorial k

private def rank (z : ℤ) : ℕ := if 0 < z then 2 * z.toNat - 1 else 2 * (-z).toNat

private theorem unrank_rank (z : ℤ) : unrank (rank z) = z := by
  by_cases hz : 0 < z
  · simp only [rank, if_pos hz, unrank]
    have ht : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have hp : 0 < z.toNat := by omega
    have hm : (2 * z.toNat - 1) % 2 = 1 := by omega
    rw [if_pos hm]
    have hd : (2 * z.toNat - 1 + 1) / 2 = z.toNat := by omega
    rw [hd, ht]
  · simp only [rank, if_neg hz, unrank]
    have ht : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    have hm : (2 * (-z).toNat) % 2 ≠ 1 := by omega
    rw [if_neg hm]
    have hd : 2 * (-z).toNat / 2 = (-z).toNat := by omega
    rw [hd, ht]
    omega

private theorem rank_unrank (r : ℕ) : rank (unrank r) = r := by
  unfold unrank
  split_ifs with hr
  · unfold rank
    have hp : 0 < (r + 1) / 2 := by omega
    rw [if_pos (by omega)]
    simp only [Int.toNat_natCast]
    omega
  · unfold rank
    rw [if_neg (by omega)]
    simp only [neg_neg, Int.toNat_natCast]
    omega

private theorem rank_order (x y : ℤ) :
    rank x ≤ rank y ↔ x.natAbs < y.natAbs ∨
      (x.natAbs = y.natAbs ∧ y ≤ x) := by
  have hx := Int.natCast_natAbs x
  have hy := Int.natCast_natAbs y
  unfold rank
  split_ifs <;> omega

private theorem abs_le_sum (l : List ℤ) (z : ℤ) (hz : z ∈ l) :
    z.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp at hz
  | cons x l ih =>
      simp only [List.mem_cons] at hz
      simp only [List.map_cons, List.sum_cons]
      rcases hz with rfl | hz
      · omega
      · have := ih hz
        omega

private theorem exists_next (l : List ℤ) (c : ℤ) :
    ∃ r, unrank r ∉ l ∧ IsFactorial (c - unrank r).natAbs := by
  let N := (l.map Int.natAbs).sum + c.natAbs + 2
  let z : ℤ := c + (Nat.factorial N : ℤ)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hf := Nat.self_le_factorial N
  have hc := Int.natCast_natAbs c
  have hz : (l.map Int.natAbs).sum < z := by dsimp [z, N] at *; omega
  refine ⟨rank z, ?_, ?_⟩
  · rw [unrank_rank]
    intro hm
    have hb := abs_le_sum l z hm
    have ha := Int.natCast_natAbs z
    omega
  · rw [unrank_rank]
    refine ⟨N, hN, ?_⟩
    have hd : c - z = -(Nat.factorial N : ℤ) := by dsimp [z]; omega
    rw [hd]
    simp

/-- The least-ranked integer outside `l` at factorial distance from `c`. -/
noncomputable def next (l : List ℤ) (c : ℤ) : ℤ := by
  classical exact unrank (Nat.find (exists_next l c))

/-- `terms n = [a(n), a(n-1), …, a(0)]`. -/
noncomputable def terms : ℕ → List ℤ
  | 0 => [0]
  | n + 1 => next (terms n) ((terms n).headD 0) :: terms n

/-- OEIS A393434: `a(n)`. -/
noncomputable def a (n : ℕ) : ℤ := (terms n).headD 0

/-- A393434 conjecture: every integer appears. -/
def claim : Prop := ∀ z : ℤ, ∃ n : ℕ, a n = z

private theorem next_spec (l : List ℤ) (c : ℤ) :
    next l c ∉ l ∧ IsFactorial (c - next l c).natAbs := by
  classical
  exact Nat.find_spec (exists_next l c)

private theorem next_least (l : List ℤ) (c z : ℤ)
    (hz : z ∉ l) (hd : IsFactorial (c - z).natAbs) :
    rank (next l c) ≤ rank z := by
  classical
  unfold next
  rw [rank_unrank]
  apply Nat.find_min'
  simpa only [unrank_rank] using And.intro hz hd

private theorem next_eq (l : List ℤ) (c z : ℤ)
    (hz : z ∉ l) (hd : IsFactorial (c - z).natAbs)
    (hmin : ∀ w : ℤ, w ∉ l → IsFactorial (c - w).natAbs → rank z ≤ rank w) :
    next l c = z := by
  have hs := next_spec l c
  have he := Nat.le_antisymm (next_least l c z hz hd) (hmin _ hs.1 hs.2)
  have := congrArg unrank he
  simpa only [unrank_rank] using this

private theorem terms_length (n : ℕ) : (terms n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [terms, List.length_cons, ih]

private theorem terms_nodup (n : ℕ) : (terms n).Nodup := by
  induction n with
  | zero => simp [terms]
  | succ n ih =>
      rw [terms, List.nodup_cons]
      exact ⟨(next_spec _ _).1, ih⟩

private theorem mem_terms (n : ℕ) (z : ℤ) :
    z ∈ terms n ↔ ∃ i ≤ n, a i = z := by
  induction n with
  | zero => simp [terms, a, eq_comm]
  | succ n ih =>
      simp only [terms, List.mem_cons, ih]
      have hs : a (n + 1) = next (terms n) ((terms n).headD 0) := rfl
      constructor
      · rintro (hz | ⟨i, hi, hz⟩)
        · exact ⟨n + 1, le_rfl, hs.trans hz.symm⟩
        · exact ⟨i, by omega, hz⟩
      · rintro ⟨i, hi, hz⟩
        by_cases he : i = n + 1
        · left; subst i; exact hz.symm.trans hs
        · right; exact ⟨i, by omega, hz⟩

private theorem factorial_gap (k d : ℕ) (hk : 1 ≤ k) (hd : IsFactorial d)
    (hgt : Nat.factorial k < d) : Nat.factorial (k + 1) ≤ d := by
  obtain ⟨j, hj, rfl⟩ := hd
  have hkj : k < j := (Nat.factorial_lt (by omega : 0 < k)).mp hgt
  exact Nat.factorial_le (by omega)

private theorem factorial_small (d : ℕ) (hd : d ≤ 24) :
    IsFactorial d ↔ d = 1 ∨ d = 2 ∨ d = 6 ∨ d = 24 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hb : k ≤ 4 := by
      by_contra hn
      have hf := Nat.factorial_le (show 5 ≤ k by omega)
      norm_num [Nat.factorial] at hf
      omega
    interval_cases k <;> norm_num [Nat.factorial] at *
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨3, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩

private theorem jump_up (l : List ℤ) (b k : ℕ)
    (hf : Nat.factorial k = 2 * b) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hl : ∀ z : ℤ, z ∈ l ↔ -(b : ℤ) ≤ z ∧ z ≤ b) :
    next l (1 - (b : ℤ)) = b + 1 := by
  apply next_eq
  · rw [hl]; omega
  · refine ⟨k, hk, ?_⟩
    have he : 1 - (b : ℤ) - ((b : ℤ) + 1) = -((2 * b : ℕ) : ℤ) := by omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast, hf]
  · intro w hw _
    have hu : ¬ (-(b : ℤ) ≤ w ∧ w ≤ b) := by simpa only [hl] using hw
    rw [rank_order]
    have ha := Int.natCast_natAbs w
    have habs := Int.natAbs_of_nonneg (show 0 ≤ (b : ℤ) + 1 by omega)
    omega

private theorem ascent_next (l : List ℤ) (b B k x : ℕ)
    (hk : 1 ≤ k) (hf : Nat.factorial k = 2 * b)
    (hF : Nat.factorial (k + 1) = 2 * B)
    (hx : b < x) (hxB : x < B)
    (hl : ∀ z : ℤ, z ∈ l ↔ -(b : ℤ) ≤ z ∧ z ≤ x) :
    next l x = x + 1 := by
  apply next_eq
  · rw [hl]; omega
  · refine ⟨1, by decide, ?_⟩
    have he : (x : ℤ) - ((x : ℤ) + 1) = -1 := by omega
    rw [he]; decide
  · intro w hw hd
    have hu : ¬ (-(b : ℤ) ≤ w ∧ w ≤ x) := by simpa only [hl] using hw
    rw [rank_order]
    by_cases hwpos : 0 ≤ w
    · have hwabs := Int.natAbs_of_nonneg hwpos
      have hxabs := Int.natAbs_of_nonneg (show 0 ≤ (x : ℤ) + 1 by omega)
      omega
    · have hwabs := Int.natAbs_of_nonneg (show 0 ≤ -w by omega)
      simp only [Int.natAbs_neg] at hwabs
      have hdabs := Int.natAbs_of_nonneg (show 0 ≤ (x : ℤ) - w by omega)
      have hdgt : Nat.factorial k < ((x : ℤ) - w).natAbs := by rw [hf]; omega
      have hgap := factorial_gap k _ hk hd hdgt
      rw [hF] at hgap
      have hxabs := Int.natAbs_of_nonneg (show 0 ≤ (x : ℤ) + 1 by omega)
      omega

private theorem jump_down (l : List ℤ) (b B k : ℕ)
    (hk : 1 ≤ k) (hf : Nat.factorial k = 2 * b)
    (hF : Nat.factorial (k + 1) = 2 * B) (hbB : b < B)
    (hl : ∀ z : ℤ, z ∈ l ↔ -(b : ℤ) ≤ z ∧ z ≤ B) :
    next l B = -(B : ℤ) := by
  apply next_eq
  · rw [hl]; omega
  · refine ⟨k + 1, by omega, ?_⟩
    have he : (B : ℤ) - -(B : ℤ) = ((2 * B : ℕ) : ℤ) := by omega
    rw [he, Int.natAbs_natCast, hF]
  · intro w hw hd
    have hu : ¬ (-(b : ℤ) ≤ w ∧ w ≤ B) := by simpa only [hl] using hw
    rw [rank_order]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    by_cases hwpos : 0 ≤ w
    · have hwabs := Int.natAbs_of_nonneg hwpos
      omega
    · have hwabs := Int.natAbs_of_nonneg (show 0 ≤ -w by omega)
      simp only [Int.natAbs_neg] at hwabs
      have hdabs := Int.natAbs_of_nonneg (show 0 ≤ (B : ℤ) - w by omega)
      have hdgt : Nat.factorial k < ((B : ℤ) - w).natAbs := by rw [hf]; omega
      have hgap := factorial_gap k _ hk hd hdgt
      rw [hF] at hgap
      omega

private theorem a_succ (n : ℕ) : a (n + 1) = next (terms n) (a n) := rfl

private theorem mem_terms_succ (n : ℕ) (z : ℤ) :
    z ∈ terms (n + 1) ↔ z = a (n + 1) ∨ z ∈ terms n := by
  exact List.mem_cons

private theorem rank_abs_le (x y : ℤ) (h : rank x ≤ rank y) :
    x.natAbs ≤ y.natAbs := by
  rw [rank_order] at h
  omega

private def Frame (n L B : ℕ) : Prop :=
  (∀ z : ℤ, z ∈ terms n → -(B : ℤ) ≤ z ∧ z ≤ B) ∧
  (∀ z : ℤ, -(L : ℤ) < z → z ≤ B → z ∈ terms n)

private def Sparse (n L B : ℕ) : Prop :=
  ∀ t : ℕ, L < t → t < B → -(t : ℤ) ∈ terms n → -((t + 1 : ℕ) : ℤ) ∉ terms n

private theorem descent_step (n L B r : ℕ) (hL : 1 ≤ L)
    (hr : L < r) (hrB : r ≤ B) (hf : Frame n L B)
    (hc : a n = -(r : ℤ))
    (hh : ∀ t : ℕ, L ≤ t → t < r → -(t : ℤ) ∉ terms n) :
    ∃ s : ℕ, L ≤ s ∧ s < r ∧ a (n + 1) = -(s : ℤ) ∧
      (s = L ∨ s + 1 < r) := by
  have hnot : -((r - 1 : ℕ) : ℤ) ∉ terms n := hh _ (by omega) (by omega)
  have hdist : IsFactorial (a n - -((r - 1 : ℕ) : ℤ)).natAbs := by
    rw [hc]
    have he : -(r : ℤ) - -((r - 1 : ℕ) : ℤ) = -1 := by omega
    rw [he]
    exact ⟨1, by decide, by decide⟩
  have hbound := rank_abs_le _ _ (next_least (terms n) (a n) _ hnot hdist)
  rw [← a_succ] at hbound
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at hbound
  have hnew : a (n + 1) ∉ terms n := by rw [a_succ]; exact (next_spec _ _).1
  have hw : a (n + 1) ≤ -(L : ℤ) := by
    by_contra hn
    have habs := Int.natCast_natAbs (a (n + 1))
    exact hnew (hf.2 _ (by omega) (by omega))
  let s := (a (n + 1)).natAbs
  have hs : a (n + 1) = -(s : ℤ) := by
    have he := Int.natAbs_of_nonneg (show 0 ≤ -a (n + 1) by omega)
    simp only [Int.natAbs_neg] at he
    dsimp [s]
    omega
  have hsL : L ≤ s := by omega
  have hsr : s < r := by dsimp [s]; omega
  refine ⟨s, hsL, hsr, hs, ?_⟩
  by_cases hr2 : L + 2 ≤ r
  · have hnot2 : -((r - 2 : ℕ) : ℤ) ∉ terms n := hh _ (by omega) (by omega)
    have hdist2 : IsFactorial (a n - -((r - 2 : ℕ) : ℤ)).natAbs := by
      rw [hc]
      have he : -(r : ℤ) - -((r - 2 : ℕ) : ℤ) = -2 := by omega
      rw [he]
      exact ⟨2, by decide, by decide⟩
    have hb2 := rank_abs_le _ _ (next_least (terms n) (a n) _ hnot2 hdist2)
    rw [← a_succ, hs] at hb2
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hb2
    right; omega
  · left; omega

private theorem descent_finish (L B r n : ℕ) (hL : 1 ≤ L)
    (hrL : L ≤ r) (hrB : r ≤ B) (hf : Frame n L B) (hp : Sparse n L B)
    (hc : a n = -(r : ℤ))
    (hh : ∀ t : ℕ, L ≤ t → t < r → -(t : ℤ) ∉ terms n)
    (hB : -(B : ℤ) ∈ terms n) :
    ∃ m : ℕ, Frame m L B ∧ Sparse m L B ∧ a m = -(L : ℤ) ∧
      -(B : ℤ) ∈ terms m := by
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    by_cases he : r = L
    · subst r
      exact ⟨n, hf, hp, hc, hB⟩
    obtain ⟨s, hsL, hsr, hs, hgap⟩ := descent_step n L B r hL (by omega) hrB hf hc hh
    have hfs : Frame (n + 1) L B := by
      constructor
      · intro z hz
        rw [mem_terms_succ, hs] at hz
        rcases hz with rfl | hz
        · constructor <;> omega
        · exact hf.1 _ hz
      · intro z hzlo hzhi
        exact (mem_terms_succ _ _).2 (Or.inr (hf.2 _ hzlo hzhi))
    have hps : Sparse (n + 1) L B := by
      intro t ht htB htm htm1
      rw [mem_terms_succ, hs] at htm htm1
      rcases htm with hts | htm
      · have htsN : t = s := by omega
        subst t
        rcases htm1 with hss | htm1
        · omega
        · apply hh (s + 1) (by omega) (by omega)
          exact htm1
      · rcases htm1 with hts | htm1
        · have htsN : t + 1 = s := by omega
          apply hh t (by omega) (by omega)
          exact htm
        · exact hp t ht htB htm htm1
    have hhs : ∀ t : ℕ, L ≤ t → t < s → -(t : ℤ) ∉ terms (n + 1) := by
      intro t ht hts htm
      rw [mem_terms_succ, hs] at htm
      rcases htm with he | htm
      · omega
      · exact hh t ht (by omega) htm
    have hBs : -(B : ℤ) ∈ terms (n + 1) :=
      (mem_terms_succ _ _).2 (Or.inr hB)
    exact ih s hsr (n + 1) hsL (by omega) hfs hps hs hhs hBs

private theorem negative_min (l : List ℤ) (c : ℤ) (s : ℕ) (_hs : 0 < s)
    (hused : ∀ w : ℤ, w.natAbs < s → w ∈ l) (hpos : (s : ℤ) ∈ l)
    (hnot : -(s : ℤ) ∉ l) (hd : IsFactorial (c - -(s : ℤ)).natAbs) :
    next l c = -(s : ℤ) := by
  apply next_eq l c _ hnot hd
  intro w hw _
  rw [rank_order]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]
  have hsize : s ≤ w.natAbs := by
    by_contra hn
    exact hw (hused w (by omega))
  by_cases he : s = w.natAbs
  · right
    constructor
    · exact he
    · by_cases hwpos : 0 ≤ w
      · have ha := Int.natAbs_of_nonneg hwpos
        have hwEq : w = s := by omega
        exact False.elim (hw (hwEq.symm ▸ hpos))
      · have ha := Int.natAbs_of_nonneg (show 0 ≤ -w by omega)
        simp only [Int.natAbs_neg] at ha
        omega
  · left; omega

private theorem fill_finish (L B q n r : ℕ) (hL : 1 ≤ L) (hrL : L ≤ r)
    (hrB : r < B) (hbudget : B - r ≤ q) (hf : Frame n L B)
    (hc : a n = -(r : ℤ)) (hB : -(B : ℤ) ∈ terms n)
    (hlo : ∀ t : ℕ, t ≤ r → -(t : ℤ) ∈ terms n)
    (hp : ∀ t : ℕ, r < t → t < B → -(t : ℤ) ∈ terms n →
      -((t + 1 : ℕ) : ℤ) ∉ terms n) :
    ∃ m : ℕ, (∀ z : ℤ, z ∈ terms m ↔ -(B : ℤ) ≤ z ∧ z ≤ B) ∧
      a m = 1 - (B : ℤ) := by
  induction q generalizing n r with
  | zero => omega
  | succ q ih =>
    by_cases hrend : r + 1 = B
    · refine ⟨n, ?_, ?_⟩
      · intro z
        constructor
        · exact hf.1 z
        · intro hz
          by_cases hzpos : 0 ≤ z
          · exact hf.2 z (by omega) hz.2
          · let t := z.natAbs
            have ht : z = -(t : ℤ) := by
              have ha := Int.natAbs_of_nonneg (show 0 ≤ -z by omega)
              simp only [Int.natAbs_neg] at ha
              dsimp [t]; omega
            rw [ht]
            by_cases he : t = B
            · simpa only [he] using hB
            · apply hlo; omega
      · rw [hc]; omega
    have hr2 : r + 2 ≤ B := by omega
    by_cases hskip : -((r + 1 : ℕ) : ℤ) ∈ terms n
    · have hsB : r + 2 < B := by
        by_contra hn
        have hbEq : r + 2 = B := by omega
        have hn := hp (r + 1) (by omega) (by omega) hskip
        exact hn (hbEq.symm ▸ hB)
      have hsnot : -((r + 2 : ℕ) : ℤ) ∉ terms n :=
        hp (r + 1) (by omega) (by omega) hskip
      have hused : ∀ w : ℤ, w.natAbs < r + 2 → w ∈ terms n := by
        intro w hw
        by_cases hwpos : 0 ≤ w
        · have ha := Int.natAbs_of_nonneg hwpos
          exact hf.2 w (by omega) (by omega)
        · let t := w.natAbs
          have ht : w = -(t : ℤ) := by
            have ha := Int.natAbs_of_nonneg (show 0 ≤ -w by omega)
            simp only [Int.natAbs_neg] at ha
            dsimp [t]; omega
          rw [ht]
          by_cases he : t = r + 1
          · simpa only [he] using hskip
          · apply hlo; dsimp [t] at *; omega
      have hspos : ((r + 2 : ℕ) : ℤ) ∈ terms n := hf.2 _ (by omega) (by omega)
      have hsdist : IsFactorial (a n - -((r + 2 : ℕ) : ℤ)).natAbs := by
        rw [hc]
        have he : -(r : ℤ) - -((r + 2 : ℕ) : ℤ) = 2 := by omega
        rw [he]
        exact ⟨2, by decide, by decide⟩
      have hs : a (n + 1) = -((r + 2 : ℕ) : ℤ) := by
        rw [a_succ]
        exact negative_min _ _ _ (by omega) hused hspos hsnot hsdist
      have hfs : Frame (n + 1) L B := by
        constructor
        · intro z hz
          rw [mem_terms_succ, hs] at hz
          rcases hz with rfl | hz
          · constructor <;> omega
          · exact hf.1 _ hz
        · intro z hzlo hzhi
          exact (mem_terms_succ _ _).2 (Or.inr (hf.2 _ hzlo hzhi))
      have hlos : ∀ t : ℕ, t ≤ r + 2 → -(t : ℤ) ∈ terms (n + 1) := by
        intro t ht
        rw [mem_terms_succ, hs]
        by_cases he : t = r + 2
        · left; omega
        · right
          by_cases he1 : t = r + 1
          · simpa only [he1] using hskip
          · exact hlo t (by omega)
      have hps : ∀ t : ℕ, r + 2 < t → t < B → -(t : ℤ) ∈ terms (n + 1) →
          -((t + 1 : ℕ) : ℤ) ∉ terms (n + 1) := by
        intro t ht htB htm htm1
        rw [mem_terms_succ, hs] at htm htm1
        rcases htm with he | htm
        · omega
        · rcases htm1 with he | htm1
          · omega
          · exact hp t (by omega) htB htm htm1
      exact ih (n + 1) (r + 2) (by omega) hsB (by omega) hfs hs
        ((mem_terms_succ _ _).2 (Or.inr hB)) hlos hps
    · have hused : ∀ w : ℤ, w.natAbs < r + 1 → w ∈ terms n := by
        intro w hw
        by_cases hwpos : 0 ≤ w
        · have ha := Int.natAbs_of_nonneg hwpos
          exact hf.2 w (by omega) (by omega)
        · let t := w.natAbs
          have ht : w = -(t : ℤ) := by
            have ha := Int.natAbs_of_nonneg (show 0 ≤ -w by omega)
            simp only [Int.natAbs_neg] at ha
            dsimp [t]; omega
          rw [ht]
          apply hlo; dsimp [t] at *; omega
      have hspos : ((r + 1 : ℕ) : ℤ) ∈ terms n := hf.2 _ (by omega) (by omega)
      have hsdist : IsFactorial (a n - -((r + 1 : ℕ) : ℤ)).natAbs := by
        rw [hc]
        have he : -(r : ℤ) - -((r + 1 : ℕ) : ℤ) = 1 := by omega
        rw [he]
        exact ⟨1, by decide, by decide⟩
      have hs : a (n + 1) = -((r + 1 : ℕ) : ℤ) := by
        rw [a_succ]
        exact negative_min _ _ _ (by omega) hused hspos hskip hsdist
      have hfs : Frame (n + 1) L B := by
        constructor
        · intro z hz
          rw [mem_terms_succ, hs] at hz
          rcases hz with rfl | hz
          · constructor <;> omega
          · exact hf.1 _ hz
        · intro z hzlo hzhi
          exact (mem_terms_succ _ _).2 (Or.inr (hf.2 _ hzlo hzhi))
      have hlos : ∀ t : ℕ, t ≤ r + 1 → -(t : ℤ) ∈ terms (n + 1) := by
        intro t ht
        rw [mem_terms_succ, hs]
        by_cases he : t = r + 1
        · left; omega
        · right; exact hlo t (by omega)
      have hps : ∀ t : ℕ, r + 1 < t → t < B → -(t : ℤ) ∈ terms (n + 1) →
          -((t + 1 : ℕ) : ℤ) ∉ terms (n + 1) := by
        intro t ht htB htm htm1
        rw [mem_terms_succ, hs] at htm htm1
        rcases htm with he | htm
        · omega
        · rcases htm1 with he | htm1
          · omega
          · exact hp t (by omega) htB htm htm1
      exact ih (n + 1) (r + 1) (by omega) (by omega) (by omega) hfs hs
        ((mem_terms_succ _ _).2 (Or.inr hB)) hlos hps

private theorem next_checked (l : List ℤ) (c : ℤ) (r : ℕ)
    (h : unrank r ∉ l ∧ IsFactorial (c - unrank r).natAbs)
    (hm : ∀ s : ℕ, s < r → unrank s ∈ l ∨ ¬IsFactorial (c - unrank s).natAbs) :
    next l c = unrank r := by
  apply next_eq l c _ h.1 h.2
  intro w hw hd
  rw [rank_unrank]
  by_contra hn
  have hs := hm (rank w) (by omega)
  simp only [unrank_rank] at hs
  exact hs.elim hw (fun hnot => hnot hd)

private def Block (k : ℕ) : Prop :=
  ∃ n : ℕ, (∀ z : ℤ, z ∈ terms n ↔
    -((Nat.factorial k / 2 : ℕ) : ℤ) ≤ z ∧ z ≤ (Nat.factorial k / 2 : ℕ)) ∧
    a n = 1 - ((Nat.factorial k / 2 : ℕ) : ℤ)

local macro "checked_factorial_step " r:num k:num : tactic =>
  `(tactic| (refine (next_checked _ _ $r ?_ ?_).trans ?_
             · constructor
               · norm_num [unrank]
               · refine ⟨$k, by decide, ?_⟩
                 norm_num [unrank, Nat.factorial]
             · intro t ht
               interval_cases t <;> norm_num [unrank, factorial_small]
             · norm_num [unrank]))

private theorem base_block : Block 4 := by
  have ht0 : terms 0 = [0] := rfl
  have hn1 : next ([0] : List ℤ) (0) = 1 := by
    checked_factorial_step 1 1
  have ht1 : terms 1 = [1, 0] := by
    rw [terms, ht0]
    simp only [List.headD_cons, hn1]
  have hn2 : next ([1, 0] : List ℤ) (1) = -1 := by
    checked_factorial_step 2 2
  have ht2 : terms 2 = [-1, 1, 0] := by
    rw [terms, ht1]
    simp only [List.headD_cons, hn2]
  have hn3 : next ([-1, 1, 0] : List ℤ) (-1) = -2 := by
    checked_factorial_step 4 1
  have ht3 : terms 3 = [-2, -1, 1, 0] := by
    rw [terms, ht2]
    simp only [List.headD_cons, hn3]
  have hn4 : next ([-2, -1, 1, 0] : List ℤ) (-2) = -3 := by
    checked_factorial_step 6 1
  have ht4 : terms 4 = [-3, -2, -1, 1, 0] := by
    rw [terms, ht3]
    simp only [List.headD_cons, hn4]
  have hn5 : next ([-3, -2, -1, 1, 0] : List ℤ) (-3) = 3 := by
    checked_factorial_step 5 3
  have ht5 : terms 5 = [3, -3, -2, -1, 1, 0] := by
    rw [terms, ht4]
    simp only [List.headD_cons, hn5]
  have hn6 : next ([3, -3, -2, -1, 1, 0] : List ℤ) (3) = 2 := by
    checked_factorial_step 3 1
  have ht6 : terms 6 = [2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht5]
    simp only [List.headD_cons, hn6]
  have hn7 : next ([2, 3, -3, -2, -1, 1, 0] : List ℤ) (2) = 4 := by
    checked_factorial_step 7 2
  have ht7 : terms 7 = [4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht6]
    simp only [List.headD_cons, hn7]
  have hn8 : next ([4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (4) = 5 := by
    checked_factorial_step 9 1
  have ht8 : terms 8 = [5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht7]
    simp only [List.headD_cons, hn8]
  have hn9 : next ([5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (5) = 6 := by
    checked_factorial_step 11 1
  have ht9 : terms 9 = [6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht8]
    simp only [List.headD_cons, hn9]
  have hn10 : next ([6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (6) = 7 := by
    checked_factorial_step 13 1
  have ht10 : terms 10 = [7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht9]
    simp only [List.headD_cons, hn10]
  have hn11 : next ([7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (7) = 8 := by
    checked_factorial_step 15 1
  have ht11 : terms 11 = [8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht10]
    simp only [List.headD_cons, hn11]
  have hn12 : next ([8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (8) = 9 := by
    checked_factorial_step 17 1
  have ht12 : terms 12 = [9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht11]
    simp only [List.headD_cons, hn12]
  have hn13 : next ([9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (9) = 10 := by
    checked_factorial_step 19 1
  have ht13 : terms 13 = [10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht12]
    simp only [List.headD_cons, hn13]
  have hn14 : next ([10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (10) = 11 := by
    checked_factorial_step 21 1
  have ht14 : terms 14 = [11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht13]
    simp only [List.headD_cons, hn14]
  have hn15 : next ([11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (11) = 12 := by
    checked_factorial_step 23 1
  have ht15 : terms 15 = [12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht14]
    simp only [List.headD_cons, hn15]
  have hn16 : next ([12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (12) =
      -12 := by
    checked_factorial_step 24 4
  have ht16 : terms 16 = [-12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht15]
    simp only [List.headD_cons, hn16]
  have hn17 : next ([-12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (-12) =
      -6 := by
    checked_factorial_step 12 3
  have ht17 : terms 17 = [-6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht16]
    simp only [List.headD_cons, hn17]
  have hn18 : next ([-6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] : List ℤ) (-6) =
      -4 := by
    checked_factorial_step 8 2
  have ht18 : terms 18 = [-4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht17]
    simp only [List.headD_cons, hn18]
  have hn19 : next ([-4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0]
      : List ℤ) (-4) =
      -5 := by
    checked_factorial_step 10 1
  have ht19 : terms 19 = [-5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1,
      0] := by
    rw [terms, ht18]
    simp only [List.headD_cons, hn19]
  have hn20 : next ([-5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0]
      : List ℤ) (-5) =
      -7 := by
    checked_factorial_step 14 2
  have ht20 : terms 20 = [-7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2,
      -1, 1, 0] := by
    rw [terms, ht19]
    simp only [List.headD_cons, hn20]
  have hn21 : next ([-7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1, 1, 0]
      : List ℤ) (-7) =
      -8 := by
    checked_factorial_step 16 1
  have ht21 : terms 21 = [-8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3,
      -2, -1, 1, 0] := by
    rw [terms, ht20]
    simp only [List.headD_cons, hn21]
  have hn22 : next ([-8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2, -1,
      1, 0] : List ℤ) (-8) = -9 := by
    checked_factorial_step 18 1
  have ht22 : terms 22 = [-9, -8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3,
      -3, -2, -1, 1, 0] := by
    rw [terms, ht21]
    simp only [List.headD_cons, hn22]
  have hn23 : next ([-9, -8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3, -3, -2,
      -1, 1, 0] : List ℤ) (-9) = -10 := by
    checked_factorial_step 20 1
  have ht23 : terms 23 = [-10, -9, -8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2,
      3, -3, -2, -1, 1, 0] := by
    rw [terms, ht22]
    simp only [List.headD_cons, hn23]
  have hn24 : next ([-10, -9, -8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5, 4, 2, 3,
      -3, -2, -1, 1, 0] : List ℤ) (-10) = -11 := by
    checked_factorial_step 22 1
  have ht24 : terms 24 = [-11, -10, -9, -8, -7, -5, -4, -6, -12, 12, 11, 10, 9, 8, 7, 6, 5,
      4, 2, 3, -3, -2, -1, 1, 0] := by
    rw [terms, ht23]
    simp only [List.headD_cons, hn24]
  refine ⟨24, ?_, ?_⟩
  · intro z
    rw [ht24]
    norm_num [Nat.factorial, List.mem_cons, List.mem_singleton]
    omega
  · unfold a
    rw [ht24]
    norm_num [Nat.factorial]


private theorem ascent_finish (q n b B k x : ℕ) (hk : 1 ≤ k)
    (hf : Nat.factorial k = 2 * b) (hF : Nat.factorial (k + 1) = 2 * B)
    (hx : b < x) (hxB : x ≤ B) (hbudget : B - x ≤ q)
    (hl : ∀ z : ℤ, z ∈ terms n ↔ -(b : ℤ) ≤ z ∧ z ≤ x)
    (hc : a n = x) :
    ∃ m : ℕ, (∀ z : ℤ, z ∈ terms m ↔ -(b : ℤ) ≤ z ∧ z ≤ B) ∧ a m = B := by
  induction q generalizing n x with
  | zero =>
      have he : x = B := by omega
      exact ⟨n, he ▸ hl, he ▸ hc⟩
  | succ q ih =>
      by_cases he : x = B
      · exact ⟨n, he ▸ hl, he ▸ hc⟩
      have hs : a (n + 1) = ((x + 1 : ℕ) : ℤ) := by
        rw [a_succ, hc]
        simpa only [Nat.cast_add, Nat.cast_one] using
          ascent_next (terms n) b B k x hk hf hF hx (by omega) hl
      have hls : ∀ z : ℤ, z ∈ terms (n + 1) ↔ -(b : ℤ) ≤ z ∧ z ≤ (x + 1 : ℕ) := by
        intro z
        rw [mem_terms_succ, hs, hl]
        omega
      exact ih (n + 1) (x + 1) (by omega) (by omega) (by omega) hls hs

private theorem factorial_half (k : ℕ) (hk : 2 ≤ k) :
    Nat.factorial k = 2 * (Nat.factorial k / 2) := by
  have hd := Nat.factorial_dvd_factorial hk
  norm_num [Nat.factorial] at hd
  have hm := Nat.mod_eq_zero_of_dvd hd
  omega

private theorem block_step (k : ℕ) (hk : 4 ≤ k) (hblock : Block k) : Block (k + 1) := by
  obtain ⟨n, hl, hc⟩ := hblock
  let b := Nat.factorial k / 2
  let B := Nat.factorial (k + 1) / 2
  let L := b + 1
  have hf : Nat.factorial k = 2 * b := factorial_half k (by omega)
  have hF : Nat.factorial (k + 1) = 2 * B := factorial_half (k + 1) (by omega)
  have hb : 12 ≤ b := by
    have hsmall := Nat.factorial_le hk
    norm_num [Nat.factorial] at hsmall
    omega
  have hLB : L + 1 < B := by
    have hg := Nat.mul_le_mul_right (Nat.factorial k) (show 3 ≤ k + 1 by omega)
    rw [← Nat.factorial_succ] at hg
    dsimp [L]
    omega
  change (∀ z : ℤ, z ∈ terms n ↔ -(b : ℤ) ≤ z ∧ z ≤ b) at hl
  change a n = 1 - (b : ℤ) at hc
  have hfirst : a (n + 1) = (L : ℤ) := by
    rw [a_succ, hc]
    simpa only [L, Nat.cast_add, Nat.cast_one] using
      jump_up (terms n) b k hf (by omega) (by omega) hl
  have hlfirst : ∀ z : ℤ, z ∈ terms (n + 1) ↔ -(b : ℤ) ≤ z ∧ z ≤ L := by
    intro z
    rw [mem_terms_succ, hfirst, hl]
    dsimp [L]
    omega
  obtain ⟨m, hlm, hcm⟩ := ascent_finish B (n + 1) b B k L (by omega) hf hF
    (by dsimp [L]; omega) (by omega) (by omega) hlfirst hfirst
  have hdown : a (m + 1) = -(B : ℤ) := by
    rw [a_succ, hcm]
    exact jump_down (terms m) b B k (by omega) hf hF (by dsimp [L] at hLB; omega) hlm
  have hmem : ∀ z : ℤ, z ∈ terms (m + 1) ↔ z = -(B : ℤ) ∨ (-(b : ℤ) ≤ z ∧ z ≤ B) := by
    intro z
    rw [mem_terms_succ, hdown, hlm]
  have hframe : Frame (m + 1) L B := by
    constructor
    · intro z hz
      rw [hmem] at hz
      dsimp [L] at hLB
      omega
    · intro z hlo hhi
      rw [hmem]
      dsimp [L] at hlo
      omega
  have hsparse : Sparse (m + 1) L B := by
    intro t ht htB htm
    rw [hmem] at htm
    dsimp [L] at ht
    omega
  have hholes : ∀ t : ℕ, L ≤ t → t < B → -(t : ℤ) ∉ terms (m + 1) := by
    intro t ht htB htm
    rw [hmem] at htm
    dsimp [L] at ht
    omega
  have hBmem : -(B : ℤ) ∈ terms (m + 1) := (hmem _).2 (Or.inl rfl)
  obtain ⟨d, hfd, hpd, hcd, hBd⟩ := descent_finish L B B (m + 1)
    (by dsimp [L]; omega) (by omega) le_rfl hframe hsparse hdown hholes hBmem
  have hlower : ∀ t : ℕ, t ≤ L → -(t : ℤ) ∈ terms d := by
    intro t ht
    by_cases he : t = L
    · rw [he, ← hcd]
      exact (mem_terms d (a d)).2 ⟨d, le_rfl, rfl⟩
    · exact hfd.2 _ (by omega) (by omega)
  obtain ⟨f, hlf, hcf⟩ := fill_finish L B B d L (by dsimp [L]; omega) le_rfl
    (by omega) (by omega) hfd hcd hBd hlower hpd
  exact ⟨f, hlf, hcf⟩

private theorem all_blocks (k : ℕ) (hk : 4 ≤ k) : Block k := by
  exact Nat.le_induction base_block (fun j hj hb => block_step j hj hb) k hk


private def intervalList (b : ℕ) : List ℤ :=
  (List.range (2 * b + 1)).map (fun i : ℕ => (i : ℤ) - (b : ℤ))

private theorem mem_intervalList (b : ℕ) (z : ℤ) :
    z ∈ intervalList b ↔ -(b : ℤ) ≤ z ∧ z ≤ b := by
  simp only [intervalList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    constructor <;> omega
  · intro hz
    refine ⟨(z + b).toNat, ?_, ?_⟩
    · omega
    · omega

private theorem intervalList_nodup (b : ℕ) : (intervalList b).Nodup := by
  apply List.Nodup.map (f := fun i : ℕ => (i : ℤ) - (b : ℤ))
  · intro i j he
    dsimp at he
    omega
  · exact List.nodup_range

private theorem block_invariant (k : ℕ) (hk : 4 ≤ k) :
    (terms (Nat.factorial k)).Perm (intervalList (Nat.factorial k / 2)) ∧
      a (Nat.factorial k) = 1 - ((Nat.factorial k / 2 : ℕ) : ℤ) := by
  obtain ⟨n, hn, hc⟩ := all_blocks k hk
  have hp : (terms n).Perm (intervalList (Nat.factorial k / 2)) := by
    apply (List.perm_ext_iff_of_nodup (terms_nodup n) (intervalList_nodup _)).2
    intro z
    rw [hn, mem_intervalList]
  have hlen := hp.length_eq
  rw [terms_length] at hlen
  simp only [intervalList, List.length_map, List.length_range] at hlen
  have hf := factorial_half k (by omega)
  have he : n = Nat.factorial k := by omega
  exact ⟨he ▸ hp, he ▸ hc⟩

/-- Every integer occurs in the literal factorial Heraclitus recurrence. -/
theorem result : claim := by
  intro z
  let k := 4 + 2 * z.natAbs
  obtain ⟨hp, _⟩ := block_invariant k (by dsimp [k]; omega)
  have hf := Nat.self_le_factorial k
  have hz : z ∈ intervalList (Nat.factorial k / 2) := by
    rw [mem_intervalList]
    dsimp [k] at *
    constructor <;> omega
  obtain ⟨i, _, hi⟩ := (mem_terms (Nat.factorial k) z).1 (hp.mem_iff.mpr hz)
  exact ⟨i, hi⟩

end D5.S3.Combinatorics.Permutation.FactorialHeraclitusTransform

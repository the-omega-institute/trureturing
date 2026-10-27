/- GID: D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The maximal arithmetic-geometric entry index is 2d-5 for d >= 5, and 2 for d=3. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex

/-- The arithmetic-mean matrix of the source probability vector. -/
def arith {d : ℕ} (p : Fin d → ℝ) (ij : Fin d × Fin d) : ℝ :=
  (p ij.1 + p ij.2) / 2

/-- The geometric-mean matrix, counting both ordered positions. -/
def geom {d : ℕ} (p : Fin d → ℝ) (ij : Fin d × Fin d) : ℝ :=
  Real.sqrt (p ij.1 * p ij.2)

/-- The sum of the `m` largest entries, with multiplicity. This maximum over position
sets equals the sorted-prefix sum for every real-valued `f`; it includes all entries
when `m ≥ d*d`. -/
def topSum {d : ℕ} (f : Fin d × Fin d → ℝ) (m : ℕ) : ℝ :=
  (Finset.univ.powersetCard (min m (d * d))).sup'
    (Finset.powersetCard_nonempty.mpr (by simpa using Nat.min_le_right m (d * d)))
    (fun s => ∑ ij ∈ s, f ij)

/-- Nonnegativity and unit total mass. -/
def IsProbability {d : ℕ} (p : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Indices for which the source inequality holds for every probability vector. -/
def admissibleIndices (d : ℕ) : Set ℕ :=
  {m | ∀ p : Fin d → ℝ, IsProbability p → topSum (arith p) m + topSum (geom p) m ≤ d}

private lemma top_sum_le {d m : ℕ} (f : Fin d × Fin d → ℝ) (a : ℝ)
    (h : ∀ s : Finset (Fin d × Fin d), s.card = min m (d * d) →
      ∑ ij ∈ s, f ij ≤ a) : topSum f m ≤ a := by
  sorry

private lemma sum_le_top_sum {d m : ℕ} (f : Fin d × Fin d → ℝ)
    (s : Finset (Fin d × Fin d)) (hs : s.card = min m (d * d)) :
    ∑ ij ∈ s, f ij ≤ topSum f m := by
  sorry

private lemma top_sum_attained {d m : ℕ} (f : Fin d × Fin d → ℝ) :
    ∃ s : Finset (Fin d × Fin d), s.card = min m (d * d) ∧
      topSum f m = ∑ ij ∈ s, f ij := by
  sorry

private lemma top_sum_mono {d : ℕ} (f : Fin d × Fin d → ℝ) (hf : ∀ ij, 0 ≤ f ij) :
    Monotone (topSum f) := by
  sorry

/-- A finite-dimensional quadratic certificate for the support budget. -/
private lemma support_budget_bound {n k : ℕ} (f p : Finset (Fin n))
    (h : Fin n → Fin n → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hdisj : Disjoint f p) (hsym : ∀ i j, h i j = h j i)
    (hzero : ∀ i j, 0 ≤ h i j) (hone : ∀ i j, h i j ≤ 1)
    (hsupp : ∀ i j, i ∉ f ∨ j ∉ f → h i j = 0)
    (hbudget : 2 * (f.card : ℝ) + p.card + ∑ i, ∑ j, h i j ≤ 2 * k) :
    2 * x * ((∑ i ∈ f, y i) + (∑ i ∈ p, y i) / 2) +
        (∑ i, ∑ j, h i j * y i * y j) ≤
      ((k : ℝ) + 2) * (∑ i, (y i) ^ 2) + k / ((k : ℝ) + 2) * x ^ 2 := by
  sorry

private lemma small_coordinate_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) (ht : ∀ i, p i ≤ 2 / 3)
    (s t : Finset (Fin d × Fin d)) (hs : s.card = 2 * d - 5)
    (htc : t.card = 2 * d - 5) :
    (∑ ij ∈ s, arith p ij) + (∑ ij ∈ t, geom p ij) ≤ d := by
  sorry

/-- Reduction of an optimal geometric selection to its full and partial cross supports. -/
private lemma large_coordinate_reduction {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) (i : Fin d) (hi : 2 / 3 < p i)
    (s t : Finset (Fin d × Fin d)) (hs : s.card = 2 * d - 5)
    (ht : t.card = 2 * d - 5)
    (hopt : ∀ u : Finset (Fin d × Fin d), u.card = t.card →
      (∑ ij ∈ u, geom p ij) ≤ ∑ ij ∈ t, geom p ij) :
    ∃ (f q : Finset (Fin d)) (h : Fin d → Fin d → ℝ) (x : ℝ) (y : Fin d → ℝ),
      Disjoint f q ∧ (∀ a b, h a b = h b a) ∧
      (∀ a b, 0 ≤ h a b) ∧ (∀ a b, h a b ≤ 1) ∧
      (∀ a b, a ∉ f ∨ b ∉ f → h a b = 0) ∧
      2 * (f.card : ℝ) + q.card + ∑ a, ∑ b, h a b ≤ 2 * (d - 3 : ℕ) ∧
      x ^ 2 + (∑ a, (y a) ^ 2) = 1 ∧
      (∑ ij ∈ s, arith p ij) + (∑ ij ∈ t, geom p ij) ≤
        ((d - 3 : ℕ) + 2 : ℝ) * x ^ 2 + (∑ a, (y a) ^ 2) +
        2 * x * ((∑ a ∈ f, y a) + (∑ a ∈ q, y a) / 2) +
        (∑ a, ∑ b, h a b * y a * y b) := by
  sorry

private lemma large_coordinate_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) (i : Fin d) (hi : 2 / 3 < p i)
    (s t : Finset (Fin d × Fin d)) (hs : s.card = 2 * d - 5)
    (ht : t.card = 2 * d - 5)
    (hopt : ∀ u : Finset (Fin d × Fin d), u.card = t.card →
      (∑ ij ∈ u, geom p ij) ≤ ∑ ij ∈ t, geom p ij) :
    (∑ ij ∈ s, arith p ij) + (∑ ij ∈ t, geom p ij) ≤ d := by
  obtain ⟨f, q, h, x, y, hdj, hsy, hz, ho, hsp, hb, hn, he⟩ :=
    large_coordinate_reduction hd p hp i hi s t hs ht hopt
  have hm := support_budget_bound f q h x y hdj hsy hz ho hsp hb
  have hk : ((d - 3 : ℕ) : ℝ) + 3 = d := by
    have : d - 3 + 3 = d := Nat.sub_add_cancel (by omega)
    exact_mod_cast this
  have hq : ((d - 3 : ℕ) : ℝ) / (((d - 3 : ℕ) : ℝ) + 2) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hy : 0 ≤ ∑ a, (y a) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_right hq (sq_nonneg x)]

private lemma main_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) :
    topSum (arith p) (2 * d - 5) + topSum (geom p) (2 * d - 5) ≤ d := by
  obtain ⟨s, hs, he⟩ := top_sum_attained (arith p) (m := 2 * d - 5)
  obtain ⟨t, ht, hf⟩ := top_sum_attained (geom p) (m := 2 * d - 5)
  have hm : min (2 * d - 5) (d * d) = 2 * d - 5 := by
    apply Nat.min_eq_left
    nlinarith
  rw [hm] at hs ht
  rw [he, hf]
  by_cases hi : ∀ i, p i ≤ 2 / 3
  · exact small_coordinate_bound hd p hp hi s t hs ht
  · push_neg at hi
    obtain ⟨i, hi⟩ := hi
    apply large_coordinate_bound hd p hp i hi s t hs ht
    intro u hu
    rw [← hf]
    exact sum_le_top_sum _ u (hu.trans (ht.trans hm.symm))

private lemma failure_next {d : ℕ} (hd : 5 ≤ d) :
    ∃ p : Fin d → ℝ, IsProbability p ∧
      (d : ℝ) < topSum (arith p) (2 * d - 4) + topSum (geom p) (2 * d - 4) := by
  sorry

private lemma three_bound (p : Fin 3 → ℝ) (hp : IsProbability p) :
    topSum (arith p) 2 + topSum (geom p) 2 ≤ 3 := by
  sorry

private lemma three_failure :
    ∃ p : Fin 3 → ℝ, IsProbability p ∧
      3 < topSum (arith p) 3 + topSum (geom p) 3 := by
  sorry

private lemma greatest_of_bound_failure {d m : ℕ}
    (hb : m ∈ admissibleIndices d)
    (hf : ∃ p : Fin d → ℝ, IsProbability p ∧
      (d : ℝ) < topSum (arith p) (m + 1) + topSum (geom p) (m + 1)) :
    IsGreatest (admissibleIndices d) m := by
  refine ⟨hb, ?_⟩
  intro n hn
  by_contra hmn
  have hmn : m + 1 ≤ n := by omega
  obtain ⟨p, hp, hf⟩ := hf
  have ha := top_sum_mono (arith p) (fun ij => by
    dsimp only [arith]
    positivity) hmn
  have hg := top_sum_mono (geom p) (fun _ => Real.sqrt_nonneg _) hmn
  have hh := hn p hp
  linarith

/-- The Caro–Graswald maximal-index conjecture in dimensions at least five,
and its corrected three-dimensional boundary. -/
theorem result :
    (∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (2 * d - 5)) ∧
      IsGreatest (admissibleIndices 3) 2 := by
  constructor
  · intro d hd
    apply greatest_of_bound_failure
    · exact fun p hp => main_bound hd p hp
    · have h : 2 * d - 5 + 1 = 2 * d - 4 := by omega
      rw [h]
      exact failure_next hd
  · apply greatest_of_bound_failure
    · exact three_bound
    · exact three_failure

end D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex

/- GID: D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The maximal arithmetic-geometric entry index is 2d-5 for d >= 5, and 2 for d=3. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push

/-! The two mean matrices are optimized over independent sets of ordered positions. -/

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
  classical
  unfold topSum
  apply Finset.sup'_le
  intro s hs
  exact h s (Finset.mem_powersetCard.mp hs).2

private lemma sum_le_top_sum {d m : ℕ} (f : Fin d × Fin d → ℝ)
    (s : Finset (Fin d × Fin d)) (hs : s.card = min m (d * d)) :
    ∑ ij ∈ s, f ij ≤ topSum f m := by
  classical
  unfold topSum
  exact Finset.le_sup' (fun s : Finset (Fin d × Fin d) => ∑ ij ∈ s, f ij)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs⟩)

private lemma top_sum_attained {d m : ℕ} (f : Fin d × Fin d → ℝ) :
    ∃ s : Finset (Fin d × Fin d), s.card = min m (d * d) ∧
      topSum f m = ∑ ij ∈ s, f ij := by
  classical
  unfold topSum
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ.powersetCard (min m (d * d)))
    (Finset.powersetCard_nonempty.mpr (by simp))
    (fun s : Finset (Fin d × Fin d) => ∑ ij ∈ s, f ij)
  exact ⟨s, (Finset.mem_powersetCard.mp hs).2, he⟩

private lemma top_sum_mono {d : ℕ} (f : Fin d × Fin d → ℝ) (hf : ∀ ij, 0 ≤ f ij) :
    Monotone (topSum f) := by
  classical
  intro a b hab
  apply top_sum_le
  intro s hs
  obtain ⟨t, hst, _, ht⟩ := Finset.exists_subsuperset_card_eq (n := min b (d * d))
    (Finset.subset_univ s) (hs.trans_le (min_le_min_right (d * d) hab))
    (by simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      using Nat.min_le_right b (d * d))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hst (fun ij _ _ => hf ij)).trans
    (sum_le_top_sum f t ht)

private lemma young_weight (a x y : ℝ) (ha : 0 < a) :
    2 * x * y ≤ y ^ 2 / a + a * x ^ 2 := by
  apply (mul_le_mul_iff_left₀ ha).mp
  calc
    2 * x * y * a ≤ y ^ 2 + (a * x) ^ 2 := by
      nlinarith [sq_nonneg (y - a * x)]
    _ = (y ^ 2 / a + a * x ^ 2) * a := by field_simp [ne_of_gt ha]

private lemma weighted_schur_bound {n : ℕ} (s : Finset (Fin n))
    (h : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (l x : ℝ) (y : Fin n → ℝ)
    (hsym : ∀ i j, h i j = h j i) (hh : ∀ i j, 0 ≤ h i j)
    (hv : ∀ i ∈ s, 0 < v i)
    (hrow : ∀ i ∈ s, 1 + ∑ j ∈ s, h i j * v j ≤ l * v i) :
    2 * x * (∑ i ∈ s, y i) + (∑ i ∈ s, ∑ j ∈ s, h i j * y i * y j) ≤
      l * (∑ i ∈ s, (y i) ^ 2) + (∑ i ∈ s, v i) * x ^ 2 := by
  have hlinear := Finset.sum_le_sum (s := s) (fun i hi => young_weight (v i) x (y i) (hv i hi))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hlinear
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s, h i j * (v i / v j * (y j) ^ 2)) =
        ∑ i ∈ s, ∑ j ∈ s, h i j * (v j / v i * (y i) ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  have hquad :
      2 * (∑ i ∈ s, ∑ j ∈ s, h i j * y i * y j) ≤
        (∑ i ∈ s, ∑ j ∈ s, h i j * (v j / v i * (y i) ^ 2)) +
        (∑ i ∈ s, ∑ j ∈ s, h i j * (v i / v j * (y j) ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hy := young_weight (v i / v j) (y j) (y i) (div_pos (hv i hi) (hv j hj))
    have hy' : 2 * y i * y j ≤ v j / v i * (y i) ^ 2 +
        v i / v j * (y j) ^ 2 := by
      convert hy using 1 <;> field_simp <;> ring
    nlinarith [mul_le_mul_of_nonneg_left hy' (hh i j)]
  rw [hswap] at hquad
  have hfactor :
      (∑ i ∈ s, ∑ j ∈ s, h i j * (v j / v i * (y i) ^ 2)) =
        ∑ i ∈ s, (∑ j ∈ s, h i j * v j) * ((y i) ^ 2 / v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfactor] at hquad
  have hdiag :
      (∑ i ∈ s, (y i) ^ 2 / v i) +
          (∑ i ∈ s, (∑ j ∈ s, h i j * v j) * ((y i) ^ 2 / v i)) ≤
        l * (∑ i ∈ s, (y i) ^ 2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hhrow := mul_le_mul_of_nonneg_right (hrow i hi)
      (div_nonneg (sq_nonneg (y i)) (hv i hi).le)
    have he : l * v i * ((y i) ^ 2 / v i) = l * (y i) ^ 2 := by
      field_simp [ne_of_gt (hv i hi)]
    rw [he] at hhrow
    nlinarith
  linarith

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
  classical
  let r : ℝ := f.card
  let l : ℝ := (k : ℝ) + 2
  let b : ℝ := ∑ i ∈ f, ∑ j ∈ f, h i j
  have hrestrict (a : Fin n → Fin n → ℝ) :
      (∑ i, ∑ j, h i j * a i j) = ∑ i ∈ f, ∑ j ∈ f, h i j * a i j := by
    symm
    calc
      _ = ∑ i ∈ f, ∑ j, h i j * a i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_subset (Finset.subset_univ f)
        intro j hj hjf
        rw [hsupp i j (Or.inr hjf), zero_mul]
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_univ f)
        intro i hi hif
        apply Finset.sum_eq_zero
        intro j hj
        rw [hsupp i j (Or.inl hif), zero_mul]
  have hb : 0 ≤ b := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hzero i j))
  have htotal : (∑ i, ∑ j, h i j) = b := by
    simpa only [mul_one] using hrestrict (fun _ _ => 1)
  rw [htotal] at hbudget
  have hr : r ≤ k := by dsimp only [r]; nlinarith [(Nat.cast_nonneg p.card : (0 : ℝ) ≤ p.card)]
  have hl : 0 < l := by dsimp only [l]; positivity
  have hgap : 2 ≤ l - r := by dsimp only [l]; linarith
  have hgap0 : 0 < l - r := by linarith
  have hrows (i : Fin n) : 0 ≤ ∑ j ∈ f, h i j :=
    Finset.sum_nonneg (fun j _ => hzero i j)
  have hrowle (i : Fin n) : (∑ j ∈ f, h i j) ≤ r := by
    calc
      _ ≤ ∑ _j ∈ f, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hone i j)
      _ = r := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl
  let v : Fin n → ℝ := fun i => (1 + (∑ j ∈ f, h i j) / (l - r)) / l
  have hv (i : Fin n) : 0 < v i := by
    exact div_pos (by linarith [div_nonneg (hrows i) hgap0.le]) hl
  have hvle (i : Fin n) : v i ≤ 1 / (l - r) := by
    apply (div_le_iff₀ hl).mpr
    have hrdiv := (div_le_div_iff_of_pos_right hgap0).mpr (hrowle i)
    have he : 1 + r / (l - r) = (1 / (l - r)) * l := by
      field_simp <;> ring
    linarith
  have hsuper (i : Fin n) : 1 + (∑ j ∈ f, h i j * v j) ≤ l * v i := by
    have hle : (∑ j ∈ f, h i j * v j) ≤ (∑ j ∈ f, h i j) / (l - r) := by
      calc
        _ ≤ ∑ j ∈ f, h i j * (1 / (l - r)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hvle j) (hzero i j))
        _ = _ := by rw [← Finset.sum_mul]; ring
    have he : l * v i = 1 + (∑ j ∈ f, h i j) / (l - r) := by
      dsimp only [v]
      field_simp [ne_of_gt hl]
    linarith
  have hf := weighted_schur_bound f h v l x y hsym hzero (fun i _ => hv i)
    (fun i _ => hsuper i)
  have hp := weighted_schur_bound p (fun _ _ => 0) (fun _ => 1 / l) l (x / 2) y
    (fun _ _ => rfl) (fun _ _ => le_rfl) (fun _ _ => div_pos (by norm_num) hl)
    (fun _ _ => by
      simp only [zero_mul, Finset.sum_const_zero, add_zero]
      exact le_of_eq (by field_simp [ne_of_gt hl]))
  simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at hp
  have hsv : (∑ i ∈ f, v i) = (r + b / (l - r)) / l := by
    dsimp only [v, r, b]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbd : b / (l - r) ≤ b / 2 := by
    apply (div_le_iff₀ hgap0).mpr
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hgap)]
  have hcoef : (∑ i ∈ f, v i) + (p.card : ℝ) / (4 * l) ≤ (k : ℝ) / l := by
    calc
      _ = (r + b / (l - r) + (p.card : ℝ) / 4) / l := by
        rw [hsv]; field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp only [r]; linarith) hl.le
  have hnorm : (∑ i ∈ f, (y i) ^ 2) + (∑ i ∈ p, (y i) ^ 2) ≤ ∑ i, (y i) ^ 2 := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg (y i))
  have hq : (∑ i, ∑ j, h i j * y i * y j) =
      ∑ i ∈ f, ∑ j ∈ f, h i j * y i * y j := by
    simpa only [mul_assoc] using hrestrict (fun i j => y i * y j)
  rw [hq]
  have hpid : (p.card : ℝ) * (1 / l) * (x / 2) ^ 2 =
      ((p.card : ℝ) / (4 * l)) * x ^ 2 := by field_simp <;> ring
  rw [hpid] at hp
  have hcombine := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
  have hn := mul_le_mul_of_nonneg_left hnorm hl.le
  change _ ≤ l * (∑ i, (y i) ^ 2) + (k : ℝ) / l * x ^ 2
  nlinarith

private lemma small_coordinate_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) (ht : ∀ i, p i ≤ 2 / 3)
    (s t : Finset (Fin d × Fin d)) (hs : s.card = 2 * d - 5)
    (htc : t.card = 2 * d - 5) :
    (∑ ij ∈ s, arith p ij) + (∑ ij ∈ t, geom p ij) ≤ d := by
  sorry

private lemma probability_le_one {d : ℕ} {p : Fin d → ℝ} (hp : IsProbability p)
    (i : Fin d) : p i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
    hp.1 j) (Finset.mem_univ i)
  exact h.trans_eq hp.2

private lemma probability_pair_le_one {d : ℕ} {p : Fin d → ℝ}
    (hp : IsProbability p) {i j : Fin d} (hij : i ≠ j) : p i + p j ≤ 1 := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({i, j} : Finset (Fin d))) (fun a _ _ => hp.1 a)
  simpa only [Finset.sum_pair hij, hp.2] using h

private lemma optimal_selection_exchange {d : ℕ} (v : Fin d × Fin d → ℝ)
    (t : Finset (Fin d × Fin d))
    (hopt : ∀ u : Finset (Fin d × Fin d), u.card = t.card →
      (∑ ij ∈ u, v ij) ≤ ∑ ij ∈ t, v ij)
    {a b : Fin d × Fin d} (ha : a ∈ t) (hab : v a < v b) : b ∈ t := by
  classical
  by_contra hb
  have hbe : b ∉ t.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  have hcard : (insert b (t.erase a)).card = t.card := by
    rw [Finset.card_insert_of_notMem hbe, Finset.card_erase_of_mem ha]
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  have hh := hopt (insert b (t.erase a)) hcard
  rw [Finset.sum_insert hbe] at hh
  have he := Finset.sum_erase_add t v ha
  linarith

private lemma large_arithmetic_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : IsProbability p) (i : Fin d) (hi : 2 / 3 < p i)
    (s : Finset (Fin d × Fin d)) (hs : s.card = 2 * d - 5) :
    (∑ ij ∈ s, arith p ij) ≤ ((d - 3 : ℕ) + 1 : ℝ) * p i + (1 - p i) := by
  classical
  let e : Fin d × Fin d → ℝ := fun ab =>
    if ab.1 = i then p ab.2 / 2 else if ab.2 = i then p ab.1 / 2 else 0
  have he : ∀ ab, 0 ≤ e ab := by
    intro ab
    dsimp only [e]
    split_ifs <;> positivity
  have hpoint : ∀ ab, arith p ab ≤ p i / 2 + e ab := by
    rintro ⟨a, b⟩
    dsimp only [arith, e]
    by_cases ha : a = i
    · subst a; rw [if_pos rfl]; linarith
    · rw [if_neg ha]
      by_cases hb : b = i
      · subst b; rw [if_pos rfl]; linarith
      · rw [if_neg hb]
        have hpa := probability_pair_le_one hp ha
        have hpb := probability_pair_le_one hp hb
        linarith
  have heval : (∑ ab, e ab) = 1 - p i / 2 := by
    rw [Fintype.sum_prod_type]
    change (∑ a, ∑ b, if a = i then p b / 2 else if b = i then p a / 2 else 0) = _
    simp only [ite_apply, Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, ← Finset.sum_div, hp.2]
    rw [Finset.sum_ite]
    simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
    have herase : (∑ a ∈ Finset.univ.filter (fun a => ¬a = i), p a / 2) =
        (1 - p i) / 2 := by
      rw [Finset.filter_ne', ← Finset.sum_div]
      have hh := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
      rw [hp.2] at hh
      congr 1
      linarith
    rw [herase]
    ring
  have hh := Finset.sum_le_sum (s := s) (fun ab _ => hpoint ab)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hs] at hh
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun ab _ _ => he ab)
  rw [heval] at hsub
  have hcast : ((2 * d - 5 : ℕ) : ℝ) = 2 * (d : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  have hk : ((d - 3 : ℕ) : ℝ) = (d : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcast, hk] at *
  linarith

private lemma selected_tail_closed {d : ℕ} (p : Fin d → ℝ) (hp : IsProbability p)
    (i : Fin d) (hi : 2 / 3 < p i) (t : Finset (Fin d × Fin d))
    (hopt : ∀ u : Finset (Fin d × Fin d), u.card = t.card →
      (∑ ij ∈ u, geom p ij) ≤ ∑ ij ∈ t, geom p ij) :
    ∀ a b, a ≠ i → b ≠ i → (a, b) ∈ t → 0 < p a → 0 < p b →
      (i, a) ∈ t ∧ (a, i) ∈ t ∧ (i, b) ∈ t ∧ (b, i) ∈ t := by
  intro a b hai hbi hab hpa hpb
  have hia : p a < p i := by
    have := probability_pair_le_one hp hai
    linarith
  have hib : p b < p i := by
    have := probability_pair_le_one hp hbi
    linarith
  have hmul := mul_nonneg (hp.1 a) (hp.1 b)
  have hga : geom p (a, b) < geom p (i, a) := by
    apply Real.sqrt_lt_sqrt hmul
    dsimp only
    nlinarith
  have hgb : geom p (a, b) < geom p (i, b) := by
    apply Real.sqrt_lt_sqrt hmul
    dsimp only
    nlinarith
  have hgas : geom p (i, a) = geom p (a, i) := by
    dsimp only [geom]; rw [mul_comm]
  have hgbs : geom p (i, b) = geom p (b, i) := by
    dsimp only [geom]; rw [mul_comm]
  exact ⟨optimal_selection_exchange (geom p) t hopt hab hga,
    optimal_selection_exchange (geom p) t hopt hab (hga.trans_eq hgas),
    optimal_selection_exchange (geom p) t hopt hab hgb,
    optimal_selection_exchange (geom p) t hopt hab (hgb.trans_eq hgbs)⟩

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
  have ha := large_arithmetic_bound hd p hp i hi s hs
  have hc := selected_tail_closed p hp i hi t hopt
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
    have : 2 * d ≤ d * d := by nlinarith
    omega
  rw [hm] at hs ht
  rw [he, hf]
  by_cases hi : ∀ i, p i ≤ 2 / 3
  · exact small_coordinate_bound hd p hp hi s t hs ht
  · push Not at hi
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
    exact div_nonneg (add_nonneg (hp.1 _) (hp.1 _)) (by norm_num)) hmn
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

/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: All-total integer extrema and equality classes for replica three. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
import Mathlib.Data.Fin.Tuple.Sort

/-!
Positive integer mode counts only. The balanced and extreme classes include
every permutation and all ties. Scientific source: Haobo Ma then Wenlin Zhang,
4 November 2026, CC BY 4.0; Camargo–Nishida for the physical family and
Marshall–Olkin–Arnold for majorization. The actual integral bridge and the
strict scalar comparison are reused with their exact parameters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema

open ReplicaThreeScalar ReplicaThreeMajorization ReplicaThree
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing

/-- Descending balanced sizes: exactly `N % 3` entries exceed `N / 3`. -/
def balanced (N : ℕ) : Fin 3 → ℕ :=
  ![N / 3 + if 0 < N % 3 then 1 else 0,
    N / 3 + if 1 < N % 3 then 1 else 0, N / 3]

/-- The positive-integer extreme vector. -/
def extreme (N : ℕ) : Fin 3 → ℕ := ![N - 2, 1, 1]

/-- Pairwise distances at most one, expressed without truncated subtraction. -/
def IsBalanced (x : Fin 3 → ℕ) : Prop := ∀ i j, x i ≤ x j + 1

private def realVector (x : Fin 3 → ℕ) : Fin 3 → ℝ := fun i => x i

private def sortedPerm (x : Fin 3 → ℕ) : Equiv.Perm (Fin 3) :=
  Fin.revPerm.trans (Tuple.sort x)

private lemma sorted_antitone (x : Fin 3 → ℕ) : Antitone (x ∘ sortedPerm x) := by
  intro i j hij
  exact Tuple.monotone_sort x (Fin.rev_le_rev.mpr hij)

private lemma desc_sorted (x : Fin 3 → ℕ) :
    desc (realVector x) = List.ofFn (realVector (x ∘ sortedPerm x)) := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
  · exact List.pairwise_mergeSort' (fun a b : ℝ => b ≤ a) _
  · have h : Antitone (realVector (x ∘ sortedPerm x)) := by
      intro i j hij
      dsimp only [realVector]
      exact_mod_cast sorted_antitone x hij
    exact h.sortedGE_ofFn.pairwise
  · exact (List.mergeSort_perm _ _).trans
      ((sortedPerm x).ofFn_comp_perm (realVector x)).symm

private lemma desc_antitone (x : Fin 3 → ℕ) (hx : Antitone x) :
    desc (realVector x) = List.ofFn (realVector x) := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
  · exact List.pairwise_mergeSort' (fun a b : ℝ => b ≤ a) _
  · have h : Antitone (realVector x) := by
      intro i j hij
      dsimp only [realVector]
      exact_mod_cast hx hij
    exact h.sortedGE_ofFn.pairwise
  · exact List.mergeSort_perm _ _

private lemma balanced_facts (N : ℕ) (hN : 3 ≤ N) :
    Antitone (balanced N) ∧ (∀ i, 0 < balanced N i) ∧
      (∑ i, balanced N i) = N ∧ IsBalanced (balanced N) := by
  have hr := Nat.mod_lt N (by norm_num : 0 < 3)
  have hdiv := Nat.mod_add_div N 3
  have hq : 0 < N / 3 := Nat.div_pos hN (by norm_num)
  have cases : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
  rcases cases with h | h | h <;>
    simp only [balanced, h, Nat.zero_lt_one, Nat.zero_lt_succ, ite_true,
      Nat.lt_irrefl, not_lt_zero, ite_false, Nat.reduceLT, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_three] <;>
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all <;> omega)
    | (intro i; fin_cases i <;> simp_all <;> omega)
    | omega
    | (intro i j; fin_cases i <;> fin_cases j <;> simp_all <;> omega)

private lemma sorted_bounds (N : ℕ) (x : Fin 3 → ℕ) (hx : Antitone x)
    (hs : (∑ i, x i) = N) :
    balanced N 0 ≤ x 0 ∧ x 2 ≤ balanced N 2 ∧
      (IsBalanced x ↔ x = balanced N) := by
  have h01 := hx (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := hx (show (1 : Fin 3) ≤ 2 by decide)
  have hr := Nat.mod_lt N (by norm_num : 0 < 3)
  have hdiv := Nat.mod_add_div N 3
  simp only [Fin.sum_univ_three] at hs
  have hbeq : IsBalanced x ↔ x 0 ≤ x 2 + 1 := by
    constructor
    · intro h; exact h 0 2
    · intro h i j
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
  rw [hbeq]
  have cases : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
  rcases cases with h | h | h <;>
    simp only [balanced, h, Nat.zero_lt_one, Nat.zero_lt_succ, ite_true,
      Nat.lt_irrefl, not_lt_zero, ite_false, Nat.reduceLT, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    refine ⟨by omega, by omega, ?_⟩
  all_goals constructor
  all_goals first
    | (intro h; funext i; fin_cases i <;> simp <;> omega)
    | (intro h; have h0 := congrFun h 0; have h2 := congrFun h 2; simp_all <;> omega)

private lemma moreMixed_bounds (x y : Fin 3 → ℕ) (hy : Antitone y)
    (hs : (∑ i, x i) = ∑ i, y i)
    (h0 : x (sortedPerm x 0) ≤ y 0) (h2 : y 2 ≤ x (sortedPerm x 2)) :
    moreMixed (realVector x) (realVector y) := by
  have hsum : (∑ i, (x ∘ sortedPerm x) i) = ∑ i, y i :=
    (Equiv.sum_comp (sortedPerm x) x).trans hs
  simp only [Fin.sum_univ_three, Function.comp_apply] at hsum
  unfold moreMixed
  rw [desc_sorted, desc_antitone y hy]
  constructor
  · intro n hn
    interval_cases n <;>
      simp [prefixSum, List.ofFn_succ, realVector] <;> norm_cast <;> omega
  · simp [prefixSum, List.ofFn_succ, realVector]
    exact_mod_cast (by omega : x (sortedPerm x 0) + (x (sortedPerm x 1) + x (sortedPerm x 2)) = y 0 + (y 1 + y 2))

private lemma moreMixed_balanced (N : ℕ) (hN : 3 ≤ N) (x : Fin 3 → ℕ)
    (hs : (∑ i, x i) = N) : moreMixed (realVector (balanced N)) (realVector x) := by
  have hb := balanced_facts N hN
  have hx := sorted_antitone x
  have hs' : (∑ i, (x ∘ sortedPerm x) i) = N :=
    (Equiv.sum_comp (sortedPerm x) x).trans hs
  have bounds := sorted_bounds N (x ∘ sortedPerm x) hx hs'
  have hsum : (∑ i, balanced N i : ℕ) = ∑ i, (x ∘ sortedPerm x) i := hb.2.2.1.trans hs'.symm
  simp only [Fin.sum_univ_three, Function.comp_apply] at hsum bounds
  have hm : moreMixed (realVector (balanced N))
      (realVector (x ∘ sortedPerm x)) := by
    unfold moreMixed
    rw [desc_antitone _ hb.1, desc_antitone _ hx]
    constructor
    · intro n hn
      interval_cases n <;>
        simp [prefixSum, List.ofFn_succ, realVector] <;>
        norm_cast <;> omega
    · simp [prefixSum, List.ofFn_succ, realVector]
      exact_mod_cast (by omega : balanced N 0 + (balanced N 1 + balanced N 2) =
        x (sortedPerm x 0) + (x (sortedPerm x 1) + x (sortedPerm x 2)))
  have hd : desc (realVector (x ∘ sortedPerm x)) = desc (realVector x) := by
    rw [desc_antitone _ hx, desc_sorted]
  simpa only [moreMixed, hd] using hm

private lemma moreMixed_extreme (N : ℕ) (hN : 3 ≤ N) (x : Fin 3 → ℕ)
    (hp : ∀ i, 0 < x i) (hs : (∑ i, x i) = N) :
    moreMixed (realVector x) (realVector (extreme N)) := by
  have hsum := (Equiv.sum_comp (sortedPerm x) x).trans hs
  simp only [Fin.sum_univ_three, Function.comp_apply] at hsum
  apply moreMixed_bounds x (extreme N)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [extreme] <;> omega
  · simp only [Fin.sum_univ_three] at hs ⊢
    simp only [extreme, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  · have h1 := hp (sortedPerm x 1)
    have h2 := hp (sortedPerm x 2)
    simp [extreme]
    omega
  · simpa [extreme] using Nat.succ_le_of_lt (hp (sortedPerm x 2))

private lemma balanced_iff_perm (N : ℕ) (hN : 3 ≤ N) (x : Fin 3 → ℕ)
    (hs : (∑ i, x i) = N) :
    IsBalanced x ↔ ∃ σ : Equiv.Perm (Fin 3), x = balanced N ∘ σ := by
  constructor
  · intro h
    have hs' : (∑ i, (x ∘ sortedPerm x) i) = N :=
      (Equiv.sum_comp (sortedPerm x) x).trans hs
    have he := (sorted_bounds N (x ∘ sortedPerm x) (sorted_antitone x) hs').2.2.mp
      (fun i j => h _ _)
    refine ⟨(sortedPerm x).symm, ?_⟩
    funext i
    simpa [Function.comp_def] using congrFun he ((sortedPerm x).symm i)
  · rintro ⟨σ,rfl⟩ i j
    exact (balanced_facts N hN).2.2.2 _ _

private lemma real_perm_iff (x y : Fin 3 → ℕ) :
    (∃ σ : Equiv.Perm (Fin 3), realVector x = realVector y ∘ σ) ↔
      ∃ σ : Equiv.Perm (Fin 3), x = y ∘ σ := by
  constructor <;> rintro ⟨σ,h⟩ <;> refine ⟨σ, ?_⟩ <;> funext i
  · have hi := congrFun h i
    dsimp only [realVector, Function.comp_apply] at hi ⊢
    exact_mod_cast hi
  · have hi := congrFun h i
    dsimp only [realVector, Function.comp_apply] at hi ⊢
    exact_mod_cast hi

private lemma perm_symm (x y : Fin 3 → ℕ) :
    (∃ σ : Equiv.Perm (Fin 3), x = y ∘ σ) ↔
      ∃ σ : Equiv.Perm (Fin 3), y = x ∘ σ := by
  constructor <;> rintro ⟨σ,h⟩ <;> refine ⟨σ.symm, ?_⟩ <;> funext i
  all_goals simpa [Function.comp_def] using (congrFun h (σ.symm i)).symm

/-- All-total scalar bounds on positive integer triples, with both iff
classifications. `balanced N` gives the value for every residue class of N. -/
theorem integer_extrema (k : ℝ) (hk : 0 < k) (N : ℕ) (hN : 3 ≤ N)
    (x : Fin 3 → ℕ) (hp : ∀ i, 0 < x i) (hs : (∑ i, x i) = N) :
    value k (balanced N 0) (balanced N 1) (balanced N 2) ≤
        value k (x 0) (x 1) (x 2) ∧
    value k (x 0) (x 1) (x 2) ≤ value k (extreme N 0) (extreme N 1) (extreme N 2) ∧
    (value k (x 0) (x 1) (x 2) =
        value k (balanced N 0) (balanced N 1) (balanced N 2) ↔ IsBalanced x) ∧
    (value k (x 0) (x 1) (x 2) =
        value k (extreme N 0) (extreme N 1) (extreme N 2) ↔
      ∃ σ : Equiv.Perm (Fin 3), x = extreme N ∘ σ) := by
  have hpr : ∀ i, 0 < realVector x i := by
    intro i; dsimp only [realVector]; exact_mod_cast hp i
  have hb : ∀ i, 0 < realVector (balanced N) i := by
    intro i; dsimp only [realVector]; exact_mod_cast (balanced_facts N hN).2.1 i
  have he : ∀ i, 0 < realVector (extreme N) i := by
    intro i; fin_cases i <;> simp [realVector, extreme] <;> omega
  obtain ⟨hmin,heqmin⟩ := schur_comparison k (realVector (balanced N)) (realVector x)
    hk hb hpr (moreMixed_balanced N hN x hs)
  obtain ⟨hmax,heqmax⟩ := schur_comparison k (realVector x) (realVector (extreme N))
    hk hpr he (moreMixed_extreme N hN x hp hs)
  refine ⟨hmin, hmax, ?_, ?_⟩
  · change (value k (realVector x 0) (realVector x 1) (realVector x 2) =
        value k (realVector (balanced N) 0) (realVector (balanced N) 1)
          (realVector (balanced N) 2) ↔ IsBalanced x)
    rw [eq_comm, heqmin, real_perm_iff, perm_symm, ← balanced_iff_perm N hN x hs]
  · exact heqmax.trans (real_perm_iff x (extreme N))

/-- All-total extrema of the actual integral-defined family. The two endpoint
values are the exact logarithmic formula evaluated at the displayed labelled
representatives. The minimum has `N % 3` entries equal to `N / 3 + 1`.
No real-valued party size is used in the physical family. -/
theorem GM3_three_extrema (N : ℕ) (hN : 3 ≤ N) (a : ℝ) (ha : 1 < a)
    (x : Fin 3 → ℕ) (hp : ∀ i, 0 < x i) (hs : (∑ i, x i) = N) :
    value (kappa N a) (balanced N 0) (balanced N 1) (balanced N 2) ≤
        GaussianMultiEntropyAsymptotic.GM3 3 (x 0) (x 1) (x 2) a ∧
    GaussianMultiEntropyAsymptotic.GM3 3 (x 0) (x 1) (x 2) a ≤
        value (kappa N a) (N - 2 : ℕ) 1 1 ∧
    (GaussianMultiEntropyAsymptotic.GM3 3 (x 0) (x 1) (x 2) a =
        value (kappa N a) (balanced N 0) (balanced N 1) (balanced N 2) ↔
      IsBalanced x) ∧
    (GaussianMultiEntropyAsymptotic.GM3 3 (x 0) (x 1) (x 2) a =
        value (kappa N a) (N - 2 : ℕ) 1 1 ↔
      ∃ σ : Equiv.Perm (Fin 3), x = extreme N ∘ σ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hk : 0 < kappa N a := by
    unfold kappa
    exact div_pos (by nlinarith) (by linarith)
  have hsum : (x 0 : ℝ) + x 1 + x 2 = N := by
    exact_mod_cast (show x 0 + x 1 + x 2 = N by simpa only [Fin.sum_univ_three] using hs)
  have hrepr : GaussianMultiEntropyAsymptotic.GM3 3 (x 0) (x 1) (x 2) a =
      value (kappa N a) (x 0) (x 1) (x 2) := by
    rw [GM3_three_closed _ _ _ a (hp 0) (hp 1) (hp 2) ha.le, hsum]
    exact (value_eq_log_ratio _ _ _ _ hk.le (by positivity) (by positivity)
      (by positivity)).symm
  rw [hrepr]
  simpa only [extreme, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Nat.cast_one] using integer_extrema (kappa N a) hk N hN x hp hs

/-- The two integer extremal classes coincide exactly for totals three and
four. For larger totals their scalar values are strictly separated. -/
theorem extremal_degeneracy (k : ℝ) (hk : 0 < k) (N : ℕ) (hN : 3 ≤ N) :
    (IsBalanced (extreme N) ↔ N = 3 ∨ N = 4) ∧
      (value k (balanced N 0) (balanced N 1) (balanced N 2) =
          value k (extreme N 0) (extreme N 1) (extreme N 2) ↔ N = 3 ∨ N = 4) := by
  have he : ∀ i, 0 < extreme N i := by
    intro i; fin_cases i <;> simp [extreme] <;> omega
  have hs : (∑ i, extreme N i) = N := by
    simp [Fin.sum_univ_three, extreme]; omega
  have hb : IsBalanced (extreme N) ↔ N = 3 ∨ N = 4 := by
    constructor
    · intro h
      have h02 := h 0 2
      simp only [extreme, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h02
      omega
    · intro h i j
      rcases h with rfl | rfl <;> fin_cases i <;> fin_cases j <;> norm_num [extreme]
  refine ⟨hb, ?_⟩
  rw [eq_comm, (integer_extrema k hk N hN (extreme N) he hs).2.2.1, hb]

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema

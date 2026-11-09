/- GID: D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Gao–Li's complete maximal identity conjecture for clique–path products. -/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
import D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination
import D5.S3.Factorization.BoninShadowMarkoffPositivity

/-! The complete maximal identity property for Cartesian products of cliques and paths. -/

open scoped BigOperators Matrix
open Polynomial Chebyshev

namespace D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity

/-- The maximal stable configuration belongs to the reduced integer Laplacian image. -/
def maximalIdentityAt (i j : ℕ) (s : Fin i × Fin j) : Prop := by
  classical
  exact ∃ f : {v : Fin i × Fin j // v ≠ s} → ℤ,
    ∀ v : {v : Fin i × Fin j // v ≠ s},
      ∑ w : {v : Fin i × Fin j // v ≠ s},
        ((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).lapMatrix ℤ v.1 w.1 *
          f w =
        (((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).degree v.1 : ℤ) - 1

/-- Gao–Li's classification under the reduced-Laplacian image reading. -/
def claim : Prop :=
  ∀ i j : ℕ, 2 ≤ i → 2 ≤ j →
    ((∀ s : Fin i × Fin j, maximalIdentityAt i j s) ↔ (i = 4 ∧ j = 2))

open Classical in
private lemma product_row (i j : ℕ) (f : Fin i × Fin j → ℤ) (a : Fin i) (t : Fin j) :
    (((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).lapMatrix ℤ *ᵥ f) (a, t) =
      (i : ℤ) * f (a, t) - ∑ b : Fin i, f (b, t) +
        ((SimpleGraph.pathGraph j).lapMatrix ℤ *ᵥ fun u => f (a, u)) t := by
  classical
  have ha := a.isLt
  rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.lapMatrix_mulVec_apply,
    SimpleGraph.degree_boxProd, SimpleGraph.neighborFinset_boxProd]
  simp only [Finset.sum_disjUnion, Finset.sum_product, Finset.sum_singleton,
    SimpleGraph.neighborFinset_top, SimpleGraph.IsRegularOfDegree.top.degree_eq,
    Fintype.card_fin, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
  have hs := Finset.sum_compl_add_sum ({a} : Finset (Fin i)) (fun b => f (b, t))
  simp only [Finset.sum_singleton] at hs
  linear_combination -hs

private lemma path_neighbors (j : ℕ) (t : Fin j) :
    (SimpleGraph.pathGraph j).neighborFinset t =
      (if h : 0 < t.val then {⟨t.val - 1, by omega⟩} else ∅) ∪
      (if h : t.val + 1 < j then {⟨t.val + 1, h⟩} else ∅) := by
  ext u
  have ht := t.isLt
  have hu := u.isLt
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj, Finset.mem_union]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

private lemma path_degree (j : ℕ) (t : Fin j) :
    ((SimpleGraph.pathGraph j).degree t : ℤ) =
      (if 0 < t.val then 1 else 0) + (if t.val + 1 < j then 1 else 0) := by
  have h :=
    D5.S3.Combinatorics.Graph.Domination.LeeLiuThreeRowIntegerDomination.path_neighbor_sum
      (fun _ => 1) t
  have h' : (SimpleGraph.pathGraph j).degree t =
      (if 0 < t.val then 1 else 0) + (if t.val + 1 < j then 1 else 0) := by
    simpa only [SimpleGraph.degree, Finset.card_eq_sum_ones, dite_eq_ite] using h
  exact_mod_cast h'

private lemma path_row (j : ℕ) (f : Fin j → ℤ) (t : Fin j) :
    ((SimpleGraph.pathGraph j).lapMatrix ℤ *ᵥ f) t =
      (if h : 0 < t.val then f t - f ⟨t.val - 1, by omega⟩ else 0) +
      (if h : t.val + 1 < j then f t - f ⟨t.val + 1, h⟩ else 0) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply', path_neighbors, Finset.sum_union]
  · split_ifs <;> simp
  · split_ifs <;> simp [Fin.ext_iff]

open Classical in
private lemma total_mass (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) :
    ∑ v : Fin i × Fin j,
      ((((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).degree v : ℤ) - 1) =
        (i : ℤ) * ((i : ℤ) * j - 2) := by
  have hp : ∑ t : Fin j, ((SimpleGraph.pathGraph j).degree t : ℤ) = 2 * ((j : ℤ) - 1) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ j)
    have hl : ∑ t : Fin (n + 1), (if 0 < t.val then 1 else 0 : ℤ) = n := by
      rw [Fin.sum_univ_succ]
      simp
    have hr : ∑ t : Fin (n + 1), (if t.val + 1 < n + 1 then 1 else 0 : ℤ) = n := by
      rw [Fin.sum_univ_castSucc]
      simp
    simp only [path_degree, Finset.sum_add_distrib, hl, hr, Nat.cast_add, Nat.cast_one]
    ring
  simp only [Fintype.sum_prod_type, SimpleGraph.degree_boxProd,
    SimpleGraph.IsRegularOfDegree.top.degree_eq, Fintype.card_fin,
    Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hp, Fintype.card_prod, Nat.cast_mul]
  ring

open Classical in
private lemma lift_equations (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (s : Fin i × Fin j)
    (h : maximalIdentityAt i j s) :
    ∃ f : Fin i × Fin j → ℤ, ∀ v : Fin i × Fin j,
      ((((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).lapMatrix ℤ) *ᵥ f) v =
        (((⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)).degree v : ℤ) - 1 -
          (if v = s then (i : ℤ) * ((i : ℤ) * j - 2) else 0) := by
  obtain ⟨g, hg⟩ := h
  let f : Fin i × Fin j → ℤ := fun v => if hv : v = s then 0 else g ⟨v, hv⟩
  have hf : f s = 0 := by simp [f]
  let G := (⊤ : SimpleGraph (Fin i)).boxProd (SimpleGraph.pathGraph j)
  have hr (v : Fin i × Fin j) (hv : v ≠ s) :
      (G.lapMatrix ℤ *ᵥ f) v = (G.degree v : ℤ) - 1 := by
    change ∑ w, G.lapMatrix ℤ v w * f w = _
    rw [Fintype.sum_eq_add_sum_subtype_ne _ s, hf, mul_zero, zero_add]
    convert hg ⟨v, hv⟩ using 1
    apply Finset.sum_congr rfl
    intro w hw
    simp only [f, dite_eq_right w.property]
    rfl
  have hz : ∑ v, (G.lapMatrix ℤ *ᵥ f) v = 0 := by
    have h := Matrix.dotProduct_transpose_mulVec (G.lapMatrix ℤ) f (1 : Fin i × Fin j → ℤ)
    rw [(G.isSymm_lapMatrix ℤ).eq, G.lapMatrix_mulVec_one_eq_zero ℤ] at h
    simpa only [dotProduct_zero, one_dotProduct] using h.symm
  have hm := total_mass i j hi hj
  change ∑ v, ((G.degree v : ℤ) - 1) = _ at hm
  rw [Fintype.sum_eq_add_sum_subtype_ne _ s] at hz hm
  have ht : ∑ v : {v : Fin i × Fin j // v ≠ s}, (G.lapMatrix ℤ *ᵥ f) v =
      ∑ v : {v : Fin i × Fin j // v ≠ s}, ((G.degree v : ℤ) - 1) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact hr v v.property
  rw [ht] at hz
  refine ⟨f, fun v => ?_⟩
  by_cases hv : v = s
  · subst v
    rw [ite_eq_left rfl]
    change (G.lapMatrix ℤ *ᵥ f) s = _
    linarith
  · rw [ite_eq_right hv, sub_zero]
    exact hr v hv

private lemma path_reduction (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : maximalIdentityAt i j (⟨0, by omega⟩, ⟨0, by omega⟩)) :
    ∃ x : ℕ → ℤ,
      x 1 = (i + 1 : ℤ) * x 0 ∧
      (∀ k : ℕ, k + 2 < j → x (k + 2) = (i + 2 : ℤ) * x (k + 1) - x k) ∧
      (i + 1 : ℤ) * x (j - 1) - x (j - 2) = -(i : ℤ) * ((i : ℤ) * j - 2) := by
  classical
  let a : Fin i := ⟨0, by omega⟩
  let b : Fin i := ⟨1, by omega⟩
  let z : Fin j := ⟨0, by omega⟩
  obtain ⟨f, hf⟩ := lift_equations i j hi hj (a, z) h
  let d : Fin j → ℤ := fun t => f (a, t) - f (b, t)
  have hd (t : Fin j) :
      (i : ℤ) * d t + ((SimpleGraph.pathGraph j).lapMatrix ℤ *ᵥ d) t =
        if t = z then -(i : ℤ) * ((i : ℤ) * j - 2) else 0 := by
    have ha := hf (a, t)
    have hb := hf (b, t)
    rw [product_row] at ha hb
    have hba : (b, t) ≠ (a, z) := by
      intro he
      have he' := congrArg (fun v : Fin i × Fin j => v.1.val) he
      norm_num [a, b] at he'
    have hat : (a, t) = (a, z) ↔ t = z := by simp only [Prod.mk.injEq, true_and]
    simp only [hba, ite_false, hat, SimpleGraph.degree_boxProd,
      SimpleGraph.IsRegularOfDegree.top.degree_eq] at ha hb
    change (i : ℤ) * (f (a, t) - f (b, t)) +
      ((SimpleGraph.pathGraph j).lapMatrix ℤ *ᵥ
        ((fun u => f (a, u)) - (fun u => f (b, u)))) t = _
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    by_cases ht : t = z
    · rw [ite_eq_left ht] at ha ⊢
      linear_combination ha - hb
    · rw [ite_eq_right ht] at ha ⊢
      linear_combination ha - hb
  let x : ℕ → ℤ := fun k => if hk : k < j then d ⟨j - 1 - k, by omega⟩ else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · have ht := hd ⟨j - 1, by omega⟩
    rw [path_row] at ht
    have hn : (⟨j - 1, by omega⟩ : Fin j) ≠ z := by
      intro he
      have he' := congrArg Fin.val he
      change j - 1 = 0 at he'
      omega
    simp only [dite_eq_left (by omega : 0 < j - 1),
      dite_eq_right (by omega : ¬ j - 1 + 1 < j), add_zero, ite_eq_right hn] at ht
    simp only [x, dite_eq_left (by omega : 1 < j), dite_eq_left (by omega : 0 < j), Nat.sub_zero]
    linear_combination -ht
  · intro k hk
    have ht := hd ⟨j - 2 - k, by omega⟩
    rw [path_row] at ht
    have hn : (⟨j - 2 - k, by omega⟩ : Fin j) ≠ z := by
      intro he
      have he' := congrArg Fin.val he
      change j - 2 - k = 0 at he'
      omega
    simp only [dite_eq_left (by omega : 0 < j - 2 - k),
      dite_eq_left (by omega : j - 2 - k + 1 < j), ite_eq_right hn] at ht
    simp only [x, dite_eq_left hk, dite_eq_left (by omega : k + 1 < j),
      dite_eq_left (by omega : k < j),
      show j - 1 - (k + 2) = j - 2 - k - 1 by omega,
      show j - 1 - (k + 1) = j - 2 - k by omega,
      show j - 1 - k = j - 2 - k + 1 by omega]
    linear_combination -ht
  · have ht := hd z
    rw [path_row] at ht
    simp only [z, dite_eq_right (by omega : ¬ 0 < 0), zero_add,
      dite_eq_left (by omega : 1 < j), ite_true] at ht
    simp only [x, dite_eq_left (by omega : j - 1 < j), dite_eq_left (by omega : j - 2 < j),
      Nat.sub_self, show j - 1 - (j - 2) = 1 from tsub_tsub_tsub_cancel_left hj]
    change (i + 1 : ℤ) * d z - d ⟨1, by omega⟩ = _
    linear_combination ht

private lemma path_elimination (i j : ℕ) (hj : 2 ≤ j) (x : ℕ → ℤ)
    (h0 : x 1 = (i + 1 : ℤ) * x 0)
    (hr : ∀ k : ℕ, k + 2 < j → x (k + 2) = (i + 2 : ℤ) * x (k + 1) - x k) :
    (i + 1 : ℤ) * x (j - 1) - x (j - 2) =
      (i : ℤ) * (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) * x 0 := by
  have hf : ∀ k : ℕ, k < j → x k =
      ((S ℤ (k : ℤ)).eval (i + 2 : ℤ) -
        (S ℤ ((k : ℤ) - 1)).eval (i + 2 : ℤ)) * x 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    have he := D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.bounded_continuant_endpoint
      k (by omega) (i + 2 : ℝ) (fun n => (x n : ℝ)) (by
        intro n hn
        exact_mod_cast hr n (by omega))
    have hs (n : ℤ) : (((S ℤ n).eval (i + 2 : ℤ) : ℤ) : ℝ) = (S ℝ n).eval (i + 2 : ℝ) := by
      simpa using (algebraMap_eval_S (R := ℤ) (R' := ℝ) (i + 2 : ℤ) n)
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hs, hs]
    have h0' : (x 1 : ℝ) = (i + 1 : ℝ) * (x 0 : ℝ) := by exact_mod_cast h0
    have ht := congrArg (Polynomial.eval (i + 2 : ℝ)) (S_add_one ℝ ((k : ℤ) - 1))
    simp only [eval_sub, eval_mul, eval_X, sub_add_cancel,
      show (k : ℤ) - 1 - 1 = (k : ℤ) - 2 from sub_sub (k : ℤ) 1 1] at ht
    rw [h0'] at he
    linear_combination he - (x 0 : ℝ) * ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [show n + 2 - 1 = n + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) n,
    show n + 2 - 2 = n from Nat.add_sub_cancel n 2,
    hf (n + 1) (by omega), hf n (by omega)]
  have ht := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_one ℤ (n : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at ht
  push_cast
  rw [show (n : ℤ) + 1 - 1 = (n : ℤ) from add_sub_cancel_right (n : ℤ) 1,
    show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 from add_sub_assoc (n : ℤ) 2 1]
  linear_combination x 0 * ht

private lemma identity_divisibility (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : maximalIdentityAt i j (⟨0, by omega⟩, ⟨0, by omega⟩)) :
    (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) ∣ (i : ℤ) * j - 2 := by
  obtain ⟨x, h0, hr, he⟩ := path_reduction i j hi hj h
  have hx := path_elimination i j hj x h0 hr
  have hi0 : (i : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : i ≠ 0)
  refine ⟨-x 0, ?_⟩
  apply mul_left_cancel₀ hi0
  nlinarith [he, hx]

private lemma continuant_growth (i j : ℕ) (hi : 2 ≤ i) (hj : 3 ≤ j) :
    (i : ℤ) * j - 2 < (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) := by
  have hi' : (2 : ℚ) ≤ i := by exact_mod_cast hi
  let a : ℕ → ℚ := fun n => (((S ℤ (n : ℤ)).eval (i + 2 : ℤ) : ℤ) : ℚ)
  have h0 : a 0 = 1 := by simp [a]
  have h1 : a 1 = (i : ℚ) + 2 := by simp [a]
  have hr : ∀ n, a (n + 2) = ((i : ℚ) + 2) * a (n + 1) - a n := by
    intro n
    have hs := congrArg (Polynomial.eval (i + 2 : ℤ)) (S_add_two ℤ (n : ℤ))
    simp only [eval_sub, eval_mul, eval_X] at hs
    dsimp [a]
    push_cast
    exact_mod_cast hs
  have ha := D5.S3.Factorization.BoninShadowMarkoffPositivity.real_recurrence_growth
    a ((i : ℚ) + 2) (by linarith) (by rw [h0]; norm_num)
    (by rw [h0, h1]; linarith) (by rw [h0, h1]; simp) hr
  let d : ℕ → ℚ := fun n => a (n + 1) - a n
  have hd0 : d 0 = (i : ℚ) + 1 := by dsimp [d]; rw [h0, h1]; ring
  have hd := D5.S3.Factorization.BoninShadowMarkoffPositivity.real_recurrence_growth
    d ((i : ℚ) + 2) (by linarith) (by rw [hd0]; linarith)
    (by
      have hp := mul_pos (show (0 : ℚ) < i by linarith) (ha 1).1
      dsimp [d]
      rw [hr 0]
      nlinarith)
    (by dsimp [d]; rw [hr 0, h0, h1]; nlinarith)
    (by
      intro n
      dsimp [d]
      linear_combination (hr (n + 1)) - (hr n))
  have hdm : Monotone d := monotone_nat_of_le_succ fun n => (hd n).2.1.le
  have hbound (n : ℕ) : (i : ℚ) < d n := by
    have := hdm (Nat.zero_le n)
    rw [hd0] at this
    linarith
  have hb : Monotone (fun n : ℕ => a (n + 2) - (i : ℚ) * n) := by
    apply monotone_nat_of_le_succ
    intro n
    have h := hbound (n + 2)
    dsimp [d] at h
    push_cast
    linarith
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have hbase := hr 0
  rw [h0, h1] at hbase
  have hm := hb (Nat.zero_le n)
  have hfinal : (i : ℚ) * (n + 3) - 2 < a (n + 2) := by
    push_cast at hm ⊢
    nlinarith [sq_nonneg (i : ℚ)]
  dsimp [a] at hfinal
  push_cast at hfinal ⊢
  rw [show (n : ℤ) + 3 - 1 = (n : ℤ) + 2 by ring]
  exact_mod_cast hfinal

private lemma divisibility_classification (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : (Polynomial.Chebyshev.S ℤ ((j : ℤ) - 1)).eval (i + 2 : ℤ) ∣ (i : ℤ) * j - 2) :
    i = 4 ∧ j = 2 := by
  by_cases hj2 : j = 2
  · subst j
    norm_num at h
    have h6 : (i + 2 : ℤ) ∣ 6 := by
      convert dvd_sub (dvd_mul_right (i + 2 : ℤ) 2) h using 1
      ring
    have hb := Int.le_of_dvd (by norm_num : (0 : ℤ) < 6) h6
    have hc : i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hc with rfl | rfl | rfl
    · norm_num at h
    · norm_num at h
    · exact ⟨rfl, rfl⟩
  · have hg := continuant_growth i j hi (by omega)
    have hp : (0 : ℤ) < (i : ℤ) * j - 2 := by
      have hi' : (2 : ℤ) ≤ i := Int.ofNat_le.mpr hi
      have hj' : (3 : ℤ) ≤ j := Int.ofNat_le.mpr (by omega : 3 ≤ j)
      nlinarith
    have hb := Int.le_of_dvd hp h
    omega

theorem result : claim := by
  intro i j hi hj
  constructor
  · intro h
    exact divisibility_classification i j hi hj
      (identity_divisibility i j hi hj (h (⟨0, by omega⟩, ⟨0, by omega⟩)))
  · rintro ⟨rfl, rfl⟩
    classical
    intro s
    let f : Fin 4 × Fin 2 → ℤ := fun v =>
      if v = s then 0 else if v.2 = s.2 then 5 else if v.1 = s.1 then 6 else 7
    refine ⟨fun v => f v, ?_⟩
    intro v
    have hf : f s = 0 := by simp only [f, ite_eq_left rfl]
    have hs := Fintype.sum_eq_add_sum_subtype_ne
      (fun w => ((⊤ : SimpleGraph (Fin 4)).boxProd (SimpleGraph.pathGraph 2)).lapMatrix ℤ
        v.1 w * f w) s
    rw [hf, mul_zero, zero_add] at hs
    rw [← hs]
    change
      ((((⊤ : SimpleGraph (Fin 4)).boxProd (SimpleGraph.pathGraph 2)).lapMatrix ℤ) *ᵥ f) v.1 = _
    rw [product_row, path_row, SimpleGraph.degree_boxProd, Nat.cast_add, path_degree]
    rcases s with ⟨a, t⟩
    rcases v with ⟨⟨b, u⟩, hv⟩
    fin_cases a <;> fin_cases t <;> fin_cases b <;> fin_cases u <;>
      first
      | exact (hv rfl).elim
      | norm_num [f, Fin.sum_univ_succ, SimpleGraph.IsRegularOfDegree.top.degree_eq]

end D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity

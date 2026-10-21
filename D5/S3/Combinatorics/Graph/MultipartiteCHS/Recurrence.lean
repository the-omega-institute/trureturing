/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Elementary symmetric part polynomials and their reciprocal coefficient recurrence. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence

open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs

set_option autoImplicit false

def esymmParts {r : ℕ} (a : Fin r → ℕ) (j : ℕ) : ℕ :=
  ∑ S ∈ (Finset.univ : Finset (Fin r)).powersetCard j, ∏ i ∈ S, a i

noncomputable def recH {r : ℕ} (a : Fin r → ℕ) (d : ℕ) : ℝ :=
  Nat.strongRecOn d (fun d rec =>
    if hzero : d = 0 then 1 else
      ∑ j ∈ Finset.range (d + 1),
        if h : 2 ≤ j then
          ((j : ℝ) - 1) * (esymmParts a j : ℝ) * rec (d - j) (by omega)
        else 0)

theorem recH_zero {r} (a : Fin r → ℕ) : recH a 0 = 1 := by
  rw [recH, Nat.strongRecOn_eq]
  simp

theorem recH_eq {r} (a : Fin r → ℕ) {d : ℕ} (hd : 1 ≤ d) :
    recH a d = ∑ j ∈ Finset.Icc 2 d,
      ((j : ℝ) - 1) * (esymmParts a j : ℝ) * recH a (d - j) := by
  cases d with
  | zero => omega
  | succ d =>
      rw [recH, Nat.strongRecOn_eq]
      rw [dite_eq_right (by omega)]
      change (∑ j ∈ Finset.range (d + 1 + 1),
        if 2 ≤ j then
          ((j : ℝ) - 1) * (esymmParts a j : ℝ) * recH a ((d + 1) - j)
        else 0) = _
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega

theorem esymmParts_nonneg {r : ℕ} (a : Fin r → ℕ) (j : ℕ) :
    0 ≤ (esymmParts a j : ℝ) := by
  unfold esymmParts
  positivity

theorem recH_nonneg {r : ℕ} (a : Fin r → ℕ) : ∀ d, 0 ≤ recH a d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd : d = 0
      · simp [hd, recH_zero]
      · rw [recH_eq a (by omega)]
        apply Finset.sum_nonneg
        intro j hj
        have hjlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        have hrec : 0 ≤ recH a (d - j) := ih (d - j) (by omega)
        have he : 0 ≤ (esymmParts a j : ℝ) := esymmParts_nonneg a j
        have hc : 0 ≤ (j : ℝ) - 1 := by
          have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
          linarith
        positivity

theorem esymmParts_two_pos {r : ℕ} (hr : 2 ≤ r) (a : Fin r → ℕ)
    (ha : ∀ i, 0 < a i) : 0 < (esymmParts a 2 : ℝ) := by
  unfold esymmParts
  have hnat : 0 < ∑ S ∈ (Finset.univ : Finset (Fin r)).powersetCard 2,
      ∏ i ∈ S, a i := by
    apply Finset.sum_pos'
    · intro S hS
      exact Nat.zero_le _
    · obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty_of_le
          (s := (Finset.univ : Finset (Fin r))) (by simpa using hr)
      exact ⟨S, hS, by
        apply Finset.prod_pos
        intro i hi
        exact ha i⟩
  exact_mod_cast hnat

theorem recH_two_mul_pos {r m : ℕ} (hr : 2 ≤ r) (a : Fin r → ℕ)
    (ha : ∀ i, 0 < a i) (hm : 1 ≤ m) :
    0 < recH a (2 * m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm1 : m = 1
      · subst hm1
        rw [recH_eq a (by omega)]
        apply Finset.sum_pos'
        · intro j hj
          have hjlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
          have hrec : 0 ≤ recH a (2 - j) := recH_nonneg a _
          have he : 0 ≤ (esymmParts a j : ℝ) := esymmParts_nonneg a j
          have hc : 0 ≤ (j : ℝ) - 1 := by
            have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
            linarith
          positivity
        · exact ⟨2, by simp, by
            have he := esymmParts_two_pos hr a ha
            norm_num [recH_zero] at he ⊢
            positivity⟩
      · rw [recH_eq a (by omega)]
        apply Finset.sum_pos'
        · intro j hj
          have hjlo : 2 ≤ j := (Finset.mem_Icc.mp hj).1
          have hrec : 0 ≤ recH a ((2 * m) - j) := recH_nonneg a _
          have he : 0 ≤ (esymmParts a j : ℝ) := esymmParts_nonneg a j
          have hc : 0 ≤ (j : ℝ) - 1 := by
            have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
            linarith
          positivity
        · refine ⟨2, by simp only [Finset.mem_Icc]; omega, ?_⟩
          have hm' : 1 ≤ m - 1 := by omega
          have hpos : 0 < recH a (2 * (m - 1)) := ih (m - 1) (by omega) hm'
          have he := esymmParts_two_pos hr a ha
          have heq : (2 * m) - 2 = 2 * (m - 1) := by omega
          rw [heq]
          positivity

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence

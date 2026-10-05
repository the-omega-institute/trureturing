/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeFeedbackDigits
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeFeedbackDigits
   mirror-E: none(waiver:prefix-dependent-feedback)
   anchors: []
   utility: none
   digest: Prefix-dependent Hall choices construct bounded digits with all positions controlled. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- Hall choices depend on the current prefix, rather than a predetermined target
sequence. The diagonal construction preserves every prefix. A finite-stage induction
classifies all positions, including the joins, as centers or four-digit Hall blocks. -/
theorem feedback_digit_construction (seed : List ℕ) (A B : ℕ)
    (hseed : ∀ a ∈ seed, 0 < a ∧ a ≤ A) (T : List ℕ → ℝ)
    (hT : ∀ p, 6 < T p ∧ T p ≤ (B : ℝ)) :
    ∃ P : ℕ → List ℕ, ∃ d c : ℕ → ℕ, ∃ x y : ℕ → ℝ,
      ∃ u v : ℕ → ℕ → ℕ,
      P 0 = seed ∧
      (∀ j, P j = List.ofFn (fun i : Fin (P j).length => d i)) ∧
      StrictMono c ∧
      (∀ i, 0 < d i ∧ d i ≤ max A (max 4 B)) ∧
      (∀ i, seed.length ≤ i → (∀ j, i ≠ c j) → d i ≤ 4) ∧
      ∀ j, x j ∈ hallCantor ∧ y j ∈ hallCantor ∧
        T (P j) = (d (c j) : ℝ) + x j + y j ∧
        5 ≤ d (c j) ∧ d (c j) ≤ B ∧ c j = (P j).length + (j + 1) ∧
        (∀ i, (0 < u j i ∧ u j i ≤ 4 ∧
          (GenContFract.of (x j)).s.get? i = some ⟨1, (u j i : ℝ)⟩) ∧
          (0 < v j i ∧ v j i ≤ 4 ∧
          (GenContFract.of (y j)).s.get? i = some ⟨1, (v j i : ℝ)⟩)) ∧
        P (j + 1) = P j ++ (List.ofFn (fun i : Fin (j + 1) => u j i)).reverse ++
          [d (c j)] ++ List.ofFn (fun i : Fin (j + 1) => v j i) := by
  classical
  choose N x hx y hy ht using fun p : List ℕ => hall_cantor_sum.2 (T p)
  choose u hu using fun p i => (hx p).2.2.2 i
  choose v hv using fun p i => (hy p).2.2.2 i
  have hN (p : List ℕ) : 5 ≤ (N p).toNat ∧ (N p).toNat ≤ B ∧
      ((N p).toNat : ℝ) = (N p : ℝ) := by
    have hl : (4 : ℝ) < N p := by
      linarith [(hT p).1, (hx p).2.2.1, (hy p).2.2.1, ht p]
    have hl' : (5 : ℤ) ≤ N p := by
      have : (4 : ℤ) < N p := by exact_mod_cast hl
      omega
    have hb : (N p : ℝ) ≤ B := by
      linarith [(hT p).2, (hx p).2.1, (hy p).2.1, ht p]
    have hb' : N p ≤ (B : ℤ) := by exact_mod_cast hb
    have he : ((N p).toNat : ℤ) = N p := Int.toNat_of_nonneg (by omega)
    refine ⟨by omega, by omega, ?_⟩
    exact_mod_cast he
  let L (p : List ℕ) (j : ℕ) := (List.ofFn (fun i : Fin (j + 1) => u p i)).reverse
  let R (p : List ℕ) (j : ℕ) := List.ofFn (fun i : Fin (j + 1) => v p i)
  let P : ℕ → List ℕ := fun j => Nat.rec seed
    (fun j p => p ++ L p j ++ [(N p).toNat] ++ R p j) j
  have hzero : P 0 = seed := rfl
  have hstep (j : ℕ) :
      P (j + 1) = P j ++ L (P j) j ++ [(N (P j)).toNat] ++ R (P j) j := rfl
  have hL (p : List ℕ) (j : ℕ) : (L p j).length = j + 1 := by simp [L]
  have hR (p : List ℕ) (j : ℕ) : (R p j).length = j + 1 := by simp [R]
  have hlen (j : ℕ) : (P (j + 1)).length = (P j).length + 2 * (j + 1) + 1 := by
    simp only [hstep, List.length_append, List.length_singleton, hL, hR]
    omega
  have hprefix : ∀ n m, n ≤ m → P n <+: P m := by
    intro n m hnm
    induction hnm with
    | refl => exact List.prefix_refl _
    | @step m hnm ih =>
        apply ih.trans
        rw [hstep, List.append_assoc, List.append_assoc]
        exact List.prefix_append _ _
  have hgrowth : ∀ j, seed.length + j ≤ (P j).length := by
    intro j
    induction j with
    | zero => simp only [hzero, Nat.add_zero, le_refl]
    | succ j ih => rw [hlen]; omega
  have hin (i : ℕ) : i < (P (i + 1)).length := by
    have := hgrowth (i + 1)
    omega
  let d (i : ℕ) : ℕ := (P (i + 1))[i]'(hin i)
  have hmatch (j i : ℕ) (hi : i < (P j).length) : d i = (P j)[i] := by
    let m := max j (i + 1)
    have h₁ := (hprefix (i + 1) m (le_max_right _ _)).getElem (hin i)
    have h₂ := (hprefix j m (le_max_left _ _)).getElem hi
    exact h₁.trans h₂.symm
  have hrealize (j : ℕ) : P j = List.ofFn (fun i : Fin (P j).length => d i) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      exact (hmatch j i hi).symm
  have hblockL (p : List ℕ) (j : ℕ) : ∀ a ∈ L p j, 0 < a ∧ a ≤ 4 := by
    intro a ha
    simp only [L, List.mem_reverse, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨(hu p i).1, (hu p i).2.1⟩
  have hblockR (p : List ℕ) (j : ℕ) : ∀ a ∈ R p j, 0 < a ∧ a ≤ 4 := by
    intro a ha
    simp only [R, List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    exact ⟨(hv p i).1, (hv p i).2.1⟩
  have hbounded : ∀ j a, a ∈ P j → 0 < a ∧ a ≤ max A (max 4 B) := by
    intro j
    induction j with
    | zero =>
        intro a ha
        have hh := hseed a ha
        exact ⟨hh.1, hh.2.trans (le_max_left _ _)⟩
    | succ j ih =>
        intro a ha
        rw [hstep] at ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ((ha | ha) | ha) | ha
        · exact ih a ha
        · have hh := hblockL (P j) j a ha
          exact ⟨hh.1, hh.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
        · subst a
          have hh := hN (P j)
          exact ⟨by omega, hh.2.1.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
        · have hh := hblockR (P j) j a ha
          exact ⟨hh.1, hh.2.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
  let c (j : ℕ) := (P j).length + (j + 1)
  have hc : StrictMono c := by
    apply strictMono_nat_of_lt_succ
    intro j
    dsimp only [c]
    rw [hlen]
    omega
  have hcenter (j : ℕ) : d (c j) = (N (P j)).toNat := by
    have hi : c j < (P (j + 1)).length := by dsimp [c]; rw [hlen]; omega
    rw [hmatch (j + 1) (c j) hi]
    simp only [hstep]
    have hp : c j < (P j ++ L (P j) j ++ [(N (P j)).toNat]).length := by
      simp only [List.length_append, List.length_singleton, hL]
      dsimp only [c]
      omega
    rw [List.getElem_append_left hp]
    have hpl : (P j ++ L (P j) j).length = c j := by
      simp only [List.length_append, hL, c]
    rw [List.getElem_append_right (by omega)]
    simp [hpl]
  have hclass : ∀ j i, ∀ hi : i < (P j).length, seed.length ≤ i →
      (P j)[i] ≤ 4 ∨ ∃ l < j, i = c l := by
    intro j
    induction j with
    | zero => intro i hi hs; rw [hzero] at hi; omega
    | succ j ih =>
        intro i hi hs
        by_cases hp : i < (P j).length
        · have hh := ih i hp hs
          rcases hh with hh | ⟨l, hl, he⟩
          · left
            have he := (hprefix j (j + 1) (by omega)).getElem hp
            exact he ▸ hh
          · exact Or.inr ⟨l, by omega, he⟩
        · by_cases hic : i = c j
          · exact Or.inr ⟨j, Nat.lt_succ_self _, hic⟩
          · left
            simp only [hstep]
            by_cases hleft : i < (P j ++ L (P j) j).length
            · have hleft' : i < (P j ++ L (P j) j ++ [(N (P j)).toNat]).length := by
                simp only [List.length_append, List.length_singleton] at *
                omega
              rw [List.getElem_append_left hleft', List.getElem_append_left hleft,
                List.getElem_append_right (by omega)]
              exact (hblockL (P j) j _ (List.getElem_mem _)).2
            · have hright : (P j ++ L (P j) j ++ [(N (P j)).toNat]).length ≤ i := by
                simp only [List.length_append, List.length_singleton, hL] at *
                dsimp only [c] at hic
                omega
              rw [List.getElem_append_right hright]
              exact (hblockR (P j) j _ (List.getElem_mem _)).2
  refine ⟨P, d, c, fun j => x (P j), fun j => y (P j),
    fun j => u (P j), fun j => v (P j), hzero, hrealize, hc, ?_, ?_, ?_⟩
  · intro i
    exact hbounded (i + 1) _ (List.getElem_mem (hin i))
  · intro i hs hnc
    rcases hclass (i + 1) i (hin i) hs with hh | ⟨l, _, he⟩
    · exact hh
    · exact (hnc l he).elim
  · intro j
    refine ⟨hx (P j), hy (P j), ?_, ?_, ?_, rfl, ?_, ?_⟩
    · rw [hcenter, (hN (P j)).2.2]
      exact ht (P j)
    · rw [hcenter]; exact (hN (P j)).1
    · rw [hcenter]; exact (hN (P j)).2.1
    · intro i
      exact ⟨hu (P j) i, hv (P j) i⟩
    · simpa only [hcenter] using hstep j

end D5.S1.Words.KAbelianLagrange

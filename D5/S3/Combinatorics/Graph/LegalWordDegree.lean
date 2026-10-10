/- GID: D5/S3/Combinatorics/Graph/LegalWordDegree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWordDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal Hamming-one words have a sharp flippable-zero and occupation count. -/

import D5.S3.Combinatorics.Graph.Hypercube
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWordDegree

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.Hypercube

/-- The literal admissible words with the adjacency inherited from the Boolean hypercube. -/
def legalWordGraph (n : ℕ) : SimpleGraph {w : Fin n → Bool // Adm n w} :=
  (hypercube n).induce {w | Adm n w}

/-- A zero with no occupied immediate neighbour. Missing endpoint neighbours are zero. -/
def FlippableZero {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Prop :=
  w i = false ∧ ∀ j : Fin n, j.val + 1 = i.val ∨ i.val + 1 = j.val → w j = false

open Classical in
/-- The number of zero positions whose two neighbours, with zero padding, are zero. -/
noncomputable def flippableZeroCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ∑ i, if FlippableZero w i then 1 else 0

open Classical in
/-- Neighbours are exactly the legal additions at flippable zeros and removals at ones. -/
theorem degree_eq_flippable_add_occupation (n : ℕ)
    (b : {w : Fin n → Bool // Adm n w}) :
    (legalWordGraph n).degree b = flippableZeroCount b.val + occupationCount b.val := by
  classical
  let flip (i : Fin n) : Fin n → Bool := Function.update b.val i (!b.val i)
  have hlegal := (adm_iff_no_adjacent_true n b.val).mp b.property
  have hflegal (i : Fin n) :
      Adm n (flip i) ↔ b.val i = true ∨ FlippableZero b.val i := by
    rw [adm_iff_no_adjacent_true]
    constructor
    · intro h
      cases hi : b.val i with
      | true => exact Or.inl rfl
      | false =>
          refine Or.inr ⟨hi, ?_⟩
          intro j hj
          have hji : j ≠ i := by intro he; subst j; omega
          rcases hj with hj | hj
          · have := h j i hj
            simpa [flip, hi, Function.update_of_ne hji] using this
          · have := h i j hj
            simpa [flip, hi, Function.update_of_ne hji] using this
    · rintro (hi | hi) j k hjk
      · by_cases hji : j = i
        · subst j
          exact Or.inl (by simp [flip, hi])
        · by_cases hki : k = i
          · subst k
            exact Or.inr (by simp [flip, hi])
          · simpa [flip, Function.update_of_ne hji, Function.update_of_ne hki]
              using hlegal j k hjk
      · by_cases hji : j = i
        · subst j
          have hki : k ≠ i := by intro he; subst k; omega
          apply Or.inr
          simpa [flip, Function.update_of_ne hki] using (hi.2 k (Or.inr hjk))
        · by_cases hki : k = i
          · subst k
            apply Or.inl
            simpa [flip, Function.update_of_ne hji] using (hi.2 j (Or.inl hjk))
          · simpa [flip, Function.update_of_ne hji, Function.update_of_ne hki]
              using hlegal j k hjk
  let S : Finset (Fin n) := Finset.univ.filter
    (fun i => b.val i = true ∨ FlippableZero b.val i)
  let f : S → (legalWordGraph n).neighborSet b := fun i =>
    ⟨⟨flip i.val, (hflegal i.val).mpr (Finset.mem_filter.mp i.property).2⟩, by
      change (Finset.univ.filter (fun j => b.val j ≠ flip i.val j)).card = 1
      have hs : Finset.univ.filter (fun j => b.val j ≠ flip i.val j) = {i.val} := by
        ext j
        by_cases hj : j = i.val
        · subst j
          simp [flip]
        · simp [flip, hj]
      rw [hs, Finset.card_singleton]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      apply Subtype.ext
      by_contra hij
      have hv := congrArg
        (fun y : (legalWordGraph n).neighborSet b => y.val.val i.val) he
      simp [f, flip, Function.update_of_ne hij] at hv
    · intro y
      have hy : (Finset.univ.filter (fun i => b.val i ≠ y.val.val i)).card = 1 :=
        y.property
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hy
      have hmem (j : Fin n) : b.val j ≠ y.val.val j ↔ j = i := by
        have := Finset.ext_iff.mp hi j
        simpa using this
      have he : flip i = y.val.val := by
        funext j
        by_cases hj : j = i
        · subst j
          have hne := (hmem i).mpr rfl
          simp only [flip, Function.update_self]
          cases hx : b.val i <;> cases hyi : y.val.val i <;> simp_all
        · have heq : b.val j = y.val.val j := by
            by_contra hne
            exact hj ((hmem j).mp hne)
          simpa [flip, Function.update_of_ne hj] using heq
      refine ⟨⟨i, ?_⟩, ?_⟩
      · have h := (hflegal i).mp (by rw [he]; exact y.val.property)
        simpa [S] using h
      · apply Subtype.ext
        exact Subtype.ext he
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (Equiv.ofBijective f hf)]
  simp only [Fintype.card_coe, S, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [flippableZeroCount, occupationCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : b.val i <;> simp [FlippableZero, hi]

/-- The sharp universal count bound, including its unique alternating equality words. -/
theorem flippable_bound_and_equality (n : ℕ) (b : {w : Fin n → Bool // Adm n w}) :
    flippableZeroCount b.val + 2 * occupationCount b.val ≤ n + 1 ∧
      (flippableZeroCount b.val + 2 * occupationCount b.val = n + 1 ↔
        Odd n ∧ ∀ i : Fin n, b.val i = decide (i.val % 2 = 0)) := by
  classical
  induction n using Nat.twoStepInduction with
  | zero => simp [flippableZeroCount, occupationCount, Nat.not_odd_zero]
  | one =>
      have hw : b.val = fun _ => b.val 0 := by
        funext i
        exact congrArg b.val (Fin.eq_zero i)
      cases h0 : b.val 0 <;>
        simp [hw, flippableZeroCount, FlippableZero, occupationCount, h0]
  | more n ih ih1 =>
      have hlegal := (adm_two_iff n b.val).mp b.property
      cases h0 : b.val 0 with
      | false =>
          let c : {w : Fin (n + 1) → Bool // Adm (n + 1) w} :=
            ⟨Fin.tail b.val, hlegal.2⟩
          have ht (i : Fin (n + 1)) :
              FlippableZero b.val i.succ ↔ FlippableZero c.val i := by
            constructor
            · rintro ⟨hi, h⟩
              refine ⟨hi, ?_⟩
              intro j hj
              exact h j.succ (by simp only [Fin.val_succ]; omega)
            · rintro ⟨hi, h⟩
              refine ⟨hi, ?_⟩
              intro j hj
              revert hj
              refine Fin.cases ?_ (fun j => ?_) j
              · intro _
                exact h0
              · intro hj
                exact h j (by simp only [Fin.val_succ] at hj; omega)
          have hf : FlippableZero b.val 0 ↔ b.val 1 = false := by
            constructor
            · intro h
              exact h.2 1 (Or.inr (by simp))
            · intro h1
              refine ⟨h0, ?_⟩
              intro j hj
              have hj1 : j = 1 := by
                apply Fin.ext
                simp only [Fin.val_zero] at hj
                have hv : (1 : Fin (n + 2)).val = 1 := by simp
                rw [hv]
                omega
              simpa [hj1] using h1
          have hu : flippableZeroCount b.val =
              (if b.val 1 = false then 1 else 0) + flippableZeroCount c.val := by
            simp only [flippableZeroCount, Fin.sum_univ_succ, hf, ht]
          have hk : occupationCount b.val = occupationCount c.val := by
            simp [occupationCount, Fin.sum_univ_succ, h0, c, Fin.tail]
          obtain ⟨hcb, hce⟩ := ih1 c
          have hs : flippableZeroCount b.val + 2 * occupationCount b.val < n + 3 := by
            by_cases h1 : b.val 1 = false
            · have hne : flippableZeroCount c.val + 2 * occupationCount c.val ≠ n + 2 := by
                intro he
                have ha := (hce.mp he).2 0
                have hc0 : c.val 0 = false := by
                  simpa [c, Fin.tail, Fin.succ_zero_eq_one] using h1
                simp [hc0] at ha
              simp [h1] at hu
              omega
            · simp [h1] at hu
              omega
          refine ⟨by omega, ?_⟩
          constructor
          · intro he
            omega
          · rintro ⟨_, ha⟩
            have := ha 0
            simp [h0] at this
      | true =>
          have h1 : b.val 1 = false := by
            cases hb1 : b.val 1
            · rfl
            · exact False.elim (hlegal.1 ⟨h0, hb1⟩)
          let c : {w : Fin n → Bool // Adm n w} :=
            ⟨Fin.tail (Fin.tail b.val),
              adm_tail_of_head_false n (Fin.tail b.val) hlegal.2
                (by simpa [Fin.tail, Fin.succ_zero_eq_one] using h1)⟩
          have ht (i : Fin n) :
              FlippableZero b.val i.succ.succ ↔ FlippableZero c.val i := by
            constructor
            · rintro ⟨hi, h⟩
              refine ⟨hi, ?_⟩
              intro j hj
              exact h j.succ.succ (by simp only [Fin.val_succ]; omega)
            · rintro ⟨hi, h⟩
              refine ⟨hi, ?_⟩
              intro j hj
              revert hj
              refine Fin.cases ?_ (fun j => ?_) j
              · intro hj
                simp only [Fin.val_zero, Fin.val_succ] at hj
                omega
              · revert j
                intro j
                refine Fin.cases ?_ (fun j => ?_) j
                · intro _
                  simpa [Fin.succ_zero_eq_one] using h1
                · intro hj
                  exact h j (by simp only [Fin.val_succ] at hj; omega)
          have hf0 : ¬ FlippableZero b.val 0 := by simp [FlippableZero, h0]
          have hf1 : ¬ FlippableZero b.val 1 := by
            intro h
            have := h.2 0 (Or.inl (by simp))
            simp [h0] at this
          have hu : flippableZeroCount b.val = flippableZeroCount c.val := by
            simp only [flippableZeroCount, Fin.sum_univ_succ,
              Fin.succ_zero_eq_one, hf0, hf1, ite_false, zero_add, ht]
          have hk : occupationCount b.val = 1 + occupationCount c.val := by
            simp [occupationCount, Fin.sum_univ_succ, h0, h1, c,
              Fin.tail, Fin.succ_zero_eq_one]
          have halt :
              (∀ i : Fin (n + 2), b.val i = decide (i.val % 2 = 0)) ↔
                (∀ i : Fin n, c.val i = decide (i.val % 2 = 0)) := by
            have hmod (i : Fin n) : i.succ.succ.val % 2 = i.val % 2 := by
              simp only [Fin.val_succ]
              omega
            constructor
            · intro h i
              simpa only [c, Fin.tail, hmod] using h i.succ.succ
            · intro h i
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa using h0
              · refine Fin.cases ?_ (fun j => ?_) j
                · simpa [Fin.succ_zero_eq_one] using h1
                · simpa only [c, Fin.tail, hmod] using h j
          have hc := ih c
          refine ⟨by omega, ?_⟩
          have ho : Odd (n + 2) ↔ Odd n := by
            rw [Nat.odd_iff, Nat.odd_iff]
            omega
          rw [halt, ho]
          constructor
          · intro he
            apply hc.2.mp
            omega
          · intro he
            have := hc.2.mpr he
            omega

#print axioms degree_eq_flippable_add_occupation
#print axioms flippable_bound_and_equality
#check degree_eq_flippable_add_occupation
#check flippable_bound_and_equality

end D5.S3.Combinatorics.Graph.LegalWordDegree

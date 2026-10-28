/- GID: D5/S3/Combinatorics/Graph/Domination/TotalDominationBlowup
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TotalDominationBlowup
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Actual independent-fibre subsets preserve total domination. -/

import D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds

/-!
Independent fibres retain the open-neighbourhood total condition.
The H-join substitution formula is a known ingredient of the direct density route
(Subramanian--Selvakumar, Filomat 2025); no new identity credit is claimed.
This source is an unfinished ingredient of the original issue 23313 consumer.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Domination.TotalDominationBlowup

open scoped Classical

open Finset Polynomial
open D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds

variable {V W : Type} [Fintype V] [Fintype W]

/-- All fibres are independent; only original adjacency joins two fibres. -/
def blowupGraph (G : SimpleGraph V) (W : Type) : SimpleGraph (V × W) := G.comap Prod.fst

/-- A family of actual subsets of each finite fibre is an actual global subset. -/
noncomputable def subsetFamilyEquiv : Finset (V × W) ≃ (V → Finset W) := by
  classical
  exact {
    toFun := fun S v => univ.filter (fun w => (v,w) ∈ S)
    invFun := fun f => univ.filter (fun p => p.2 ∈ f p.1)
    left_inv := by intro S; ext p; simp
    right_inv := by intro f; funext v; ext w; simp }

/-- The support records occupied actual fibres, rather than arbitrary labels. -/
noncomputable def support (f : V → Finset W) : Finset V := by
  classical
  exact univ.filter (fun v => (f v).Nonempty)

private theorem subset_family_card (f : V → Finset W) :
    (subsetFamilyEquiv.symm f).card = ∑ v, (f v).card := by
  classical
  change (univ.filter (fun p : V × W => p.2 ∈ f p.1)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp

private theorem total_family [Nonempty W] (G : SimpleGraph V) (f : V → Finset W) :
    IsTotal (blowupGraph G W) (subsetFamilyEquiv.symm f) ↔ IsTotal G (support f) := by
  classical
  constructor
  · intro h v
    obtain ⟨i⟩ := ‹Nonempty W›
    obtain ⟨⟨u,j⟩, hu, hadj⟩ := h (v,i)
    change (u,j) ∈ univ.filter (fun p : V × W => p.2 ∈ f p.1) at hu
    refine ⟨u, ?_, hadj⟩
    simp only [support, mem_filter, mem_univ, true_and]
    exact ⟨j, (mem_filter.mp hu).2⟩
  · intro h p
    obtain ⟨u, hu, hadj⟩ := h p.1
    have hfu : (f u).Nonempty := (mem_filter.mp hu).2
    obtain ⟨j, hj⟩ := hfu
    refine ⟨(u,j), ?_, hadj⟩
    change (u,j) ∈ univ.filter (fun q : V × W => q.2 ∈ f q.1)
    simpa using hj

private theorem all_subsets :
    (∑ S : Finset W, (X : ℂ[X]) ^ S.card) = (1 + X) ^ Fintype.card W := by
  classical
  have h := Finset.prod_add (fun _ : W => (X : ℂ[X])) (fun _ => (1 : ℂ[X])) univ
  simpa [add_comm] using h.symm

private theorem occupied_subsets :
    (∑ S : Finset W, if S.Nonempty then (X : ℂ[X]) ^ S.card else 0) =
      (1 + X) ^ Fintype.card W - 1 := by
  classical
  have he := Finset.sum_erase_add (univ : Finset (Finset W))
    (fun B => (X : ℂ[X]) ^ B.card) (by simp : (∅ : Finset W) ∈ univ)
  have hf : (∑ S : Finset W, if S.Nonempty then (X : ℂ[X]) ^ S.card else 0) =
      ∑ S ∈ (univ : Finset (Finset W)).erase ∅, (X : ℂ[X]) ^ S.card := by
    rw [← Finset.sum_filter]
    congr 1
    ext S
    simp [Finset.nonempty_iff_ne_empty]
  rw [hf, ← all_subsets]
  simpa only [card_empty, pow_zero] using eq_sub_iff_add_eq.mpr he

private theorem fixed_support_sum (A : Finset V) :
    (∑ f : V → Finset W, if support f = A then
      ∏ v, (X : ℂ[X]) ^ (f v).card else 0) =
      ((1 + X) ^ Fintype.card W - 1) ^ A.card := by
  classical
  have hs (f : V → Finset W) : support f = A ↔
      ∀ v, (f v).Nonempty ↔ v ∈ A := by
    simp [Finset.ext_iff, support]
  simp_rw [hs, ← Fintype.prod_ite_zero]
  rw [← Fintype.prod_sum (fun (v : V) (B : Finset W) =>
    if B.Nonempty ↔ v ∈ A then (X : ℂ[X]) ^ B.card else 0)]
  have hi (v : V) :
      (∑ B : Finset W, if B.Nonempty ↔ v ∈ A then (X : ℂ[X]) ^ B.card else 0) =
      if v ∈ A then ((1 + X) ^ Fintype.card W - 1) else 1 := by
    by_cases hv : v ∈ A
    · simpa [hv] using (occupied_subsets (W := W))
    · simp [hv, Finset.nonempty_iff_ne_empty]
  simp_rw [hi]
  simp [Finset.prod_ite]

private theorem group_support (G : SimpleGraph V) :
    (∑ f : V → Finset W, if IsTotal G (support f) then
      ∏ v, (X : ℂ[X]) ^ (f v).card else 0) =
      ∑ A : Finset V, if IsTotal G A then
        ((1 + X) ^ Fintype.card W - 1) ^ A.card else 0 := by
  classical
  simp_rw [← fixed_support_sum (W := W)]
  have hs (A : Finset V) :
      (if IsTotal G A then ∑ f : V → Finset W, if support f = A then
        ∏ v, (X : ℂ[X]) ^ (f v).card else 0 else 0) =
      ∑ f : V → Finset W, if support f = A then
        (if IsTotal G A then ∏ v, (X : ℂ[X]) ^ (f v).card else 0) else 0 := by
    by_cases ha : IsTotal G A <;> simp [ha]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simp

/-- The known substitution identity, with actual subsets and actual independent fibres. -/
theorem blowup_polynomial [Nonempty W] (G : SimpleGraph V) :
    complexPolynomial (blowupGraph G W) =
      (complexPolynomial G).comp ((1 + X) ^ Fintype.card W - 1) := by
  classical
  unfold complexPolynomial
  have he :
      (∑ S : Finset (V × W), if IsTotal (blowupGraph G W) S then
        (X : ℂ[X]) ^ S.card else 0) =
      ∑ f : V → Finset W, if IsTotal (blowupGraph G W) (subsetFamilyEquiv.symm f)
        then X ^ (subsetFamilyEquiv.symm f).card else 0 := by
    exact (Fintype.sum_equiv subsetFamilyEquiv.symm _ _ (fun f => rfl)).symm
  rw [he]
  simp_rw [total_family, subset_family_card, ← Finset.prod_pow_eq_pow_sum]
  rw [group_support]
  simp only [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> simp

private theorem polynomial_nonzero (G : SimpleGraph V)
    (h : ∀ v, ∃ u, G.Adj v u) : complexPolynomial G ≠ 0 := by
  classical
  have ht : IsTotal G univ := by
    intro v
    obtain ⟨u, hu⟩ := h v
    exact ⟨u, mem_univ _, hu⟩
  have hc : (complexPolynomial G).coeff (Fintype.card V) = 1 := by
    unfold complexPolynomial
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single univ]
    · simp [ht]
    · intro S _ hS
      have hlt : S.card < Fintype.card V := by
        simpa using Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨subset_univ S, hS⟩)
      by_cases hs : IsTotal G S <;>
        simp [hs, Polynomial.coeff_X_pow, Nat.ne_of_lt hlt, (Nat.ne_of_lt hlt).symm]
    · simp
  intro he
  rw [he] at hc
  norm_num at hc

private theorem blowup_no_isolates [Nonempty W] (G : SimpleGraph V)
    (h : ∀ v, ∃ u, G.Adj v u) : ∀ v, ∃ u, (blowupGraph G W).Adj v u := by
  intro v
  obtain ⟨u, hu⟩ := h v.1
  obtain ⟨j⟩ := ‹Nonempty W›
  exact ⟨(u,j), hu⟩

/-- The seed roots pull back along every allowed independent-fibre power map. -/
theorem seed_blowup_roots (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℝ),
      2 ≤ n ∧ 0 < 1 + r ∧ 1 + r < ε ∧
      complexPolynomial G ≠ 0 ∧
      (∀ v, ∃ u, G.Adj v u) ∧
      complexPolynomial (blowupGraph G (Fin k)) ≠ 0 ∧
      (∀ v, ∃ u, (blowupGraph G (Fin k)).Adj v u) ∧
      ∀ w : ℂ, (1 + w) ^ k = (1 + r : ℝ) →
        (complexPolynomial (blowupGraph G (Fin k))).IsRoot w := by
  classical
  obtain ⟨n, G, r, hn, hni, hnz, hc, hl, hclose⟩ := complex_seed_accumulation ε hε
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hr : 1 + r < ε := by
    have he : (r : ℂ) - (-1 : ℂ) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl] using hclose
  have hb := blowup_no_isolates (W := Fin k) G hni
  refine ⟨n, G, r, hn, hl, hr, hnz, hni, polynomial_nonzero _ hb, hb, ?_⟩
  intro w hw
  rw [blowup_polynomial]
  simp only [Polynomial.IsRoot, Polynomial.eval_comp, Fintype.card_fin,
    eval_sub, eval_pow, eval_add, eval_one, eval_X]
  have harg : (1 + w) ^ k - 1 = (r : ℂ) := by rw [hw]; push_cast; ring
  rw [harg]
  exact hc

#print axioms seed_blowup_roots

#print axioms blowup_polynomial

end D5.S3.Combinatorics.Graph.Domination.TotalDominationBlowup

/- GID: D5/S3/Fourier/Concentration/MatchedResidualOccupation
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/MatchedResidualOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise matchability bounds the multinomial mass of two residual occupations. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
import D5.S3.Quantum.Schatten.MatrixSimilarity
import D5.S3.PrimeGaps.GreedyResidues

/-! Bounds for occupations that admit a pointwise matching along a finite relation. -/

set_option autoImplicit false
noncomputable section
open Finset
open D5.S3.Quantum.Entanglement.OccupancyWordSectors

namespace D5.S3.Fourier.Concentration.MatchedResidualOccupation

private def align {J : Type*} {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    Word J d × Word J d ≃ (Fin d → J × J) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr σ.symm (Equiv.refl J))).trans
    (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => J) (fun _ => J)).symm

private theorem matched_words_mass_le {J : Type*} [Fintype J] {d : ℕ}
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (E : J → J → Prop)
    [DecidableRel E] (S : Finset (Word J d × Word J d))
    (hS : ∀ x ∈ S, ∃ σ : Equiv.Perm (Fin d), ∀ i, E (x.1 i) (x.2 (σ i))) :
    (∑ x ∈ S, (∏ i, w (x.1 i)) * ∏ i, w (x.2 i)) ≤
      (d.factorial : ℝ) * (∑ e : J × J, if E e.1 e.2 then w e.1 * w e.2 else 0) ^ d := by
  classical
  let k (e : J × J) : ℝ := if E e.1 e.2 then w e.1 * w e.2 else 0
  let H (x : Word J d × Word J d) (σ : Equiv.Perm (Fin d)) : ℝ :=
    ∏ i, k (align σ x i)
  let term (x : Word J d × Word J d) := (∏ i, w (x.1 i)) * ∏ i, w (x.2 i)
  let event (σ : Equiv.Perm (Fin d)) (x : Word J d × Word J d) :=
    ∀ i, E (x.1 i) (x.2 (σ i))
  have hnonneg (x) : 0 ≤ term x :=
    mul_nonneg (prod_nonneg fun i _ => hw _) (prod_nonneg fun i _ => hw _)
  have hmask (σ) (x) : H x σ = term x * (if event σ x then 1 else 0) := by
    change (∏ i, if E (x.1 i) (x.2 (σ i)) then w (x.1 i) * w (x.2 (σ i)) else 0) = _
    rw [Fintype.prod_ite_zero, prod_mul_distrib, Equiv.prod_comp σ (fun i => w (x.2 i))]
    simp only [term, event, mul_ite, mul_one, mul_zero]
    split_ifs <;> rfl
  have hcovered : S ⊆ univ.filter (fun x => ∃ σ, event σ x) := by
    intro x hx
    exact mem_filter.mpr ⟨mem_univ x, hS x hx⟩
  have hcol (σ : Equiv.Perm (Fin d)) :
      (∑ x, H x σ) = (∑ e, k e) ^ d := by
    rw [show (∑ x, H x σ) = ∑ z : Fin d → J × J, ∏ i, k (z i) from
      (align σ).sum_comp (fun z => ∏ i, k (z i))]
    simpa using (Finset.sum_pow' (univ : Finset (J × J)) k d).symm
  change _ ≤ (d.factorial : ℝ) * (∑ e, k e) ^ d
  calc
    _ ≤ ∑ x ∈ univ.filter (fun x => ∃ σ, event σ x), term x :=
      sum_le_sum_of_subset_of_nonneg hcovered fun x _ _ => hnonneg x
    _ = ∑ x, term x * (if ∃ σ, event σ x then 1 else 0) := by
      rw [sum_filter]
      simp only [mul_ite, mul_one, mul_zero]
    _ ≤ ∑ σ, ∑ x, term x * (if event σ x then 1 else 0) :=
      LongGapsBetweenPrimes.weighted_union_bound term event hnonneg
    _ = ∑ σ, ∑ x, H x σ := by simp only [hmask]
    _ = _ := by simp [hcol, Fintype.card_perm, nsmul_eq_mul]

open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)

private theorem exists_reindex {J : Type*} {d : ℕ} {u v : Word J d}
    (h : occupation u = occupation v) :
    ∃ σ : Equiv.Perm (Fin d), ∀ i, u i = v (σ i) := by
  have h' : univ.val.map u = univ.val.map v := by simpa [occupation] using h
  obtain ⟨σ, hσ⟩ := (Multiset.map_univ_eq_iff u v).mp h'
  exact ⟨σ, congrFun hσ⟩

private theorem word_weight_eq {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}
    (w : J → ℝ) (u : Word J d) :
    (∏ i, w (u i)) = ∏ j, w j ^ (occupation u).count j := by
  calc
    _ = ((occupation u).map w).prod := by
      rw [occupation, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, Fin.prod_ofFn]
      rfl
    _ = ∏ j ∈ (occupation u).toFinset, w j ^ (occupation u).count j :=
      prod_multiset_map_count _ w
    _ = _ := prod_subset (subset_univ _) fun j _ hj => by
      have hn : j ∉ occupation u := fun h => hj (Multiset.mem_toFinset.mpr h)
      rw [Multiset.count_eq_zero.mpr hn, pow_zero]

private theorem sector_weight {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}
    (w : J → ℝ) (a : Multiset J) (ha : a.card = d) :
    (∑ u ∈ sectorWords d a, ∏ i, w (u i)) = monomialWeight w a.count := by
  have h (u) (hu : u ∈ sectorWords d a) : (∏ i, w (u i)) = ∏ j, w j ^ a.count j := by
    rw [word_weight_eq, (mem_filter.mp hu).2]
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, sector_words_card_multinomial a ha]
  rfl

/-- The weight of count-vector pairs with a pointwise matching is controlled by the
one-edge mass, uniformly in the degree. -/
theorem matched_occupation_mass_le {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (E : J → J → Prop) [DecidableRel E]
    (S : Finset ((J → ℕ) × (J → ℕ)))
    (hS : ∀ x ∈ S, ∃ u v : Word J d, (occupation u).count = x.1 ∧
      (occupation v).count = x.2 ∧ ∀ i, E (u i) (v i)) :
    let budget (dr : ℕ × ℝ) := (dr.1.factorial : ℝ) * dr.2 ^ dr.1
    (∑ x ∈ S, monomialWeight w x.1 * monomialWeight w x.2) ≤
      budget (d, ∑ e : J × J, if E e.1 e.2 then w e.1 * w e.2 else 0) := by
  classical
  let occ (x : Word J d × Word J d) := ((occupation x.1).count, (occupation x.2).count)
  let W : Finset (Word J d × Word J d) := univ.filter fun x => occ x ∈ S
  let wt (x : Word J d × Word J d) := (∏ i, w (x.1 i)) * ∏ i, w (x.2 i)
  have hW (x) (hx : x ∈ W) : occ x ∈ S := (mem_filter.mp hx).2
  have hmatch (x) (hx : x ∈ W) :
      ∃ σ : Equiv.Perm (Fin d), ∀ i, E (x.1 i) (x.2 (σ i)) := by
    obtain ⟨u, v, hu, hv, hE⟩ := hS (occ x) (hW x hx)
    obtain ⟨σ, hσ⟩ := exists_reindex (Multiset.ext.mpr (congrFun hu.symm))
    obtain ⟨τ, hτ⟩ := exists_reindex (Multiset.ext.mpr (congrFun hv))
    exact ⟨σ.trans τ, fun i => by simpa only [Equiv.trans_apply, hσ, ← hτ] using hE (σ i)⟩
  have hmass : (∑ x ∈ W, wt x) =
      ∑ a ∈ S, monomialWeight w a.1 * monomialWeight w a.2 := by
    rw [← sum_fiberwise_of_maps_to hW wt]
    refine sum_congr rfl fun x hx => ?_
    obtain ⟨u, v, hu, hv, _⟩ := hS x hx
    rcases x with ⟨a, b⟩
    dsimp at hu hv
    have hfiber :
        W.filter (fun y => occ y = (a, b)) = sectorWords d (occupation u) ×ˢ
          sectorWords d (occupation v) := by
      ext y
      simp only [mem_product, sectorWords, W, occ, mem_filter, mem_univ, true_and]
      rw [← hu, ← hv]
      simp only [Prod.mk.injEq]
      exact ⟨fun hy => ⟨Multiset.ext.mpr (congrFun hy.2.1), Multiset.ext.mpr (congrFun hy.2.2)⟩,
        fun hy => ⟨by simpa only [hy.1, hy.2, hu, hv] using hx,
          by rw [hy.1], by rw [hy.2]⟩⟩
    rw [hfiber, sum_product, ← hu, ← hv]
    simp only [wt, ← mul_sum, ← sum_mul, sector_weight w _ (occupation_card u),
      sector_weight w _ (occupation_card v)]
  rw [← hmass]
  exact matched_words_mass_le w hw E W hmatch

end D5.S3.Fourier.Concentration.MatchedResidualOccupation

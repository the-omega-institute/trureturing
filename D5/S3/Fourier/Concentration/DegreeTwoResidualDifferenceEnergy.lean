/- GID: D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared endpoints correct the directed difference energy to the disjoint degree-two mass. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
import D5.S3.Quantum.Entanglement.OccupancyWordSectors

/-! A collision sum of directed differences counts degree-two pairs after endpoint corrections. -/

set_option autoImplicit false
noncomputable section

open Finset

namespace D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy

open scoped Classical

variable {J : Type*} [Fintype J] [DecidableEq J]

private def kernel (g w : J → ℝ) (η : ℝ) (i j l k : J) : ℝ :=
  if |(g i - g j) - (g l - g k)| ≤ η then w i * w j * w l * w k else 0

private def edgePairWeight (g w : J → ℝ) (η : ℝ) (i j l k : J) : ℝ :=
  if i ≠ j ∧ l ≠ k then kernel g w η i j l k else 0

private def fourSum (f : J → J → J → J → ℝ) : ℝ := ∑ i, ∑ j, ∑ l, ∑ k, f i j l k

private def C (g w : J → ℝ) (η : ℝ) (i : J) : ℝ :=
  D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.nearCollisionMass
    (univ.erase i) g w η

private theorem overlap_expand (g w : J → ℝ) (η : ℝ) :
    fourSum (fun i j l k =>
      if i ≠ l ∧ j ≠ k then edgePairWeight g w η i j l k else 0) =
      fourSum (edgePairWeight g w η) -
      fourSum (fun i j l k => if l = i then edgePairWeight g w η i j l k else 0) -
      fourSum (fun i j l k => if k = j then edgePairWeight g w η i j l k else 0) +
      fourSum (fun i j l k => if l = i ∧ k = j then edgePairWeight g w η i j l k else 0) := by
  simp only [fourSum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro k _
  by_cases hi : l = i <;> by_cases hj : k = j <;> simp [hi, hj, Ne.symm]

private theorem shared_left (g w : J → ℝ) (η : ℝ) :
    fourSum (fun i j l k => if l = i then edgePairWeight g w η i j l k else 0) =
      ∑ i, w i ^ 2 * C g w η i := by
  unfold fourSum C
  apply sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ∑ k, edgePairWeight g w η i j i k := by
      apply sum_congr rfl
      intro j _
      simp [sum_ite_eq', mem_univ]
    _ = _ := by
      unfold D5.S3.Fourier.Concentration.FiniteSincCollisionMoment.nearCollisionMass
      have herase (f : J → ℝ) :
          (∑ j ∈ univ.erase i, f j) = ∑ j, if j ≠ i then f j else 0 := by
        rw [← sum_filter]
        congr 1
        ext j
        simp
      simp_rw [mul_sum, herase]
      apply sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [edgePairWeight]
      · rw [ite_eq_left hj]
        apply sum_congr rfl
        intro k _
        by_cases hk : k = i
        · subst k
          simp [edgePairWeight]
        · have heq : (g i - g j) - (g i - g k) = -(g j - g k) := by ring
          rw [edgePairWeight, ite_eq_left (show i ≠ j ∧ i ≠ k from ⟨Ne.symm hj, Ne.symm hk⟩)]
          simp only [ite_eq_left hk, kernel, heq, abs_neg, mul_ite, mul_zero]
          split_ifs <;> ring

private theorem shared_right (g w : J → ℝ) (η : ℝ) :
    fourSum (fun i j l k => if k = j then edgePairWeight g w η i j l k else 0) =
      ∑ i, w i ^ 2 * C g w η i := by
  let reverse : (J × J) × (J × J) ≃ (J × J) × (J × J) :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.prodComm J J) (Equiv.prodComm J J))
  let f (a : (J × J) × (J × J)) :=
    if a.2.1 = a.1.1 then edgePairWeight g w η a.1.1 a.1.2 a.2.1 a.2.2 else 0
  have hterm (i j l k : J) : f (reverse ((i, j), (l, k))) =
      if k = j then edgePairWeight g w η i j l k else 0 := by
    change (if j = k then edgePairWeight g w η k l j i else 0) = _
    by_cases h : k = j
    · simp [h, edgePairWeight, kernel, ne_comm, and_comm]
      split_ifs <;> ring
    · simp [h, Ne.symm h]
  rw [← shared_left g w η]
  have h := reverse.sum_comp f
  simp only [Fintype.sum_prod_type] at h
  unfold fourSum
  simpa only [hterm, f] using h

private theorem shared_both (g w : J → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    fourSum (fun i j l k => if l = i ∧ k = j then edgePairWeight g w η i j l k else 0) =
      ∑ i, ∑ j ∈ univ.erase i, w i ^ 2 * w j ^ 2 := by
  unfold fourSum
  apply sum_congr rfl
  intro i _
  have hcollapse (j : J) :
      (∑ l, ∑ k, if l = i ∧ k = j then edgePairWeight g w η i j l k else 0) =
        if j ≠ i then w i ^ 2 * w j ^ 2 else 0 := by
    have hsplit (l k : J) :
        (if l = i ∧ k = j then edgePairWeight g w η i j l k else 0) =
          if l = i then (if k = j then edgePairWeight g w η i j l k else 0) else 0 := by
      split_ifs <;> simp_all
    simp only [hsplit, sum_ite_irrel, sum_ite_eq', mem_univ, ite_true]
    by_cases h : j = i
    · simp [h, edgePairWeight]
    · simp [h, Ne.symm h, edgePairWeight, kernel, hη]
      ring
  simp_rw [hcollapse]
  rw [← sum_filter]
  congr 1
  ext j
  simp

private theorem disjoint_word_weight (g w : J → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    fourSum (fun i j l k =>
      if i ≠ l ∧ j ≠ k then edgePairWeight g w η i j l k else 0) =
      fourSum (edgePairWeight g w η) - 2 * (∑ i, w i ^ 2 * C g w η i) +
        ∑ i, ∑ j ∈ univ.erase i, w i ^ 2 * w j ^ 2 := by
  rw [overlap_expand, shared_left, shared_right, shared_both g w hη]
  ring

open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight monomialFrequency)

private theorem wordWeight_eq (w : J → ℝ) (u : Word J 2) :
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

private theorem wordFrequency_eq (g : J → ℝ) (u : Word J 2) :
    (∑ i, g (u i)) = monomialFrequency g (occupation u).count := by
  calc
    _ = ((occupation u).map g).sum := by
      rw [occupation, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Fin.sum_ofFn]
      rfl
    _ = ∑ j ∈ (occupation u).toFinset, (occupation u).count j • g j :=
      sum_multiset_map_count _ g
    _ = _ := by
      unfold monomialFrequency
      simp only [nsmul_eq_mul]
      apply sum_subset (subset_univ _)
      intro j _ hj
      have hn : j ∉ occupation u := fun h => hj (Multiset.mem_toFinset.mpr h)
      simp [Multiset.count_eq_zero.mpr hn]

omit [Fintype J] in
private theorem word_occupations_disjoint (u v : Word J 2) :
    (∀ j, (occupation u).count j = 0 ∨ (occupation v).count j = 0) ↔
      (u 0 ≠ v 0 ∧ u 0 ≠ v 1 ∧ u 1 ≠ v 0 ∧ u 1 ≠ v 1) := by
  have hmem (z : Word J 2) (j : J) : j ∈ occupation z ↔ j = z 0 ∨ j = z 1 := by
    change j ∈ List.ofFn z ↔ _
    rw [List.mem_ofFn]
    simp [Fin.exists_fin_two, eq_comm]
  simp only [Multiset.count_eq_zero, hmem]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e
      exact (h (u 0)).elim (fun h => h (Or.inl rfl)) (fun h => h (Or.inl e))
    · intro e
      exact (h (u 0)).elim (fun h => h (Or.inl rfl)) (fun h => h (Or.inr e))
    · intro e
      exact (h (u 1)).elim (fun h => h (Or.inr rfl)) (fun h => h (Or.inl e))
    · intro e
      exact (h (u 1)).elim (fun h => h (Or.inr rfl)) (fun h => h (Or.inr e))
  · rintro ⟨h00, h01, h10, h11⟩ j
    by_cases h : j = u 0 ∨ j = u 1
    · right
      rintro (e | e)
      · exact h.elim (fun h => h00 (h.symm.trans e)) (fun h => h10 (h.symm.trans e))
      · exact h.elim (fun h => h01 (h.symm.trans e)) (fun h => h11 (h.symm.trans e))
    · exact Or.inl h

private theorem count_sector_sum (w : J → ℝ) (a : J → ℕ)
    (ha : a ∈ piAntidiag univ 2) :
    (∑ u ∈ (univ : Finset (Word J 2)).filter (fun u => (occupation u).count = a),
      ∏ i, w (u i)) = monomialWeight w a := by
  let s := (Sym.equivNatSumOfFintype (α := J) (n := 2)).symm
    ⟨a, (mem_piAntidiag.mp ha).1⟩
  have hs : (s : Multiset J).count = a := by
    ext j
    exact congrArg (fun c : {P : J → ℕ // ∑ i, P i = 2} => c.val j)
      ((Sym.equivNatSumOfFintype (α := J) (n := 2)).apply_symm_apply _)
  have hfilter : (univ : Finset (Word J 2)).filter (fun u => (occupation u).count = a) =
      sectorWords 2 s := by
    ext u
    simp only [sectorWords, mem_filter, mem_univ, true_and, ← hs]
    exact ⟨fun h => Multiset.ext.mpr (congrFun h), fun h => by rw [h]⟩
  rw [hfilter]
  have h (u) (hu : u ∈ sectorWords 2 s) : (∏ i, w (u i)) = ∏ j, w j ^ a j := by
    have hu' : occupation u = s := (mem_filter.mp hu).2
    rw [wordWeight_eq, hu']
    exact prod_congr rfl fun j _ => by rw [congrFun hs j]
  have hcard : (sectorWords 2 (s : Multiset J)).card = Nat.multinomial univ a :=
    (sector_words_card_multinomial _ s.prop).trans (congrArg (Nat.multinomial univ) hs)
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul]
  change ((sectorWords 2 (s : Multiset J)).card : ℝ) * _ = _
  rw [hcard]
  rfl

private def residualCut (g : J → ℝ) (η : ℝ) (a b : J → ℕ) : Prop :=
  (∀ j, a j = 0 ∨ b j = 0) ∧
    |monomialFrequency g a - monomialFrequency g b| ≤ η

private theorem occupation_to_words (g w : J → ℝ) (η : ℝ) :
    (∑ a ∈ piAntidiag univ 2, ∑ b ∈ piAntidiag univ 2,
      if residualCut g η a b then monomialWeight w a * monomialWeight w b else 0) =
    ∑ u : Word J 2, ∑ v : Word J 2,
      if residualCut g η (occupation u).count (occupation v).count then
        (∏ i, w (u i)) * ∏ i, w (v i) else 0 := by
  classical
  let cuts := piAntidiag (univ : Finset J) 2
  let occ (u : Word J 2) := (occupation u).count
  let weight (u : Word J 2) := ∏ i, w (u i)
  have hm (u : Word J 2) (_ : u ∈ (univ : Finset (Word J 2))) : occ u ∈ cuts := by
    exact mem_piAntidiag.mpr ⟨
      (Multiset.sum_count_eq_card fun _ _ => mem_univ _).trans (occupation_card u),
      fun _ _ => mem_univ _⟩
  change _ = ∑ u, ∑ v, if residualCut g η (occ u) (occ v) then weight u * weight v else 0
  symm
  calc
    _ = ∑ a ∈ cuts, ∑ u ∈ univ.filter (fun u => occ u = a),
          ∑ v, if residualCut g η a (occ v) then weight u * weight v else 0 := by
      rw [← sum_fiberwise_of_maps_to hm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun u hu => ?_
      rw [(mem_filter.mp hu).2]
    _ = ∑ a ∈ cuts, ∑ u ∈ univ.filter (fun u => occ u = a),
          ∑ b ∈ cuts, ∑ v ∈ univ.filter (fun v => occ v = b),
            if residualCut g η a b then weight u * weight v else 0 := by
      refine sum_congr rfl fun a _ => sum_congr rfl fun u _ => ?_
      rw [← sum_fiberwise_of_maps_to hm]
      refine sum_congr rfl fun b _ => sum_congr rfl fun v hv => ?_
      rw [(mem_filter.mp hv).2]
    _ = _ := by
      refine sum_congr rfl fun a ha => ?_
      rw [sum_comm]
      refine sum_congr rfl fun b hb => ?_
      by_cases h : residualCut g η a b
      · simp only [ite_eq_left h, ← mul_sum, ← sum_mul, weight, occ,
          count_sector_sum w _ ha, count_sector_sum w _ hb]
      · simp [h]

private theorem words_to_edges (g w : J → ℝ) (η : ℝ) :
    (∑ u : Word J 2, ∑ v : Word J 2,
      if residualCut g η (occupation u).count (occupation v).count then
        (∏ i, w (u i)) * ∏ i, w (v i) else 0) =
    fourSum (fun i j l k =>
      if i ≠ l ∧ j ≠ k then edgePairWeight g w η i j l k else 0) := by
  classical
  let f (e : (J × J) × (J × J)) :=
    if e.1.1 ≠ e.2.1 ∧ e.1.2 ≠ e.2.2 then
      edgePairWeight g w η e.1.1 e.1.2 e.2.1 e.2.2 else 0
  let e : (Word J 2 × Word J 2) ≃ (J × J) × (J × J) :=
    (Equiv.prodCongr (finTwoArrowEquiv J) (finTwoArrowEquiv J)).trans
      (Equiv.prodProdProdComm J J J J) |>.trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm J J))
  have ht (u v : Word J 2) :
      (if residualCut g η (occupation u).count (occupation v).count then
        (∏ i, w (u i)) * ∏ i, w (v i) else 0) = f (e (u, v)) := by
    change _ = if u 0 ≠ v 1 ∧ v 0 ≠ u 1 then
      edgePairWeight g w η (u 0) (v 0) (v 1) (u 1) else 0
    have hgap : g (u 0) + g (u 1) - (g (v 0) + g (v 1)) =
        (g (u 0) - g (v 0)) - (g (v 1) - g (u 1)) := by ring
    simp only [residualCut, word_occupations_disjoint, ← wordFrequency_eq,
      Fin.sum_univ_two, Fin.prod_univ_two, hgap, edgePairWeight, kernel]
    by_cases h00 : u 0 = v 0 <;> by_cases h01 : u 0 = v 1 <;>
      by_cases h10 : u 1 = v 0 <;> by_cases h11 : u 1 = v 1 <;>
      simp [h00, h01, h10, h11, Ne.symm, eq_comm]
    split_ifs <;> ring
  have he := e.sum_comp f
  change _ = ∑ i, ∑ j, ∑ l, ∑ k, f ((i,j),(l,k))
  simpa only [Fintype.sum_prod_type, ← ht] using he

open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (nearCollisionMass)

/-- Weight of near-colliding degree-two count vectors with disjoint supports. -/
def degreeTwoResidualMass (g w : J → ℝ) (η : ℝ) : ℝ :=
  ∑ a ∈ piAntidiag univ 2, ∑ b ∈ piAntidiag univ 2,
    if residualCut g η a b then monomialWeight w a * monomialWeight w b else 0

private theorem directed_difference_mass (g w : J → ℝ) (η : ℝ) :
    fourSum (edgePairWeight g w η) =
      nearCollisionMass ((univ : Finset (J × J)).filter (fun e => e.1 ≠ e.2))
        (fun e => g e.1 - g e.2) (fun e => w e.1 * w e.2) η := by
  unfold fourSum nearCollisionMass
  simp only [sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases hij : i = j
  · simp [edgePairWeight, hij]
  · simp only [ite_eq_left hij, Ne, edgePairWeight, kernel]
    apply sum_congr rfl
    intro l _
    apply sum_congr rfl
    intro k _
    by_cases hlk : l = k
    · simp [hlk, hij]
    · simp [hlk, hij]
      split_ifs <;> ring

/-- Shared endpoints account exactly for the difference between edge energy and disjoint mass. -/
theorem degree_two_residual (g w : J → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    let rate (x : ℝ × ℝ) := x.1 - x.2
    degreeTwoResidualMass g w η =
      nearCollisionMass ((univ : Finset (J × J)).filter (fun e => e.1 ≠ e.2))
        (fun e => rate (g e.1, g e.2)) (fun e => w e.1 * w e.2) η -
      2 * (∑ i, w i ^ 2 * nearCollisionMass (univ.erase i) g w η) +
        ∑ i, ∑ j ∈ univ.erase i, w i ^ 2 * w j ^ 2 := by
  dsimp only
  unfold degreeTwoResidualMass
  rw [occupation_to_words, words_to_edges, disjoint_word_weight g w hη, directed_difference_mass]
  rfl

end D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy

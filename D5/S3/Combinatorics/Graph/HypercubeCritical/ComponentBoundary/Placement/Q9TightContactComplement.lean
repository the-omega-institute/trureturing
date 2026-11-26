/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightContactComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The two complementary axes act on contacts of a tight minimum displacement family. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-! Antipodal symmetries of minimum contacts in a tight displacement family. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement

open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator
open private cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private differingAxes foldl_flip_apply differingAxes_foldl_flip first_is_flip_word
  mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-- If the minimum displacements on parity `b` are all the `d`-subsets of `A`,
flipping the two axes of `A \ T` at both endpoints of a contact of displacement `T`
gives another contact of displacement `T` on the same starting parity. -/
theorem minimum_contact_flip_complement
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ} {A T : Finset (Fin 9)} {x y : Q 9}
    (hd : 0 < d) (hsep : ∀ u ∈ C, ∀ v ∈ D, d ≤ hammingDist u v)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0))
    (hA : A.card = d + 2) (hfamily : minimumDisplacements C D b d = A.powersetCard d)
    (hx : x ∈ C) (hy : y ∈ D) (hxb : parity x = b)
    (hdist : hammingDist x y = d) (hT : differingAxes x y = T) :
    (A \ T).card = 2 ∧
      let x' := (A \ T).toList.foldl flip x
      let y' := (A \ T).toList.foldl flip y
      x' ∈ C ∧ y' ∈ D ∧ parity x' = b ∧ hammingDist x' y' = d ∧ differingAxes x' y' = T ∧
        differingAxes x x' = A \ T ∧ differingAxes y y' = A \ T := by
  classical
  have hmem : T ∈ minimumDisplacements C D b d :=
    mem_minimumDisplacements.mpr ⟨x, hx, y, hy, hxb, hdist, hT⟩
  rw [hfamily] at hmem
  obtain ⟨hTA, hTcard⟩ := Finset.mem_powersetCard.mp hmem
  have hcomplement_card : (A \ T).card = 2 := by
    rw [Finset.card_sdiff_of_subset hTA, hA, hTcard]
    omega
  have hTpos : 0 < T.card := by simpa only [hTcard] using hd
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hTpos
  let ridge := (T.erase i).toList
  have hnd : ridge.Nodup := Finset.nodup_toList _
  have hlen : ridge.length + 1 = d := by
    dsimp [ridge]
    rw [Finset.length_toList, Finset.card_erase_add_one hi, hTcard]
  have hs : ∀ u ∈ C, ∀ v ∈ D, ridge.length + 1 ≤ hammingDist u v := by
    rw [hlen]
    exact hsep
  have hxi : RidgeContact C D b ridge i x :=
    ⟨by simp [ridge], hx, hxb, (first_is_flip_word T hT hi).symm ▸ hy⟩
  obtain ⟨f, hf, hAf⟩ := hC i
  obtain ⟨g, hg, hAg⟩ := hD (!(wordParity ridge b))
  obtain ⟨z, hzx, hz, hzcell⟩ :=
    minimum_distance_contact_has_companion hnd hs f g hf hg hAf hAg hxi

  have hword (l : Fin 9) (hl : l ∉ ridge) : (ridge ++ [l]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha k hk heq
    exact hl ((heq.trans (List.mem_singleton.mp hk)) ▸ ha)
  have hRidgeDisplacement (l : Fin 9) (hl : l ∉ ridge) (u : Q 9) :
      differingAxes u (flip (ridge.foldl flip u) l) = insert l (T.erase i) := by
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.toFinset_append,
      List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, ridge,
      Finset.toList_toFinset, Finset.union_singleton] using
      differingAxes_foldl_flip (ridge ++ [l]) (hword l hl) u
  have hCompetitor (l : Fin 9) (ha : RidgeActiveAxis C D b ridge l) (hli : l ≠ i) :
      l ∈ A \ T := by
    obtain ⟨u, hlu, hu, hub, hv⟩ := ha
    let v := flip (ridge.foldl flip u) l
    have hdispl : differingAxes u v = insert l (T.erase i) := hRidgeDisplacement l hlu u
    have hnotErase : l ∉ T.erase i := fun hl => hlu (Finset.mem_toList.mpr hl)
    have hdv : hammingDist u v = d := by
      change (differingAxes u v).card = d
      rw [hdispl, Finset.card_insert_of_notMem hnotErase, Finset.card_erase_add_one hi, hTcard]
    have hmem' : insert l (T.erase i) ∈ minimumDisplacements C D b d :=
      mem_minimumDisplacements.mpr ⟨u, hu, v, hv, hub, hdv, hdispl⟩
    rw [hfamily] at hmem'
    exact Finset.mem_sdiff.mpr
      ⟨(Finset.mem_powersetCard.mp hmem').1 (Finset.mem_insert_self _ _),
        fun hl => hnotErase (Finset.mem_erase.mpr ⟨hli, hl⟩)⟩

  have hsubset : differingAxes x z ⊆ A \ T := by
    intro l hl
    have hne : x l ≠ z l := (Finset.mem_filter.mp hl).2
    have hactive : RidgeActiveAxis C D b ridge l ∧ l ≠ i := by
      by_contra hn
      exact hne (hzcell l hn).symm
    exact hCompetitor l hactive.1 hactive.2
  have hdiff_card : 1 < (differingAxes x z).card := by
    change 1 < hammingDist x z
    have hzero : hammingDist x z ≠ 0 := fun h => hzx (hammingDist_eq_zero.mp h).symm
    have hone : hammingDist x z ≠ 1 := fun h =>
      cubeParity_ne_of_adj (show (D5.S3.Combinatorics.Graph.Hypercube.hypercube 9).Adj x z
        from h) (hxb.trans hz.2.2.1.symm)
    omega
  have hCdiff : differingAxes x z = A \ T :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)

  let endpoint (u : Q 9) : Q 9 := (ridge ++ [i]).foldl flip u
  have hEndpoint (u : Q 9) : endpoint u = flip (ridge.foldl flip u) i := by
    simp only [endpoint, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hxy : endpoint x = y := (hEndpoint x).trans (first_is_flip_word T hT hi)
  have hwD : endpoint z ∈ D := (hEndpoint z).symm ▸ hz.2.2.2
  have hzw : differingAxes z (endpoint z) = T := by
    rw [hEndpoint z, hRidgeDisplacement i hxi.1 z, Finset.insert_erase hi]
  have hCommon : differingAxes (endpoint x) (endpoint z) = differingAxes x z := by
    ext l
    simp only [endpoint, differingAxes, Finset.mem_filter, Finset.mem_univ, true_and,
      foldl_flip_apply _ (hword i hxi.1)]
    by_cases hl : l ∈ ridge ++ [i]
    · simp [hl]
    · simp [hl]
  have hDdiff : differingAxes y (endpoint z) = A \ T := by
    rw [← hxy, hCommon, hCdiff]

  have flip_eq (u v : Q 9) (h : differingAxes u v = A \ T) :
      (A \ T).toList.foldl flip u = v := by
    funext l
    rw [foldl_flip_apply _ (Finset.nodup_toList _)]
    have hl : l ∈ (A \ T).toList ↔ u l ≠ v l := by
      rw [Finset.mem_toList, ← h]
      simp [differingAxes]
    simp only [hl]
    cases u l <;> cases v l <;> decide
  have hxflip := flip_eq x z hCdiff
  have hyflip := flip_eq y (endpoint z) hDdiff
  have hzw_dist : hammingDist z (endpoint z) = d := by
    change (differingAxes z (endpoint z)).card = d
    rw [hzw, hTcard]
  refine ⟨hcomplement_card, ?_⟩
  simpa only [hxflip, hyflip] using
    (show z ∈ C ∧ endpoint z ∈ D ∧ parity z = b ∧ hammingDist z (endpoint z) = d ∧
      differingAxes z (endpoint z) = T ∧ differingAxes x z = A \ T ∧
      differingAxes y (endpoint z) = A \ T from
      ⟨hz.2.1, hwD, hz.2.2.1, hzw_dist, hzw, hCdiff, hDdiff⟩)

private theorem differingAxes_symm (x y : Q 9) :
    differingAxes x y = differingAxes y x := by
  ext j
  simp only [differingAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Ne.symm, Ne.symm⟩

private theorem differingAxes_right_inj {x y z : Q 9}
    (h : differingAxes x y = differingAxes x z) : y = z := by
  funext j
  have he : x j ≠ y j ↔ x j ≠ z j := by
    simpa only [differingAxes, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.ext_iff.mp h j)
  cases hx : x j <;> cases hy : y j <;> cases hz : z j <;> simp_all

private theorem differingAxes_flip_cell (A : Finset (Fin 9)) (x y : Q 9)
    (hxy : differingAxes x y ⊆ A) :
    differingAxes x (A.toList.foldl flip y) = A \ differingAxes x y := by
  classical
  ext j
  simp only [Finset.mem_sdiff, differingAxes, Finset.mem_filter, Finset.mem_univ, true_and,
    foldl_flip_apply _ (Finset.nodup_toList _), Finset.mem_toList]
  by_cases hj : j ∈ A
  · cases x j <;> cases y j <;> simp [hj]
  · have hab : x j = y j := by
      by_contra hn
      exact hj (hxy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    simp [hj, hab]

private theorem flip_cell_involution (A : Finset (Fin 9)) (x : Q 9) :
    A.toList.foldl flip (A.toList.foldl flip x) = x := by
  funext j
  simp only [foldl_flip_apply _ (Finset.nodup_toList _)]
  by_cases hj : j ∈ A.toList <;> simp [hj]

/-- In a cell on the axes of a tight displacement family, the antipodal flip
matches the two parity slices wherever both are present. -/
theorem minimum_contact_cell_antipodes
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ} {A : Finset (Fin 9)} {x y : Q 9}
    (hd : 0 < d) (hsep : ∀ u ∈ C, ∀ v ∈ D, d ≤ hammingDist u v)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0))
    (hA : A.card = d + 2) (hfamily : minimumDisplacements C D b d = A.powersetCard d)
    (hx : x ∈ C) (hy : y ∈ D) (hpx : parity x = b)
    (hpy : parity (A.toList.foldl flip y) = b)
    (hcell : ∀ j ∉ A, x j = y j) :
    A.toList.foldl flip y ∈ C ∧ A.toList.foldl flip x ∈ D := by
  classical
  let T := differingAxes x y
  have hTA : T ⊆ A := by
    intro j hj
    by_contra hn
    exact (Finset.mem_filter.mp hj).2 (hcell j hn)
  have hcom : differingAxes x (A.toList.foldl flip y) = A \ T :=
    differingAxes_flip_cell A x y hTA
  have hdlo : d ≤ T.card := hsep x hx y hy
  have hcomp : hammingDist x (A.toList.foldl flip y) + T.card = d + 2 := by
    change (differingAxes x (A.toList.foldl flip y)).card + T.card = d + 2
    rw [hcom, Finset.card_sdiff_add_card_eq_card hTA, hA]
  by_cases hzero : hammingDist x (A.toList.foldl flip y) = 0
  · have he := hammingDist_eq_zero.mp hzero
    exact ⟨he ▸ hx, by simpa only [he, flip_cell_involution] using hy⟩
  · have hone : hammingDist x (A.toList.foldl flip y) ≠ 1 := fun h =>
      cubeParity_ne_of_adj
        (show (D5.S3.Combinatorics.Graph.Hypercube.hypercube 9).Adj x
          (A.toList.foldl flip y) from h) (hpx.trans hpy.symm)
    have hdist : hammingDist x y = d := by
      change T.card = d
      omega
    obtain ⟨_, hflip⟩ :=
      minimum_contact_flip_complement hd hsep hC hD hA hfamily hx hy hpx hdist (T := T) rfl
    dsimp only at hflip
    have hfirst : (A \ T).toList.foldl flip x = A.toList.foldl flip y :=
      differingAxes_right_inj (hflip.2.2.2.2.2.1.trans hcom.symm)
    have hrev : differingAxes y (A.toList.foldl flip x) = A \ T := by
      rw [differingAxes_flip_cell A y x (by simpa only [differingAxes_symm y x] using hTA),
        differingAxes_symm y x]
    have hsecond : (A \ T).toList.foldl flip y = A.toList.foldl flip x :=
      differingAxes_right_inj (hflip.2.2.2.2.2.2.trans hrev.symm)
    exact ⟨hfirst ▸ hflip.1, hsecond ▸ hflip.2.1⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement

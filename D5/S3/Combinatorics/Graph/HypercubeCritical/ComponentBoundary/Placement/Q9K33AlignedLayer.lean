/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The six-axis antipode aligns contacting slices as three-by-three rectangles. -/

import Mathlib.Data.Set.Card
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
import D5.S3.Combinatorics.ContactSwapRectangle
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression

/-! Transport the actual contacts in a six-axis cube layer to rectangle swaps. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33AlignedLayer

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (directions mem_directions flip_injective)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (RidgeContact minimumDisplacements)
open Q9DegreeThreeContactOrbit (translated_contact_of_three_partners exterior_midpoint_directions)
open Omega.ContactSwapRectangle (ClosedUnderContactSwaps eq_prod_of_contact)
open SixAxisGridSignedCompression (flip_append_left flip_append_right)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

private def orientedRow (σ : Equiv.Perm (Fin 9)) (a : Fin 3) : Fin 9 := σ (a.castAdd 6)
private def orientedCol (σ : Equiv.Perm (Fin 9)) (a : Fin 3) : Fin 9 :=
  σ (Fin.natAdd 3 (a.castAdd 3))
private def orientedVertex (σ : Equiv.Perm (Fin 9)) (a b z : Q 3) : Q 9 :=
  fun k => SixAxisGridSignedCompression.vertex a b z (σ.symm k)

variable {σ : Equiv.Perm (Fin 9)}
local notation "rowAxis" => orientedRow σ
local notation "colAxis" => orientedCol σ

private def anti (a : Q 3) : Q 3 := fun i => !a i
private def blockParity (a : Q 3) : Bool := (a 0 + a 1) + a 2

private theorem flip_reindex (x : Q 9) (i : Fin 9) :
    flip (fun k => x (σ.symm k)) (σ i) = fun k => flip x i (σ.symm k) := by
  funext k
  by_cases hk : k = σ i
  · subst k
    simp [BalancedCriticalSpectrum.flip]
  · have hne : σ.symm k ≠ i := fun he => hk (by rw [← he, Equiv.apply_symm_apply])
    simp [BalancedCriticalSpectrum.flip, hk, hne]

private theorem flip_row (a b z : Q 3) (i : Fin 3) :
    flip (orientedVertex σ a b z) (rowAxis i) = orientedVertex σ (flip a i) b z := by
  unfold orientedRow orientedVertex
  rw [flip_reindex]
  simp only [SixAxisGridSignedCompression.vertex, flip_append_left]

private theorem flip_col (a b z : Q 3) (j : Fin 3) :
    flip (orientedVertex σ a b z) (colAxis j) = orientedVertex σ a (flip b j) z := by
  unfold orientedCol orientedVertex
  rw [flip_reindex]
  simp only [SixAxisGridSignedCompression.vertex, flip_append_right, flip_append_left]

private theorem row_col_ne (i j : Fin 3) : rowAxis i ≠ colAxis j := by
  intro he
  have hn := congrArg (Fin.val : Fin 9 → ℕ) (σ.injective he)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hn
  omega

private theorem injective_row : Function.Injective rowAxis := fun _ _ h =>
  Fin.ext (congrArg (Fin.val : Fin 9 → ℕ) (σ.injective h))

private theorem injective_col : Function.Injective colAxis := by
  intro i j hij
  have hn := congrArg (Fin.val : Fin 9 → ℕ) (σ.injective hij)
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_right_inj] at hn
  exact Fin.ext hn

set_option maxRecDepth 10000 in
private theorem block_contact :
    ∀ a c : Q 3, blockParity a = blockParity c → a ≠ c →
    ∃ i : Fin 3, flip a i = anti c ∧ flip c i = anti a ∧
      flip (flip a (i + 1)) (i + 2) = c ∧
      flip (flip (anti c) (i + 1)) (i + 2) = anti a := by
  decide +kernel

private theorem row_parity (a a' b z : Q 3) (ha : blockParity a = blockParity a') :
    parity (orientedVertex σ a b z) = parity (orientedVertex σ a' b z) := by
  by_cases he : a = a'
  · rw [he]
  obtain ⟨i, _, _, h, _⟩ := block_contact a a' ha he
  rw [← h, ← flip_row, ← flip_row, parity_flip, parity_flip, Bool.not_not]

private theorem col_parity (a b b' z : Q 3) (hb : blockParity b = blockParity b') :
    parity (orientedVertex σ a b z) = parity (orientedVertex σ a b' z) := by
  by_cases he : b = b'
  · rw [he]
  obtain ⟨j, _, _, h, _⟩ := block_contact b b' hb he
  rw [← h, ← flip_col, ← flip_col, parity_flip, parity_flip, Bool.not_not]

private def leftLayer (σ : Equiv.Perm (Fin 9)) (C : Finset (Q 9)) (z : Q 3) (p q : Bool) : Set (Q 3 × Q 3) :=
  {v | blockParity v.1 = p ∧ blockParity v.2 = q ∧ orientedVertex σ v.1 v.2 z ∈ C}

private def alignedLayer (σ : Equiv.Perm (Fin 9)) (D : Finset (Q 9)) (z : Q 3) (p q : Bool) : Set (Q 3 × Q 3) :=
  {v | blockParity v.1 = p ∧ blockParity v.2 = q ∧ orientedVertex σ (anti v.1) (anti v.2) z ∈ D}

/-- A contact in a K₃,₃ layer forces the two parity slices, aligned by the
six-axis antipode, to coincide with the product of their block projections. -/
theorem aligned_layers_eq_product
    {C D : Finset (Q 9)} {b p q : Bool} {z : Q 3}
    {a a' c c' : Q 3}
    (hC : ∀ i : Fin 9, ∃ f : Q 9 → ℝ,
      (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f x = 0))
    (hD : ∃ g : Q 9 → ℝ, (∀ x, g x ≠ 0 ↔ x ∈ D ∧ parity x = b) ∧
      (∀ x ∉ D, weightedLinear (fun _ => 1) g x = 0))
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hmask : ∀ i j : Fin 9, ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      (∃ r s, i = rowAxis r ∧ j = colAxis s) ∨ (∃ r s, i = colAxis s ∧ j = rowAxis r))
    (ha : (a, c) ∈ leftLayer σ C z p q) (hd : (a', c') ∈ alignedLayer σ D z p q)
    (hpar : parity (orientedVertex σ a c z) = b) (hr : a ≠ a') (hc : c ≠ c') :
    leftLayer σ C z p q = alignedLayer σ D z p q ∧
      leftLayer σ C z p q = (Prod.fst '' leftLayer σ C z p q) ×ˢ
        (Prod.snd '' leftLayer σ C z p q) := by
  apply eq_prod_of_contact _ ha hd hr hc
  intro u u' v v' hu hv hru hcv
  obtain ⟨hup, hvq, hx⟩ := hu
  obtain ⟨hup', hvq', hy⟩ := hv
  obtain ⟨i, hflipA, hflipA', hAA, hAA'⟩ := block_contact u u' (hup.trans hup'.symm) hru
  obtain ⟨j, hflipB, hflipB', hBB, hBB'⟩ := block_contact v v' (hvq.trans hvq'.symm) hcv
  have hp' : parity (orientedVertex σ u v z) = b := by
    rw [row_parity u a v z (hup.trans ha.1.symm),
      col_parity a v c z (hvq.trans ha.2.1.symm), hpar]
  have hrowContact : RidgeContact C D b [colAxis j] (rowAxis i) (orientedVertex σ u v z) := by
    refine ⟨by simp [(row_col_ne i j)], hx, hp', ?_⟩
    simpa only [List.foldl_cons, List.foldl_nil, flip_col, flip_row, hflipA, hflipB] using hy
  have hcolContact : RidgeContact C D b [rowAxis i] (colAxis j) (orientedVertex σ u v z) := by
    refine ⟨by simp [(row_col_ne i j).symm], hx, hp', ?_⟩
    simpa only [List.foldl_cons, List.foldl_nil, flip_row, flip_col, hflipA, hflipB] using hy
  have other (k t : Fin 3) : k = t ∨ k = t + 1 ∨ k = t + 2 := by
    fin_cases k <;> fin_cases t <;> decide
  have hrow (k : Fin 9) (hm : ({colAxis j, k} : Finset (Fin 9)) ∈
      minimumDisplacements C D b 2) :
      k = rowAxis i ∨ k = rowAxis (i + 1) ∨ k = rowAxis (i + 2) := by
    rcases hmask _ _ hm with ⟨l, _, he, _⟩ | ⟨l, _, _, rfl⟩
    · exact False.elim (row_col_ne l j he.symm)
    · rcases other l i with he | he | he <;> simp [he]
  have hcol (k : Fin 9) (hm : ({rowAxis i, k} : Finset (Fin 9)) ∈
      minimumDisplacements C D b 2) :
      k = colAxis j ∨ k = colAxis (j + 1) ∨ k = colAxis (j + 2) := by
    rcases hmask _ _ hm with ⟨_, l, _, rfl⟩ | ⟨_, l, he, _⟩
    · rcases other l j with he | he | he <;> simp [he]
    · exact False.elim (row_col_ne i l he)
  obtain ⟨g, hg, hAg⟩ := hD
  obtain ⟨f₁, hf₁, hAf₁⟩ := hC (rowAxis i)
  obtain ⟨f₂, hf₂, hAf₂⟩ := hC (colAxis j)
  have cycling : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  have hR := translated_contact_of_three_partners
    (fun h => cycling i (injective_row h)) hsep hrow f₁ g hf₁ hg hAf₁ hAg hrowContact
  have hS := translated_contact_of_three_partners
    (fun h => cycling j (injective_col h)) hsep hcol f₂ g hf₂ hg hAf₂ hAg hcolContact
  have hx₁ : orientedVertex σ u' v z ∈ C := by simpa only [flip_row, hAA] using hR.2.1
  have hx₂ : orientedVertex σ u v' z ∈ C := by simpa only [flip_col, hBB] using hS.2.1
  have hy₁ : orientedVertex σ (anti u) (anti v') z ∈ D := by
    simpa only [List.foldl_cons, List.foldl_nil, flip_row, flip_col, hAA, hflipA', hflipB] using hR.2.2.2
  have hy₂ : orientedVertex σ (anti u') (anti v) z ∈ D := by
    simpa only [List.foldl_cons, List.foldl_nil, flip_row, flip_col, hBB, hflipB', hflipA] using hS.2.2.2
  exact ⟨⟨⟨hup', hvq, hx₁⟩, ⟨hup, hvq', hy₁⟩⟩,
    ⟨⟨hup, hvq', hx₂⟩, ⟨hup', hvq, hy₂⟩⟩⟩


set_option maxRecDepth 10000 in
private theorem block_midpoint_split :
    ∀ a a' : Q 3, ∀ i : Fin 3, flip a i = anti a' →
      ∀ u : Q 3, blockParity u = blockParity a ↔
        u = a' ∨ ∃ k : Fin 3, u = flip (flip a i) k := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem not_block_antipode_neighbor :
    ∀ a a' : Q 3, ∀ i k : Fin 3, flip a i = anti a' →
      a' ≠ flip (flip a i) k := by
  decide +kernel

open Classical in
private theorem projection_three {C : Finset (Q 9)} {P : Set (Q 3)}
    {a a' : Q 3} {i : Fin 3} (hi : flip a i = anti a') (ha' : a' ∈ P)
    (v : Q 3 → Q 9) (axes : Fin 3 → Fin 9) (hinj : Function.Injective axes)
    (hflip : ∀ u j, flip (v u) (axes j) = v (flip u j))
    (hP : ∀ u, u ∈ P ↔ blockParity u = blockParity a ∧ v u ∈ C)
    (hsub : directions C (v (flip a i)) ⊆ univ.image axes)
    (hn : (directions C (v (flip a i))).card = 2) : P.ncard = 3 := by
  let T : Finset (Fin 3) := univ.filter fun k => axes k ∈ directions C (v (flip a i))
  have hTm (k : Fin 3) : k ∈ T ↔ v (flip (flip a i) k) ∈ C := by
    simp only [T, mem_filter, mem_univ, true_and, mem_directions, hflip]
  have himage : T.image axes = directions C (v (flip a i)) := by
    ext k
    rw [mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (mem_filter.mp hj).2
    · intro hk
      obtain ⟨j, _, rfl⟩ := mem_image.mp (hsub hk)
      exact ⟨j, mem_filter.mpr ⟨mem_univ _, hk⟩, rfl⟩
  have hT : T.card = 2 := by rw [← hn, ← himage, card_image_of_injective _ hinj]
  let f := flip (flip a i)
  have heq : P = insert a' (f '' (T : Set (Fin 3))) := by
    ext u
    rw [hP, block_midpoint_split a a' i hi, Set.mem_insert_iff]
    constructor
    · rintro ⟨rfl | ⟨k, rfl⟩, hu⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, (hTm k).mpr hu, rfl⟩
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact ⟨Or.inl rfl, ((hP _).mp ha').2⟩
      · exact ⟨Or.inr ⟨k, rfl⟩, (hTm k).mp hk⟩
  have hnot : a' ∉ f '' (T : Set (Fin 3)) := by
    rintro ⟨k, _, hk⟩
    exact not_block_antipode_neighbor a a' i k hi hk.symm
  rw [heq, Set.ncard_insert_of_notMem hnot, Set.ncard_image_of_injective _ (flip_injective _)]
  simp [hT]

open Classical in
/-- The two projections of a contacting (K_{3,3}) slice have three elements
each. The intermediate exterior vertex has exactly two neighbors in the
set of three candidate directions. The antipodal point supplies the third. -/
theorem aligned_layer_three_by_three
    {C D : Finset (Q 9)} {b p q : Bool} {z : Q 3}
    {a a' c c' : Q 3}
    (hC : ∀ i : Fin 9, ∃ f : Q 9 → ℝ,
      (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f x = 0))
    (hD : ∃ g : Q 9 → ℝ, (∀ x, g x ≠ 0 ↔ x ∈ D ∧ parity x = b) ∧
      (∀ x ∉ D, weightedLinear (fun _ => 1) g x = 0))
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hmask : ∀ i j : Fin 9, ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      (∃ r s, i = rowAxis r ∧ j = colAxis s) ∨ (∃ r s, i = colAxis s ∧ j = rowAxis r))
    (ha : (a, c) ∈ leftLayer σ C z p q) (hd : (a', c') ∈ alignedLayer σ D z p q)
    (hpar : parity (orientedVertex σ a c z) = b) (hr : a ≠ a') (hc : c ≠ c')
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) :
    (Prod.fst '' leftLayer σ C z p q).ncard = 3 ∧
      (Prod.snd '' leftLayer σ C z p q).ncard = 3 := by
  obtain ⟨hEq, hp⟩ := aligned_layers_eq_product hC hD hsep hmask ha hd hpar hr hc
  have hdLeft : (a', c') ∈ leftLayer σ C z p q := hEq.symm ▸ hd
  obtain ⟨i, hi, _, _, _⟩ := block_contact a a' (ha.1.trans hd.1.symm) hr
  obtain ⟨j, hj, _, _, _⟩ := block_contact c c' (ha.2.1.trans hd.2.1.symm) hc
  have hρ (k : Fin 9) (hm : ({colAxis j, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2) :
      k ∈ univ.image rowAxis := by
    rcases hmask _ _ hm with ⟨r, _, he, _⟩ | ⟨r, _, _, rfl⟩
    · exact (row_col_ne r j he.symm).elim
    · exact mem_image_of_mem _ (mem_univ _)
  have hσ (k : Fin 9) (hm : ({rowAxis i, k} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2) :
      k ∈ univ.image colAxis := by
    rcases hmask _ _ hm with ⟨_, s, _, rfl⟩ | ⟨_, s, he, _⟩
    · exact mem_image_of_mem _ (mem_univ _)
    · exact (row_col_ne i s he).elim
  have hA : (univ.image rowAxis).card ≤ 3 := by rw [card_image_of_injective _ injective_row]; decide
  have hB : (univ.image colAxis).card ≤ 3 := by rw [card_image_of_injective _ injective_col]; decide
  have hdRow : flip (flip (orientedVertex σ a c z) (rowAxis i)) (colAxis j) ∈ D := by
    rw [flip_row, flip_col, hi, hj]
    exact hd.2.2
  have hdCol : flip (flip (orientedVertex σ a c z) (colAxis j)) (rowAxis i) ∈ D := by
    rw [flip_col, flip_row, hi, hj]
    exact hd.2.2
  obtain ⟨hsRow, hnRow⟩ := exterior_midpoint_directions hA hρ hsep hrC hbC hpar ha.2.2 hdRow
  obtain ⟨hsCol, hnCol⟩ := exterior_midpoint_directions hB hσ hsep hrC hbC hpar ha.2.2 hdCol
  rw [flip_row] at hsRow hnRow
  rw [flip_col] at hsCol hnCol
  have hRow (u : Q 3) : u ∈ Prod.fst '' leftLayer σ C z p q ↔
      blockParity u = blockParity a ∧ orientedVertex σ u c z ∈ C := by
    constructor
    · intro hu
      have hcProj : c ∈ Prod.snd '' leftLayer σ C z p q := ⟨(a,c), ha, rfl⟩
      have hm : (u,c) ∈ leftLayer σ C z p q := hp.symm ▸ Set.mem_prod.mpr ⟨hu, hcProj⟩
      exact ⟨hm.1.trans ha.1.symm, hm.2.2⟩
    · rintro ⟨hu, hmem⟩
      exact ⟨(u,c), ⟨hu.trans ha.1, ha.2.1, hmem⟩, rfl⟩
  have hCol (u : Q 3) : u ∈ Prod.snd '' leftLayer σ C z p q ↔
      blockParity u = blockParity c ∧ orientedVertex σ a u z ∈ C := by
    constructor
    · intro hu
      have haProj : a ∈ Prod.fst '' leftLayer σ C z p q := ⟨(a,c), ha, rfl⟩
      have hm : (a,u) ∈ leftLayer σ C z p q := hp.symm ▸ Set.mem_prod.mpr ⟨haProj, hu⟩
      exact ⟨hm.2.1.trans ha.2.1.symm, hm.2.2⟩
    · rintro ⟨hu, hmem⟩
      exact ⟨(a,u), ⟨ha.1, hu.trans ha.2.1, hmem⟩, rfl⟩
  exact ⟨projection_three hi ⟨(a',c'), hdLeft, rfl⟩ (fun u => orientedVertex σ u c z)
      rowAxis injective_row (fun u k => flip_row u c z k) hRow hsRow hnRow,
    projection_three hj ⟨(a',c'), hdLeft, rfl⟩ (fun u => orientedVertex σ a u z)
      colAxis injective_col (fun u k => flip_col a u z k) hCol hsCol hnCol⟩

open private mem_minimumDisplacements differingAxes differingAxes_foldl_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)

open Q9SquareMaskGraph (activeAxes maskGraph nine_masks_on_six_axes_bipartite)
open Q9WeightedSaturation (defect signedBiadjacency)

open Classical in
private theorem orient_mask_graph {C D : Finset (Q 9)} {b : Bool}
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 6)
    {R : Finset (activeAxes (minimumDisplacements C D b 2))} (hR : R.card = 3)
    (hG : ∀ a c, (maskGraph (minimumDisplacements C D b 2)).Adj a c ↔
      (a ∈ R ∧ c ∉ R) ∨ (a ∉ R ∧ c ∈ R)) :
    ∃ σ : Equiv.Perm (Fin 9), ∀ i j : Fin 9,
      ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 →
      (∃ r s, i = orientedRow σ r ∧ j = orientedCol σ s) ∨
        (∃ r s, i = orientedCol σ s ∧ j = orientedRow σ r) := by
  let F := minimumDisplacements C D b 2
  let A := activeAxes F
  have hA : Fintype.card A = 6 := (Fintype.card_coe _).trans haxes
  have hleft : Fintype.card {a : A // a ∈ R} = 3 := (Fintype.card_coe _).trans hR
  have hright : Fintype.card {a : A // a ∉ R} = 3 := by
    rw [Fintype.card_subtype_compl, hA, hleft]
  have hext : Fintype.card {a : Fin 9 // a ∉ A} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hA]
  let rows := Fintype.equivOfCardEq (Fintype.card_fin 3 |>.trans hleft.symm)
  let cols := Fintype.equivOfCardEq (Fintype.card_fin 3 |>.trans hright.symm)
  let outside := Fintype.equivOfCardEq (Fintype.card_fin 3 |>.trans hext.symm)
  let sum₃ : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  let sum₉ : Fin 3 ⊕ Fin 6 ≃ Fin 9 := finSumFinEquiv
  let σ : Equiv.Perm (Fin 9) := sum₉.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 3)) sum₃.symm).trans
      (((Equiv.sumAssoc (Fin 3) (Fin 3) (Fin 3)).symm).trans
        ((Equiv.sumCongr
          ((Equiv.sumCongr rows cols).trans (Equiv.sumCompl (· ∈ R))) outside).trans
          (Equiv.sumCompl (· ∈ A)))))
  have hrow (a : A) (ha : a ∈ R) : ∃ r, a.val = orientedRow σ r := by
    let r := rows.symm ⟨a, ha⟩
    have h : sum₉.symm (r.castAdd 6) = Sum.inl r := finSumFinEquiv_symm_apply_castAdd r
    have hr : rows r = ⟨a, ha⟩ := rows.apply_symm_apply _
    exact ⟨r, by simp [orientedRow, σ, h, hr]⟩
  have hcol (a : A) (ha : a ∉ R) : ∃ s, a.val = orientedCol σ s := by
    let s := cols.symm ⟨a, ha⟩
    have h₉ : sum₉.symm (Fin.natAdd 3 (s.castAdd 3)) = Sum.inr (s.castAdd 3) :=
      finSumFinEquiv_symm_apply_natAdd (s.castAdd 3)
    have h₆ : sum₃.symm (s.castAdd 3) = Sum.inl s := finSumFinEquiv_symm_apply_castAdd s
    have hs : cols s = ⟨a, ha⟩ := cols.apply_symm_apply _
    exact ⟨s, by simp [orientedCol, σ, h₉, h₆, hs]⟩
  refine ⟨σ, fun i j hm => ?_⟩
  let a : A := ⟨i, mem_axes.mpr ⟨_, hm, by simp⟩⟩
  let c : A := ⟨j, mem_axes.mpr ⟨_, hm, by simp⟩⟩
  have hadj : (maskGraph F).Adj a c := by
    refine ⟨?_, hm⟩
    intro h
    have hij : i = j := congrArg Subtype.val h
    obtain ⟨x, _, y, _, _, hd, he⟩ := mem_minimumDisplacements.mp hm
    have hsize : (differingAxes x y).card = 2 := hd
    rw [he, hij] at hsize
    simp at hsize
  rcases (hG a c).mp hadj with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · obtain ⟨r, hr⟩ := hrow a ha
    obtain ⟨s, hs⟩ := hcol c hc
    exact Or.inl ⟨r, s, hr, hs⟩
  · obtain ⟨s, hs⟩ := hcol a ha
    obtain ⟨r, hr⟩ := hrow c hc
    exact Or.inr ⟨r, s, hs, hr⟩

private theorem orientedVertex_surjective (σ : Equiv.Perm (Fin 9)) (x : Q 9) :
    ∃ a c z, orientedVertex σ a c z = x := by
  refine ⟨fun i => x (σ (i.castAdd 6)),
    fun i => x (σ (Fin.natAdd 3 (i.castAdd 3))),
    fun i => x (σ (Fin.natAdd 3 (Fin.natAdd 3 i))), ?_⟩
  funext k
  obtain ⟨k, rfl⟩ := σ.surjective k
  simp only [orientedVertex, Equiv.symm_apply_apply, SixAxisGridSignedCompression.vertex]
  refine Fin.addCases (m := 3) (n := 6) (fun i => ?_) (fun j => ?_) k
  · simp
  · rw [Fin.append_right]
    refine Fin.addCases (m := 3) (n := 3) (fun i => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
    · rw [Fin.append_right]

private theorem blockParity_anti_flip :
    ∀ (a : Q 3) (i : Fin 3), blockParity (anti (flip a i)) = blockParity a := by decide

private theorem anti_flip_ne : ∀ (a : Q 3) (i : Fin 3), a ≠ anti (flip a i) := by decide

open Classical in
/-- For a nine-mask contact family on six axes, one coordinate permutation works
for every contact on the chosen parity. At each contact the same two parity
slices, aligned by the six-axis antipode, form a three-by-three rectangle. -/
theorem nine_masks_on_six_axes_force_contact_rectangles
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 6)
    (hmask : (minimumDisplacements C D b 2).card = 9) :
    ∃ σ : Equiv.Perm (Fin 9),
      ∀ x ∈ C, ∀ y ∈ D, parity x = b → hammingDist x y = 2 →
        ∃ (a c z : Q 3) (i j : Fin 3) (R S : Set (Q 3)),
          x = orientedVertex σ a c z ∧
          y = orientedVertex σ (flip a i) (flip c j) z ∧
          R.ncard = 3 ∧ S.ncard = 3 ∧
          leftLayer σ C z (blockParity a) (blockParity c) = R ×ˢ S ∧
          alignedLayer σ D z (blockParity a) (blockParity c) = R ×ˢ S := by
  obtain ⟨R, hR, hG⟩ := nine_masks_on_six_axes_bipartite (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD haxes hmask
  obtain ⟨σ, hσ⟩ := orient_mask_graph (C := C) (D := D) (b := b) haxes hR hG
  have hC (i : Fin 9) : ∃ f : Q 9 → ℝ,
      (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f x = 0) := by
    let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by
      dsimp only [w]
      split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  have hD := exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
    (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) b
  refine ⟨σ, fun x hx y hy hp hd => ?_⟩
  have hdiff : (differingAxes x y).card = 2 := hd
  obtain ⟨k, l, _, hkl⟩ := Finset.card_eq_two.mp hdiff
  have hm : ({k, l} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 :=
    mem_minimumDisplacements.mpr ⟨x, hx, y, hy, hp, hd, hkl⟩
  obtain ⟨i, j, hij⟩ :
      ∃ i j, differingAxes x y = {orientedRow σ i, orientedCol σ j} := by
    rcases hσ k l hm with ⟨i, j, hk, hl⟩ | ⟨i, j, hk, hl⟩
    · exact ⟨i, j, by simpa only [hk, hl] using hkl⟩
    · exact ⟨i, j, by simpa only [hk, hl, Finset.pair_comm] using hkl⟩
  have hyflip : y = flip (flip x (orientedRow σ i)) (orientedCol σ j) := by
    apply differingAxes_right_inj
    rw [hij]
    simpa only [List.foldl_cons, List.foldl_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_empty] using
      (differingAxes_foldl_flip [orientedRow σ i, orientedCol σ j]
        (by simp [row_col_ne]) x).symm
  obtain ⟨a, c, z, rfl⟩ := orientedVertex_surjective σ x
  rw [flip_row, flip_col] at hyflip
  let L := leftLayer σ C z (blockParity a) (blockParity c)
  have ha : (a, c) ∈ L := ⟨rfl, rfl, hx⟩
  have hy' : (anti (flip a i), anti (flip c j)) ∈
      alignedLayer σ D z (blockParity a) (blockParity c) := by
    refine ⟨blockParity_anti_flip a i, blockParity_anti_flip c j, ?_⟩
    have invol : ∀ u : Q 3, anti (anti u) = u := by
      intro u
      funext t
      exact Bool.not_not _
    simpa only [invol, ← hyflip] using hy
  obtain ⟨he, hprod⟩ := aligned_layers_eq_product hC hD hsep hσ ha hy' hp
    (anti_flip_ne a i) (anti_flip_ne c j)
  obtain ⟨hrows, hcols⟩ := aligned_layer_three_by_three hC hD hsep hσ ha hy' hp
    (anti_flip_ne a i) (anti_flip_ne c j) hrC hbC
  exact ⟨a, c, z, i, j, Prod.fst '' L, Prod.snd '' L, rfl, hyflip, hrows, hcols,
    hprod, he.symm.trans hprod⟩

#print axioms nine_masks_on_six_axes_force_contact_rectangles

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33AlignedLayer

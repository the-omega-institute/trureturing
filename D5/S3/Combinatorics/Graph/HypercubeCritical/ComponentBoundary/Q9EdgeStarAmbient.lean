/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EdgeStarAmbient
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EdgeStarAmbient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: none
   digest: Opposite defects on two masks at a cubic edge force degree four. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourFaceDefect
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport

/-! Opposite projected-parity witnesses in the rooted five-face of a cubic edge. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient

section FourFaceTranslation

open BalancedCriticalSpectrum (Q)
open Q4FaceCapacity
open scoped BigOperators
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private def translate {n : ℕ} (v : Q n) : Q n ≃ Q n where
  toFun x j := x j + v j
  invFun x j := x j + v j
  left_inv x := by
    funext j
    change (x j + v j) + v j = x j
    cases x j <;> cases v j <;> rfl
  right_inv x := by
    funext j
    change (x j + v j) + v j = x j
    cases x j <;> cases v j <;> rfl

private theorem parity_translate {n : ℕ} (v x : Q n) :
    cubeParity (translate v x) = cubeParity x + cubeParity v :=
  Finset.sum_add_distrib

private theorem translate_lift (a : Fin 4) (v : Q 4) (ε : Bool) (x : Q 3) :
    translate v (lift a ε x) = lift a (ε + v a) (translate (project a v) x) := by
  funext j
  refine Fin.succAboveCases a ?_ (fun k => ?_) j
  · change lift a ε x a + v a = _
    simp
  · change lift a ε x (a.succAbove k) + v (a.succAbove k) = _
    simp [translate, project, Fin.removeNth]

private theorem translate_antipode (v x : Q 3) :
    translate v (antipode x) = antipode (translate v x) := by
  funext j
  change (!x j) + v j = !(x j + v j)
  cases x j <;> cases v j <;> rfl

private theorem parity_eq_add (x b c : Bool) : x + c = b + c ↔ x = b := by
  cases x <;> cases b <;> cases c <;> decide

private theorem neg_add (b c : Bool) : Bool.not (b + c) = Bool.not b + c := by
  cases b <;> cases c <;> decide

private theorem finset_map_eq {α β : Type*} (e : α ≃ β)
    (S : Finset α) (T : Finset β) (h : ∀ x, x ∈ S ↔ e x ∈ T) :
    S.map e.toEmbedding = T := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Finset.mem_map_equiv]
  rw [e.symm_apply_apply]
  exact h x

open Classical in
/-- XOR translates paired columns and empty rows together, preserving the
deficiency classification with the translated projected parity. -/
private theorem deficiencyWitness_translate (A : Finset (Q 4)) (a : Fin 4) (b : Bool) (v : Q 4)
    (h : DeficiencyWitness A a b) :
    DeficiencyWitness (A.map (translate v).toEmbedding) a
      (b + cubeParity (project a v)) := by
  let B := A.map (translate v).toEmbedding
  let e := translate (project a v)
  let c := b + cubeParity (project a v)
  let P := doubleColumns A a b
  let T := emptyRows A a b
  let P' := doubleColumns B a c
  let T' := emptyRows B a c
  have hmem (x : Q 4) : translate v x ∈ B ↔ x ∈ A := by
    unfold B
    rw [Finset.mem_map_equiv]
    rw [Equiv.symm_apply_apply]
  have hpair (x : Q 3) :
      (lift a false (e x) ∈ B ∧ lift a true (e x) ∈ B) ↔
      (lift a false x ∈ A ∧ lift a true x ∈ A) := by
    have hf := hmem (lift a false x)
    have ht := hmem (lift a true x)
    rw [translate_lift] at hf ht
    cases hv : v a
    · rw [hv] at hf ht
      exact and_congr hf ht
    · rw [hv] at hf ht
      exact ((and_congr ht hf).trans and_comm)
  have hempty (x : Q 3) :
      (lift a false (e x) ∉ B ∧ lift a true (e x) ∉ B) ↔
      (lift a false x ∉ A ∧ lift a true x ∉ A) := by
    have hf := not_congr (hmem (lift a false x))
    have ht := not_congr (hmem (lift a true x))
    simp only [translate_lift] at hf ht
    cases hv : v a
    · rw [hv] at hf ht
      exact and_congr hf ht
    · rw [hv] at hf ht
      exact ((and_congr ht hf).trans and_comm)
  have hPm (x : Q 3) : x ∈ P ↔ e x ∈ P' := by
    simp only [P, P', doubleColumns, parityClass, Finset.mem_filter,
      Finset.mem_univ, true_and, hpair, c]
    change _ ↔ (cubeParity (translate (project a v) x) = _ ∧ _)
    rw [parity_translate, parity_eq_add]
  have hTm (x : Q 3) : x ∈ T ↔ e x ∈ T' := by
    simp only [T, T', emptyRows, parityClass, Finset.mem_filter,
      Finset.mem_univ, true_and, hempty, c]
    change _ ↔ (cubeParity (translate (project a v) x) = _ ∧ _)
    rw [parity_translate, neg_add, parity_eq_add]
  have hPc : P'.card = P.card := by rw [← finset_map_eq e P P' hPm, Finset.card_map]
  have hTc : T'.card = T.card := by rw [← finset_map_eq e T T' hTm, Finset.card_map]
  have outsideP (x : Q 3) (hx : x ∈ parityClass b \ P) :
      e x ∈ parityClass c \ P' := by
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨?_, fun hq => hn ((hPm x).mpr hq)⟩
    simp only [parityClass, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    change cubeParity (translate (project a v) x) = b + cubeParity (project a v)
    rw [parity_translate, hp]
  have outsideT (x : Q 3) (hx : x ∈ parityClass (!b) \ T) :
      e x ∈ parityClass (!c) \ T' := by
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨?_, fun hq => hn ((hTm x).mpr hq)⟩
    simp only [parityClass, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    change cubeParity (translate (project a v) x) = !(b + cubeParity (project a v))
    rw [parity_translate, hp, neg_add]
  change T.card < P.card ∨
    (P.card = 1 ∧ T.card = 1 ∧ ∃ x ∈ P, antipode x ∈ T) ∨
    (P.card = 3 ∧ T.card = 3 ∧
      ∃ x ∈ parityClass b \ P, antipode x ∈ parityClass (!b) \ T) at h
  change T'.card < P'.card ∨
    (P'.card = 1 ∧ T'.card = 1 ∧ ∃ x ∈ P', antipode x ∈ T') ∨
    (P'.card = 3 ∧ T'.card = 3 ∧
      ∃ x ∈ parityClass c \ P', antipode x ∈ parityClass (!c) \ T')
  rw [hPc, hTc]
  rcases h with hlt | ⟨hp, ht, x, hx, hm⟩ | ⟨hp, ht, x, hx, hm⟩
  · exact Or.inl hlt
  · refine Or.inr (Or.inl ⟨hp, ht, e x, (hPm x).mp hx, ?_⟩)
    exact translate_antipode (project a v) x ▸ (hTm _).mp hm
  · refine Or.inr (Or.inr ⟨hp, ht, e x, outsideP x hx, ?_⟩)
    exact translate_antipode (project a v) x ▸ outsideT _ hm

end FourFaceTranslation

section OppositeWitnesses

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q4FaceCapacity

/-- Two forced empty rows and a forbidden column in the four-column deficiency
test force all other columns to be paired and the matched row to be occupied. -/
private theorem deficiency_forces_three {α : Type*} [DecidableEq α]
    (C P T R : Finset α) (mate : α → α) (q : α)
    (hC : C.card = 4) (hPC : P ⊆ C) (hqC : q ∈ C) (hqP : q ∉ P)
    (hRT : R ⊆ T) (hR : R.card = 2) (hqR : mate q ∉ R)
    (hdef : T.card < P.card ∨ (P.card = 1 ∧ T.card = 1) ∨
      (P.card = 3 ∧ T.card = 3 ∧ ∃ x ∈ C \ P, mate x ∉ T)) :
    P = C.erase q ∧ mate q ∉ T := by
  have hsub : P ⊆ C.erase q := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hqP (h ▸ hx), hPC hx⟩
  have herase : (C.erase q).card = 3 := by
    rw [Finset.card_erase_of_mem hqC, hC]
  have hp := Finset.card_le_card hsub
  have ht := Finset.card_le_card hRT
  have hfill (h : P.card = 3) : P = C.erase q :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rcases hdef with hlt | ⟨_, hone⟩ | ⟨hthree, _, x, hx, hxt⟩
  · have hr : R = T := Finset.eq_of_subset_of_card_le hRT (by omega)
    exact ⟨hfill (by omega), hr ▸ hqR⟩
  · omega
  · have hP := hfill hthree
    have hxq : x = q := by
      have ⟨hxC, hxP⟩ := Finset.mem_sdiff.mp hx
      by_contra hne
      exact hxP (hP ▸ Finset.mem_erase.mpr ⟨hne, hxC⟩)
    exact ⟨hP, hxq ▸ hxt⟩

private def zero (n : ℕ) : Q n := fun _ => false
private def unit {n : ℕ} (j : Fin n) : Q n := flip (zero n) j

/-- Insert the main-axis bit before the four transverse coordinates. -/
private def headLift (a : Bool) (z : Q 4) : Q 5 :=
  Fin.insertNth (α := fun _ => Bool) 0 a z

/-- The main-axis edge and one leaf in each transverse direction. -/
private def edgeStar (s : Fin 4 → Bool) : Finset (Q 5) :=
  {headLift false (zero 4), headLift true (zero 4)} ∪
    Finset.univ.image (fun j => headLift (s j) (unit j))

private abbrev fill (r : Fin 4) (ε : Bool) (z : Q 4) : Q 5 :=
  Fin.insertNth (α := fun _ => Bool) r.succ ε z

private def transverseSlice (D : Finset (Q 5)) (r : Fin 4) (ε : Bool) : Finset (Q 4) :=
  Finset.univ.filter (fun z => fill r ε z ∈ D)

/-- A four-face deficiency witness whose column parity and omitted bit have odd sum. -/
def OppositeWitness (D : Finset (Q 5)) (r : Fin 4) : Prop :=
  ∃ ε : Bool, DeficiencyWitness (transverseSlice D r ε) 0 (!ε)

def BalancedLeaves (s : Fin 4 → Bool) : Prop :=
  (Finset.univ.filter (fun j => s j = false)).card = 2

def Separated (s : Fin 4 → Bool) (D : Finset (Q 5)) : Prop :=
  ∀ x ∈ edgeStar s, ∀ y ∈ D, x ≠ y ∧ ¬ (hypercube 5).Adj x y

private theorem mem_slice {D : Finset (Q 5)} {r : Fin 4} {ε : Bool} {z : Q 4} :
    z ∈ transverseSlice D r ε ↔ fill r ε z ∈ D := by
  simp [transverseSlice]

private theorem endpoint_mem (s : Fin 4 → Bool) (a : Bool) :
    headLift a (zero 4) ∈ edgeStar s := by
  cases a <;> simp [edgeStar]

private theorem leaf_mem (s : Fin 4 → Bool) (j : Fin 4) :
    headLift (s j) (unit j) ∈ edgeStar s := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

private theorem flip_not_mem {s : Fin 4 → Bool} {D : Finset (Q 5)}
    (hsep : Separated s D) {x : Q 5} (hx : x ∈ edgeStar s) (i : Fin 5) :
    flip x i ∉ D :=
  fun hy => (hsep x hx _ hy).2 (flip_adj x i)

private theorem fill_adj (r : Fin 4) (ε : Bool) {x y : Q 4}
    (h : (hypercube 4).Adj x y) : (hypercube 5).Adj (fill r ε x) (fill r ε y) := by
  obtain ⟨j, rfl⟩ := adjacent_exists_flip h
  have he : flip (fill r ε x) (r.succ.succAbove j) = fill r ε (flip x j) := by
    simpa only [BalancedCriticalSpectrum.flip, fill, Fin.insertNth_apply_succAbove] using
      (Fin.insertNth_update (α := fun _ => Bool) r.succ ε j (!x j) x).symm
  rw [← he]
  exact flip_adj _ _

private def slicedStar (u : Fin 3 → Bool) : Finset (Q 4) :=
  {lift 0 false (zero 3), lift 0 true (zero 3)} ∪
    Finset.univ.image (fun j => lift 0 (u j) (unit j))

private def forcedRows (s : Fin 4 → Bool) (r : Fin 4) : Finset (Q 3) :=
  (Finset.univ.filter fun j : Fin 3 => s (r.succAbove j) ≠ s r).image unit

-- These checks use only the four leaf bits and the omitted coordinate.
private theorem leaf_counts :
    ∀ (s : Fin 4 → Bool) (r : Fin 4), BalancedLeaves s →
      (∃ j k : Fin 3, s (r.succAbove j) ≠ s (r.succAbove k)) ∧
      (forcedRows s r).card = 2 := by
  unfold BalancedLeaves
  decide +kernel

private theorem slicedStar_defect :
    ∀ u : Fin 3 → Bool, DeficiencyWitness (slicedStar u) 0 false := by
  unfold DeficiencyWitness
  decide +kernel

private theorem slicedStar_subcubic :
    ∀ u : Fin 3 → Bool, (∃ j k, u j ≠ u k) →
      ∀ z : Q 4, z ∈ slicedStar u →
        (Finset.univ.filter (fun i =>
          BalancedCriticalSpectrum.flip z i ∈ slicedStar u)).card ≤ 3 := by
  decide +kernel

private theorem fill_zero_side :
    (∀ (r : Fin 4) (a : Bool),
      fill r false (lift 0 a (zero 3)) = headLift a (zero 4)) ∧
    (∀ (r : Fin 4) (a : Bool) (j : Fin 3),
      fill r false (lift 0 a (unit j)) = headLift a (unit (r.succAbove j))) := by
  decide +kernel

private theorem zero_side_impossible {s : Fin 4 → Bool} {D : Finset (Q 5)}
    (hs : BalancedLeaves s) (hsep : Separated s D) (r : Fin 4)
    (hw : DeficiencyWitness (transverseSlice D r false) 0 true) : False := by
  let u : Fin 3 → Bool := fun j => s (r.succAbove j)
  have hstar : ∀ x ∈ slicedStar u, fill r false x ∈ edgeStar s := by
    intro x hx
    rcases Finset.mem_union.mp hx with he | hl
    · rcases Finset.mem_insert.mp he with rfl | he
      · rw [fill_zero_side.1]
        exact endpoint_mem s false
      · have he' := Finset.mem_singleton.mp he
        subst x
        rw [fill_zero_side.1]
        exact endpoint_mem s true
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
      rw [fill_zero_side.2]
      exact leaf_mem s (r.succAbove j)
  have hsub : transverseSlice D r false ⊆ exterior (slicedStar u) := by
    intro y hy
    have hyD := mem_slice.mp hy
    apply mem_exterior.mpr
    refine ⟨fun hyS => (hsep _ (hstar y hyS) _ hyD).1 rfl, ?_⟩
    intro x hx hadj
    exact (hsep _ (hstar x hx) _ hyD).2 (fill_adj r false hadj.symm)
  have hdeg : ∀ z ∈ slicedStar u, (directions (slicedStar u) z).card ≤ 3 := by
    intro z hz
    simpa only [directions] using slicedStar_subcubic u (leaf_counts s r hs).1 z hz
  have hcap := exterior_card_le_three (slicedStar u) 0 false hdeg (slicedStar_defect u)
  exact (by decide : ¬ 5 ≤ 3)
    ((five_le_card_of_deficiencyWitness hw).trans ((Finset.card_le_card hsub).trans hcap))

/-- The transverse antipode of the anchor edge. -/
private def top : Q 4 := fun _ => true

private theorem fill_one_side :
    (∀ (r : Fin 4) (a : Bool),
      fill r true (lift 0 a (zero 3)) = headLift a (unit r)) ∧
    (∀ (r : Fin 4) (a : Bool) (j : Fin 3),
      fill r true (lift 0 a (unit j)) =
        flip (headLift a (unit r)) (r.succAbove j).succ ∧
      fill r true (lift 0 a (unit j)) =
        flip (headLift a (unit (r.succAbove j))) r.succ) ∧
    (∀ (r : Fin 4) (a : Bool),
      fill r true (lift 0 a (antipode (zero 3))) = headLift a top) ∧
    (∀ (r : Fin 4) (a : Bool) (j : Fin 3),
      fill r true (lift 0 a (antipode (unit j))) =
        flip (headLift a top) (r.succAbove j).succ) := by
  decide +kernel

private theorem flip_head_leaf :
    ∀ (j : Fin 4) (a : Bool),
      flip (headLift a (unit j)) 0 = headLift (!a) (unit j) := by
  decide +kernel

private theorem parity_facts :
    (parityClass false).card = 4 ∧
    zero 3 ∈ parityClass false ∧
    antipode (zero 3) ∈ parityClass true ∧
    ∀ j : Fin 3, unit j ∈ parityClass true ∧
      antipode (unit j) ∈ (parityClass false).erase (zero 3) ∧
      unit j ≠ antipode (zero 3) := by
  decide +kernel

private theorem one_side_forces {s : Fin 4 → Bool} {D : Finset (Q 5)}
    (hs : BalancedLeaves s) (hsep : Separated s D) (r : Fin 4)
    (hw : DeficiencyWitness (transverseSlice D r true) 0 false) :
    (∃ a : Bool, headLift a top ∈ D) ∧
      ∀ (j : Fin 4), j ≠ r → ∀ a : Bool, flip (headLift a top) j.succ ∈ D := by
  let A := transverseSlice D r true
  let P := doubleColumns A 0 false
  let T := emptyRows A 0 false
  have hPC : P ⊆ parityClass false := fun _ hx => (Finset.mem_filter.mp hx).1
  have hblocked (a : Bool) : lift 0 a (zero 3) ∉ A := by
    intro ha
    have hD := mem_slice.mp ha
    rw [fill_one_side.1] at hD
    by_cases h : a = s r
    · subst a
      exact (hsep _ (leaf_mem s r) _ hD).1 rfl
    · rw [Bool.eq_not_of_ne h, ← flip_head_leaf] at hD
      exact flip_not_mem hsep (leaf_mem s r) 0 hD
  have hqP : zero 3 ∉ P := fun hx => hblocked false (Finset.mem_filter.mp hx).2.1
  have hRT : forcedRows s r ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hdiff := (Finset.mem_filter.mp hj).2
    have hrow (a : Bool) : lift 0 a (unit j) ∉ A := by
      intro ha
      have hD := mem_slice.mp ha
      by_cases ha' : a = s r
      · rw [(fill_one_side.2.1 r a j).1, ha'] at hD
        exact flip_not_mem hsep (leaf_mem s r) _ hD
      · have hj' : a = s (r.succAbove j) :=
          (Bool.eq_not_of_ne ha').trans (Bool.eq_not_of_ne hdiff).symm
        rw [(fill_one_side.2.1 r a j).2, hj'] at hD
        exact flip_not_mem hsep (leaf_mem s (r.succAbove j)) _ hD
    exact Finset.mem_filter.mpr
      ⟨(parity_facts.2.2.2 j).1, hrow false, hrow true⟩
  have hqR : antipode (zero 3) ∉ forcedRows s r := by
    intro hx
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hx
    exact (parity_facts.2.2.2 j).2.2 he
  have hdef : T.card < P.card ∨ (P.card = 1 ∧ T.card = 1) ∨
      (P.card = 3 ∧ T.card = 3 ∧
        ∃ x ∈ parityClass false \ P, antipode x ∉ T) := by
    unfold DeficiencyWitness at hw
    rcases hw with h | ⟨hp, ht, _⟩ | ⟨hp, ht, x, hx, hxt⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hp, ht⟩)
    · exact Or.inr (Or.inr ⟨hp, ht, x, hx, (Finset.mem_sdiff.mp hxt).2⟩)
  obtain ⟨hP, hT⟩ := deficiency_forces_three _ P T _ antipode _ parity_facts.1 hPC
    parity_facts.2.1 hqP hRT (leaf_counts s r hs).2 hqR hdef
  constructor
  · have hocc : ∃ a : Bool, lift 0 a (antipode (zero 3)) ∈ A := by
      by_cases hf : lift 0 false (antipode (zero 3)) ∈ A
      · exact ⟨false, hf⟩
      by_cases ht : lift 0 true (antipode (zero 3)) ∈ A
      · exact ⟨true, ht⟩
      exact (hT (Finset.mem_filter.mpr ⟨parity_facts.2.2.1, hf, ht⟩)).elim
    obtain ⟨a, ha⟩ := hocc
    exact ⟨a, fill_one_side.2.2.1 r a ▸ mem_slice.mp ha⟩
  · intro j hj a
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    have hk : antipode (unit k) ∈ P := hP ▸ (parity_facts.2.2.2 k).2.1
    have ha : lift 0 a (antipode (unit k)) ∈ A := by
      have h := (Finset.mem_filter.mp hk).2
      cases a
      · exact h.1
      · exact h.2
    exact fill_one_side.2.2.2 r a k ▸ mem_slice.mp ha

private theorem oppositeWitness_forces {s : Fin 4 → Bool} {D : Finset (Q 5)}
    (hs : BalancedLeaves s) (hsep : Separated s D) (r : Fin 4)
    (hw : OppositeWitness D r) :
    (∃ a : Bool, headLift a top ∈ D) ∧
      ∀ (j : Fin 4), j ≠ r → ∀ a : Bool, flip (headLift a top) j.succ ∈ D := by
  obtain ⟨ε, hε⟩ := hw
  cases ε
  · exact (zero_side_impossible hs hsep r hε).elim
  · exact one_side_forces hs hsep r hε

private def leafSide (j : Fin 4) : Bool := decide (2 ≤ j.val)

/-- Combining two witnesses may force four neighbors across different supports. -/
private theorem mixed_witness_forces_four {s : Fin 4 → Bool} {D E : Finset (Q 5)}
    (hs : BalancedLeaves s) (hsepD : Separated s D) (hsepE : Separated s E)
    {r t : Fin 4} (hne : r ≠ t) (hr : OppositeWitness D r) (ht : OppositeWitness E t) :
    ∃ x ∈ D, ∀ j : Fin 4,
      flip x j.succ ∈ D ∨ flip x j.succ ∈ E := by
  obtain ⟨⟨a, ha⟩, hnr⟩ := oppositeWitness_forces hs hsepD r hr
  have hnt := (oppositeWitness_forces hs hsepE t ht).2
  refine ⟨headLift a top, ha, fun j => ?_⟩
  by_cases hj : j = r
  · exact Or.inr (hnt j (hj.trans_ne hne) a)
  · exact Or.inl (hnr j hj a)

end OppositeWitnesses

section RootedFiveFace

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open BalancedCubeComponentBoundary (directions mem_directions)
open private CubeCoordinateFace.lift CubeCoordinateFace.lift_flip
  CubeCoordinateFace.adj_lift_iff CubeCoordinateFace.lift_active
  CubeCoordinateFace.lift_inactive from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport

private def rootBits (axes : Fin 5 ↪ Fin 9) (root : Q 9) : Q 5 :=
  fun j => root (axes j)

private abbrev addRoot (axes : Fin 5 ↪ Fin 9) (root : Q 9) (x : Q 5) : Q 5 :=
  translate (rootBits axes root) x

/-- The ordered five-face through the root, with the root as its zero vertex. -/
private def basedLift (axes : Fin 5 ↪ Fin 9) (root : Q 9) (x : Q 5) : Q 9 :=
  CubeCoordinateFace.lift axes root (addRoot axes root x)

private theorem addRoot_flip (axes : Fin 5 ↪ Fin 9) (root : Q 9) (x : Q 5) (j : Fin 5) :
    addRoot axes root (BalancedCriticalSpectrum.flip x j) =
      BalancedCriticalSpectrum.flip (addRoot axes root x) j := by
  funext k
  by_cases hk : k = j
  · subst k
    simp only [addRoot, translate, rootBits, Equiv.coe_fn_mk,
      BalancedCriticalSpectrum.flip_apply_same]
    cases x j <;> cases root (axes j) <;> rfl
  · simp [addRoot, translate, rootBits, BalancedCriticalSpectrum.flip, hk]

private theorem basedLift_flip (axes : Fin 5 ↪ Fin 9) (root : Q 9) (x : Q 5) (j : Fin 5) :
    basedLift axes root (BalancedCriticalSpectrum.flip x j) =
      BalancedCriticalSpectrum.flip (basedLift axes root x) (axes j) := by
  unfold basedLift
  rw [addRoot_flip, CubeCoordinateFace.lift_flip]

private theorem addRoot_adj (axes : Fin 5 ↪ Fin 9) (root : Q 9) {x y : Q 5}
    (hxy : (hypercube 5).Adj x y) :
    (hypercube 5).Adj (addRoot axes root x) (addRoot axes root y) := by
  obtain ⟨j, rfl⟩ := BalancedCubeGirth.adjacent_exists_flip hxy
  rw [addRoot_flip]
  exact BalancedCriticalSpectrum.flip_adj _ _

open Classical in
/-- The part of the selected support lying in the rooted five-face. -/
private def localSupport (axes : Fin 5 ↪ Fin 9) (root : Q 9) (D : Finset (Q 9)) : Finset (Q 5) :=
  Finset.univ.filter fun x => basedLift axes root x ∈ D

@[simp] private theorem mem_localSupport (axes : Fin 5 ↪ Fin 9) (root : Q 9)
    (D : Finset (Q 9)) (x : Q 5) :
    x ∈ localSupport axes root D ↔ basedLift axes root x ∈ D := by
  classical
  simp [localSupport]

/-- Two different masks with opposite-parity witnesses near the same edge
force a point of the ambient selected set to have four selected neighbors.
The two witnesses can belong to separate components. -/
private theorem two_masks_force_ambient_degree_four
    (axes : Fin 5 ↪ Fin 9) (root : Q 9) (s : Fin 4 → Bool)
    (U C D E : Finset (Q 9)) (hs : BalancedLeaves s)
    (hstar : ∀ x ∈ edgeStar s, basedLift axes root x ∈ C)
    (hD : D ⊆ U) (hE : E ⊆ U)
    (hsepD : ∀ a ∈ C, ∀ b ∈ D, a ≠ b ∧ ¬ (hypercube 9).Adj a b)
    (hsepE : ∀ a ∈ C, ∀ b ∈ E, a ≠ b ∧ ¬ (hypercube 9).Adj a b)
    {r t : Fin 4} (hne : r ≠ t)
    (hr : OppositeWitness (localSupport axes root D) r)
    (ht : OppositeWitness (localSupport axes root E) t) :
    ∃ x ∈ U, 4 ≤ (directions U x).card := by
  have separated (F : Finset (Q 9))
      (hf : ∀ a ∈ C, ∀ b ∈ F, a ≠ b ∧ ¬ (hypercube 9).Adj a b) :
      Separated s (localSupport axes root F) := by
    intro a ha b hb
    obtain ⟨hne, hna⟩ := hf _ (hstar a ha) _ ((mem_localSupport axes root F b).mp hb)
    refine ⟨fun hab => hne (congrArg (basedLift axes root) hab), ?_⟩
    intro hab
    exact hna ((CubeCoordinateFace.adj_lift_iff axes root _ _).mpr (addRoot_adj axes root hab))
  obtain ⟨x, hx, hN⟩ := mixed_witness_forces_four
    hs (separated D hsepD) (separated E hsepE) hne hr ht
  let y := basedLift axes root x
  refine ⟨y, hD ((mem_localSupport axes root D x).mp hx), ?_⟩
  calc
    4 = (Finset.univ : Finset (Fin 4)).card := by simp
    _ ≤ (directions U y).card := by
      apply Finset.card_le_card_of_injOn (fun j : Fin 4 => axes j.succ)
      · intro j _
        change axes j.succ ∈ directions U (basedLift axes root x)
        rw [mem_directions, ← basedLift_flip]
        rcases hN j with hj | hj
        · exact hD ((mem_localSupport axes root D _).mp hj)
        · exact hE ((mem_localSupport axes root E _).mp hj)
      · exact (axes.injective.comp (Fin.succ_injective 4)).injOn

private theorem lift_zero (axes : Fin 5 ↪ Fin 9) (root : Q 9) :
    basedLift axes root (fun _ => false) = root := by
  funext j
  by_cases h : ∃ k, axes k = j
  · obtain ⟨k, rfl⟩ := h
    unfold basedLift
    rw [CubeCoordinateFace.lift_active]
    change false + root (axes k) = root (axes k)
    cases root (axes k) <;> rfl
  · exact CubeCoordinateFace.lift_inactive axes root _ h

private theorem leaf_words :
    headLift false (fun _ => false) = (fun _ => false) ∧
    headLift true (fun _ => false) =
      BalancedCriticalSpectrum.flip (fun _ => false) 0 ∧
    ∀ j : Fin 4, headLift (leafSide j)
        (BalancedCriticalSpectrum.flip (fun _ => false) j) =
      BalancedCriticalSpectrum.flip
        (if leafSide j then BalancedCriticalSpectrum.flip (fun _ => false) 0
          else fun _ => false) j.succ := by
  decide +kernel

/-- The two ends of a selected edge of a Huang-balanced cubic support determine
four distinct transverse directions. They form the balanced anchor star in
a rooted five-face. -/
private theorem exists_based_star (C : Finset (Q 9)) (hbal : BalancedCriticalSpectrum.IsBalanced C)
    (root : Q 9) (i : Fin 9) (hx : root ∈ C)
    (hy : BalancedCriticalSpectrum.flip root i ∈ C)
    (hxdeg : (directions C root).card = 3)
    (hydeg : (directions C (BalancedCriticalSpectrum.flip root i)).card = 3) :
    ∃ (axes : Fin 5 ↪ Fin 9) (s : Fin 4 → Bool), axes 0 = i ∧ BalancedLeaves s ∧
      ∀ x ∈ edgeStar s, basedLift axes root x ∈ C := by
  classical
  let y := BalancedCriticalSpectrum.flip root i
  let A := (directions C root).erase i
  let B := (directions C y).erase i
  have hiX : i ∈ directions C root := (mem_directions _ _ _).mpr hy
  have hiY : i ∈ directions C y := (mem_directions _ _ _).mpr (by
    simpa only [y, BalancedCriticalSpectrum.flip_flip] using hx)
  have hA : A.card = 2 := by
    rw [Finset.card_erase_of_mem hiX, hxdeg]
  have hB : B.card = 2 := by
    rw [Finset.card_erase_of_mem hiY, show (directions C y).card = 3 from hydeg]
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j hjA hjB
    obtain ⟨hji, hjX⟩ := Finset.mem_erase.mp hjA
    have hjY := (Finset.mem_erase.mp hjB).2
    exact BalancedCubeGirth.no_selected_square hbal hji.symm hx hy
      ((mem_directions _ _ _).mp hjX) ((mem_directions _ _ _).mp hjY)
  obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp hA
  obtain ⟨c, d, hcd, hCD⟩ := Finset.card_eq_two.mp hB
  have ha : a ∈ A := by rw [hAB]; simp
  have hb : b ∈ A := by rw [hAB]; simp
  have hc : c ∈ B := by rw [hCD]; simp
  have hd : d ∈ B := by rw [hCD]; simp
  have hai := (Finset.mem_erase.mp ha).1
  have hbi := (Finset.mem_erase.mp hb).1
  have hci := (Finset.mem_erase.mp hc).1
  have hdi := (Finset.mem_erase.mp hd).1
  have hac : a ≠ c := fun e => Finset.disjoint_left.mp hdis ha (e.symm ▸ hc)
  have had : a ≠ d := fun e => Finset.disjoint_left.mp hdis ha (e.symm ▸ hd)
  have hbc : b ≠ c := fun e => Finset.disjoint_left.mp hdis hb (e.symm ▸ hc)
  have hbd : b ≠ d := fun e => Finset.disjoint_left.mp hdis hb (e.symm ▸ hd)
  let axes : Fin 5 ↪ Fin 9 := ⟨![i, a, b, c, d], by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all⟩
  refine ⟨axes, leafSide, rfl, by unfold BalancedLeaves; decide +kernel, ?_⟩
  have hleaf0 := leaf_words.1
  have hleaf1 := leaf_words.2.1
  have hn (j : Fin 4) : basedLift axes root
      (headLift (leafSide j)
        (BalancedCriticalSpectrum.flip (fun _ => false) j)) ∈ C := by
    rw [leaf_words.2.2, basedLift_flip]
    have normal : basedLift axes root
        (if leafSide j then BalancedCriticalSpectrum.flip (fun _ => false) 0
          else fun _ => false) = if leafSide j then y else root := by
      by_cases h : leafSide j = true
      · simp only [h, ite_true, basedLift_flip, lift_zero]
        rfl
      · have h' : leafSide j = false := Bool.eq_false_iff.mpr h
        simp [h', lift_zero]
    rw [normal]
    have ha' := (mem_directions _ _ _).mp (Finset.mem_erase.mp ha).2
    have hb' := (mem_directions _ _ _).mp (Finset.mem_erase.mp hb).2
    have hc' := (mem_directions _ _ _).mp (Finset.mem_erase.mp hc).2
    have hd' := (mem_directions _ _ _).mp (Finset.mem_erase.mp hd).2
    fin_cases j <;> first | exact ha' | exact hb' | exact hc' | exact hd'
  intro x hstar
  rw [edgeStar] at hstar
  rcases Finset.mem_union.mp hstar with h | h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · change basedLift axes root (headLift false (fun _ => false)) ∈ C
      rw [hleaf0, lift_zero]
      exact hx
    · change basedLift axes root (headLift true (fun _ => false)) ∈ C
      rw [hleaf1, basedLift_flip, lift_zero]
      exact hy
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    exact hn j

end RootedFiveFace

section ParityTransport

open BalancedCriticalSpectrum (Q)
open Q4FaceCapacity (DeficiencyWitness project)
open scoped BigOperators
open private CubeCoordinateFace.lift from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

/-- Express the selection in the five active coordinates without translating their origin. -/
private def literalSupport (axes : Fin 5 ↪ Fin 9) (root : Q 9) (D : Finset (Q 9)) : Finset (Q 5) :=
  Finset.univ.filter fun x => CubeCoordinateFace.lift axes root x ∈ D

private def faceMask (r : Fin 4) (v : Q 5) : Q 4 :=
  Fin.removeNth (α := fun _ => Bool) r.succ v

private theorem translate_fill (r : Fin 4) (v : Q 5) (ε : Bool) (x : Q 4) :
    translate v (fill r ε x) = fill r (ε + v r.succ) (translate (faceMask r v) x) := by
  funext j
  refine Fin.succAboveCases r.succ ?_ (fun k => ?_) j
  · change fill r ε x r.succ + v r.succ = _
    simp [fill]
  · change fill r ε x (r.succ.succAbove k) + v (r.succ.succAbove k) = _
    simp [fill, translate, faceMask, Fin.removeNth]

private theorem skip_main (r : Fin 4) (j : Fin 3) :
    r.succ.succAbove j.succ = (r.succAbove j).succ := by
  fin_cases r <;> fin_cases j <;> decide +kernel

private theorem parity_faceMask (r : Fin 4) (v : Q 5) :
    (∑ j : Fin 4, v j.succ) = v r.succ + cubeParity (project 0 (faceMask r v)) := by
  rw [Fin.sum_univ_succAbove _ r]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change v (r.succAbove j).succ = v (r.succ.succAbove j.succ)
  rw [skip_main]

open Classical in
private theorem slice_image (axes : Fin 5 ↪ Fin 9) (root : Q 9) (D : Finset (Q 9))
    (r : Fin 4) (ε : Bool) :
    transverseSlice (localSupport axes root D) r (ε + rootBits axes root r.succ) =
      (transverseSlice (literalSupport axes root D) r ε).map
        (translate (faceMask r (rootBits axes root))).toEmbedding := by
  let v := rootBits axes root
  let e := translate (faceMask r v)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Finset.mem_map_equiv]
  change e x ∈ transverseSlice (localSupport axes root D) r (ε + v r.succ) ↔
    e.symm (e x) ∈ transverseSlice (literalSupport axes root D) r ε
  rw [e.symm_apply_apply]
  unfold transverseSlice
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_localSupport]
  unfold literalSupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold basedLift
  have hw : fill r (ε + v r.succ) (e x) = translate v (fill r ε x) :=
    (translate_fill r v ε x).symm
  rw [hw]
  have he : addRoot axes root (translate v (fill r ε x)) = fill r ε x :=
    (translate v).left_inv _
  rw [he]

/-- A literal defect with projected parity opposite to the root's becomes an
opposite witness in the coordinates based at the root. -/
private theorem oppositeWitness_of_literal (axes : Fin 5 ↪ Fin 9) (root : Q 9)
    (D : Finset (Q 9)) (r : Fin 4) (ε b : Bool)
    (hpar : b + ε ≠ ∑ j : Fin 4, root (axes j.succ))
    (h : DeficiencyWitness (transverseSlice (literalSupport axes root D) r ε) 0 b) :
    OppositeWitness (localSupport axes root D) r := by
  let v := rootBits axes root
  let p := cubeParity (project 0 (faceMask r v))
  have hs : (∑ j : Fin 4, root (axes j.succ)) = v r.succ + p :=
    parity_faceMask r v
  have hnew : b + p = Bool.not (ε + v r.succ) := by
    rw [hs] at hpar
    generalize h₁ : v r.succ = f at hpar ⊢
    generalize h₂ : p = g at hpar ⊢
    revert hpar
    cases b <;> cases ε <;> cases f <;> cases g <;> decide
  refine ⟨ε + v r.succ, ?_⟩
  rw [slice_image axes root D r ε, ← hnew]
  exact deficiencyWitness_translate _ _ _ _ h

end ParityTransport

section AmbientWitnesses

open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCubeComponentBoundary (directions)
open Q9ThreeAxisBlock (active)
open Q9ThreeAxisBoundaryTransport (columnParity)
open scoped BigOperators
open CoordinateHalves.Q9ThreeAxisCapacityTransport (faceSupport)
open private CubeCoordinateFace.lift CubeCoordinateFace.lift_active CubeCoordinateFace.lift_inactive
  CoordinateHalves.Q9ThreeAxisCapacityTransport.fourEmbedding
  CoordinateHalves.Q9ThreeAxisCapacityTransport.liftFour_eq
  Q9ThreeAxisBoundaryTransport.frozenParity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport

def remainingAxes (axes : Fin 5 ↪ Fin 9) (r : Fin 4) : Fin 3 ↪ Fin 9 :=
  ⟨fun j => axes (r.succ.succAbove j.succ),
    axes.injective.comp ((Fin.succAbove_right_injective (p := r.succ)).comp (Fin.succ_injective 3))⟩

private theorem main_not_active (axes : Fin 5 ↪ Fin 9) (r : Fin 4) :
    axes 0 ∉ active (remainingAxes axes r) := by
  rw [active, Finset.mem_map]
  rintro ⟨j, _, hj⟩
  have hh := axes.injective hj
  have hzero := Fin.succ_succAbove_zero r
  have h := Fin.succAbove_right_injective (p := r.succ) (hh.trans hzero.symm)
  exact Fin.succ_ne_zero j h

private theorem four_embedding (axes : Fin 5 ↪ Fin 9) (r : Fin 4) (j : Fin 4) :
    CoordinateHalves.Q9ThreeAxisCapacityTransport.fourEmbedding
      (remainingAxes axes r) (axes 0) (main_not_active axes r) j =
      axes (r.succ.succAbove j) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · change axes 0 = axes (r.succ.succAbove 0)
    rw [Fin.succ_succAbove_zero]
  · rfl

open Classical in
/-- A four-face through a point agreeing with the five-face's frozen bits is
the corresponding coordinate slice of the same five-face. -/
private theorem faceSupport_eq_slice (axes : Fin 5 ↪ Fin 9) (root z : Q 9) (D : Finset (Q 9))
    (r : Fin 4) (hag : ∀ j, (¬ ∃ k, axes k = j) → z j = root j) :
    faceSupport D (remainingAxes axes r) z (axes 0) =
      transverseSlice (literalSupport axes root D) r (z (axes r.succ)) := by
  let f := CoordinateHalves.Q9ThreeAxisCapacityTransport.fourEmbedding
    (remainingAxes axes r) (axes 0) (main_not_active axes r)
  have hLift (x : Q 4) :
      CubeCoordinateFace.lift f z x =
        CubeCoordinateFace.lift axes root (fill r (z (axes r.succ)) x) := by
    funext j
    by_cases h : ∃ k, axes k = j
    · obtain ⟨k, rfl⟩ := h
      rw [CubeCoordinateFace.lift_active]
      refine Fin.succAboveCases r.succ ?_ (fun t => ?_) k
      · have hf : ¬ ∃ t, f t = axes r.succ := by
          rintro ⟨t, ht⟩
          have hEq := axes.injective ((four_embedding axes r t).symm.trans ht)
          exact Fin.succAbove_ne r.succ t hEq
        rw [CubeCoordinateFace.lift_inactive _ _ _ hf]
        simp [fill]
      · rw [← four_embedding axes r t]
        change CubeCoordinateFace.lift f z x (f t) = _
        simp [CubeCoordinateFace.lift_active, fill]
    · have hf : ¬ ∃ t, f t = j := by
        rintro ⟨t, ht⟩
        exact h ⟨_, (four_embedding axes r t).symm.trans ht⟩
      rw [CubeCoordinateFace.lift_inactive _ _ _ hf,
        CubeCoordinateFace.lift_inactive _ _ _ h, hag j h]
  ext x
  unfold faceSupport transverseSlice literalSupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [CoordinateHalves.Q9ThreeAxisCapacityTransport.liftFour_eq _ _ _
    (main_not_active axes r)]
  exact Iff.of_eq (congrArg (fun q => q ∈ D) (hLift x))

private theorem bool_zero_sum (a b : Bool) (h : a + b = false) : a = b := by
  revert h
  cases a <;> cases b <;> decide

private theorem bool_cancel_middle (a b p c : Bool)
    (h : a + p = c + (a + b)) : p = c + b := by
  revert h
  cases a <;> cases b <;> cases p <;> cases c <;> decide

private theorem column_with_frozen_bit (axes : Fin 5 ↪ Fin 9) (z : Q 9) (r : Fin 4)
    (hz : (∑ j : Fin 9, z j) = false) :
    columnParity (remainingAxes axes r) z false + z (axes r.succ) =
      ∑ j : Fin 4, z (axes j.succ) := by
  let a := remainingAxes axes r
  have hsplit := Finset.sum_sdiff (f := z) (Finset.subset_univ (active a))
  have hf : (∑ j ∈ Finset.univ \ active a, z j) = ∑ j ∈ active a, z j :=
    bool_zero_sum _ _ (hsplit.trans hz)
  have hp : (∑ j ∈ active a, z j) = ∑ j : Fin 3, z (axes (r.succAbove j).succ) := by
    rw [active, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    change z (axes (r.succ.succAbove j.succ)) = _
    rw [skip_main]
  have hcol : columnParity a z false = ∑ j ∈ active a, z j := by
    unfold columnParity Q9ThreeAxisBoundaryTransport.frozenParity
    rw [show (false : Bool) = 0 from rfl, zero_add, hf]
  rw [hcol, hp, Fin.sum_univ_succAbove (fun j : Fin 4 => z (axes j.succ)) r, add_comm]

private theorem projected_eq_split (axes : Fin 5 ↪ Fin 9) (z : Q 9) :
    (∑ j : Fin 8, z ((axes 0).succAbove j)) =
      (∑ j ∈ Finset.univ \ (Finset.univ.map axes), z j) +
        (∑ j : Fin 4, z (axes j.succ)) := by
  have hsplit := Finset.sum_sdiff (f := z) (Finset.subset_univ (Finset.univ.map axes))
  rw [Finset.sum_map, Fin.sum_univ_succAbove (fun j => z (axes j)) 0] at hsplit
  rw [Fin.sum_univ_succAbove z (axes 0)] at hsplit
  simpa only [Fin.succAbove_zero_apply] using bool_cancel_middle _ _ _ _ hsplit.symm

private theorem projected_ne_of_agree (axes : Fin 5 ↪ Fin 9) (root z : Q 9)
    (hag : ∀ j, (¬ ∃ k, axes k = j) → z j = root j)
    (hp : (∑ j : Fin 8, z ((axes 0).succAbove j)) ≠
      ∑ j : Fin 8, root ((axes 0).succAbove j)) :
    (∑ j : Fin 4, z (axes j.succ)) ≠ ∑ j : Fin 4, root (axes j.succ) := by
  have he : (∑ j ∈ Finset.univ \ Finset.univ.map axes, z j) =
      ∑ j ∈ Finset.univ \ Finset.univ.map axes, root j := by
    apply Finset.sum_congr rfl
    intro j hj
    refine hag j ?_
    rintro ⟨k, hk⟩
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, hk⟩)
  intro heq
  apply hp
  rw [projected_eq_split, projected_eq_split, he, heq]

/-- A witness from the boundary-kernel construction inside the edge's five-face
has the local opposite parity when its projected parity differs from the anchor. -/
private theorem oppositeWitness_of_ambient (axes : Fin 5 ↪ Fin 9) (root z : Q 9)
    (D : Finset (Q 9)) (r : Fin 4)
    (hag : ∀ j, (¬ ∃ k, axes k = j) → z j = root j)
    (hz : (∑ j : Fin 9, z j) = false)
    (hp : (∑ j : Fin 8, z ((axes 0).succAbove j)) ≠
      ∑ j : Fin 8, root ((axes 0).succAbove j))
    (h : Q4FaceCapacity.DeficiencyWitness
      (faceSupport D (remainingAxes axes r) z (axes 0)) 0
      (columnParity (remainingAxes axes r) z false)) :
    OppositeWitness (localSupport axes root D) r := by
  apply oppositeWitness_of_literal axes root D r (z (axes r.succ))
    (columnParity (remainingAxes axes r) z false)
  · rw [column_with_frozen_bit axes z r hz]
    exact projected_ne_of_agree axes root z hag hp
  · rw [← faceSupport_eq_slice axes root z D r hag]
    exact h

/-- A boundary-kernel witness inside the anchor five-face, using the
opposite projected parity from the root. -/
def HasOppositeFace (axes : Fin 5 ↪ Fin 9) (root : Q 9) (D : Finset (Q 9))
    (r : Fin 4) : Prop :=
  ∃ z : Q 9, (∀ j, (¬ ∃ k, axes k = j) → z j = root j) ∧
    (∑ j : Fin 9, z j) = false ∧
    (∑ j : Fin 8, z ((axes 0).succAbove j)) ≠
      (∑ j : Fin 8, root ((axes 0).succAbove j)) ∧
    Q4FaceCapacity.DeficiencyWitness
      (faceSupport D (remainingAxes axes r) z (axes 0)) 0
      (columnParity (remainingAxes axes r) z false)

/-- The five-face of a Huang-balanced edge with cubic endpoints admits at most
one omitted transverse axis with an opposite projected-parity witness in
subsets of a common subcubic support separated from the anchor support. -/
theorem edge_has_at_most_one_opposite_mask (U C : Finset (Q 9))
    (hU : ∀ x ∈ U, (directions U x).card ≤ 3)
    (hbal : BalancedCriticalSpectrum.IsBalanced C)
    (root : Q 9) (i : Fin 9) (hx : root ∈ C)
    (hy : BalancedCriticalSpectrum.flip root i ∈ C)
    (hxdeg : (directions C root).card = 3)
    (hydeg : (directions C (BalancedCriticalSpectrum.flip root i)).card = 3) :
    ∃ axes : Fin 5 ↪ Fin 9, axes 0 = i ∧
      ∀ (D E : Finset (Q 9)), D ⊆ U → E ⊆ U →
      (∀ a ∈ C, ∀ b ∈ D, a ≠ b ∧ ¬ (hypercube 9).Adj a b) →
      (∀ a ∈ C, ∀ b ∈ E, a ≠ b ∧ ¬ (hypercube 9).Adj a b) →
      ∀ r t : Fin 4, HasOppositeFace axes root D r →
        HasOppositeFace axes root E t → r = t := by
  obtain ⟨axes, s, hi, hs, hstar⟩ :=
    exists_based_star C hbal root i hx hy hxdeg hydeg
  refine ⟨axes, hi, fun D E hD hE hsepD hsepE r t hr ht => ?_⟩
  obtain ⟨z, hzagree, hzeven, hzpar, hz⟩ := hr
  obtain ⟨w, hwagree, hweven, hwpar, hw⟩ := ht
  by_contra hne
  obtain ⟨x, hxU, hfour⟩ := two_masks_force_ambient_degree_four
    axes root s U C D E hs hstar hD hE hsepD hsepE hne
    (oppositeWitness_of_ambient axes root z D r hzagree hzeven hzpar hz)
    (oppositeWitness_of_ambient axes root w E t hwagree hweven hwpar hw)
  exact (by decide : ¬ 4 ≤ 3) (hfour.trans (hU x hxU))

end AmbientWitnesses

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient

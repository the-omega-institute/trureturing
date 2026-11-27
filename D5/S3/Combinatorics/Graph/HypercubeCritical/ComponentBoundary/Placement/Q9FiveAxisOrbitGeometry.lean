/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Shared midpoint counts and weighted contact translations justify the finite tableau directly from the separated supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitCover
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizeNineMasks
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedMidpointFiveAxes

/-! Occupancy semantics of the finite five-axis tableau. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec cubeBitVec_xor_single)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (origin)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements RidgeContact)
open Q9FiveAxisMissingContact (Geometry firstFiveAxes missingMask rightRoot)
open Q9FiveAxisOrbitCover
open Q9TightDistanceTwoNormalized (normalize_minimumDisplacements)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open private normalize_flip_axis normalize_directions parity_normalize_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized
open private parity_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open Q9TightDistanceTwoCNF (support)
open Q9DegreeThreeContactOrbit (translated_contact_of_three_partners)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9NormalizeNineMasks (exists_normalized_nine_mask_contact)
open private contact_mask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DegreeThreeContactOrbit
open private row_contact from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

def family : Finset (Finset (Fin 9)) := firstFiveAxes.powersetCard 2 \ {missingMask}

private def axis (i : Axis) : Fin 9 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

private theorem axis_injective : Function.Injective axis := fun _ _ h =>
  Fin.ext (congrArg (fun j : Fin 9 => j.val) h)

private theorem step_cube (w : Word) (i : Axis) :
    cubeBitVec 9 (step w i) = flip (cubeBitVec 9 w) (axis i) :=
  cubeBitVec_xor_single w (axis i)

private def decode (n : Nat) : Word := evenWords[n % 16]!

private def occupancy (C D : Finset (Q 9)) : Sat.Valuation := fun n =>
  cubeBitVec 9 (decode n) ∈ support C D (decide (16 ≤ n))

private theorem occupancy_at (C D : Finset (Q 9)) (s : Bool) {w : Word} (hw : w ∈ evenWords) :
    occupancy C D (atom s w) ↔ cubeBitVec 9 w ∈ support C D s := by
  have h : (evenWords.all fun x => decide (∀ t : Bool,
    decode (atom t x) = x ∧ decide (16 ≤ atom t x) = t)) = true := by decide +kernel
  obtain ⟨hword, hside⟩ := (of_decide_eq_true (List.all_eq_true.mp h w hw)) s
  rw [occupancy, hword, hside]

set_option maxHeartbeats 0 in
private theorem even_data (w : Word) (hw : w ∈ evenWords) :
    parity (cubeBitVec 9 w) = false ∧ (w ^^^ 6) ∈ evenWords ∧
      ∀ i j : Axis, step (step w i) j ∈ evenWords := by
  have h : (evenWords.all fun x => decide
      (parity (cubeBitVec 9 x) = false ∧ (x ^^^ 6) ∈ evenWords ∧
        ∀ i j : Axis, step (step x i) j ∈ evenWords)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem mem_evenWords_iff : ∀ w : Word,
    w ∈ evenWords ↔ w.toNat < 32 ∧ parity (cubeBitVec 9 w) = false := by
  decide +kernel

private theorem odd_step (w : Word) (hw : w ∈ oddWords) (i : Axis) :
    step w i ∈ evenWords := by
  have h : (oddWords.all fun x => decide (∀ k : Axis, step x k ∈ evenWords)) = true := by
    decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp h w hw)) i

private theorem mask_subset {T : Finset (Fin 9)} (hT : T ∈ family) : T ⊆ firstFiveAxes :=
  (mem_powersetCard.mp (mem_sdiff.mp hT).1).1

private theorem active_iff : ∀ k : Fin 9, k ∈ firstFiveAxes ↔ k.val < 5 := by decide +kernel

private theorem partner_axes : ∀ (i : Axis) (k : Fin 9), (i = 1 ∨ i = 2) →
    ({axis i, k} : Finset (Fin 9)) ∈ family → k = 0 ∨ k = 3 ∨ k = 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem partner_triple :
    ∀ j p q : Axis, ({j, p, q} : Finset Axis) = {0, 3, 4} →
      (∀ i : Axis, (i = 1 ∨ i = 2) → i ≠ j) ∧ p ≠ q ∧
        ∀ k : Fin 9, (k = 0 ∨ k = 3 ∨ k = 4) → k = axis j ∨ k = axis p ∨ k = axis q := by
  decide +kernel

/-- The number of directions at each side of a shared even contact. -/
def MidpointCounts (C D : Finset (Q 9)) : Prop :=
  ∀ (z : Q 9) (i j : Fin 9), flip z i ∈ C → flip z j ∈ D →
    parity (flip z i) = false →
    (directions C z).card = 2 ∧ (directions D z).card = 2

/-- The two endpoint memberships after translating by the other partners. -/
def ContactTranslations (C D : Finset (Q 9)) : Prop :=
  ∀ (x : Q 9) (i j p q : Axis), parity x = false → (i = 1 ∨ i = 2) →
    ({j, p, q} : Finset Axis) = {0, 3, 4} →
    x ∈ C → flip (flip x (axis i)) (axis j) ∈ D →
    flip (flip x (axis p)) (axis q) ∈ C ∧
      flip (flip (flip (flip x (axis i)) (axis j)) (axis p)) (axis q) ∈ D

/-- A shared midpoint has two neighbors on each side, all on the five active axes. -/
private theorem shared_directions {C D : Finset (Q 9)}
    (h : Geometry C D) (hfamily : minimumDisplacements C D false 2 = family)
    (hcounts : MidpointCounts C D)
    {z : Q 9} {i j : Fin 9} (hi : flip z i ∈ C) (hj : flip z j ∈ D)
    (hp : parity (flip z i) = false) :
    ((directions C z).card = 2 ∧ directions C z ⊆ firstFiveAxes) ∧
    ((directions D z).card = 2 ∧ directions D z ⊆ firstFiveAxes) := by
  have hmask : ∀ T ∈ minimumDisplacements C D false 2, T ⊆ firstFiveAxes := by
    rw [hfamily]
    exact fun _ => mask_subset
  obtain ⟨hC, hD⟩ := hcounts z i j hi hj hp
  have hpar (k : Fin 9) : parity (flip z k) = false := by
    simpa only [parity_flip] using hp
  have hne {a b : Fin 9} (ha : flip z a ∈ C) (hb : flip z b ∈ D) : a ≠ b := by
    rintro rfl
    simpa using h.separated _ ha _ hb
  refine ⟨⟨hC, ?_⟩, ⟨hD, ?_⟩⟩
  · intro k hk
    have hCk := (mem_directions C z k).mp hk
    exact hmask _ (row_contact hCk hj (hne hCk hj) (hpar k)) (by simp)
  · intro k hk
    have hDk := (mem_directions D z k).mp hk
    exact hmask _ (row_contact hi hDk (hne hi hDk) hp) (by simp)

private theorem cube_root_zero : cubeBitVec 9 (0 : Word) = origin := by
  funext i; fin_cases i <;> decide

private theorem cube_root_three : cubeBitVec 9 (3 : Word) = rightRoot := by
  funext i; fin_cases i <;> decide

open Classical in
/-- Interpret all five row types using occupancy in the normalized supports. -/
theorem tableau_of_normalized {C D : Finset (Q 9)}
    (h : Geometry C D) (hfamily : minimumDisplacements C D false 2 = family)
    (hcounts : MidpointCounts C D) (htranslate : ContactTranslations C D) :
    Tableau (occupancy C D) := by
  let v := occupancy C D
  have vat (s : Bool) {w : Word} (hw : w ∈ evenWords) :
      v (atom s w) ↔ cubeBitVec 9 w ∈ support C D s := occupancy_at C D s hw
  have vstep (s : Bool) {z : Word} (hz : z ∈ oddWords) (i : Axis) :
      v (atom s (step z i)) ↔ axis i ∈ directions (support C D s) (cubeBitVec 9 z) := by
    rw [vat s (odd_step z hz i), step_cube, mem_directions]
  have vshared (s : Bool) {z : Word} (hz : z ∈ oddWords) (j i : Axis)
      (hj : v (atom (!s) (step z j))) (hi : v (atom s (step z i))) :
      (directions (support C D s) (cubeBitVec 9 z)).card = 2 ∧
        directions (support C D s) (cubeBitVec 9 z) ⊆ firstFiveAxes := by
    have pe (k : Axis) : parity (flip (cubeBitVec 9 z) (axis k)) = false := by
      rw [← step_cube]
      exact (even_data _ (odd_step z hz k)).1
    cases s with
    | false =>
      exact (shared_directions h hfamily hcounts
        ((mem_directions _ _ _).mp ((vstep false hz i).mp hi))
        ((mem_directions _ _ _).mp ((vstep true hz j).mp hj)) (pe i)).1
    | true =>
      exact (shared_directions h hfamily hcounts
        ((mem_directions _ _ _).mp ((vstep false hz j).mp hj))
        ((mem_directions _ _ _).mp ((vstep true hz i).mp hi)) (pe j)).2
  intro r hv
  cases r with
  | root s =>
    cases s
    · intro hn
      exact hn ((vat false (by decide : (0 : Word) ∈ evenWords)).mpr
        (by change cubeBitVec 9 (0 : Word) ∈ C; rw [cube_root_zero]; exact h.left_root))
    · intro hn
      exact hn ((vat true (by decide : (3 : Word) ∈ evenWords)).mpr
        (by change cubeBitVec 9 (3 : Word) ∈ D; rw [cube_root_three]; exact h.right_root))
  | separation w m =>
    obtain ⟨hw, hm⟩ := hv
    intro hx hy
    have hx' : cubeBitVec 9 w ∈ C := (vat false hw).mp hx
    rcases hm with rfl | rfl
    · change v (atom true (w ^^^ 0#9)) at hy
      have hy' : cubeBitVec 9 w ∈ D := (vat true hw).mp (by simpa only [BitVec.xor_zero] using hy)
      simpa using h.separated _ hx' _ hy'
    · have hy' : cubeBitVec 9 (w ^^^ 6) ∈ D := (vat true (even_data w hw).2.1).mp hy
      have he : w ^^^ (6 : Word) = step (step w 1) 2 := by
        simp only [step, BitVec.xor_assoc] <;> rfl
      rw [he, step_cube, step_cube] at hy'
      have hc : RidgeContact C D false [axis 1] (axis 2) (cubeBitVec 9 w) :=
        ⟨by decide, hx', (even_data w hw).1, hy'⟩
      have hm' := contact_mask hc
      rw [hfamily] at hm'
      exact (by decide : ({axis 1, axis 2} : Finset (Fin 9)) ∉ family) hm'
  | translate w i j p q s =>
    obtain ⟨hw, hi, htriple⟩ := hv
    let y := step (step w i) j
    have hy : y ∈ evenWords := (even_data w hw).2.2 i j
    intro hx hy' hn
    have hxC : cubeBitVec 9 w ∈ C := (vat false hw).mp hx
    have hyD : cubeBitVec 9 y ∈ D := (vat true hy).mp hy'
    obtain ⟨htC, htD⟩ :=
      htranslate (cubeBitVec 9 w) i j p q (even_data w hw).1 hi htriple hxC
        (by simpa only [y, step_cube] using hyD)
    cases s
    · exact hn ((vat false ((even_data w hw).2.2 p q)).mpr
        (by simpa [step_cube, support] using htC))
    · exact hn ((vat true ((even_data y hy).2.2 p q)).mpr
        (by simpa [y, step_cube, support] using htD))
  | upper z s j a b c =>
    obtain ⟨hz, hab, hbc⟩ := hv
    intro hj ha hb hc
    have hcard := (vshared s hz j a hj ha).1
    have hsub : ({axis a, axis b, axis c} : Finset (Fin 9)) ⊆
        directions (support C D s) (cubeBitVec 9 z) := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨(vstep s hz a).mp ha, (vstep s hz b).mp hb, (vstep s hz c).mp hc⟩
    have hcount := card_le_card hsub
    have hab' : axis a ≠ axis b := fun he => hab.ne (axis_injective he)
    have hac' : axis a ≠ axis c := fun he => (hab.trans hbc).ne (axis_injective he)
    have hbc' : axis b ≠ axis c := fun he => hbc.ne (axis_injective he)
    have hthree : ({axis a, axis b, axis c} : Finset (Fin 9)).card = 3 := by
      rw [card_insert_of_notMem (by simp [hab', hac']), card_pair hbc']
    omega
  | lower z s j i =>
    have hz : z ∈ oddWords := hv
    intro hj hi
    obtain ⟨hcard, hsub⟩ := vshared s hz j i hj hi
    obtain ⟨k, hk, hki⟩ := exists_mem_ne (by rw [hcard]; decide) (axis i)
    let l : Axis := ⟨k.val, (active_iff k).mp (hsub hk)⟩
    have hl : axis l = k := Fin.ext rfl
    have hli : l ≠ i := fun he => hki (hl.symm.trans (congrArg axis he))
    have hlmem : l ∈ otherAxes i := by
      have hall : ∀ t : Axis, t ∈ ([0, 1, 2, 3, 4] : List Axis) := by decide
      simp [otherAxes, hall, hli]
    apply satisfies_of_falsified
    intro hall
    have hpos := hall (pos s (step z l)) (List.mem_map.mpr ⟨l, hlmem, rfl⟩)
    apply hpos
    exact (vstep s hz l).mpr (hl.symm ▸ hk)

open Classical in
/-- The two actual occupancy subsets in the normalized layer agree with an
explicit pattern from an orbit of one of the six representatives. -/
theorem covers_normalized {C D : Finset (Q 9)}
    (h : Geometry C D) (hfamily : minimumDisplacements C D false 2 = family)
    (hcounts : MidpointCounts C D) (htranslate : ContactTranslations C D) :
    ∃ r ∈ representatives, ∃ p ∈ orbit r, ∀ (s : Bool) (w : Word), w ∈ evenWords →
      (cubeBitVec 9 w ∈ support C D s ↔ w ∈ p.on s) := by
  obtain ⟨r, hr, p, hp, hm⟩ := covers (tableau_of_normalized h hfamily hcounts htranslate)
  exact ⟨r, hr, p, hp, fun s w hw => (occupancy_at C D s hw).symm.trans (hm s w hw)⟩

private theorem flip_four (x : Q 9) (a b c d : Fin 9) :
    flip (flip (flip (flip x a) b) c) d = flip (flip (flip (flip x c) d) a) b := by
  rw [flip_comm (flip x a) b c, flip_comm x a c,
    flip_comm (flip (flip x c) a) b d, flip_comm (flip x c) a d]

open Classical in
/-- Pull the midpoint and weighted-contact hypotheses back to the actual
supports before applying their geometric theorems. The covering pattern is
read in the chosen normalized coordinates. -/
theorem covers_of_normalization {C D : Finset (Q 9)} {b : Bool}
    (σ : Equiv.Perm (Fin 9)) (o : Q 9) (ho : parity o = b)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hC : ∀ j : Fin 9, ∃ f : Q 9 → ℝ,
      (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f x = 0))
    (hD : ∃ g : Q 9 → ℝ, (∀ x, g x ≠ 0 ↔ x ∈ D ∧ parity x = b) ∧
      (∀ x ∉ D, weightedLinear (fun _ => 1) g x = 0)) :
    let e := normalize σ o
    let X := C.map e.toEmbedding
    let Y := D.map e.toEmbedding
    Geometry X Y → minimumDisplacements X Y false 2 = family →
      MidpointCounts X Y ∧ ContactTranslations X Y ∧
      ∃ r ∈ representatives, ∃ p ∈ orbit r, ∀ (s : Bool) (w : Word), w ∈ evenWords →
        (cubeBitVec 9 w ∈ support X Y s ↔ w ∈ p.on s) := by
  dsimp only
  intro hgeom hfamily
  let e := normalize σ o
  let X := C.map e.toEmbedding
  let Y := D.map e.toEmbedding
  change Geometry X Y at hgeom
  change minimumDisplacements X Y false 2 = family at hfamily
  have shift : b + parity o = false := by rw [ho]; cases b <;> rfl
  have memX (x : Q 9) : x ∈ X ↔ e.symm x ∈ C := mem_map_equiv
  have memY (x : Q 9) : x ∈ Y ↔ e.symm x ∈ D := mem_map_equiv
  have pullFlip (x : Q 9) (i : Fin 9) : e.symm (flip x i) = flip (e.symm x) (σ i) := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa only [show normalize σ o (e.symm x) = x from e.apply_symm_apply x] using
      (normalize_flip_axis σ o (e.symm x) i).symm
  have pullParity (x : Q 9) (hx : parity x = false) : parity (e.symm x) = b := by
    apply (parity_normalize_eq σ o (e.symm x) b).mp
    simpa only [shift, show normalize σ o (e.symm x) = x from e.apply_symm_apply x] using hx
  have pullCard (S : Finset (Q 9)) (z : Q 9) :
      (directions (S.map e.toEmbedding) z).card = (directions S (e.symm z)).card := by
    simpa only [card_map, show normalize σ o (e.symm z) = z from e.apply_symm_apply z] using
      congrArg Finset.card (normalize_directions σ o (e.symm z) S)
  have mapped_masks :
      (minimumDisplacements C D b 2).map (mapEmbedding σ.symm.toEmbedding).toEmbedding =
        family := by
    rw [← normalize_minimumDisplacements σ o C D b 2, shift]
    exact hfamily
  have maskMap {T : Finset (Fin 9)} (hT : T ∈ minimumDisplacements C D b 2) :
      T.map σ.symm.toEmbedding ∈ family := by
    rw [← mapped_masks]
    exact mem_map.mpr ⟨T, hT, rfl⟩
  have hmask : ∀ T ∈ minimumDisplacements C D b 2,
      T ⊆ firstFiveAxes.map σ.toEmbedding := by
    intro T hT k hk
    have hk' : σ.symm k ∈ T.map σ.symm.toEmbedding := mem_map.mpr ⟨k, hk, rfl⟩
    exact mem_map.mpr ⟨σ.symm k, mask_subset (maskMap hT) hk', σ.apply_symm_apply k⟩
  have hcounts : MidpointCounts X Y := by
    intro z i j hi hj hp
    have hi' := (memX _).mp hi
    have hj' := (memY _).mp hj
    have hp' := pullParity _ hp
    rw [pullFlip] at hi' hj' hp'
    have hcard : (firstFiveAxes.map σ.toEmbedding).card ≤ 5 := by rw [card_map]; decide
    obtain ⟨hleft, hright⟩ := Q9SharedMidpointFiveAxes.two_neighbors_each
      hcard hmask hsep hrC hrD hbC hbD hi' hj' hp'
    exact ⟨(pullCard C z).trans hleft, (pullCard D z).trans hright⟩
  have htranslate : ContactTranslations X Y := by
    intro x i j p q hxpar hi htriple hx hy
    obtain ⟨hij, hpq, hrest⟩ := partner_triple j p q htriple
    let a (k : Axis) := σ (axis k)
    have ha : Function.Injective a := σ.injective.comp axis_injective
    have hji : a j ≠ a i := fun he => hij i hi (ha he).symm
    have hy' := (memY _).mp hy
    rw [pullFlip, pullFlip] at hy'
    have contact : RidgeContact C D b [a i] (a j) (e.symm x) :=
      ⟨by simpa using hji, (memX _).mp hx, pullParity _ hxpar, hy'⟩
    have partners (k : Fin 9) (hk : ({a i, k} : Finset (Fin 9)) ∈
        minimumDisplacements C D b 2) : k = a j ∨ k = a p ∨ k = a q := by
      have hk' : ({axis i, σ.symm k} : Finset (Fin 9)) ∈ family := by
        simpa only [a, map_insert, map_singleton, Equiv.coe_toEmbedding,
          Equiv.symm_apply_apply] using maskMap hk
      rcases hrest _ (partner_axes i _ hi hk') with he | he | he
      · exact Or.inl (by simpa only [a, Equiv.apply_symm_apply] using congrArg σ he)
      · exact Or.inr (Or.inl (by simpa only [a, Equiv.apply_symm_apply] using congrArg σ he))
      · exact Or.inr (Or.inr (by simpa only [a, Equiv.apply_symm_apply] using congrArg σ he))
    obtain ⟨f, hf, hAf⟩ := hC (a j)
    obtain ⟨g, hg, hAg⟩ := hD
    have ht := translated_contact_of_three_partners
      (fun he => hpq (ha he)) hsep partners f g hf hg hAf hAg contact
    refine ⟨(memX _).mpr ?_, (memY _).mpr ?_⟩
    · rw [pullFlip, pullFlip]
      exact ht.2.1
    · rw [pullFlip, pullFlip, pullFlip, pullFlip]
      exact (flip_four (e.symm x) (a p) (a q) (a i) (a j)) ▸ ht.2.2.2
  exact ⟨hcounts, htranslate, covers_normalized hgeom hfamily hcounts htranslate⟩

open Classical in
/-- A pair with the five-axis one-edge-deleted contact family admits the rooted
normalization and its even contact layer agrees with one of the orbit patterns. -/
theorem exists_covered_normalization {C D : Finset (Q 9)} {b : Bool}
    {A : Finset (Fin 9)} (hA : A.card = 5)
    (hnine : (minimumDisplacements C D b 2).card = 9)
    (haxes : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    ∃ (o : Q 9) (σ : Equiv.Perm (Fin 9)),
      let e := normalize σ o
      let X := C.map e.toEmbedding
      let Y := D.map e.toEmbedding
      parity o = b ∧ Geometry X Y ∧ minimumDisplacements X Y false 2 = family ∧
        MidpointCounts X Y ∧ ContactTranslations X Y ∧
        ∃ r ∈ representatives, ∃ p ∈ orbit r, ∀ (s : Bool) (w : Word),
          w.toNat < 32 → parity (cubeBitVec 9 w) = false →
          (cubeBitVec 9 w ∈ support X Y s ↔ w ∈ p.on s) := by
  have hsubfamily : minimumDisplacements C D b 2 ⊆ A.powersetCard 2 := by
    intro T hT
    refine mem_powersetCard.mpr ⟨haxes T hT, ?_⟩
    obtain ⟨_, _, _, _, _, hdist, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hdist
  have hmissCard : (A.powersetCard 2 \ minimumDisplacements C D b 2).card = 1 := by
    rw [card_sdiff_of_subset hsubfamily, card_powersetCard, hA, hnine] <;> decide
  obtain ⟨P, hmissing⟩ := card_eq_one.mp hmissCard
  have hP : P ∈ A.powersetCard 2 := by
    have hm : P ∈ A.powersetCard 2 \ minimumDisplacements C D b 2 := by
      rw [hmissing]
      simp
    exact (mem_sdiff.mp hm).1
  have hfamily := (Finset.sdiff_sdiff_eq_self hsubfamily).symm
  rw [hmissing] at hfamily
  obtain ⟨o, σ, ho, hgeom, hnormalized⟩ :=
    exists_normalized_nine_mask_contact hA hP hfamily hsep hrC hrD hbC hbD
  have hleft (j : Fin 9) :=
    exists_both_parity_supported_of_signed_defect_singular
      C hrC hcC hbC (fun k => if k = j then 2 else 1)
      (fun k => by split <;> norm_num) (hdetC _) b
  have hright := exists_both_parity_supported_of_signed_defect_singular
    D hrD hcD hbD (fun _ => 1) (fun _ => by norm_num) (hdetD _) b
  obtain ⟨counts, translates, r, hr, p, hp, hmatch⟩ :=
    covers_of_normalization σ o ho hsep hrC hrD hbC hbD hleft hright hgeom hnormalized
  exact ⟨o, σ, ho, hgeom, hnormalized, counts, translates, r, hr, p, hp,
    fun s w hw hpw => hmatch s w ((mem_evenWords_iff w).mpr ⟨hw, hpw⟩)⟩

#print axioms exists_covered_normalization

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry

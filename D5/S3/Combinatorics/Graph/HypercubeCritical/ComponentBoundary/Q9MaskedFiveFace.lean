/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedFiveFace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedFiveFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A singular five-axis mask of one triple type forces an eleven-vertex normal form. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SingleTripleFiveCube
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! Coordinate transport for the five-axis Huang saturation obstruction. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedFiveFace

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open TwoBalancedComponents (componentFinset)
open Q9ComponentSaturation (componentDefect)
open Q9IsotropicHuang (flipSign flipSign_cast)
open Q9MaskedGram (maskWeight)
open Q9MaskedSpectrum (maskedGraph exists_positive_masked_component)
open HuangCubeCovariance (exists_edge_gauge)

private theorem balanced_pullback {D : Finset (Q 5)} {S : Finset (Q 9)}
    (F : Q 5 → Q 9) (a : Fin 5 ↪ Fin 9)
    (hflip : ∀ x i, F (flip x i) = flip (F x) (a i))
    (hmem : ∀ x ∈ D, F x ∈ S) (hb : IsBalanced S) : IsBalanced D := by
  obtain ⟨θ, hθ, he⟩ := exists_edge_gauge F a hflip
  obtain ⟨s, hs⟩ := hb
  refine ⟨fun x => θ x * s (F x), ?_, ?_⟩
  · intro x hx
    rcases sq_eq_one_iff.mp (hθ x) with h | h <;>
      rcases hs.1 _ (hmem x hx) with h' | h' <;> simp [h, h']
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    have hs' : (flipSign (a i) (F x) : ℝ) = s (F x) * s (F (flip x i)) := by
      have hyS := hmem _ hy
      rw [hflip] at hyS ⊢
      rw [flipSign_cast]
      exact hs.2 _ (hmem x hx) _ hyS (flip_adj _ _)
    calc
      _ = (flipSign i x : ℝ) := (flipSign_cast i x).symm
      _ = θ x ^ 2 * (flipSign i x : ℝ) * θ (flip x i) ^ 2 := by
        rw [hθ x, hθ (flip x i), one_mul, mul_one]
      _ = θ x * (flipSign (a i) (F x) : ℝ) * θ (flip x i) := by
        simp only [flipSign_cast, he x i]
        ring
      _ = _ := by rw [hs']; ring

open Classical in
/-- In a subcubic balanced actual component, a singular five-axis mask whose
full direction triples all equal one set has an eleven-vertex masked component.
Its two full-triple vertices differ by the two complementary coordinate flips,
and its support is the union of three four-edge paths between them. -/
theorem exists_eleven_vertex_masked_component (U : Finset (Q 9)) (b : Bool)
    (C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (I T : Finset (Fin 9)) (hI : I.card = 5)
    (hb : IsBalanced (componentFinset U C))
    (hdeg : ∀ x ∈ componentFinset U C, (directions (componentFinset U C) x).card ≤ 3)
    (ht : ∀ x ∈ componentFinset U C, (directions (componentFinset U C) x).card = 3 →
      directions (componentFinset U C) x ⊆ I → directions (componentFinset U C) x = T)
    (hdet : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ K : ((maskedGraph I).induce (componentFinset U C : Set (Q 9))).ConnectedComponent,
      Fintype.card K = 11 ∧
      ∃ a b : Fin 9, a ≠ b ∧ I \ T = {a, b} ∧
        ∃ x y : K, y.val.val = flip (flip x.val.val a) b ∧
          directions (componentFinset U C) x.val.val = T ∧
          directions (componentFinset U C) y.val.val = T ∧
          ∀ z : Q 9, (∃ w : K, z = w.val.val) ↔ z = x.val.val ∨ z = y.val.val ∨
            ∃ i ∈ T, z = flip x.val.val i ∨ z = flip (flip x.val.val i) a ∨
              z = flip y.val.val i := by
  classical
  let S := componentFinset U C
  let G := (maskedGraph I).induce (S : Set (Q 9))
  obtain ⟨K, f, hf⟩ := exists_positive_masked_component U b C I
    (Finset.card_pos.mp (by omega)) hb hdet
  obtain ⟨root, hroot⟩ := K.nonempty_supp
  let a : Fin 5 ↪ Fin 9 := (Finset.equivFinOfCardEq hI).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩
  have ha (i : Fin 5) : a i ∈ I := ((Finset.equivFinOfCardEq hI).symm i).property
  have ha' {j : Fin 9} (hj : j ∈ I) : ∃ i, a i = j := by
    refine ⟨Finset.equivFinOfCardEq hI ⟨j, hj⟩, ?_⟩
    exact congrArg Subtype.val ((Finset.equivFinOfCardEq hI).symm_apply_apply ⟨j, hj⟩)
  let restrictBits (x : Q 9) : Q 5 := fun i => x (a i)
  let F (x : Q 5) : Q 9 := Function.extend a x root.val
  have hF (x : Q 5) (i : Fin 5) : F x (a i) = x i := a.injective.extend_apply _ _ _
  have hFout (x : Q 5) {j : Fin 9} (hj : j ∉ I) : F x j = root.val j :=
    Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj (ha i))
  have hFinj : Function.Injective F := by
    intro x y he
    funext i
    rw [← hF x i, ← hF y i, he]
  have hflip (x : Q 5) (i : Fin 5) : F (flip x i) = flip (F x) (a i) := by
    funext j
    by_cases hj : j ∈ I
    · obtain ⟨k, rfl⟩ := ha' hj
      by_cases hk : k = i
      · subst k
        rw [hF, BalancedCriticalSpectrum.flip_apply_same, BalancedCriticalSpectrum.flip_apply_same, hF]
      · rw [hF]
        simp [BalancedCriticalSpectrum.flip, hk, a.injective.ne hk, hF]
    · rw [hFout _ hj]
      simp [BalancedCriticalSpectrum.flip, show j ≠ a i from fun h => hj (h ▸ ha i), hFout _ hj]
  have face (x : (S : Set (Q 9))) (hx : x ∈ K.supp) {j : Fin 9} (hj : j ∉ I) :
      x.val j = root.val j := by
    have fixed {w : (S : Set (Q 9))} (p : Relation.ReflTransGen G.Adj root w) :
        w.val j = root.val j := by
      induction p with
      | refl => rfl
      | @tail v w _ hadj ih =>
        obtain ⟨i, hi, he⟩ := (show (maskedGraph I).Adj v.val w.val from hadj)
        rw [← he]
        have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
        exact (Function.update_of_ne hji _ _).trans ih
    exact fixed ((SimpleGraph.reachable_iff_reflTransGen root x).mp
      (K.reachable_of_mem_supp hroot hx))
  have decode (x : K) : F (restrictBits x.val.val) = x.val.val := by
    funext j
    by_cases hj : j ∈ I
    · obtain ⟨i, rfl⟩ := ha' hj
      exact hF _ _
    · rw [hFout _ hj, face x.val x.property hj]
  let D := Finset.univ.image (fun x : K => restrictBits x.val.val)
  have encoder_inj : Function.Injective (fun x : K => restrictBits x.val.val) := by
    intro x y he
    change restrictBits x.val.val = restrictBits y.val.val at he
    apply Subtype.ext
    apply Subtype.ext
    rw [← decode x, ← decode y, he]
  have hD (x : Q 5) : x ∈ D ↔ ∃ y : K, F x = y.val.val := by
    simp only [D, Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_congr fun y => ⟨fun h => by rw [← h, decode], fun h => hFinj ((decode y).trans h.symm)⟩
  have hmem (x : Q 5) (hx : x ∈ D) : F x ∈ S := by
    obtain ⟨y, hy⟩ := (hD x).mp hx
    rw [hy]
    exact y.val.property
  have adj (x y : Q 5) : (hypercube 5).Adj x y ↔ (maskedGraph I).Adj (F x) (F y) := by
    constructor
    · intro h
      obtain ⟨i, rfl⟩ := adjacent_exists_flip h
      exact ⟨a i, ha i, (hflip x i).symm⟩
    · rintro ⟨i, hi, he⟩
      obtain ⟨j, rfl⟩ := ha' hi
      rw [← hflip] at he
      rw [← hFinj he]
      exact flip_adj x j
  let xK (x : (D : Set (Q 5))) : K :=
    ⟨⟨F x.val, hmem x.val x.property⟩, by
      obtain ⟨y, hy⟩ := (hD x.val).mp x.property
      exact (show (⟨F x.val, hmem x.val x.property⟩ : (S : Set (Q 9))) = y.val from Subtype.ext hy) ▸ y.property⟩
  let e : (D : Set (Q 5)) ≃ K := Equiv.ofBijective xK ⟨
    fun _ _ h => Subtype.ext (hFinj (congrArg (fun u : K => u.val.val) h)), by
      intro y
      let x := restrictBits y.val.val
      refine ⟨⟨x, (hD x).mpr ⟨y, decode y⟩⟩, Subtype.ext (Subtype.ext (decode y))⟩⟩
  let iso : ((hypercube 5).induce (D : Set (Q 5))) ≃g K.toSimpleGraph :=
    { toEquiv := e
      map_rel_iff' := fun {x y} => (adj x.val y.val).symm }
  have hc := iso.connected_iff.mpr K.connected_toSimpleGraph
  let maskD := Finset.univ.filter (fun i : Fin 5 => a i ∈ T)
  have hdirs (x : Q 5) (hx : x ∈ D) :
      (directions D x).map a = I ∩ directions S (F x) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_inter, mem_directions]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [← hflip]
      exact ⟨ha i, hmem _ hi⟩
    · rintro ⟨hj, hv⟩
      obtain ⟨i, rfl⟩ := ha' hj
      have hK : (⟨flip (F x) (a i), hv⟩ : (S : Set (Q 9))) ∈ K.supp :=
        K.mem_supp_of_adj_mem_supp (xK ⟨x, hx⟩).property (show G.Adj _ _ from ⟨a i, ha i, rfl⟩)
      exact ⟨i, (hD _).mpr ⟨⟨⟨_, hv⟩, hK⟩, hflip x i⟩, rfl⟩
  have hsub (x : Q 5) (hx : x ∈ D) : (directions D x).map a ⊆ directions S (F x) := by
    rw [hdirs x hx]
    exact Finset.inter_subset_right
  have hdeg' (x : Q 5) (hx : x ∈ D) : (directions D x).card ≤ 3 := by
    have h := Finset.card_le_card (hsub x hx)
    rw [Finset.card_map] at h
    exact h.trans (hdeg _ (hmem x hx))
  have hfull (x : Q 5) (hx : x ∈ D) (h3 : (directions D x).card = 3) :
      (directions D x).map a = directions S (F x) ∧ directions S (F x) = T := by
    have he := Finset.eq_of_subset_of_card_le (hsub x hx)
      (by rw [Finset.card_map, h3]; exact hdeg _ (hmem x hx))
    exact ⟨he, ht _ (hmem x hx) (by rw [← he, Finset.card_map, h3]) (by
      rw [← he, hdirs x hx]
      exact Finset.inter_subset_left)⟩
  have ht' (x : Q 5) (hx : x ∈ D) (h3 : (directions D x).card = 3) :
      directions D x = maskD := by
    obtain ⟨he, he'⟩ := hfull x hx h3
    ext i
    have hi : a i ∈ (directions D x).map a ↔ i ∈ directions D x := Finset.mem_map' a
    rw [he, he'] at hi
    simpa [maskD] using hi.symm
  let Femb : Q 5 ↪ Q 9 := ⟨F, hFinj⟩
  have hneighbors (x : Q 5) (hx : x ∈ D) :
      (D.filter ((hypercube 5).Adj x)).map Femb = S.filter ((maskedGraph I).Adj (F x)) := by
    ext z
    simp only [Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy, hadj⟩, rfl⟩
      exact ⟨hmem y hy, (adj x y).mp hadj⟩
    · rintro ⟨hz, hadj⟩
      have hzK : (⟨z, hz⟩ : (S : Set (Q 9))) ∈ K.supp :=
        K.mem_supp_of_adj_mem_supp (xK ⟨x, hx⟩).property (show G.Adj _ _ from hadj)
      let y : K := ⟨⟨z, hz⟩, hzK⟩
      refine ⟨restrictBits z, ⟨(hD _).mpr ⟨y, decode y⟩, (adj x _).mpr ?_⟩, decode y⟩
      rwa [decode y]
  have hrow (x : Q 5) (hx : x ∈ D) :
      (∑ y ∈ D.filter ((hypercube 5).Adj x), f (F y)) = Real.sqrt 5 * f (F x) := by
    have hr := (hf (xK ⟨x, hx⟩).val (xK ⟨x, hx⟩).property).2
    change (∑ y ∈ S.filter ((maskedGraph I).Adj (F x)), f y) = _ at hr
    rw [← hneighbors x hx, Finset.sum_map] at hr
    change (∑ y ∈ D.filter ((hypercube 5).Adj x), f (F y)) =
      Real.sqrt (I.card : ℝ) * f (F x) at hr
    simpa only [hI, Nat.cast_ofNat] using hr
  obtain ⟨u, j, k, hjk, hcompl, huT, hvT, hcard, hshape⟩ :=
    SingleTripleFiveCube.eleven_vertex_normal_form D maskD
    hc (balanced_pullback F a hflip hmem hb) hdeg' ht' (f ∘ F)
    (fun x hx => (hf (xK ⟨x, hx⟩).val (xK ⟨x, hx⟩).property).1) hrow
  let v := flip (flip u j) k
  have hu : u ∈ D := (hshape u).2 (Or.inl rfl)
  have hv : v ∈ D := (hshape v).2 (Or.inr (Or.inl rfl))
  have h3 : maskD.card = 3 := by
    have h := Finset.card_sdiff_of_subset (Finset.subset_univ maskD)
    rw [hcompl, Finset.card_pair hjk, Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨humap, huFull⟩ := hfull u hu (by rw [huT, h3])
  have hvFull := (hfull v hv (by rw [hvT, h3])).2
  have hmap : maskD.map a = T := by rw [← huT, humap, huFull]
  have hinactive (i : Fin 5) : a i ∉ T ↔ i = j ∨ i = k := by
    have hi := Finset.ext_iff.mp hcompl i
    simpa [maskD] using hi
  have hcompl' : I \ T = {a j, a k} := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hiT⟩
      obtain ⟨l, rfl⟩ := ha' hi
      simpa only [a.injective.eq_iff] using (hinactive l).1 hiT
    · rintro (rfl | rfl)
      · exact ⟨ha j, (hinactive j).2 (Or.inl rfl)⟩
      · exact ⟨ha k, (hinactive k).2 (Or.inr rfl)⟩
  refine ⟨K, ?_, a j, a k, a.injective.ne hjk, hcompl', xK ⟨u, hu⟩, xK ⟨v, hv⟩,
    ?_, huFull, hvFull, ?_⟩
  · simpa only [D, Finset.card_image_of_injective _ encoder_inj, Finset.card_univ] using hcard
  · change F (flip (flip u j) k) = flip (flip (F u) (a j)) (a k)
    rw [hflip, hflip]
  · intro z
    change (∃ w : K, z = w.val.val) ↔ z = F u ∨ z = F v ∨
      ∃ i ∈ T, z = flip (F u) i ∨ z = flip (flip (F u) i) (a j) ∨ z = flip (F v) i
    constructor
    · rintro ⟨w, rfl⟩
      have hw := (hD _).2 ⟨w, decode w⟩
      rw [← decode w]
      rcases (hshape _).1 hw with he | he | ⟨i, hi, he⟩
      · exact Or.inl (congrArg F he)
      · exact Or.inr (Or.inl (congrArg F he))
      · exact Or.inr (Or.inr ⟨a i, hmap ▸ Finset.mem_map_of_mem a hi, by
          simpa only [← hflip, hFinj.eq_iff] using he⟩)
    · rintro (rfl | rfl | ⟨i, hi, he⟩)
      · exact (hD u).1 hu
      · exact (hD v).1 hv
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp (hmap.symm ▸ hi)
        simp only [← hflip] at he
        rcases he with h | h | h
        · rw [h]
          exact (hD _).1 ((hshape _).2 (Or.inr (Or.inr ⟨l, hl, Or.inl rfl⟩)))
        · rw [h]
          exact (hD _).1 ((hshape _).2 (Or.inr (Or.inr ⟨l, hl, Or.inr (Or.inl rfl)⟩)))
        · rw [h]
          exact (hD _).1 ((hshape _).2 (Or.inr (Or.inr ⟨l, hl, Or.inr (Or.inr rfl)⟩)))

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedFiveFace.exists_eleven_vertex_masked_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_eleven_vertex_masked_component

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedFiveFace

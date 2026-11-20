/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TernaryFaceStars
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TernaryFaceStars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A ternary kernel word on one parity contains a three-axis face star. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis

/-! A ternary weighted kernel word restricts to a self-orthogonal word on each
three-axis face. Three support vertices on one parity then determine a star.
At total order 258 the two components and their complement support these stars
on a common parity. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TernaryFaceStars

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj flip_apply_same IsBalanced)
open Q9MixedBoundaryCollisions (Separated)
open Q9IsotropicParityTransfer (ParityVertices)
open private extendParity extendParity_apply extendParity_off weightedAction_extendParity
  supported_action_word_of_code exists_common_parity_of_integer_weights
  exists_complement_word_of_common_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open Q9IsotropicHuang (parity flipSign weightedAction weightedAction_image_eq_kernel)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private huangMatrix_symmetric cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private theorem parity_flip (x : Q 9) (i : Fin 9) : parity (flip x i) = !parity x :=
  (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x i))).symm

private theorem flip_apply_other (x : Q 9) {i j : Fin 9} (h : j ≠ i) :
    flip x i j = x j :=
  Function.update_of_ne h _ _

/-- The face through `z` with free coordinates `I`. -/
private def face (I : Finset (Fin 9)) (z : Q 9) : Finset (Q 9) := by
  classical
  exact Finset.univ.filter (fun x => ∀ j ∉ I, x j = z j)

private theorem mem_face {I : Finset (Fin 9)} {x z : Q 9} :
    x ∈ face I z ↔ ∀ j ∉ I, x j = z j := by
  classical
  simp [face]

private theorem flip_mem_face {I : Finset (Fin 9)} {z x : Q 9} {i : Fin 9} (hi : i ∈ I) :
    flip x i ∈ face I z ↔ x ∈ face I z := by
  have houtside : ∀ j ∉ I, flip x i j = x j :=
    fun j hj => flip_apply_other x (fun e => hj (e.symm ▸ hi))
  constructor <;> intro hx <;> apply mem_face.mpr <;> intro j hj
  · rw [← houtside j hj]
    exact mem_face.mp hx j hj
  · rw [houtside j hj]
    exact mem_face.mp hx j hj

private theorem face_card (I : Finset (Fin 9)) (z : Q 9) :
    (face I z).card = 2 ^ I.card := by
  classical
  let extend (u : I → Bool) (j : Fin 9) : Bool := if hj : j ∈ I then u ⟨j, hj⟩ else z j
  let e : (face I z : Type) ≃ (I → Bool) :=
    { toFun := fun x j => x.val j.val
      invFun := fun u => ⟨extend u, mem_face.mpr (fun j hj => by simp [extend, hj])⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext j
        by_cases hj : j ∈ I
        · simp [extend, hj]
        · simp [extend, hj, mem_face.mp x.property j hj]
      right_inv := by
        intro u
        funext j
        simp [extend, j.property] }
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] using Fintype.card_congr e

private theorem face_half_card {I : Finset (Fin 9)} (hI : I.card = 3) (z : Q 9) (p : Bool) :
    ((face I z).filter fun x => parity x = p).card = 4 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hswap : ((face I z).filter fun x => parity x = p).card =
      ((face I z).filter fun x => parity x ≠ p).card := by
    apply Finset.card_bij (fun x _ => flip x i)
    · intro x hx
      simp only [Finset.mem_filter, flip_mem_face hi, parity_flip] at hx ⊢
      exact ⟨hx.1, by simp [hx.2]⟩
    · intro x _ y _ hxy
      simpa only [BalancedCriticalSpectrum.flip_flip] using
        congrArg (fun u => BalancedCriticalSpectrum.flip u i) hxy
    · intro x hx
      simp only [Finset.mem_filter] at hx
      refine ⟨flip x i, Finset.mem_filter.mpr ⟨(flip_mem_face hi).mpr hx.1, ?_⟩,
        BalancedCriticalSpectrum.flip_flip x i⟩
      rw [parity_flip]
      exact Bool.not_eq_iff.mpr hx.2
  have htotal := Finset.card_filter_add_card_filter_not (s := face I z) (fun x => parity x = p)
  rw [face_card, hI, ← hswap] at htotal
  omega

/-- Flipping each of the three free coordinates gives the opposite-parity antipode. -/
private theorem exists_face_antipode {I : Finset (Fin 9)} (hI : I.card = 3)
    {z y : Q 9} (hy : y ∈ face I z) :
    ∃ x ∈ face I z, parity x = !parity y ∧ ∀ i ∈ I, x i = !y i := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hI
  have ha : a ∈ ({a, b, c} : Finset (Fin 9)) := by simp
  have hb : b ∈ ({a, b, c} : Finset (Fin 9)) := by simp
  have hc : c ∈ ({a, b, c} : Finset (Fin 9)) := by simp
  refine ⟨flip (flip (flip y a) b) c,
    (flip_mem_face hc).mpr ((flip_mem_face hb).mpr ((flip_mem_face ha).mpr hy)), ?_, ?_⟩
  · simp only [parity_flip, Bool.not_not]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rw [flip_apply_other _ hac, flip_apply_other _ hab, flip_apply_same]
    · rw [flip_apply_other _ hbc, flip_apply_same, flip_apply_other _ hab.symm]
    · rw [flip_apply_same, flip_apply_other _ hbc.symm, flip_apply_other _ hac.symm]

/-- Three occupied vertices of a parity half of a three-face form a star. -/
private theorem exists_face_star {I : Finset (Fin 9)} (hI : I.card = 3) {z : Q 9} {p : Bool}
    {T : Finset (Q 9)} (hT : T ⊆ (face I z).filter (fun x => parity x = p))
    (hcard : T.card = 3) :
    ∃ x : Q 9, parity x = !p ∧ ∀ i ∈ I, flip x i ∈ T := by
  let P := (face I z).filter (fun x => parity x = p)
  have hmissing : (P \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hT, face_half_card hI, hcard]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hmissing
  have hyP : y ∈ P := by
    apply (Finset.mem_sdiff.mp (show y ∈ P \ T by simp [hy])).1
  obtain ⟨hxface, hyp⟩ := Finset.mem_filter.mp hyP
  obtain ⟨x, hx, hp, hbits⟩ := exists_face_antipode hI hxface
  have hxp : parity x = !p := by rw [hp, hyp]
  refine ⟨x, hxp, fun i hi => ?_⟩
  have hflip : flip x i ∈ P := Finset.mem_filter.mpr
    ⟨(flip_mem_face hi).mpr hx, by simp only [parity_flip, hxp, Bool.not_not]⟩
  have hmore : (I.erase i).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hi, hI]
    decide)
  obtain ⟨j, hj⟩ := hmore
  obtain ⟨hji, hjI⟩ := Finset.mem_erase.mp hj
  have hne : flip x i ≠ y := by
    intro e
    have he := congrFun e j
    rw [flip_apply_other x hji, hbits j hjI] at he
    exact (Bool.not_ne_self (y j)) he
  by_contra hnot
  have hm : flip x i ∈ P \ T := Finset.mem_sdiff.mpr ⟨hflip, hnot⟩
  rw [hy, Finset.mem_singleton] at hm
  exact hne hm

private theorem flipSign_on_edge (x : Q 9) (i : Fin 9) : flipSign i (flip x i) = flipSign i x := by
  apply Int.cast_injective (α := ℝ)
  rw [flipSign_cast, flipSign_cast, BalancedCriticalSpectrum.flip_flip]
  exact huangMatrix_symmetric _ _

private theorem weighted_pairing_symm (w : Fin 9 → ZMod 3) (f h : Q 9 → ZMod 3) :
    (∑ x, f x * weightedAction w h x) = ∑ x, h x * weightedAction w f x := by
  simp only [weightedAction, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun x i => h x * (w i * (flipSign i x : ZMod 3) * f (flip x i)))]
  apply Finset.sum_congr rfl
  intro i _
  let e : Q 9 ≃ Q 9 := (show Function.Involutive (fun x : Q 9 => flip x i) from
    fun x => BalancedCriticalSpectrum.flip_flip x i).toPerm
  apply Fintype.sum_equiv e
  intro x
  change _ = h (flip x i) * (w i * (flipSign i (flip x i) : ZMod 3) * f (flip (flip x i) i))
  rw [flipSign_on_edge, BalancedCriticalSpectrum.flip_flip]
  ac_rfl

private theorem zmod_three_sq (a : ZMod 3) : a ≠ 0 → a ^ 2 = 1 := by
  revert a
  decide

private theorem sum_sq_eq_support_card {α : Type*} [Fintype α] (f : α → ZMod 3) :
    (∑ x, f x ^ 2) = ((Finset.univ.filter (fun x => f x ≠ 0)).card : ZMod 3) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f x = 0
  · simp [hx]
  · simp [hx, zmod_three_sq _ hx]

private theorem weightedAction_restrict_face (I : Finset (Fin 9)) (z : Q 9)
    (w : Fin 9 → ZMod 3) (hw : ∀ i ∉ I, w i = 0) (g : Q 9 → ZMod 3) (x : Q 9) :
    weightedAction w (fun y => if y ∈ face I z then g y else 0) x =
      if x ∈ face I z then weightedAction w g x else 0 := by
  unfold weightedAction
  by_cases hx : x ∈ face I z
  · rw [ite_eq_left hx]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ I
    · simp only [ite_eq_left ((flip_mem_face hi).mpr hx)]
    · simp [hw i hi]
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ I
    · simp only [ite_eq_right (show flip x i ∉ face I z from
        fun h => hx ((flip_mem_face hi).mp h)), mul_zero]
    · simp [hw i hi]

/-- A nonzero ternary weighted Huang kernel word on one parity contains all
three active neighbors of some vertex on the opposite parity. -/
theorem exists_star_of_ternary_weighted_kernel
    (I : Finset (Fin 9)) (hI : I.card = 3) (w : Fin 9 → ZMod 3)
    (hw : ∀ i, w i ≠ 0 ↔ i ∈ I) (S : Finset (Q 9)) (p : Bool)
    (g : Q 9 → ZMod 3) (hg : g ≠ 0)
    (hgS : ∀ x ∉ S, g x = 0) (hgp : ∀ x, parity x ≠ p → g x = 0)
    (hker : weightedAction w g = 0) :
    ∃ x : Q 9, parity x = !p ∧ ∀ i ∈ I, flip x i ∈ S := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra! hall
    exact hg (funext hall)
  let f : Q 9 → ZMod 3 := fun x => if x ∈ face I z then g x else 0
  have hwoff : ∀ i ∉ I, w i = 0 :=
    fun i hi => not_ne_iff.mp (mt (hw i).mp hi)
  have hfker : weightedAction w f = 0 := by
    funext x
    rw [weightedAction_restrict_face I z w hwoff, hker]
    simp
  have hweights : ∑ i, w i ^ 2 = 0 := by
    rw [sum_sq_eq_support_card]
    have hsupport : Finset.univ.filter (fun i => w i ≠ 0) = I := by
      ext i
      simpa using hw i
    rw [hsupport, hI]
    decide
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have him : f ∈ Set.range (weightedAction w) := by
    rw [weightedAction_image_eq_kernel w hweights i ((hw i).mpr hi)]
    exact hfker
  obtain ⟨h, hpre⟩ := him
  have hzero : ∑ x, f x ^ 2 = 0 := by
    calc
      (∑ x, f x ^ 2) = ∑ x, f x * weightedAction w h x := by simp only [hpre, pow_two]
      _ = ∑ x, h x * weightedAction w f x := weighted_pairing_symm w f h
      _ = 0 := by simp [hfker]
  let T := Finset.univ.filter (fun x => f x ≠ 0)
  have hdiv : 3 ∣ T.card := by
    rw [sum_sq_eq_support_card] at hzero
    exact (ZMod.natCast_eq_zero_iff T.card 3).mp hzero
  have hmem {x : Q 9} (hx : x ∈ T) : x ∈ face I z ∧ g x ≠ 0 := by
    have hfx := (Finset.mem_filter.mp hx).2
    by_cases hface : x ∈ face I z
    · exact ⟨hface, by simpa [f, hface] using hfx⟩
    · exact False.elim (hfx (ite_eq_right hface))
  have hsub : T ⊆ (face I z).filter (fun x => parity x = p) :=
    fun _ hx => Finset.mem_filter.mpr ⟨(hmem hx).1, by
      by_contra hp
      exact (hmem hx).2 (hgp _ hp)⟩
  have hpos : 0 < T.card := by
    apply Finset.card_pos.mpr
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hzface : z ∈ face I z := mem_face.mpr (fun _ _ => rfl)
    simpa [f, hzface] using hz
  have hle := Finset.card_le_card hsub
  rw [face_half_card hI] at hle
  have hcard : T.card = 3 := by omega
  obtain ⟨x, hx, hstar⟩ := exists_face_star hI hsub hcard
  refine ⟨x, hx, fun j hj => ?_⟩
  by_contra hnot
  exact (hmem (hstar j hj)).2 (hgS _ hnot)

private theorem exists_ternary_integer_weights (I : Finset (Fin 9)) (hI : I.card = 3) :
    ∃ t : Fin 9 → ℤ, (∀ i, 0 < (t i : ℝ)) ∧ (∑ i, t i ^ 2 = 144) ∧
      ∀ i, (t i : ZMod 3) ≠ 0 ↔ i ∈ I := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hinactive : (Finset.univ \ I).card = 6 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin, hI]
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (Finset.univ \ I).card by rw [hinactive]; decide)
  have hAI {i : Fin 9} (hi : i ∈ I) : i ∉ A :=
    fun hj => (Finset.mem_sdiff.mp (hA hj)).2 hi
  let t (i : Fin 9) : ℤ := if i ∈ I then (if i = a then 1 else 2) else if i ∈ A then 3 else 6
  refine ⟨t, ?_, ?_, ?_⟩
  · intro i
    dsimp only [t]
    split_ifs <;> norm_num
  · have hterm (i : Fin 9) : t i ^ 2 =
        36 - (if i ∈ I then 32 else 0) - (if i = a then 3 else 0) -
          (if i ∈ A then 27 else 0) := by
      by_cases hi : i = a
      · subst i
        norm_num [t, ha, hAI ha]
      · by_cases hj : i ∈ I
        · norm_num [t, hi, hj, hAI hj]
        · by_cases hk : i ∈ A <;> norm_num [t, hi, hj, hk]
    have hacard : ((Finset.univ : Finset (Fin 9)).filter (fun i => i = a)).card = 1 := by
      rw [show ((Finset.univ : Finset (Fin 9)).filter (fun i => i = a)) = {a} by
        ext i
        simp]
      simp
    simp_rw [hterm, Finset.sum_sub_distrib]
    rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
    norm_num [hI, hacard, hAcard]
  · intro i
    by_cases hi : i ∈ I
    · rw [iff_true_intro hi]
      dsimp only [t]
      rw [ite_eq_left hi]
      split_ifs <;> decide
    · rw [iff_false_intro hi]
      dsimp only [t]
      rw [ite_eq_right hi]
      split_ifs <;> decide

private theorem stars_on_distinct_faces {I : Finset (Fin 9)} (hI : I.card = 3)
    {A B : Finset (Q 9)} (hAB : Disjoint A B) {p : Bool} {x y : Q 9}
    (hx : parity x = !p) (hy : parity y = !p)
    (hxA : ∀ i ∈ I, flip x i ∈ A) (hyB : ∀ i ∈ I, flip y i ∈ B) :
    ∃ j ∉ I, x j ≠ y j := by
  classical
  by_contra! h
  have hface : face I x = face I y := by
    ext z
    simp only [mem_face]
    exact forall_congr' fun j => forall_congr' fun hj => by rw [h j hj]
  have hsubset {z : Q 9} (hz : parity z = !p) :
      I.image (flip z) ⊆ (face I z).filter (fun u => parity u = p) := by
    rintro _ hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr
      ⟨(flip_mem_face hi).mpr (mem_face.mpr (fun _ _ => rfl)), by simp [parity_flip, hz]⟩
  have hdisjoint : Disjoint (I.image (flip x)) (I.image (flip y)) := by
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzx
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hzy
    exact Finset.disjoint_left.mp hAB (hxA i hi) (heq ▸ hyB j hj)
  have hbound := Finset.card_le_card (Finset.union_subset (hsubset hx) (hface.symm ▸ hsubset hy))
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injective _ (flip_injective x),
    Finset.card_image_of_injective _ (flip_injective y), face_half_card hI, hI] at hbound
  omega

attribute [local instance] Classical.propDecidable

/-- For every three active directions, each component and the exterior contain
the three active neighbors of a center. The centers have one common parity
and lie in pairwise distinct faces with those directions free. -/
theorem exists_common_parity_stars (I : Finset (Fin 9)) (hI : I.card = 3)
    {C D : Finset (Q 9)} (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ (p : Bool) (xC xD xT : Q 9),
      parity xC = !p ∧ parity xD = !p ∧ parity xT = !p ∧
      (∀ i ∈ I, flip xC i ∈ C) ∧ (∀ i ∈ I, flip xD i ∈ D) ∧
      (∀ i ∈ I, flip xT i ∈ Finset.univ \ (C ∪ D)) ∧
      (∃ j ∉ I, xC j ≠ xD j) ∧ (∃ j ∉ I, xC j ≠ xT j) ∧ (∃ j ∉ I, xD j ≠ xT j) := by
  classical
  let T : Finset (Q 9) := Finset.univ \ (C ∪ D)
  obtain ⟨t, ht, hnorm, hw⟩ := exists_ternary_integer_weights I hI
  let w (i : Fin 9) := (t i : ZMod 3)
  have hnormReal : ∑ i, (t i : ℝ) ^ 2 = 144 := by exact_mod_cast hnorm
  have hroot : Real.sqrt (∑ i, (t i : ℝ) ^ 2) = ((12 : ℤ) : ℝ) := by
    rw [hnormReal]
    norm_num
  have hweights : ∑ i, w i ^ 2 = 0 := by
    rw [sum_sq_eq_support_card]
    have hsupport : Finset.univ.filter (fun i => w i ≠ 0) = I := by
      ext i
      simpa using hw i
    rw [hsupport, hI]
    decide
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hwa : w a ≠ 0 := (hw a).mpr ha
  obtain ⟨p, hpC, hpD⟩ := exists_common_parity_of_integer_weights
    (q := 3) (s := 12) t ht hroot (by norm_num) w rfl hweights a hwa
    hsep hcard hc hd hrC hrD hbC hbD
  obtain ⟨vT, hvT, hvTU, hvTker⟩ :=
    exists_complement_word_of_common_parity w hweights a hwa hsep hcard hrC hrD hbC hbD p hpC hpD
  obtain ⟨vC, hvC⟩ := hpC
  obtain ⟨vD, hvD⟩ := hpD
  obtain ⟨gC, hgC, hgCS, hgCp, hgCker⟩ := supported_action_word_of_code w C vC hvC
  obtain ⟨gD, hgD, hgDS, hgDp, hgDker⟩ := supported_action_word_of_code w D vD hvD
  have hgT : extendParity vT ≠ 0 := by
    intro h
    exact hvT (funext fun x => (extendParity_apply vT x).symm.trans (congrFun h x.val))
  have hgTS (x : Q 9) (hx : x ∉ T) : extendParity vT x = 0 := by
    by_cases hpx : parity x = p
    · have hU : x ∈ C ∪ D := Finset.notMem_compl.mp (show x ∉ (C ∪ D)ᶜ from hx)
      exact (extendParity_apply vT ⟨x, hpx⟩).trans (hvTU _ hU)
    · exact extendParity_off vT hpx
  obtain ⟨xC, hxC, hxCS⟩ :=
    exists_star_of_ternary_weighted_kernel I hI w hw C p gC hgC hgCS hgCp hgCker
  obtain ⟨xD, hxD, hxDS⟩ :=
    exists_star_of_ternary_weighted_kernel I hI w hw D p gD hgD hgDS hgDp hgDker
  obtain ⟨xT, hxT, hxTS⟩ := exists_star_of_ternary_weighted_kernel
    I hI w hw T p (extendParity vT) hgT hgTS (fun _ => extendParity_off vT)
    (weightedAction_extendParity w vT hvTker)
  have hCT : Disjoint C T := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left D hx))
  have hDT : Disjoint D T := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right C hx))
  exact ⟨p, xC, xD, xT, hxC, hxD, hxT, hxCS, hxDS, hxTS,
    stars_on_distinct_faces hI hsep.1 hxC hxD hxCS hxDS,
    stars_on_distinct_faces hI hCT hxC hxT hxCS hxTS,
    stars_on_distinct_faces hI hDT hxD hxT hxDS hxTS⟩

#check exists_common_parity_stars
#print axioms exists_star_of_ternary_weighted_kernel
#print axioms exists_common_parity_stars

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TernaryFaceStars

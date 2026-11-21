/- GID: D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/LaoTransversalUniformMinor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A neighborhood and pair-matching criterion for a four-element uniform minor. -/

/-
Source: Peter Nelson, apnelson1/Matroid, revision 4383424967a752b51907082e9214b61ed2a2a82b.
https://github.com/apnelson1/Matroid/blob/4383424967a752b51907082e9214b61ed2a2a82b/Matroid/Constructions/Matching.lean
https://github.com/apnelson1/Matroid/blob/4383424967a752b51907082e9214b61ed2a2a82b/Matroid/ForMathlib/Function.lean#L128-L133
Modified source: specialize the right matroid to the free matroid, use the original graph's
left-to-right relation on the whole left ground, and use pinned Mathlib's native set API.
The port includes the finite-to-whole-set bridge and handles an empty right type.
Retire the port when this repository's actual Mathlib pin supplies an equivalent native
matching constructor and the all-subset independence equivalence with the accepted axioms.
The upstream Apache-2.0 license is reproduced at the end of this file.
-/

module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Combinatorics.Matroid.Minor.Order
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Preorder.Finite

/-! # A graph criterion for a four-element uniform minor of a transversal matroid -/

@[expose] public section

open Function Set Matroid

namespace D5.S3.Combinatorics.Matroids.LaoTransversalUniformMinor

variable {L R : Type*} (A : L → R → Prop)

/-- The specified left set has an edge-respecting injection into the right side. -/
def Matchable (I : Set L) : Prop :=
  ∃ f : I → R, Injective f ∧ ∀ x : I, A x (f x)

variable {A}

private lemma Matchable.mono {I J : Set L} (hJ : Matchable A J) (hIJ : I ⊆ J) :
    Matchable A I := by
  obtain ⟨f, hf, he⟩ := hJ
  exact ⟨fun x ↦ f ⟨x, hIJ x.2⟩,
    fun x y h ↦ Subtype.ext (congrArg (fun z : J ↦ (z : L)) (hf h)),
    fun x ↦ he ⟨x, hIJ x.2⟩⟩

private def IsMatching (A : L → R → Prop) (f : L → R) (I : Finset L) (T : Finset R) : Prop :=
  BijOn f I T ∧ ∀ x ∈ I, A x (f x)

private lemma IsMatching.card_eq {f : L → R} {I : Finset L} {T : Finset R}
    (h : IsMatching A f I T) : T.card = I.card := by
  classical
  rw [← Finset.card_image_of_injOn h.1.injOn]
  congr 1
  exact Finset.coe_inj.mp (by simpa using h.1.image_eq.symm)

private lemma bijOn_update [DecidableEq L] {f : L → R} {I : Set L} {T : Set R}
    {x : L} {y : R} (h : BijOn f I T) (hx : x ∈ I) (hy : y ∉ T) :
    BijOn (update f x y) I (insert y (T \ {f x})) := by
  have hEq : EqOn f (update f x y) (I \ {x}) :=
    fun z hz ↦ (update_of_ne hz.2 y f).symm
  have hRestr := (h.sdiff_singleton hx).congr hEq
  have hNew : update f x y x ∉ T \ {f x} := by simp [hy]
  simpa only [insert_sdiff_singleton, insert_eq_of_mem hx, update_self] using hRestr.insert hNew

private lemma exists_isMatching [Nonempty R] {I : Finset L} (hI : Matchable A (I : Set L)) :
    ∃ (T : Finset R) (f : L → R), IsMatching A f I T := by
  classical
  obtain ⟨g, hg, hEdge⟩ := hI
  let f : L → R := fun x ↦ if hx : x ∈ I then g ⟨x, hx⟩ else Classical.arbitrary R
  have hf : InjOn f (I : Set L) := by
    intro x hx y hy h
    change x ∈ I at hx
    change y ∈ I at hy
    exact congrArg Subtype.val (hg (show g ⟨x, hx⟩ = g ⟨y, hy⟩ by simpa [f, hx, hy] using h))
  exact ⟨I.image f, f, by simpa using hf.bijOn_image, fun x hx ↦ by
    simpa [f, hx] using hEdge ⟨x, hx⟩⟩

private lemma IsMatching.matchable {f : L → R} {I : Finset L} {T : Finset R}
    (h : IsMatching A f I T) : Matchable A (I : Set L) :=
  ⟨fun x ↦ f x, fun x y hxy ↦ Subtype.ext (h.1.injOn x.2 y.2 hxy), fun x ↦ h.2 x x.2⟩

private lemma matchable_augment [DecidableEq L] {I J : Finset L}
    (hI : Matchable A (I : Set L)) (hJ : Matchable A (J : Set L)) (hIJ : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ Matchable A (↑(insert e I) : Set L) := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt hIJ)
  let : Nonempty R := ⟨hJ.choose ⟨x, hx⟩⟩
  let T := (L → R) × Finset R
  set S := {w : T × T | IsMatching A w.1.1 I w.1.2 ∧ IsMatching A w.2.1 J w.2.2}
  have hSne : S.Nonempty := by
    obtain ⟨I₀, f, hf⟩ := exists_isMatching hI
    obtain ⟨J₀, g, hg⟩ := exists_isMatching hJ
    exact ⟨((f, I₀), (g, J₀)), hf, hg⟩
  set φ : T × T → Finset L := fun w ↦ (I ∩ J).filter (fun x ↦ w.1.1 x = w.2.1 x)
  have him : (φ '' S).Finite := by
    refine (I ∩ J).powerset.finite_toSet.subset ?_
    rintro _ ⟨w, -, rfl⟩
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  obtain ⟨⟨⟨f, I₀⟩, ⟨g, J₀⟩⟩, ⟨hf, hg⟩, hmax⟩ :=
    Set.Finite.exists_maximalFor' φ S him hSne
  change IsMatching A f I I₀ at hf
  change IsMatching A g J J₀ at hg
  rw [← hf.card_eq, ← hg.card_eq] at hIJ
  obtain ⟨z, hzJ₀, hzI₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hIJ
  obtain ⟨y, hyJ, rfl⟩ := hg.1.surjOn hzJ₀
  change y ∈ J at hyJ
  have hyI : y ∉ I := by
    intro hyI
    set I₀' := insert (g y) (I₀ \ {f y})
    set f' := update f y (g y)
    have hf' : IsMatching A f' I I₀' := by
      refine ⟨?_, fun v hv ↦ ?_⟩
      · simpa only [I₀', Finset.coe_insert, Finset.coe_sdiff, Finset.coe_singleton, f']
          using bijOn_update hf.1 hyI hzI₀
      obtain (rfl | hne) := eq_or_ne v y
      · simpa [f'] using hg.2 _ hyJ
      · rw [show f' v = f v from update_of_ne hne _ _]
        exact hf.2 v hv
    have hOld : φ ((f, I₀), (g, J₀)) ⊆ φ ((f', I₀'), (g, J₀)) := by
      intro v hv
      simp only [φ, Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      obtain (rfl | hne) := eq_or_ne v y
      · simp [f']
      · simpa [f', update_of_ne hne] using hv.2
    have hReverse : φ ((f', I₀'), (g, J₀)) ⊆ φ ((f, I₀), (g, J₀)) :=
      hmax (j := ((f', I₀'), (g, J₀))) ⟨hf', hg⟩ hOld
    have hyNew : y ∈ φ ((f', I₀'), (g, J₀)) := by simp [φ, f', hyI, hyJ]
    have heq : f y = g y := (Finset.mem_filter.mp (hReverse hyNew)).2
    exact hzI₀ (heq ▸ hf.1.mapsTo hyI)
  let f' := update f y (g y)
  have hne (v : L) (hv : v ∈ I) : v ≠ y := fun h ↦ hyI (h ▸ hv)
  have hfOld : BijOn f' (I : Set L) I₀ := hf.1.congr fun v hv ↦
    (update_of_ne (hne v hv) _ _).symm
  have hf' : IsMatching A f' (insert y I) (insert (g y) I₀) := by
    refine ⟨?_, fun v hv ↦ ?_⟩
    · have hFresh : f' y ∉ I₀ := by simpa [f'] using hzI₀
      simpa [f', Finset.coe_insert] using hfOld.insert hFresh
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · simpa [f'] using hg.2 _ hyJ
      · rw [show f' v = f v from update_of_ne (hne v hv) _ _]
        exact hf.2 v hv
  exact ⟨y, hyJ, hyI, hf'.matchable⟩

/-- The native transversal matroid on the whole left side. -/
@[no_expose] noncomputable def transversal (A : L → R → Prop) : Matroid L := by
  classical
  exact (IndepMatroid.ofFinset univ (fun I ↦ Matchable A (I : Set L))
    ⟨fun x ↦ False.elim (by simpa using x.2), fun x ↦ False.elim (by simpa using x.2),
      fun x ↦ False.elim (by simpa using x.2)⟩
    (fun {_ _} hJ hIJ ↦ Matchable.mono hJ (Finset.coe_subset.mpr hIJ))
    (fun {_ _} hI hJ hIJ ↦ matchable_augment hI hJ hIJ)
    (fun {_} _ ↦ subset_univ _)).matroid

/-- Every left vertex is on the ground of the transversal matroid, including loops. -/
@[simp] theorem transversal_ground : (transversal A).E = univ := by
  unfold transversal
  rfl

/-- Every subset is independent exactly when it has an edge-respecting injection. -/
theorem transversal_indep_iff [Finite L] (I : Set L) :
    (transversal A).Indep I ↔ Matchable A I := by
  classical
  let I₀ : Finset L := (Set.toFinite I).toFinset
  have hI₀ : (I₀ : Set L) = I := (Set.toFinite I).coe_toFinset
  rw [← hI₀]
  rw [transversal, IndepMatroid.matroid_Indep]
  exact IndepMatroid.ofFinset_indep ..

/-- All right vertices adjacent to at least one vertex of the specified left set. -/
def neighborhood (A : L → R → Prop) (I : Set L) : Set R :=
  {r | ∃ x ∈ I, A x r}

private lemma Matchable.intoNeighborhood {I J : Set L}
    (hI : Matchable A I) (hIJ : I ⊆ J) :
    ∃ f : I → neighborhood A J, Injective f ∧ ∀ x : I, A x (f x) := by
  obtain ⟨g, hg, hEdge⟩ := hI
  exact ⟨fun x ↦ ⟨g x, x, hIJ x.2, hEdge x⟩,
    fun _ _ h ↦ hg (congrArg Subtype.val h), hEdge⟩

private lemma Matchable.ncard_le_neighborhood [Finite R] {I J : Set L}
    (hI : Matchable A I) (hIJ : I ⊆ J) : I.ncard ≤ (neighborhood A J).ncard := by
  obtain ⟨f, hf, -⟩ := hI.intoNeighborhood hIJ
  exact Nat.card_le_card_of_injective f hf

/-- If every matching omits at least two vertices, some left subset has deficiency at least two. -/
private lemma exists_deficient_subset [Finite L] [Finite R] (S₀ : Set L)
    (hCap : ∀ J ⊆ S₀, Matchable A J → J.ncard + 2 ≤ S₀.ncard) :
    ∃ S ⊆ S₀, (neighborhood A S).ncard + 2 ≤ S.ncard := by
  classical
  -- Add a universal right vertex. Any matching into the augmented graph loses at most
  -- one left vertex when the new right vertex is removed.
  let choices (x : S₀) : Finset (Option R) :=
    insert none (((Set.toFinite {r : R | A x r}).toFinset).image some)
  have hNoMatch : ¬ ∃ f : S₀ → Option R, Injective f ∧ ∀ x, f x ∈ choices x := by
    rintro ⟨f, hf, hEdge⟩
    let bad : Set L := (Subtype.val : S₀ → L) '' (f ⁻¹' ({none} : Set (Option R)))
    have hBadSub : bad ⊆ S₀ := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hBadCard : bad.ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff]
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      change f x = none at hx
      change f y = none at hy
      exact congrArg Subtype.val (hf (hx.trans hy.symm))
    let J := S₀ \ bad
    have hReal (x : J) : ∃ r, f ⟨x, x.2.1⟩ = some r := by
      cases h : f ⟨x, x.2.1⟩ with
      | none => exact False.elim (x.2.2 ⟨⟨x, x.2.1⟩, h, rfl⟩)
      | some r => exact ⟨r, rfl⟩
    choose g hg using hReal
    have hMatch : Matchable A J := by
      refine ⟨g, fun x y h ↦ Subtype.ext ?_, fun x ↦ ?_⟩
      · exact congrArg (fun z : S₀ ↦ (z : L))
          (hf ((hg x).trans ((congrArg some h).trans (hg y).symm)))
      · have h := hEdge ⟨x, x.2.1⟩
        rw [hg x] at h
        simpa [choices] using h
    have hSize := ncard_sdiff_add_ncard_of_subset hBadSub
    have hTooMany := hCap J sdiff_subset hMatch
    change J.ncard + bad.ncard = S₀.ncard at hSize
    omega
  have hHall := mt (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp hNoMatch
  push Not at hHall
  obtain ⟨Q, hQ⟩ := hHall
  have hQne : Q.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hQ)
  let S : Set L := (Subtype.val : S₀ → L) '' (Q : Set S₀)
  have hSSub : S ⊆ S₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSCard : S.ncard = Q.card := by
    change ((Subtype.val : S₀ → L) '' (Q : Set S₀)).ncard = Q.card
    rw [ncard_image_of_injective _ Subtype.val_injective, ncard_coe_finset]
  let B := (Set.toFinite (neighborhood A S)).toFinset
  have hBCard : B.card = (neighborhood A S).ncard := (ncard_eq_toFinset_card _ _).symm
  have hB : insert none (B.image some) ⊆ Q.biUnion choices := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · obtain ⟨x, hx⟩ := hQne
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_self _ _⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
      have hNeighbor : r ∈ neighborhood A S := (Set.Finite.mem_toFinset _).mp hr
      obtain ⟨_, ⟨x, hx, rfl⟩, hEdge⟩ := hNeighbor
      exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa [choices] using hEdge⟩
  have hSize := Finset.card_le_card hB
  rw [Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective R), hBCard] at hSize
  exact ⟨S, hSSub, by omega⟩

/-- The native rank-two uniform matroid on the four labels in `Fin 4`. -/
noncomputable def uniform24 : Matroid (Fin 4) :=
  (IndepMatroid.ofFinite (E := univ) (Set.toFinite univ) (fun I ↦ I.ncard ≤ 2)
    (by simp) (fun {_ _} hJ hIJ ↦ (ncard_mono hIJ).trans hJ)
    (fun {I _} _ hJ hIJ ↦ by
      obtain ⟨e, heJ, heI⟩ := exists_mem_notMem_of_ncard_lt_ncard hIJ
      have he := ncard_insert_le e I
      exact ⟨e, heJ, heI, by omega⟩)
    (fun {_} _ ↦ subset_univ _)).matroid

private lemma uniform24_indep (I : Set (Fin 4)) : uniform24.Indep I ↔ I.ncard ≤ 2 :=
  Iff.rfl

private lemma relabel_uniform_iff [Finite L] (N : Matroid L) :
    (∃ e : N.E ≃ (univ : Set (Fin 4)), N.mapSetEquiv e = uniform24) ↔
      N.E.ncard = 4 ∧ ∀ J, N.Indep J ↔ J ⊆ N.E ∧ J.ncard ≤ 2 := by
  let U : Set (Fin 4) := univ
  let val : U → Fin 4 := Subtype.val
  have hVal : Injective val := Subtype.val_injective
  have hRangeVal : range val = univ := by
    ext i
    exact ⟨fun _ ↦ mem_univ _, fun _ ↦ ⟨⟨i, mem_univ _⟩, rfl⟩⟩
  have hMap (e : N.E ≃ U) (I : Set (Fin 4)) :
      (N.mapSetEquiv e).Indep I ↔ N.Indep ((Subtype.val ∘ e.symm) '' (val ⁻¹' I)) := by
    rw [mapSetEquiv_indep_iff, and_iff_left (subset_univ I), Set.image_image]
    rfl
  have hSize (e : N.E ≃ U) (I : Set (Fin 4)) :
      ((Subtype.val ∘ e.symm) '' (val ⁻¹' I)).ncard = I.ncard := by
    rw [ncard_image_of_injective _ (Subtype.val_injective.comp e.symm.injective)]
    exact ncard_preimage_of_injective_subset_range hVal (hRangeVal ▸ subset_univ I)
  have hGround (e : N.E ≃ U) : range (Subtype.val ∘ e.symm) = N.E := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ (e.symm y).2, fun hx ↦ ⟨e ⟨x, hx⟩, by simp⟩⟩
  have hFour : U.ncard = 4 := by simp [U, ncard_univ, Nat.card_eq_fintype_card]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(Nat.card_congr e).trans hFour, fun J ↦ ?_⟩
    by_cases hJ : J ⊆ N.E
    · let f : U → L := Subtype.val ∘ e.symm
      let I := val '' (f ⁻¹' J)
      have hLift : f '' (val ⁻¹' I) = J := by
        rw [show val ⁻¹' I = f ⁻¹' J from preimage_image_eq _ hVal]
        apply image_preimage_eq_iff.mpr
        rwa [hGround e]
      have hIff := hMap e I
      have hCard := hSize e I
      change (N.mapSetEquiv e).Indep I ↔ N.Indep (f '' (val ⁻¹' I)) at hIff
      change (f '' (val ⁻¹' I)).ncard = I.ncard at hCard
      rw [he, uniform24_indep, hLift] at hIff
      rw [hLift] at hCard
      simpa only [hJ, true_and, hCard] using hIff.symm
    · exact iff_of_false (fun h ↦ hJ h.subset_ground) (fun h ↦ hJ h.1)
  · rintro ⟨hN, hind⟩
    classical
    let : Fintype N.E := Fintype.ofFinite _
    let : Fintype U := Fintype.ofFinite _
    let e : N.E ≃ U := Fintype.equivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hN.trans hFour.symm)
    refine ⟨e, Matroid.ext_indep rfl (fun {I} _ ↦ ?_)⟩
    rw [hMap, hind, uniform24_indep, hSize, and_iff_right]
    exact (image_subset_range _ _).trans_eq (hGround e)

/-- Lao's Question 7.0.2 (arXiv:2611.02586v1, p. 104). A native contraction-deletion minor
relabels to the rank-two uniform matroid on `Fin 4` exactly when the graph supplies the
stated full neighborhood and pair matchings. -/
theorem has_uniform24_minor_iff [Finite L] [Finite R] (A : L → R → Prop) :
    (∃ N : Matroid L, N ≤m transversal A ∧
      ∃ e : N.E ≃ (univ : Set (Fin 4)), N.mapSetEquiv e = uniform24) ↔
    ∃ C X : Set L, Disjoint C X ∧ X.ncard = 4 ∧
      let B := neighborhood A (C ∪ X)
      B.ncard = C.ncard + 2 ∧
        ∀ P : Set L, P ⊆ X → P.ncard = 2 →
          ∃ f : (C ∪ P : Set L) → B, Bijective f ∧ ∀ x : (C ∪ P : Set L), A x (f x) := by
  classical
  simp_rw [relabel_uniform_iff]
  let M := transversal A
  constructor
  · rintro ⟨N, hN, hFour, hUniform⟩
    obtain ⟨C₀, D, hC₀, -, -, rfl⟩ := hN.exists_eq_contract_delete_disjoint
    let X := (M ／ C₀ ＼ D).E
    obtain ⟨K, hK⟩ := M.exists_isBasis C₀ hC₀
    have hCX : Disjoint C₀ X := by
      change Disjoint C₀ ((M ／ C₀ ＼ D).E)
      rw [delete_ground, contract_ground]
      exact disjoint_sdiff_right.mono_right sdiff_subset
    have hXD : Disjoint X D := by
      change Disjoint ((M ／ C₀ ＼ D).E) D
      rw [delete_ground]
      exact disjoint_sdiff_left
    have hKX : Disjoint K X := hCX.mono_left hK.subset
    have hPair {P : Set L} (hPX : P ⊆ X) (hP : P.ncard = 2) : M.Indep (K ∪ P) := by
      have hPminor := (hUniform P).mpr ⟨hPX, hP.le⟩
      rw [union_comm]
      exact (hK.contract_indep_iff_of_disjoint (hCX.mono_right hPX)).mp hPminor.of_delete
    let S₀ := K ∪ X
    have hFour' : X.ncard = 4 := hFour
    have hS₀ : S₀.ncard = K.ncard + 4 := by rw [ncard_union_eq hKX, hFour']
    obtain ⟨P₀, hP₀X, hP₀⟩ := exists_subset_card_eq (s := X) (n := 2) (by omega)
    -- Augmentation rules out a matching larger than the basis and a pair, even if
    -- the matching's left set omits some of the chosen basis.
    have hCap (J : Set L) (hJS : J ⊆ S₀) (hJ : Matchable A J) :
        J.ncard + 2 ≤ S₀.ncard := by
      by_contra! hLarge
      have hSmall : (K ∪ P₀).ncard < J.ncard := by
        rw [ncard_union_eq (hKX.mono_right hP₀X), hP₀]
        omega
      have hEnc : (K ∪ P₀).encard < J.encard := by
        rw [← (Set.toFinite (K ∪ P₀)).cast_ncard_eq, ← (Set.toFinite J).cast_ncard_eq]
        exact_mod_cast hSmall
      obtain ⟨e, he, hAug⟩ := (hPair hP₀X hP₀).augment ((transversal_indep_iff J).mpr hJ) hEnc
      have heX : e ∈ X := (hJS he.1).resolve_left (fun h ↦ he.2 (Or.inl h))
      have heP₀ : e ∉ P₀ := fun h ↦ he.2 (Or.inr h)
      have hTriple : insert e P₀ ⊆ X := insert_subset heX hP₀X
      have hContract : (M ／ C₀).Indep (insert e P₀) := by
        apply (hK.contract_indep_iff_of_disjoint (hCX.mono_right hTriple)).mpr
        rwa [insert_union, union_comm P₀ K]
      have hMinor : (M ／ C₀ ＼ D).Indep (insert e P₀) :=
        delete_indep_iff.mpr ⟨hContract, hXD.mono_left hTriple⟩
      have hBound := ((hUniform _).mp hMinor).2
      rw [ncard_insert_of_notMem heP₀, hP₀] at hBound
      omega
    obtain ⟨S, hSS₀, hDef⟩ := exists_deficient_subset S₀ hCap
    have hXS : X ⊆ S := by
      by_contra hMiss
      have hFew : (S ∩ X).ncard < X.ncard :=
        ncard_lt_ncard (ssubset_iff_subset_not_subset.mpr
          ⟨inter_subset_right, fun h ↦ hMiss (h.trans inter_subset_left)⟩)
      obtain ⟨P, hPX, hP, hLoss⟩ :
          ∃ P ⊆ X, P.ncard = 2 ∧ ((S ∩ X) \ P).ncard ≤ 1 := by
        by_cases hTwo : 2 ≤ (S ∩ X).ncard
        · obtain ⟨P, hPI, hP⟩ := exists_subset_card_eq hTwo
          have hDiff := ncard_sdiff_add_ncard_of_subset hPI
          exact ⟨P, hPI.trans inter_subset_right, hP, by omega⟩
        · obtain ⟨P, hIP, hPX, hP⟩ := exists_subsuperset_card_eq
            (s := S ∩ X) (t := X) (n := 2) inter_subset_right (by omega) (by omega)
          exact ⟨P, hPX, hP, by simp [sdiff_eq_empty.mpr hIP]⟩
      let J := S ∩ (K ∪ P)
      have hDiff : S \ J ⊆ (S ∩ X) \ P := by
        intro x hx
        have hxS : x ∈ S := hx.1
        have hxK : x ∉ K := fun h ↦ hx.2 ⟨hxS, Or.inl h⟩
        exact ⟨⟨hxS, (hSS₀ hxS).resolve_left hxK⟩, fun h ↦ hx.2 ⟨hxS, Or.inr h⟩⟩
      have hLoss' := (ncard_mono hDiff).trans hLoss
      have hSum := ncard_sdiff_add_ncard_of_subset (show J ⊆ S from inter_subset_left)
      have hJ : Matchable A J :=
        (transversal_indep_iff J).mp ((hPair hPX hP).subset inter_subset_right)
      have hLe := hJ.ncard_le_neighborhood (show J ⊆ S from inter_subset_left)
      omega
    let C := S \ X
    have hCK : C ⊆ K := fun _ hx ↦ (hSS₀ hx.1).resolve_right hx.2
    have hDisj : Disjoint C X := disjoint_sdiff_left
    have hUnion : C ∪ X = S := sdiff_union_of_subset hXS
    have hPairMatch (P : Set L) (hPX : P ⊆ X) (hP : P.ncard = 2) :
        Matchable A (C ∪ P) :=
      (transversal_indep_iff _).mp ((hPair hPX hP).subset (union_subset_union hCK Subset.rfl))
    have hSize (P : Set L) (hPX : P ⊆ X) (hP : P.ncard = 2) :
        (C ∪ P).ncard = C.ncard + 2 := by
      rw [ncard_union_eq (hDisj.mono_right hPX), hP]
    have hB : (neighborhood A (C ∪ X)).ncard = C.ncard + 2 := by
      have hLower := (hPairMatch P₀ hP₀X hP₀).ncard_le_neighborhood
        (union_subset_union (Subset.rfl : C ⊆ C) hP₀X)
      rw [hSize P₀ hP₀X hP₀] at hLower
      have hSSize := congrArg Set.ncard hUnion
      rw [ncard_union_eq hDisj, hFour'] at hSSize
      rw [hUnion] at hLower ⊢
      omega
    refine ⟨C, X, hDisj, hFour', hB, fun P hPX hP ↦ ?_⟩
    obtain ⟨f, hf, hEdge⟩ := (hPairMatch P hPX hP).intoNeighborhood
      (union_subset_union (Subset.rfl : C ⊆ C) hPX)
    exact ⟨f, (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, (hSize P hPX hP).trans hB.symm⟩, hEdge⟩
  · rintro ⟨C, X, hCX, hFour, hB, hPairs⟩
    have hMatch (P : Set L) (hPX : P ⊆ X) (hP : P.ncard = 2) : Matchable A (C ∪ P) := by
      obtain ⟨f, hf, hEdge⟩ := hPairs P hPX hP
      exact ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf.injective, hEdge⟩
    obtain ⟨P₀, hP₀X, hP₀⟩ := exists_subset_card_eq (s := X) (n := 2) (by omega)
    have hC : M.Indep C := (transversal_indep_iff C).mpr
      ((hMatch P₀ hP₀X hP₀).mono subset_union_left)
    let M' := M ／ C
    have hX : X ⊆ M'.E := by
      rw [show M'.E = M.E \ C from contract_ground M C, subset_sdiff]
      refine ⟨?_, hCX.symm⟩
      change X ⊆ (transversal A).E
      rw [transversal_ground]
      exact subset_univ X
    let D := M'.E \ X
    let N := M' ＼ D
    have hGround : N.E = X := by
      change (M' ＼ (M'.E \ X)).E = X
      rw [delete_ground, sdiff_sdiff_cancel_left hX]
    refine ⟨N, contract_delete_isMinor M C D, hGround ▸ hFour, fun J ↦ ?_⟩
    rw [hGround]
    by_cases hJX : J ⊆ X
    · have hDisj : Disjoint J C := hCX.symm.mono_left hJX
      have hJD : Disjoint J D := disjoint_sdiff_right.mono_left hJX
      change (M' ＼ D).Indep J ↔ _
      rw [delete_indep_iff, and_iff_left hJD, and_iff_right hJX]
      change (M ／ C).Indep J ↔ _
      rw [hC.contract_indep_iff, and_iff_right hDisj, union_comm J C, transversal_indep_iff]
      constructor
      · intro hJ
        have hBound := hJ.ncard_le_neighborhood (union_subset_union (Subset.rfl : C ⊆ C) hJX)
        rw [ncard_union_eq hDisj.symm, hB] at hBound
        omega
      · intro hJ
        obtain ⟨P, hJP, hPX, hP⟩ := exists_subsuperset_card_eq hJX hJ (by omega)
        exact (hMatch P hPX hP).mono (union_subset_union Subset.rfl hJP)
    · exact iff_of_false (fun h ↦ hJX (h.subset_ground.trans_eq hGround)) (fun h ↦ hJX h.1)

end D5.S3.Combinatorics.Matroids.LaoTransversalUniformMinor

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- GID: D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/ParallelCircuitCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Circuits of a loopless pullback and their ordered coordinates. -/

module

public import D5.S3.Combinatorics.Matroids.RationalTopCycleResidues
public import Mathlib.Combinatorics.Matroid.Map

/-! Circuits in an ordered parallel expansion. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.ParallelCircuitCoordinates

open Set
open scoped Matroid
set_option autoImplicit false

variable {V I : Type*} {M : Matroid I} {p : V → I}

open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
open OrderedCycleFactorization (shuffleSign)
open CircuitCycleDecomposition (restrictionSign)

private lemma parallel_pair (a b : V) (ha : M.IsNonloop (p a)) (hab : a ≠ b)
    (hp : p a = p b) : (M.comap p).IsCircuit ({a, b} : Set V) := by
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  have hp' : p '' ({a, b} : Set V) = {p a} := by simp [hp]
  constructor
  · apply Matroid.comap_dep_iff.mpr
    right
    rw [hp']
    exact ⟨Matroid.indep_singleton.mpr ha, fun h => hab (h (by simp) (by simp) hp)⟩
  · intro e he
    rcases (show e = a ∨ e = b by simpa using he) with rfl | rfl
    · have hb : (M.comap p).Indep ({b} : Set V) := by
        simpa [← hp] using Matroid.indep_singleton.mpr ha
      convert hb using 1
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      grind
    · have hb : (M.comap p).Indep ({a} : Set V) := by
        simpa using Matroid.indep_singleton.mpr ha
      convert hb using 1
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      grind

/-- Every pullback circuit is a same-fiber pair or an injective lift of a circuit. -/
theorem comap_circuit_cases {C : Set V} (hC : (M.comap p).IsCircuit C)
    (hn : ∀ a, M.IsNonloop (p a)) :
    (∃ a b, a ≠ b ∧ p a = p b ∧ C = {a,b}) ∨
      (InjOn p C ∧ M.IsCircuit (p '' C)) := by
  by_cases hi : InjOn p C
  · right
    refine ⟨hi, (Matroid.isCircuit_iff_forall_ssubset).mpr ⟨?_, ?_⟩⟩
    · rcases Matroid.comap_dep_iff.mp hC.dep with h | ⟨_, h⟩
      · exact h
      · exact (h hi).elim
    · intro J hJ
      let E := C ∩ p ⁻¹' J
      have hEC : E ⊂ C := by
        refine ssubset_of_subset_of_ne inter_subset_left ?_
        intro h
        exact hJ.ne (hJ.subset.antisymm (by
          rintro _ ⟨x, hx, rfl⟩
          exact (show x ∈ E from h.symm ▸ hx).2))
      have hIE := Matroid.comap_indep_iff.mp (hC.ssubset_indep hEC)
      apply hIE.1.subset
      intro j hj
      obtain ⟨x, hx, hpx⟩ := hJ.subset hj
      have hxJ : p x ∈ J := hpx.symm ▸ hj
      exact ⟨x, ⟨hx, hxJ⟩, hpx⟩
  · left
    classical
    simp only [InjOn, not_forall] at hi
    obtain ⟨a, ha, b, hb, hp, hab⟩ := hi
    have hc := parallel_pair a b (hn a) hab hp
    refine ⟨a, b, hab, hp, ?_⟩
    exact (hC.eq_of_dep_subset hc.dep (by simp [insert_subset_iff, ha, hb])).symm

/-- A transversal of a circuit is a circuit in the pullback. -/
theorem comap_isCircuit_of_injOn {C : Set V}
    (hinjective : InjOn p C) (hC : M.IsCircuit (p '' C)) :
    (M.comap p).IsCircuit C := by
  rw [Matroid.isCircuit_iff_forall_ssubset]
  refine ⟨Matroid.comap_dep_iff.mpr (.inl hC.dep), ?_⟩
  intro J hJ
  have himage : p '' J ⊂ p '' C :=
    (hinjective.image_ssubset_image_iff hJ.subset Subset.rfl).mpr hJ
  exact Matroid.comap_indep_iff.mpr ⟨hC.ssubset_indep himage, hinjective.mono hJ.subset⟩

/-- Contracting a set in the pullback has the same independent sets as pulling
back the contracted core, even when the ground sets differ by loops. -/
theorem comap_contract_indep_iff {C T : Set V} (hC : C ⊆ (M.comap p).E) :
    ((M.comap p) ／ C).Indep T ↔ (M ／ (p '' C)).Indep (p '' T) ∧ InjOn p T := by
  obtain ⟨J, hJ⟩ := (M.comap p).exists_isBasis C hC
  obtain ⟨hcore, hJinj, hJC⟩ := Matroid.comap_isBasis_iff.mp hJ
  rw [hJ.contract_indep_iff, hcore.contract_indep_iff, Matroid.comap_indep_iff, image_union]
  constructor
  · rintro ⟨⟨hindep, hinjective⟩, hdisjoint⟩
    refine ⟨⟨hindep, Set.disjoint_left.mpr ?_⟩, hinjective.mono subset_union_left⟩
    rintro a ha ⟨t, ht, rfl⟩
    by_cases hJmem : p t ∈ p '' J
    · obtain ⟨j, hj, heq⟩ := hJmem
      have hjt : j = t := hinjective (Or.inr hj) (Or.inl ht) heq
      exact Set.disjoint_left.mp hdisjoint (hJC (hjt ▸ hj)) ht
    · apply (hcore.insert_dep ⟨ha, hJmem⟩).not_indep
      apply hindep.subset
      exact insert_subset (Or.inl ⟨t, ht, rfl⟩) subset_union_right
  · rintro ⟨⟨hindep, hdisjoint⟩, hinjective⟩
    have hd : Disjoint C T := Set.disjoint_left.mpr fun x hxC hxT =>
      Set.disjoint_left.mp hdisjoint ⟨x, hxC, rfl⟩ ⟨x, hxT, rfl⟩
    refine ⟨⟨hindep, (Set.injOn_union (hd.mono_left hJC).symm).mpr
      ⟨hinjective, hJinj, ?_⟩⟩, hd⟩
    intro t ht j hj heq
    exact Set.disjoint_left.mp hdisjoint ⟨j, hJC hj, heq.symm⟩ ⟨t, ht, rfl⟩

/-- A basis in the contracted pullback is a transversal of a basis in the contracted core. -/
theorem comap_contract_isBase_iff (hsurj : Function.Surjective p)
    {C T : Set V} (hC : C ⊆ (M.comap p).E) :
    ((M.comap p) ／ C).IsBase T ↔ (M ／ (p '' C)).IsBase (p '' T) ∧ InjOn p T := by
  let core := M ／ (p '' C)
  let pullback := (M.comap p) ／ C
  have hindep {U : Set V} :
      pullback.Indep U ↔ core.Indep (p '' U) ∧ InjOn p U := comap_contract_indep_iff hC
  constructor
  · intro hT
    obtain ⟨hI, hinjective⟩ := hindep.mp hT.indep
    refine ⟨hI.isBase_of_maximal ?_, hinjective⟩
    intro U hU hsub
    let chooseLift := Function.surjInv hsurj
    have hright : Function.RightInverse chooseLift p := Function.rightInverse_surjInv hsurj
    let extras := chooseLift '' (U \ p '' T)
    have hextra : p '' extras = U \ p '' T := by
      rw [show extras = chooseLift '' (U \ p '' T) from rfl, ← image_comp, hright.id, image_id]
    have hdis : Disjoint T extras := by
      apply Set.disjoint_left.mpr
      intro x hx hxe
      have hmem : p x ∈ U \ p '' T := hextra ▸ mem_image_of_mem p hxe
      exact hmem.2 (mem_image_of_mem p hx)
    have himage : p '' (T ∪ extras) = U := by
      rw [image_union, hextra, union_sdiff_self, union_eq_self_of_subset_left hsub]
    have hinj : InjOn p (T ∪ extras) := by
      apply (injOn_union hdis).mpr
      refine ⟨hinjective, ?_, ?_⟩
      · rintro x ⟨a, _, rfl⟩ y ⟨b, _, rfl⟩ hab
        rw [hright a, hright b] at hab
        rw [hab]
      · intro x hx y hy heq
        have hmem : p y ∈ U \ p '' T := hextra ▸ mem_image_of_mem p hy
        exact hmem.2 (heq ▸ mem_image_of_mem p hx)
    have hlarge : pullback.Indep (T ∪ extras) := hindep.mpr ⟨himage.symm ▸ hU, hinj⟩
    exact (congrArg (p '' ·) (hT.eq_of_subset_indep hlarge subset_union_left)).trans himage
  · rintro ⟨hT, hinjective⟩
    refine (hindep.mpr ⟨hT.indep, hinjective⟩).isBase_of_maximal ?_
    intro U hU hsub
    obtain ⟨hIU, hUinj⟩ := hindep.mp hU
    have heq := hT.eq_of_subset_indep hIU (image_mono hsub)
    exact (hUinj.image_eq_image_iff hsub Subset.rfl).mp heq

private lemma order_iff_between_classes [LinearOrder V] [LinearOrder I]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    {a b : V} (hab : p a ≠ p b) :
    a < b ↔ p a < p b := by
  constructor
  · intro h
    rcases hab.lt_or_gt with hab | hba
    · exact hab
    · exact (h.not_gt (horder hba)).elim
  · intro h
    exact horder h

private lemma image_filter_lt [LinearOrder V] [LinearOrder I]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (F : Finset V) (x : V) (hout : p x ∉ F.image p) :
    (F.filter (· < x)).image p = (F.image p).filter (· < p x) := by
  apply Finset.ext
  intro j
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hax⟩, rfl⟩
    have hne : p a ≠ p x := fun h => hout (Finset.mem_image.mpr ⟨a, ha, h⟩)
    exact ⟨⟨a, ha, rfl⟩, (order_iff_between_classes horder hne).mp hax⟩
  · rintro ⟨⟨a, ha, rfl⟩, hax⟩
    exact ⟨a, ⟨ha, horder hax⟩, rfl⟩

private lemma insertionSign_image [LinearOrder V] [LinearOrder I]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (F : Finset V) (x : V) (hinj : InjOn p (F : Set V)) (hout : p x ∉ F.image p) :
    insertionSign F x = insertionSign (F.image p) (p x) := by
  unfold insertionSign
  rw [← image_filter_lt horder F x hout,
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

private lemma shuffleSign_image [LinearOrder V] [LinearOrder I]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (C T : Finset V) (hC : InjOn p (C : Set V)) (hT : InjOn p (T : Set V))
    (hdis : Disjoint (C.image p) (T.image p)) :
    shuffleSign C T = shuffleSign (C.image p) (T.image p) := by
  unfold shuffleSign
  rw [Finset.sum_image hC]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hout : p a ∉ T.image p :=
    fun h => Finset.disjoint_left.mp hdis (Finset.mem_image_of_mem p ha) h
  rw [← image_filter_lt horder T a hout,
    Finset.card_image_of_injOn (hT.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

private lemma image_erase_of_injOn [DecidableEq V] [DecidableEq I]
    (C : Finset V) (x : V) (hx : x ∈ C) (hC : InjOn p (C : Set V)) :
    (C.erase x).image p = (C.image p).erase (p x) := by
  apply Finset.ext
  intro j
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
    exact ⟨fun heq => hne (hC ha hx heq), a, ha, rfl⟩
  · rintro ⟨hne, a, ha, rfl⟩
    exact ⟨a, ⟨fun heq => hne (congrArg p heq), ha⟩, rfl⟩

private lemma restrictionSign_image [LinearOrder V] [LinearOrder I]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (C T : Finset V) {x : V} (hx : x ∈ C) (hC : InjOn p (C : Set V))
    (hT : InjOn p (T : Set V)) (hdis : Disjoint (C.image p) (T.image p)) :
    restrictionSign C x T = restrictionSign (C.image p) (p x) (T.image p) := by
  have herase : InjOn p (↑(C.erase x) : Set V) :=
    hC.mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  have hout : p x ∉ (C.erase x).image p := by
    rw [image_erase_of_injOn C x hx hC]
    exact Finset.notMem_erase _ _
  have hd : Disjoint ((C.erase x).image p) (T.image p) :=
    hdis.mono_left (Finset.image_subset_image (Finset.erase_subset _ _))
  rw [restrictionSign, restrictionSign, insertionSign_image horder _ _ herase hout,
    shuffleSign_image horder _ _ herase hT hd, image_erase_of_injOn C x hx hC]

/-- A signed readout along a transversal circuit has the same signs and projected
coordinates as its quotient readout on the core. -/
theorem signed_readout_on_transversal [LinearOrder V] [LinearOrder I]
    {A : Type*} [AddCommGroup A]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (C T : Finset V) (hC : InjOn p (C : Set V)) (hT : InjOn p (T : Set V))
    (hdis : Disjoint (C.image p) (T.image p)) (chain : Finset I → A) :
    (∑ x ∈ C, restrictionSign C x T • chain ((T ∪ C.erase x).image p)) =
      ∑ i ∈ C.image p,
        restrictionSign (C.image p) i (T.image p) • chain (T.image p ∪ (C.image p).erase i) := by
  rw [Finset.sum_image hC]
  apply Finset.sum_congr rfl
  intro x hx
  rw [restrictionSign_image horder C T hx hC hT hdis,
    Finset.image_union, image_erase_of_injOn C x hx hC]

/-- Extend a coefficient chain by constancy on transversals and zero on faces
containing two representatives of a class. -/
noncomputable def pullbackChain [DecidableEq I] {A : Type*} [Zero A]
    (p : V → I) (chain : Finset I → A) (F : Finset V) : A := by
  classical
  exact if InjOn p (F : Set V) then chain (F.image p) else 0

/-- The boundary of the pulled-back chain gives one term per class, multiplied
by the size of the corresponding fiber. -/
theorem pullbackChain_boundary [Fintype V] [Fintype I] [LinearOrder V] [LinearOrder I]
    {A : Type*} [AddCommGroup A]
    (horder : ∀ ⦃a b : V⦄, p a < p b → a < b)
    (chain : Finset I → A) (R : Finset V) (hR : InjOn p (R : Set V)) :
    (∑ x ∈ Finset.univ \ R, insertionSign R x • pullbackChain p chain (insert x R)) =
      ∑ i ∈ Finset.univ \ R.image p, insertionSign (R.image p) i •
        ((Finset.univ.filter (fun x => p x = i)).card • chain (insert i (R.image p))) := by
  classical
  let term (i : I) : A := insertionSign (R.image p) i • chain (insert i (R.image p))
  have hx_term (x : V) (hx : x ∈ Finset.univ \ R) :
      insertionSign R x • pullbackChain p chain (insert x R) =
        if p x ∈ R.image p then 0 else term (p x) := by
    have hxR : x ∉ R := (Finset.mem_sdiff.mp hx).2
    have hinj :
        InjOn p (↑(insert x R) : Set V) ↔ p x ∉ R.image p := by
      rw [Finset.coe_insert, injOn_insert hxR, and_iff_right hR]
      simp only [Finset.mem_image, Set.mem_image, Finset.mem_coe]
    by_cases he : p x ∈ R.image p
    · have hn : ¬ InjOn p (↑(insert x R) : Set V) := fun h => hinj.mp h he
      simp only [pullbackChain, hn, ite_false, smul_zero, he, ite_true]
    · simp only [pullbackChain, hinj.mpr he, ite_true, he, ite_false, Finset.image_insert,
        term, insertionSign_image horder R x hR he]
  calc
    _ = ∑ x ∈ Finset.univ \ R, (if p x ∈ R.image p then 0 else term (p x)) :=
      Finset.sum_congr rfl hx_term
    _ = ∑ x : V, (if p x ∈ R.image p then 0 else term (p x)) := by
      apply Finset.sum_subset (Finset.sdiff_subset (s := Finset.univ) (t := R))
      intro x _ hx
      have hmem : x ∈ R := by simpa using hx
      simp [Finset.mem_image_of_mem p hmem]
    _ = ∑ i : I, ∑ x ∈ Finset.univ.filter (fun x => p x = i),
        (if p x ∈ R.image p then 0 else term (p x)) :=
      (Finset.sum_fiberwise Finset.univ p _).symm
    _ = ∑ i ∈ Finset.univ \ R.image p, insertionSign (R.image p) i •
        ((Finset.univ.filter (fun x => p x = i)).card • chain (insert i (R.image p))) := by
      rw [← Finset.sum_subset (Finset.sdiff_subset
        (s := Finset.univ) (t := R.image p))]
      · apply Finset.sum_congr rfl
        intro i hi
        have hm : i ∉ R.image p := (Finset.mem_sdiff.mp hi).2
        calc
          (∑ x ∈ Finset.univ.filter (fun x => p x = i),
              (if p x ∈ R.image p then 0 else term (p x))) =
              ∑ _x ∈ Finset.univ.filter (fun x => p x = i), term i := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [(Finset.mem_filter.mp hx).2, hm]
          _ = _ := by
            rw [Finset.sum_const]
            dsimp only [term]
            exact smul_comm _ _ _
      · intro i _ hi
        have hm : i ∈ R.image p := by simpa using hi
        apply Finset.sum_eq_zero
        intro x hx
        simp [(Finset.mem_filter.mp hx).2, hm]

/-- A ridge containing two representatives of a class contributes no boundary. -/
theorem pullbackChain_boundary_of_not_injOn [Fintype V] [LinearOrder V] [DecidableEq I]
    {A : Type*} [AddCommGroup A] (chain : Finset I → A)
    (R : Finset V) (hR : ¬ InjOn p (R : Set V)) :
    ∑ x ∈ Finset.univ \ R, insertionSign R x • pullbackChain p chain (insert x R) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  have h : ¬ InjOn p (↑(insert x R) : Set V) :=
    fun hinj => hR (hinj.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)))
  simp only [pullbackChain, h, ite_false, smul_zero]

/-- Every basis of the pullback projects to a basis when all core classes
have representatives. -/
theorem isBase_comap_iff (hsurj : Function.Surjective p) {T : Set V} :
    (M.comap p).IsBase T ↔ M.IsBase (p '' T) ∧ InjOn p T := by
  rw [Matroid.comap_isBase_iff, image_preimage_eq _ hsurj, Matroid.isBasis_ground_iff]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, by
    rw [← image_subset_iff]
    exact h.1.subset_ground⟩⟩

end D5.S3.Combinatorics.Matroids.ParallelCircuitCoordinates

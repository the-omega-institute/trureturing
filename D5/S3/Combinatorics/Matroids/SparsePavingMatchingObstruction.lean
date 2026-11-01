/- GID: D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native sparse-paving obstructions for additive basis matchings. -/

import D5.S3.Combinatorics.Matroids.AliabadiZerbibMatroidMatching
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-! Native finite matroids retain their actual bases, circuits, and closure. -/

namespace D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction

open Set
open AliabadiZerbibMatroidMatching
open scoped Pointwise

/- admission_basis: escape-witness
   Escape witness: sparse_hall_obstruction constructs a base-valued repair
   of a dependent system of distinct representatives by a single exchange.
   This is an abstract structural argument, not a finite certified instance.
   Paving and ordered matching retain the existing source predicates.
   Cauchy-Davenport, Hall, and native dual-rank identities are upstream supply.
   Declaration classification after expansion of local helpers:
   small_indep: bind-only; consumers: dual_paving_card_bound, nonspanning_structure.
   dual_paving_card_bound: bind-only; consumer: nonspanning_structure.
   nonspanning_structure: bind-only; consumer: sparse_hall_obstruction.
   sparse_hall_obstruction: content; consumer: basiswise_obstruction.
   admissibleUnion: definition; consumers: sum_blocked_subset, union_card_bound,
     additive_bound, basiswise_obstruction.
   BasisMatches: definition; consumers: matches_iff_representatives,
     basiswise_obstruction.
   sum_blocked_subset: bind-only; consumers: additive_bound, basiswise_obstruction.
   additive_bound: bind-only; consumer: union_card_bound.
   union_card_bound: bind-only; consumer: basiswise_obstruction.
   matches_iff_representatives: bind-only; consumer: basiswise_obstruction.
   basiswise_obstruction: content; escape_witness: sparse_hall_obstruction.
   The witness is the new representative repair on the live path to the
   obstruction equivalence, not an instance of the supplied interval family.
-/

private lemma small_indep {α : Type*} (N : Matroid α) [N.Finite]
    (hp : IsPaving N) {r : ℕ} (hr : N.eRank = r)
    {X : Set α} (hX : X ⊆ N.E) (hc : X.ncard < r) : N.Indep X := by
  have hfin := N.ground_finite
  have hEr : r ≤ N.E.ncard := by
    have hh := N.eRk_le_encard N.E
    rw [N.eRk_ground, hr, ← hfin.cast_ncard_eq] at hh
    exact_mod_cast hh
  obtain ⟨Y, hXY, hYE, hY⟩ := Set.exists_subsuperset_card_eq hX
    (show X.ncard ≤ r - 1 by omega) (show r - 1 ≤ N.E.ncard by omega)
  apply (hp Y hYE ?_).subset hXY
  rw [← (hfin.subset hYE).cast_ncard_eq, hY, hr]
  norm_cast
  omega

private lemma dual_paving_card_bound {α : Type*} (N : Matroid α) [N.Finite]
    (hp : IsPaving N✶) {r : ℕ} (hr : N.eRank = r)
    {X : Set α} (hX : X ⊆ N.E) (hns : N.eRk X < r) : X.ncard ≤ r := by
  have hfin := N.ground_finite
  have hXfin := hfin.subset hX
  have hDfin : (N.E \ X).Finite := hfin.sdiff
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.mp
    ((Matroid.eRank_ne_top_iff N✶).mpr inferInstance)
  have hsum := N.eRank_add_eRank_dual
  rw [hr, ← hq, ← hfin.cast_ncard_eq] at hsum
  have hsum' : r + q = N.E.ncard := by exact_mod_cast hsum
  by_contra hn
  have hsd := Set.ncard_sdiff_add_ncard_of_subset hX hfin
  have hsmall : (N.E \ X).ncard < q := by omega
  have hi := small_indep N✶ hp hq.symm (by simp) hsmall
  have hid := N.eRk_dual_add_eRank (N.E \ X) sdiff_subset
  rw [hi.eRk_eq_encard, Set.sdiff_sdiff_cancel_left hX, hr,
    ← hDfin.cast_ncard_eq] at hid
  obtain ⟨I, hI⟩ := N.exists_isBasis X
  have hk : N.eRk X = (I.ncard : ℕ∞) := by
    rw [← hI.encard_eq_eRk, ← hI.indep.finite.cast_ncard_eq]
  rw [hk] at hid hns
  norm_cast at hid hns
  omega

private lemma nonspanning_structure {α : Type*} (N : Matroid α) [N.Finite]
    (hp : IsSparsePaving N) {r : ℕ} (hr : N.eRank = r)
    {X : Set α} (hX : X ⊆ N.E) (hc : r ≤ X.ncard) (hns : N.eRk X < r) :
    N.IsCircuit X ∧ N.IsFlat X ∧ X.ncard = r ∧ N.eRk X + 1 = r := by
  have hfin := N.ground_finite.subset hX
  have hle := dual_paving_card_bound N hp.2 hr hX hns
  have heq : X.ncard = r := by omega
  have hdep : N.Dep X := ⟨by
    intro hi
    have h := hi.eRk_eq_encard
    rw [← hfin.cast_ncard_eq, heq] at h
    exact hns.ne h, hX⟩
  have hcir : N.IsCircuit X := Matroid.isCircuit_iff_forall_ssubset.mpr ⟨hdep, by
    intro Y hY
    exact small_indep N hp.1 hr (hY.subset.trans hX)
      (by have := Set.ncard_lt_ncard hY hfin; omega)⟩
  have hcl := dual_paving_card_bound N hp.2 hr (N.closure_subset_ground X)
    (by simpa using hns)
  have hsub := N.subset_closure X hX
  have hcleq : N.closure X = X :=
    (Set.eq_of_subset_of_ncard_le hsub (by omega)
      (N.ground_finite.subset (N.closure_subset_ground X))).symm
  refine ⟨hcir, Matroid.isFlat_iff_closure_eq.mpr hcleq, heq, ?_⟩
  simpa [← hfin.cast_ncard_eq, heq] using hcir.eRk_add_one_eq

private lemma sparse_hall_obstruction {α ι : Type*} [Finite ι] [DecidableEq α]
    (N : Matroid α) [N.Finite] (hp : IsSparsePaving N)
    {r : ℕ} (hr : N.eRank = r) (hι : Nat.card ι = r)
    (F : ι → Finset α) (hF : ∀ i, (F i : Set α) ⊆ N.E)
    (hhall : ∀ J : Finset ι, J.card ≤ (J.biUnion F).card) :
    (¬ ∃ f : ι → α, Function.Injective f ∧ (∀ i, f i ∈ F i) ∧
      N.IsBase (Set.range f)) ↔
    N.IsCircuit (⋃ i, (F i : Set α)) ∧ N.IsFlat (⋃ i, (F i : Set α)) ∧
      (⋃ i, (F i : Set α)).ncard = r := by
  classical
  let U : Set α := ⋃ i, (F i : Set α)
  have hUE : U ⊆ N.E := by
    intro e he
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    exact hF i hi
  have hUfin := N.ground_finite.subset hUE
  have base_of_indep : ∀ (f : ι → α), Function.Injective f →
      N.Indep (Set.range f) → N.IsBase (Set.range f) := by
    intro f hf hi
    apply hi.isBase_of_eRk_ge (Set.finite_range f)
    rw [hi.eRk_eq_encard, ← (Set.finite_range f).cast_ncard_eq,
      Set.ncard_range_of_injective hf, hι, hr]
  constructor
  · intro hfail
    obtain ⟨f, hfi, hf⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' F).mp hhall
    have hQU : Set.range f ⊆ U := by
      rintro e ⟨i, rfl⟩
      exact mem_iUnion.mpr ⟨i, hf i⟩
    have hcQ : (Set.range f).ncard = r := by
      rw [Set.ncard_range_of_injective hfi, hι]
    have hnot : ¬ N.Indep (Set.range f) :=
      fun hi => hfail ⟨f, hfi, hf, base_of_indep f hfi hi⟩
    have hdep : N.Dep (Set.range f) := ⟨hnot, hQU.trans hUE⟩
    have hns : N.eRk (Set.range f) < r := by
      simpa [← (Set.finite_range f).cast_ncard_eq, hcQ] using hdep.eRk_lt_encard
    obtain ⟨hcir, hflat, -, hrk⟩ :=
      nonspanning_structure N hp hr (hQU.trans hUE) hcQ.ge hns
    have hUQ : U ⊆ Set.range f := by
      by_contra hn
      obtain ⟨e, heU, heQ⟩ := Set.not_subset.mp hn
      obtain ⟨i, hi⟩ := mem_iUnion.mp heU
      let g : ι → α := Function.update f i e
      have hgi : Function.Injective g := by
        intro j k heq
        by_cases hj : j = i
        · subst j
          by_contra hk
          have hh : e = f k := by simpa [g, Ne.symm hk] using heq
          exact heQ ⟨k, hh.symm⟩
        · by_cases hk : k = i
          · subst k
            have hh : f j = e := by simpa [g, hj] using heq
            exact False.elim (heQ ⟨j, hh⟩)
          · exact hfi (by simpa [g, hj, hk] using heq)
      have hgF : ∀ j, g j ∈ F j := by
        intro j
        by_cases hj : j = i
        · subst j; simpa [g] using hi
        · simpa [g, hj] using hf j
      have hgrange : Set.range g = insert e (Set.range f \ {f i}) := by
        ext z
        constructor
        · rintro ⟨j, rfl⟩
          by_cases hj : j = i
          · subst j; simp [g]
          · right
            refine ⟨⟨j, by simp [g, hj]⟩, ?_⟩
            simp only [g, Function.update_of_ne hj, mem_singleton_iff]
            exact fun h => hj (hfi h)
        · rintro (rfl | ⟨⟨j, rfl⟩, hj⟩)
          · exact ⟨i, by simp [g]⟩
          · have hji : j ≠ i := by
              intro hh; subst j; exact hj rfl
            exact ⟨j, by simp [g, hji]⟩
      have hind : N.Indep (Set.range g) := by
        rw [hgrange]
        apply (hcir.sdiff_singleton_indep (Set.mem_range_self i)).insert_indep_iff.mpr
        left
        refine ⟨hUE heU, ?_⟩
        rwa [hcir.closure_sdiff_singleton_eq, hflat.closure]
      exact hfail ⟨g, hgi, hgF, base_of_indep g hgi hind⟩
    have heq : U = Set.range f := hUQ.antisymm hQU
    change N.IsCircuit U ∧ N.IsFlat U ∧ U.ncard = r
    rw [heq]
    exact ⟨hcir, hflat, hcQ⟩
  · rintro ⟨hcir, hflat, hcU⟩ ⟨f, hfi, hf, hb⟩
    have hQU : Set.range f ⊆ U := by
      rintro e ⟨i, rfl⟩
      exact mem_iUnion.mpr ⟨i, hf i⟩
    have hQeq : Set.range f = U := Set.eq_of_subset_of_ncard_le hQU
      (by rw [Set.ncard_range_of_injective hfi, hι]; exact hcU.le) hUfin
    apply hcir.not_indep
    change N.Indep U
    rw [← hQeq]
    exact hb.indep


section Additive
variable {G : Type*} [AddCommGroup G]

/-- The union of the actual admissible target sets, including the empty union. -/
def admissibleUnion (A B X : Set G) : Set G :=
  {b | b ∈ B ∧ ∃ s ∈ X, s + b ∉ A}

/-- A specified source set is matched by a bijection to an actual target base. -/
def BasisMatches (A : Set G) (N : Matroid G) (S : Set G) : Prop :=
  ∃ T : Set G, N.IsBase T ∧ ∃ f : S ≃ T, ∀ s : S, (s : G) + (f s : G) ∉ A

private lemma sum_blocked_subset {A B X : Set G} (hXA : X ⊆ A) :
    X + insert 0 (B \ admissibleUnion A B X) ⊆ A := by
  rintro z ⟨x, hx, v, hv, rfl⟩
  rcases hv with rfl | hv
  · simpa using hXA hx
  · by_contra hn
    exact hv.2 ⟨hv.1, x, hx, hn⟩

private lemma additive_bound [IsAddTorsionFree G] {A B X : Set G}
    (hA : A.Finite) (hB : B.Finite) (hXA : X ⊆ A) (hne : X.Nonempty)
    (hzero : (0 : G) ∉ B) :
    X.ncard + (B \ admissibleUnion A B X).ncard ≤ A.ncard := by
  classical
  have hX := hA.subset hXA
  let U := B \ admissibleUnion A B X
  have hU : U.Finite := hB.sdiff
  have hV : (insert (0 : G) U).Finite := hU.insert 0
  have hVne : (insert (0 : G) U).Nonempty := ⟨0, mem_insert _ _⟩
  have hsum : (X + insert (0 : G) U).Finite := hX.add hV
  have hg := cauchy_davenport_of_isAddTorsionFree
    (s := hX.toFinset) (t := hV.toFinset)
    (by simpa using hne) (by simpa using hVne)
  have hco : (↑(hX.toFinset + hV.toFinset) : Set G) = X + insert 0 U := by
    simp
  have hg' : X.ncard + (insert (0 : G) U).ncard - 1 ≤
      (X + insert (0 : G) U).ncard := by
    simpa only [← Set.ncard_coe_finset, hco, Set.Finite.coe_toFinset] using hg
  have hVcard : (insert (0 : G) U).ncard = U.ncard + 1 :=
    Set.ncard_insert_of_notMem (fun h => hzero h.1) hU
  have hle := Set.ncard_le_ncard (sum_blocked_subset (B := B) hXA) hA
  change (X + insert 0 U).ncard ≤ A.ncard at hle
  rw [hVcard] at hg'
  change X.ncard + U.ncard ≤ A.ncard
  omega

private lemma union_card_bound [IsAddTorsionFree G] {A B X : Set G}
    (hA : A.Finite) (hB : B.Finite) (hXA : X ⊆ A)
    (hzero : (0 : G) ∉ B) (hsizes : A.ncard = B.ncard) :
    X.ncard ≤ (admissibleUnion A B X).ncard := by
  by_cases hne : X.Nonempty
  · have hb := additive_bound hA hB hXA hne hzero
    have hc := Set.ncard_sdiff_add_ncard_of_subset
      (show admissibleUnion A B X ⊆ B from fun _ h => h.1) hB
    omega
  · have hX : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hX]

private lemma matches_iff_representatives (A : Set G) (N : Matroid G) (S : Set G) :
    BasisMatches A N S ↔ ∃ f : S → G, Function.Injective f ∧
      (∀ s : S, f s ∈ N.E ∧ (s : G) + f s ∉ A) ∧ N.IsBase (Set.range f) := by
  classical
  constructor
  · rintro ⟨T, hT, f, hf⟩
    let g : S → G := fun s => f s
    have hgi : Function.Injective g := Subtype.val_injective.comp f.injective
    have hgT : Set.range g = T := by
      ext b
      constructor
      · rintro ⟨s, rfl⟩; exact (f s).property
      · intro hb
        obtain ⟨s, hs⟩ := f.surjective ⟨b, hb⟩
        exact ⟨s, congrArg Subtype.val hs⟩
    refine ⟨g, hgi, fun s => ⟨hT.subset_ground (f s).property, hf s⟩, ?_⟩
    rwa [hgT]
  · rintro ⟨f, hfi, hf, hb⟩
    exact ⟨Set.range f, hb, Equiv.ofInjective f hfi, fun s => (hf s).2⟩

/-- The complete native equal-size obstruction, with all four failure consequences.
The circuit and flat predicates belong to the independently specified target. -/
theorem basiswise_obstruction [IsAddTorsionFree G]
    (M N : Matroid G) [M.Finite] [N.Finite] [M.Loopless] [N.Loopless]
    {r m : ℕ} (hr : 1 ≤ r) (hMr : M.eRank = r) (hNr : N.eRank = r)
    (hp : IsSparsePaving N) (hzero : (0 : G) ∉ N.E)
    (hAm : M.E.ncard = m) (hBm : N.E.ncard = m)
    {S : Set G} (hS : M.IsBase S) :
    let C := admissibleUnion M.E N.E S
    let U := N.E \ C
    ((¬ BasisMatches M.E N S) ↔
      N.IsCircuit C ∧ N.IsFlat C ∧ N.eRk C + 1 = r ∧ C.ncard = r) ∧
    ((¬ BasisMatches M.E N S) →
      2 ≤ r ∧ r + 1 ≤ m ∧ U.ncard = m - r ∧ S + (U ∪ {0}) = M.E) := by
  classical
  dsimp only
  have hSfin := hS.indep.finite
  let : Finite S := hSfin.to_subtype
  have hScard : S.ncard = r := by
    have hc := hS.encard_eq_eRank
    rw [← hSfin.cast_ncard_eq, hMr] at hc
    exact_mod_cast hc
  let F : S → Finset G := fun s => N.ground_finite.toFinset.filter
    (fun b => (s : G) + b ∉ M.E)
  have hF : ∀ s, (F s : Set G) ⊆ N.E := by
    intro s b hb
    exact (Finset.mem_filter.mp hb).1 |> (Set.Finite.mem_toFinset _).mp
  have hU : (⋃ s, (F s : Set G)) = admissibleUnion M.E N.E S := by
    ext b
    simp only [mem_iUnion, Finset.mem_coe, F, Finset.mem_filter,
      Set.Finite.mem_toFinset, admissibleUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨s, hb, hn⟩; exact ⟨hb, s, s.property, hn⟩
    · rintro ⟨hb, s, hs, hn⟩; exact ⟨⟨s, hs⟩, hb, hn⟩
  have hhall : ∀ J : Finset S, J.card ≤ (J.biUnion F).card := by
    intro J
    let X : Set G := Subtype.val '' (J : Set S)
    have hXA : X ⊆ M.E := by
      rintro s ⟨x, hx, rfl⟩
      exact hS.subset_ground x.property
    have hcardX : X.ncard = J.card := by
      rw [Set.InjOn.ncard_image (show Set.InjOn (Subtype.val : S → G) (J : Set S)
        from fun _ _ _ _ hh => Subtype.ext hh), Set.ncard_coe_finset]
    have hCJ : (J.biUnion F : Set G) = admissibleUnion M.E N.E X := by
      ext b
      simp only [Finset.mem_coe, Finset.mem_biUnion, F, Finset.mem_filter,
        Set.Finite.mem_toFinset, admissibleUnion, mem_ofPred_eq, X, mem_image]
      constructor
      · rintro ⟨s, hs, hb, hn⟩
        exact ⟨hb, s, ⟨s, hs, rfl⟩, hn⟩
      · rintro ⟨hb, s, ⟨x, hx, rfl⟩, hn⟩
        exact ⟨x, hx, hb, hn⟩
    have hbound := union_card_bound M.ground_finite N.ground_finite hXA hzero
      (hAm.trans hBm.symm)
    rwa [← hCJ, hcardX, Set.ncard_coe_finset] at hbound
  have hcrit := sparse_hall_obstruction N hp hNr
    (by simpa only [Nat.card_coe_set_eq] using hScard) F hF hhall
  have hreps : (∃ f : S → G, Function.Injective f ∧ (∀ s, f s ∈ F s) ∧
      N.IsBase (Set.range f)) ↔ BasisMatches M.E N S := by
    rw [matches_iff_representatives]
    simp only [F, Finset.mem_filter, Set.Finite.mem_toFinset]
  rw [hreps, hU] at hcrit
  let C := admissibleUnion M.E N.E S
  have hCE : C ⊆ N.E := fun _ h => h.1
  have hCfin := N.ground_finite.subset hCE
  have hiff : (¬ BasisMatches M.E N S) ↔
      N.IsCircuit C ∧ N.IsFlat C ∧ N.eRk C + 1 = r ∧ C.ncard = r := by
    constructor
    · intro hn
      obtain ⟨hc, hf, hcard⟩ := hcrit.mp hn
      refine ⟨hc, hf, ?_, hcard⟩
      have hh := hc.eRk_add_one_eq
      change N.eRk C + 1 = C.encard at hh
      rwa [← hCfin.cast_ncard_eq, hcard] at hh
    · rintro ⟨hc, hf, hk, hn⟩
      exact hcrit.mpr ⟨hc, hf, hn⟩
  refine ⟨hiff, ?_⟩
  intro hn
  obtain ⟨hc, hf, hk, hcard⟩ := hiff.mp hn
  have hr2 : 2 ≤ r := by
    by_contra hh
    have hr1 : r = 1 := by omega
    obtain ⟨e, he⟩ := (Set.ncard_eq_one.mp (hcard.trans hr1))
    have hnloop : N.Indep ({e} : Set G) :=
      (Matroid.indep_singleton).mpr (N.isNonloop_of_loopless (hCE (he.symm ▸ mem_singleton e)))
    exact hc.not_indep (he.symm ▸ hnloop)
  have hrm : r + 1 ≤ m := by
    have hCsub := Set.ncard_le_ncard hCE N.ground_finite
    by_contra hh
    have heq : C = N.E := Set.eq_of_subset_of_ncard_le hCE
      (by rw [hcard, hBm]; omega) N.ground_finite
    rw [heq, N.eRk_ground, hNr] at hk
    exact (by simpa using hk : False)
  have hUcard : (N.E \ C).ncard = m - r := by
    have hh := Set.ncard_sdiff_add_ncard_of_subset hCE N.ground_finite
    rw [hcard, hBm] at hh
    omega
  have hsumsub : S + insert 0 (N.E \ C) ⊆ M.E :=
    sum_blocked_subset (B := N.E) hS.subset_ground
  have hUfin : (N.E \ C).Finite := N.ground_finite.sdiff
  have hVfin : (insert (0 : G) (N.E \ C)).Finite := hUfin.insert 0
  have hSne : S.Nonempty := Set.ncard_pos hSfin |>.mp (by omega)
  have hVne : (insert (0 : G) (N.E \ C)).Nonempty := ⟨0, mem_insert _ _⟩
  have hg := cauchy_davenport_of_isAddTorsionFree
    (s := hSfin.toFinset) (t := hVfin.toFinset)
    (by simpa using hSne) (by simpa using hVne)
  have hco : (↑(hSfin.toFinset + hVfin.toFinset) : Set G) =
      S + insert 0 (N.E \ C) := by simp
  have hg' : S.ncard + (insert (0 : G) (N.E \ C)).ncard - 1 ≤
      (S + insert 0 (N.E \ C)).ncard := by
    simpa only [← Set.ncard_coe_finset, hco, Set.Finite.coe_toFinset] using hg
  rw [Set.ncard_insert_of_notMem (fun hz => hzero hz.1) hUfin, hUcard,
    hScard] at hg'
  have hsumEq : S + insert 0 (N.E \ C) = M.E :=
    Set.eq_of_subset_of_ncard_le hsumsub (by rw [hAm]; omega) M.ground_finite
  refine ⟨hr2, hrm, hUcard, ?_⟩
  simpa only [Set.union_singleton, Set.insert_eq_of_mem] using hsumEq


end Additive

end D5.S3.Combinatorics.Matroids.SparsePavingMatchingObstruction

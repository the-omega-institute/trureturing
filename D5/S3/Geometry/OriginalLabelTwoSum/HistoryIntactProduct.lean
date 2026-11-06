/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryIntactProduct
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryIntactProduct
   mirror-E: none(waiver:intact-relative-product)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Relative products of actual native lists keep protected old fibres and expose the entire ordered rectangle expansion. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap

/-! SOURCE_ONLY_UNCOMPILED. This constructs lists, not just equivalences of
families. A is the old subfamily already absorbed by B. Every local pair runs
over D minus A in descending old-face order. Neither a desired product list
nor a product endpoint certificate is a premise. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
local instance historyIntactProductPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactProduct
open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem aug_retained (P : CollapsePair V) :
    nativeAug P.retained = cut (nativeAug P.ambient) {P.lower} := by
  apply SetLike.ext
  intro s
  have hn : ¬ P.lower ⊆ (∅ : Finset V) := by
    intro h
    exact Finset.not_nonempty_empty (P.lower_nonempty.mono h)
  change (s = ∅ ∨ s ∈ P.retained) ↔
    (s = ∅ ∨ s ∈ P.ambient) ∧ ∀ a ∈ ({P.lower} : Finset (Finset V)), ¬ a ⊆ s
  simp only [Finset.mem_singleton, forall_eq, CollapsePair.retained]
  constructor
  · rintro (rfl | ⟨hs, hnot⟩)
    · exact ⟨Or.inl rfl, hn⟩
    · exact ⟨Or.inr hs, hnot⟩
  · rintro ⟨rfl | hs, hnot⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hs, hnot⟩

private theorem separate_parts {X Y a b t u : Finset V} (hXY : Disjoint X Y)
    (ha : a ⊆ X) (hb : b ⊆ Y) (ht : t ⊆ X) (hu : u ⊆ Y)
    (h : a ∪ b ⊆ t ∪ u) : a ⊆ t ∧ b ⊆ u := by
  constructor
  · intro v hv
    exact (Finset.mem_union.mp (h (Finset.mem_union_left _ hv))).resolve_right
      (fun hvu => Finset.disjoint_left.mp hXY (ha hv) (hu hvu))
  · intro v hv
    exact (Finset.mem_union.mp (h (Finset.mem_union_right _ hv))).resolve_left
      (fun hvt => Finset.disjoint_left.mp hXY (ht hvt) (hb hv))

private def productSequence (X Y : Finset V) (D A B : Family V)
    (hXY : Disjoint X Y) (hD : Supported X D)
    (hA : rawJoin A (delta Y) ≤ B)
    {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (hs : Supported Y (nativeAug K))
    (hb : ∀ a ∈ D, a ∉ A → ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ nativeAug L) :
    {T : Sequence (project (B ⊔ rawJoin D (nativeAug K)))
        (project (B ⊔ rawJoin D (nativeAug L))) //
      T.pairs.map (fun P => (P.lower, P.upper)) =
        S.pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ D ∧ a ∉ A))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a)))} := by
  classical
  revert hs hb
  induction S with
  | refl K => intro hs hb; exact ⟨Sequence.refl _, rfl⟩
  | @step P Lnext S ih =>
      intro hs hb
      let F := X.powerset.filter (fun a => a ∈ D ∧ a ∉ A)
      let H := B ⊔ rawJoin D (nativeAug P.ambient)
      have memF (a : Finset V) : a ∈ F ↔ a ∈ D ∧ a ∉ A := by
        simp only [F, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun h => h.2, fun h => ⟨hD a h.1, h⟩⟩
      have hl : P.lower ∈ P.ambient :=
        (P.ambient.isRelLowerSet_faces P.upper_mem).2
          (Finset.subset_insert _ _) P.lower_nonempty
      have hlY : P.lower ⊆ Y := hs _ (Or.inr hl)
      have huY : P.upper ⊆ Y := hs _ (Or.inr P.upper_mem)
      have hvY : P.apex ∈ Y := huY (Finset.mem_insert_self _ _)
      have hnot : P.lower ∉ nativeAug Lnext := by
        intro h
        have hm : P.lower ∈ Lnext := h.elim
          (fun he => False.elim (Finset.not_nonempty_empty (he ▸ P.lower_nonempty))) id
        exact (S.monotone hm).2 le_rfl
      have baseAvoid (a : Finset V) (ha : a ∈ F) : P.lower ∪ a ∉ B := by
        intro h
        apply hnot
        exact hb a ((memF a).mp ha).1 ((memF a).mp ha).2 P.lower hlY
          (by simpa only [Finset.union_comm] using h)
      have hmem : ∀ a ∈ F, P.lower ∪ a ∈ H ∧ insert P.apex (P.lower ∪ a) ∈ H := by
        intro a ha
        have had := ((memF a).mp ha).1
        constructor
        · exact Or.inr ⟨a, had, P.lower, Or.inr hl, Finset.union_comm _ _⟩
        · exact Or.inr ⟨a, had, P.upper, Or.inr P.upper_mem, by
            simp only [CollapsePair.upper, Finset.union_insert, Finset.insert_union]
            rw [Finset.union_comm]⟩
      have hc : ∀ a ∈ F, ∀ s ∈ H, P.lower ∪ a ⊆ s →
          ∃ u ∈ F, a ⊆ u ∧ (s = P.lower ∪ u ∨ s = insert P.apex (P.lower ∪ u)) := by
        intro a ha s hs' hsub
        rcases hs' with hsB | ⟨u, hu, t, ht, rfl⟩
        · exact False.elim (baseAvoid a ha (B.lower hsub hsB))
        · have htY := hs t ht
          have parts := separate_parts hXY (hD a ((memF a).mp ha).1)
            hlY (hD u hu) htY (by simpa only [Finset.union_comm] using hsub)
          have huf : u ∈ F := (memF u).mpr ⟨hu,
            fun hua => ((memF a).mp ha).2 (A.lower parts.1 hua)⟩
          have htn : t.Nonempty := P.lower_nonempty.mono parts.2
          have htK : t ∈ P.ambient := ht.elim
            (fun he => False.elim (Finset.not_nonempty_empty (he ▸ htn))) id
          have htPair : t = P.lower ∨ t = P.upper := by
            by_cases he : t = P.lower
            · exact Or.inl he
            · exact Or.inr (P.free t htK
                (Finset.ssubset_iff_subset_ne.mpr ⟨parts.2, Ne.symm he⟩))
          refine ⟨u, huf, parts.1, ?_⟩
          rcases htPair with rfl | rfl
          · exact Or.inl (Finset.union_comm _ _)
          · right
            simp only [CollapsePair.upper, Finset.union_insert, Finset.insert_union]
            rw [Finset.union_comm]
      let R := rectangle Y X P.lower P.apex hXY.symm hlY hvY P.apex_notMem F H
        (fun a ha => hD a ((memF a).mp ha).1)
        (fun a _ => P.lower_nonempty.mono Finset.subset_union_left) hmem hc
      have hret : cut H (F.image (fun a => P.lower ∪ a)) =
          B ⊔ rawJoin D (nativeAug P.retained) := by
        apply SetLike.ext
        intro s
        constructor
        · rintro ⟨hs', hn⟩
          rcases hs' with hsB | ⟨a, ha, t, ht, rfl⟩
          · exact Or.inl hsB
          · by_cases haA : a ∈ A
            · exact Or.inl (hA ⟨a, haA, t, hs t ht, rfl⟩)
            · right
              refine ⟨a, ha, t, ?_, rfl⟩
              rw [aug_retained]
              refine ⟨ht, ?_⟩
              intro b hb' hbt
              have he : b = P.lower := Finset.mem_singleton.mp hb'
              subst b
              exact hn (P.lower ∪ a)
                (Finset.mem_image.mpr ⟨a, (memF a).mpr ⟨ha, haA⟩, rfl⟩)
                (Finset.union_subset
                  (hbt.trans Finset.subset_union_right) Finset.subset_union_left)
        · intro hs'
          have source : s ∈ H := by
            rcases hs' with hsB | ⟨a, ha, t, ht, rfl⟩
            · exact Or.inl hsB
            · rw [aug_retained] at ht
              exact Or.inr ⟨a, ha, t, ht.1, rfl⟩
          refine ⟨source, ?_⟩
          intro b hb' hbs
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
          rcases hs' with hsB | ⟨u, hu, t, ht, rfl⟩
          · exact baseAvoid a ha (B.lower hbs hsB)
          · rw [aug_retained] at ht
            have parts := separate_parts hXY (hD a ((memF a).mp ha).1)
              hlY (hD u hu) (hs t ht.1)
              (by simpa only [Finset.union_comm] using hbs)
            exact ht.2 _ (by simp) parts.2
      have hsNext : Supported Y (nativeAug P.retained) := by
        intro s hs'
        rw [aug_retained] at hs'
        exact hs s hs'.1
      let Q := ih hsNext hb
      refine ⟨(R.cast rfl (congrArg project hret)).append Q.1, ?_⟩
      rw [Sequence.pairs_append, List.map_append, Sequence.pairs_cast,
        rectangle_order, Q.2]
      simp only [Sequence.pairs, List.flatMap_cons]
      congr 1
      apply List.map_congr_left
      intro a ha
      simp only [CollapsePair.upper, Finset.insert_union]

/-- Relative product of a genuine local sequence. The protected old A-fibres
are already contained in B; every other B-intersection belongs to the FINAL
local family N. The endpoint equality and every actual rectangle coface are
proved in productSequence. The returned second field is the complete global
ordered pair expansion, not a list supplied by the caller. -/
def relativeProduct (X Y : Finset V) (D A B M N : Family V)
    (hXY : Disjoint X Y) (hD : Supported X D)
    (hA : rawJoin A (delta Y) ≤ B)
    (hM0 : (∅ : Finset V) ∈ M) (hN0 : (∅ : Finset V) ∈ N)
    (hM : Supported Y M) (S : Sequence (project M) (project N))
    (hb : ∀ a ∈ D, a ∉ A → ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ N) :
    {T : Sequence (project (B ⊔ rawJoin D M)) (project (B ⊔ rawJoin D N)) //
      T.pairs.map (fun P => (P.lower, P.upper)) =
        S.pairs.flatMap (fun P =>
          (fibres (X.powerset.filter (fun a => a ∈ D ∧ a ∉ A))).map
            (fun a => (P.lower ∪ a, P.upper ∪ a)))} := by
  let T := productSequence X Y D A B hXY hD hA S
    (by rw [reconstruct_nonvoid M hM0]; exact hM)
    (by rw [reconstruct_nonvoid N hN0]; exact hb)
  exact ⟨T.1.cast (by rw [reconstruct_nonvoid M hM0])
    (by rw [reconstruct_nonvoid N hN0]), by
      rw [Sequence.pairs_cast]
      exact T.2⟩

/-- Named rewrite rule for consumers whose old-fibre filter is a singleton.
This is the second component of the constructed relative product. -/
theorem relativeProduct_pairs (X Y : Finset V) (D A B M N : Family V)
    (hXY : Disjoint X Y) (hD : Supported X D)
    (hA : rawJoin A (delta Y) ≤ B)
    (hM0 : (∅ : Finset V) ∈ M) (hN0 : (∅ : Finset V) ∈ N)
    (hM : Supported Y M) (S : Sequence (project M) (project N))
    (hb : ∀ a ∈ D, a ∉ A → ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ N) :
    (relativeProduct X Y D A B M N hXY hD hA hM0 hN0 hM S hb).1.pairs.map
        (fun P => (P.lower, P.upper)) =
      S.pairs.flatMap (fun P =>
        (fibres (X.powerset.filter (fun a => a ∈ D ∧ a ∉ A))).map
          (fun a => (P.lower ∪ a, P.upper ∪ a))) :=
  (relativeProduct X Y D A B M N hXY hD hA hM0 hN0 hM S hb).2

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryIntactProduct

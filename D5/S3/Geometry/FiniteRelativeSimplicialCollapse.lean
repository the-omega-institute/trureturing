/- GID: D5/S3/Geometry/FiniteRelativeSimplicialCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteRelativeSimplicialCollapse
   mirror-E: none(waiver:finite-relative-simplicial-collapse)
   anchors: [mathlib/module/Mathlib.Data.List.Forall2]
   utility: none
   digest: Finite labeled collapse sequences give relative deformations, link replay, and cone extension fixing the actual apex. -/
/- Ordinary mathematical specifications (not imported axioms): sections 2–5 of
independent_general_relative_cancellation_proof.txt, SHA256
f9888966c4313557587f6c91f7a185a8aa6de6473219536205db6600e64553ad;
primitives 1–3 and the three cases of independent_two_path_proof.txt, SHA256
8f018634e27ab0a51fb94ebbebb77a1d3b96eb13c0dba0bcebaa8cd5b5fffa3c.
The present bridge concerns general complexes, not the graph arithmetic.
-/
import D5.S3.Geometry.FiniteElementaryCollapse
import D5.S3.Geometry.FiniteComponentClosure.Models
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD

/-!
Finite labeled collapses, deletion/link replay, and extension over a retained
cone. No flag, purity, connectedness, or realization-nonempty assumption is used.
`AugmentedFace` is a combinatorial predicate: its empty face contributes no
point to `realization`. Every elementary lower face is still nonempty.

The actual spaces, coordinate inclusions, elementary retractions, and elementary
relative homotopies are reused from their existing owners. Sequence retractions
are composed explicitly. The relative fixed set is the ENTIRE final realization.
-/

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteRelativeSimplicialCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation FiniteElementaryCollapse
open FiniteComponentClosure (vertexComplex)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite witness consisting solely of actual free pairs in the exact current
complex. In particular, a witness has no topological fields. -/
inductive Sequence : PreAbstractSimplicialComplex V →
    PreAbstractSimplicialComplex V → Type _
  | refl (K) : Sequence K K
  | step (P : CollapsePair V) {L} (tail : Sequence P.retained L) :
      Sequence P.ambient L

namespace Sequence

variable {K L M : PreAbstractSimplicialComplex V}

def pairs : {K L : PreAbstractSimplicialComplex V} →
    Sequence K L → List (CollapsePair V)
  | _, _, .refl _ => []
  | _, _, .step P T => P :: T.pairs

theorem monotone (S : Sequence K L) : L ≤ K := by
  induction S with
  | refl => exact le_rfl
  | step P T ih => exact ih.trans P.retained_le

/-- Every step, including its endpoint, contains the entire final complex. -/
theorem final_le_each_retained (S : Sequence K L) {P : CollapsePair V}
    (hP : P ∈ S.pairs) : L ≤ P.retained := by
  revert hP
  induction S with
  | refl => intro hP; simp [pairs] at hP
  | step Q T ih =>
      intro hP
      simp only [pairs, List.mem_cons] at hP
      rcases hP with rfl | hP
      · exact T.monotone
      · exact ih hP

theorem final_le_each_ambient (S : Sequence K L) {P : CollapsePair V}
    (hP : P ∈ S.pairs) : L ≤ P.ambient :=
  (S.final_le_each_retained hP).trans P.retained_le

def append : {K L M : PreAbstractSimplicialComplex V} →
    Sequence K L → Sequence L M → Sequence K M
  | _, _, _, .refl _, T => T
  | _, _, _, .step P S, T => .step P (S.append T)

/-- Equality transport changes no label or face. -/
def cast (S : Sequence K L) {K' L'} (hK : K = K') (hL : L = L') :
    Sequence K' L' := by
  subst K'
  subst L'
  exact S

def frames : {K L : PreAbstractSimplicialComplex V} →
    Sequence K L → List (PreAbstractSimplicialComplex V)
  | _, _, .refl K => [K]
  | _, _, .step P T => P.ambient :: frames T

theorem frames_le_source {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : ∀ M ∈ frames S, M ≤ K := by
  induction S with
  | refl K =>
      intro M hM
      simp only [frames, List.mem_singleton] at hM
      subst M
      exact le_rfl
  | @step P L T ih =>
      intro M hM
      simp only [frames, List.mem_cons] at hM
      rcases hM with rfl | hM
      · exact le_rfl
      · exact (ih M hM).trans P.retained_le

theorem frames_length {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : (frames S).length = S.pairs.length + 1 := by
  induction S with
  | refl K => rfl
  | step P S ih => simp [frames, pairs, ih, Nat.add_assoc]

@[simp] theorem pairs_cast {K L K' L' : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K = K') (hL : L = L') :
    (S.cast hK hL).pairs = S.pairs := by
  subst K'
  subst L'
  rfl

@[simp] theorem frames_cast {K L K' L' : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K = K') (hL : L = L') :
    frames (S.cast hK hL) = frames S := by
  subst K'
  subst L'
  rfl

@[simp] theorem pairs_append
    {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) :
    (S.append T).pairs = S.pairs ++ T.pairs := by
  induction S with
  | refl K => rfl
  | step P S ih => simp only [append, pairs, ih, List.cons_append]

/-- The first frame is the actual source, regardless of fallback. -/
theorem frames_source_zero {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (d : PreAbstractSimplicialComplex V) :
    S.frames.getD 0 d = K := by
  cases S <;> rfl

@[simp] theorem pairs_append_length
    {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) :
    (S.append T).pairs.length = S.pairs.length + T.pairs.length := by
  simp only [pairs_append, List.length_append]

end Sequence

/-- Output of realization, not an input to any collapse construction. -/
structure RelativeSDR (K L : PreAbstractSimplicialComplex V) (h : L ≤ K) where
  retraction : C(Space K, Space L)
  retraction_inclusion : ∀ y, retraction (realizationInclusion h y) = y
  homotopy : (ContinuousMap.id (Space K)).HomotopyRel
    ((realizationInclusion h).comp retraction) {x | x.val ∈ realization L}

namespace Sequence

variable {K L : PreAbstractSimplicialComplex V}

/-- Compose the elementary coordinate retractions. The second time segment is
i_P H_tail(t,r_P x); its relative property is proved below on ALL of |L|. -/
def realize (S : Sequence K L) : RelativeSDR K L S.monotone := by
  induction S with
  | refl K =>
      refine ⟨ContinuousMap.id _, fun _ => rfl, ?_⟩
      exact (ContinuousMap.HomotopyRel.refl (ContinuousMap.id _) _).cast rfl
        (by ext x; rfl)
  | @step P L T D =>
      let r := D.retraction.comp P.retraction
      let i := realizationInclusion (T.monotone.trans P.retained_le)
      have hri (y : Space L) : r (i y) = y := by
        change D.retraction (P.retraction
          (P.inclusion (realizationInclusion T.monotone y))) = y
        rw [P.retraction_inclusion]
        exact D.retraction_inclusion y
      let A : (ContinuousMap.id (Space P.ambient)).HomotopyRel
          (P.inclusion.comp P.retraction) {x | x.val ∈ realization L} := {
        toHomotopy := P.collapseHomotopy.toHomotopy
        prop' := by
          intro t x hx
          apply P.collapseHomotopy.eq_fst t
          obtain ⟨s, hs, hxs⟩ := (realization_mem_iff _ _).1 hx
          exact (realization_mem_iff _ _).2 ⟨s, T.monotone hs, hxs⟩ }
      let B : (P.inclusion.comp P.retraction).HomotopyRel (i.comp r)
          {x | x.val ∈ realization L} := {
        toHomotopy :=
          ((ContinuousMap.Homotopy.refl P.inclusion).comp
            (D.homotopy.toHomotopy.compContinuousMap P.retraction)).cast
              (by ext x; rfl) (by ext x; rfl)
        prop' := by
          intro t x hx
          let y : Space L := ⟨x.val, hx⟩
          have hx' : x = P.inclusion (realizationInclusion T.monotone y) :=
            Subtype.ext rfl
          have hr : P.retraction x = realizationInclusion T.monotone y := by
            rw [hx', P.retraction_inclusion]
          change P.inclusion (D.homotopy (t, P.retraction x)) =
            P.inclusion (P.retraction x)
          apply congrArg P.inclusion
          apply D.homotopy.eq_fst t
          rw [hr]
          exact hx }
      exact ⟨r, hri, A.trans B⟩

abbrev inclusion (S : Sequence K L) : C(Space L, Space K) :=
  realizationInclusion S.monotone

def sequenceRetraction (S : Sequence K L) : C(Space K, Space L) := S.realize.retraction

theorem sequenceRetraction_inclusion (S : Sequence K L) (y : Space L) :
    S.sequenceRetraction (S.inclusion y) = y := S.realize.retraction_inclusion y

def collapseHomotopy (S : Sequence K L) :
    (ContinuousMap.id (Space K)).HomotopyRel (S.inclusion.comp S.sequenceRetraction)
      {x | x.val ∈ realization L} := S.realize.homotopy

theorem collapseHomotopy_fixed (S : Sequence K L) (t : I)
    (x : Space K) (hx : x.val ∈ realization L) : S.collapseHomotopy (t, x) = x :=
  S.collapseHomotopy.eq_fst t hx

/-- Inverse is exactly the original-coordinate inclusion. -/
def collapseEquiv (S : Sequence K L) : Space K ≃ₕ Space L where
  toFun := S.sequenceRetraction
  invFun := S.inclusion
  left_inv := ⟨S.collapseHomotopy.toHomotopy.symm⟩
  right_inv := by
    have he : S.sequenceRetraction.comp S.inclusion = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro y
      exact S.sequenceRetraction_inclusion y
    rw [he]

end Sequence

/-- The augmented empty face is data, never an extra point of realization. -/
def AugmentedFace (K : PreAbstractSimplicialComplex V) (s : Finset V) : Prop :=
  s = ∅ ∨ s ∈ K

theorem augmented_downward {K : PreAbstractSimplicialComplex V} {s t : Finset V}
    (hs : AugmentedFace K s) (hts : t ⊆ s) : AugmentedFace K t := by
  by_cases ht : t = ∅
  · exact Or.inl ht
  · right
    rcases hs with rfl | hs
    · exact (ht (Finset.subset_empty.mp hts)).elim
    · exact (K.isRelLowerSet_faces hs).2 hts (Finset.nonempty_iff_ne_empty.mpr ht)

theorem augmented_retained (P : CollapsePair V) (s : Finset V) :
    AugmentedFace P.retained s ↔
      AugmentedFace P.ambient s ∧ ¬ P.lower ⊆ s := by
  constructor
  · rintro (rfl | hs)
    · exact ⟨Or.inl rfl, fun h => P.lower_nonempty.ne_empty
        (Finset.subset_empty.mp h)⟩
    · exact ⟨Or.inr hs.1, hs.2⟩
  · rintro ⟨(rfl | hs), hn⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hs, hn⟩

/-- Freshness means a ghost label on the SAME type, not a new label type. -/
def Fresh (v : V) (K : PreAbstractSimplicialComplex V) : Prop :=
  ∀ s ∈ K, v ∉ s

def deletion (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ v ∉ s}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hv⟩
    exact ⟨(K.isRelLowerSet_faces hs).1, fun t hts ht =>
      ⟨(K.isRelLowerSet_faces hs).2 hts ht, fun h => hv (hts h)⟩⟩

/-- Nonempty link faces only. The missing empty face is restored ONLY in
`AugmentedFace`, when reconstructing the faces containing v. -/
def link (K : PreAbstractSimplicialComplex V) (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ v ∉ s ∧ insert v s ∈ K}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hv, hvs⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, fun h => hv (hts h),
      (K.isRelLowerSet_faces hvs).2 (Finset.insert_subset_insert v hts)
        (Finset.insert_nonempty _ _)⟩

theorem deletion_le (K : PreAbstractSimplicialComplex V) (v : V) :
    deletion K v ≤ K := fun _ hs => hs.1

theorem deletion_fresh (K : PreAbstractSimplicialComplex V) (v : V) :
    Fresh v (deletion K v) := fun _ hs => hs.2

theorem link_le_deletion (K : PreAbstractSimplicialComplex V) (v : V) :
    link K v ≤ deletion K v := by
  intro s hs
  exact ⟨(K.isRelLowerSet_faces hs.2.2).2 (subset_insert _ _) hs.1, hs.2.1⟩

/-- The cone generated by L on the original labels. Apex singleton is present
even for L=bottom; no nonempty face or topological basepoint is added to L. -/
def cone (v : V) (L : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ AugmentedFace L (s.erase v)}
  isRelLowerSet_faces := by
    rintro s ⟨hs, he⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, augmented_downward he (Finset.erase_subset_erase v hts)⟩

@[simp] theorem apex_mem_cone (v : V) (L : PreAbstractSimplicialComplex V) :
    ({v} : Finset V) ∈ cone v L :=
  ⟨Finset.singleton_nonempty _, Or.inl (by simp)⟩

theorem cone_face (v : V) {L : PreAbstractSimplicialComplex V}
    {s : Finset V} (hs : s ∈ cone v L) : insert v s ∈ cone v L := by
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  rw [Finset.erase_insert_eq_erase]
  exact hs.2

theorem base_le_cone (v : V) (L : PreAbstractSimplicialComplex V) : L ≤ cone v L := by
  intro s hs
  exact ⟨(L.isRelLowerSet_faces hs).1,
    augmented_downward (Or.inr hs) (Finset.erase_subset _ _)⟩

theorem cone_mono (v : V) {L M : PreAbstractSimplicialComplex V} (h : L ≤ M) :
    cone v L ≤ cone v M := by
  rintro s ⟨hs, he | he⟩
  · exact ⟨hs, Or.inl he⟩
  · exact ⟨hs, Or.inr (h he)⟩

private theorem subset_erase_of_notMem {v : V} {a s : Finset V}
    (hv : v ∉ a) (h : a ⊆ s) : a ⊆ s.erase v := by
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun he => hv (he ▸ hx), h hx⟩

private theorem insert_subset_iff_erase {v : V} {a s : Finset V}
    (ha : v ∉ a) (hv : v ∈ s) :
    insert v a ⊆ s ↔ a ⊆ s.erase v := by
  constructor
  · intro h
    exact subset_erase_of_notMem ha ((Finset.subset_insert _ _).trans h)
  · intro h
    exact Finset.insert_subset_iff.mpr ⟨hv, h.trans (Finset.erase_subset _ _)⟩

private theorem mem_union_avoiding (D M : PreAbstractSimplicialComplex V)
    (v : V) (hMD : M ≤ D) {s : Finset V} (hv : v ∉ s) :
    s ∈ D ⊔ cone v M ↔ s ∈ D := by
  change (s ∈ D ∨ s ∈ cone v M) ↔ s ∈ D
  constructor
  · rintro (hs | ⟨hn, he⟩)
    · exact hs
    · rw [Finset.erase_eq_of_notMem hv] at he
      rcases he with he | he
      · exact (hn.ne_empty he).elim
      · exact hMD he
  · exact Or.inl

private theorem mem_union_containing (D M : PreAbstractSimplicialComplex V)
    (v : V) (hD : Fresh v D) {s : Finset V} (hv : v ∈ s) :
    s ∈ D ⊔ cone v M ↔ AugmentedFace M (s.erase v) := by
  change (s ∈ D ∨ s ∈ cone v M) ↔ _
  constructor
  · rintro (hs | hs)
    · exact (hD s hs hv).elim
    · exact hs.2
  · exact fun he => Or.inr ⟨⟨v, hv⟩, he⟩

/-- Exact intermediate link, not merely a link of the same homotopy type. -/
theorem link_union_cone (D M : PreAbstractSimplicialComplex V) (v : V)
    (hMD : M ≤ D) (hvD : Fresh v D) : link (D ⊔ cone v M) v = M := by
  apply SetLike.coe_injective
  ext s
  constructor
  · intro hs
    have he := (mem_union_containing D M v hvD
      (Finset.mem_insert_self v s)).mp hs.2.2
    rw [Finset.erase_insert hs.2.1] at he
    rcases he with he | he
    · exact (hs.1.ne_empty he).elim
    · exact he
  · intro hs
    have hv : v ∉ s := hvD s (hMD hs)
    refine ⟨(M.isRelLowerSet_faces hs).1, hv, ?_⟩
    exact (mem_union_containing D M v hvD (Finset.mem_insert_self v s)).mpr
      (by rw [Finset.erase_insert hv]; exact Or.inr hs)

theorem deletion_union_cone (D M : PreAbstractSimplicialComplex V) (v : V)
    (hMD : M ≤ D) (hvD : Fresh v D) : deletion (D ⊔ cone v M) v = D := by
  apply SetLike.coe_injective
  ext s
  constructor
  · intro hs
    exact (mem_union_avoiding D M v hMD hs.2).mp hs.1
  · intro hs
    exact ⟨Or.inl hs, hvD s hs⟩

/-- Reconstruction is exact only when v is an actual vertex of K. Without this
hypothesis a ghost v must NOT be materialized as an extra isolated point. -/
theorem deletion_union_link_cone (K : PreAbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∈ K) : deletion K v ⊔ cone v (link K v) = K := by
  apply le_antisymm
  · rintro s (hs | ⟨hn, he⟩)
    · exact hs.1
    · rcases he with he | he
      · have hsub : s ⊆ ({v} : Finset V) := by
          intro a ha
          by_cases hav : a = v
          · simpa [hav]
          · have : a ∈ s.erase v := Finset.mem_erase.mpr ⟨hav, ha⟩
            simpa [he] using this
        exact (K.isRelLowerSet_faces hv).2 hsub hn
      · exact (K.isRelLowerSet_faces he.2.2).2
          (Finset.insert_erase_subset _ _) hn
  · intro s hs
    by_cases hvs : v ∈ s
    · right
      refine ⟨(K.isRelLowerSet_faces hs).1, ?_⟩
      by_cases he : s.erase v = ∅
      · exact Or.inl he
      · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr he,
          Finset.notMem_erase _ _, by
            change insert v (s.erase v) ∈ K.faces
            simpa only [Finset.insert_erase hvs] using hs⟩
    · exact Or.inl ⟨hs, hvs⟩

namespace Pair

/-- A link free pair lifted over a fixed deletion D. The condition M≤D says
the link base is already in the deletion; both remain on the original labels. -/
def liftPairOver (P : CollapsePair V) (D : PreAbstractSimplicialComplex V) (v : V)
    (hPD : P.ambient ≤ D) (hvD : Fresh v D) : CollapsePair V where
  ambient := D ⊔ cone v P.ambient
  lower := insert v P.lower
  apex := P.apex
  lower_nonempty := Finset.insert_nonempty _ _
  apex_notMem := by
    have hva : v ≠ P.apex := by
      intro he
      apply hvD P.upper (hPD P.upper_mem)
      rw [he]
      exact Finset.mem_insert_self _ _
    simpa only [Finset.mem_insert, not_or] using And.intro (Ne.symm hva) P.apex_notMem
  upper_mem := by
    right
    have hvl : v ∉ P.lower := hvD _ (hPD P.lower_mem)
    have hva : v ≠ P.apex := by
      intro he
      apply hvD P.upper (hPD P.upper_mem)
      rw [he]
      exact Finset.mem_insert_self _ _
    refine ⟨Finset.insert_nonempty _ _, Or.inr ?_⟩
    rw [Finset.erase_insert_of_ne (Ne.symm hva), Finset.erase_insert hvl]
    exact P.upper_mem
  free := by
    intro s hs hstrict
    have hvl : v ∉ P.lower := hvD _ (hPD P.lower_mem)
    have hvs : v ∈ s := hstrict.subset (Finset.mem_insert_self _ _)
    have hlow : P.lower ⊆ s.erase v :=
      (insert_subset_iff_erase hvl hvs).mp hstrict.subset
    have he : AugmentedFace P.ambient (s.erase v) :=
      (mem_union_containing D P.ambient v hvD hvs).mp hs
    have heface : s.erase v ∈ P.ambient := by
      rcases he with he | he
      · exact (P.lower_nonempty.ne_empty (Finset.subset_empty.mp
          (by simpa [he] using hlow))).elim
      · exact he
    have hne : P.lower ≠ s.erase v := by
      intro heq
      apply hstrict.ne
      rw [heq, Finset.insert_erase hvs]
    have hup := P.free _ heface (Finset.ssubset_iff_subset_ne.mpr ⟨hlow, hne⟩)
    calc
      s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
      _ = insert v P.upper := congrArg (insert v) hup
      _ = insert P.apex (insert v P.lower) := by
        exact Finset.insert_comm v P.apex P.lower

theorem liftOver_retained (P : CollapsePair V) (D : PreAbstractSimplicialComplex V)
    (v : V) (hPD : P.ambient ≤ D) (hvD : Fresh v D) :
    (Pair.liftPairOver P D v hPD hvD).retained = D ⊔ cone v P.retained := by
  apply SetLike.coe_injective
  ext s
  have hvl : v ∉ P.lower := hvD _ (hPD P.lower_mem)
  change (s ∈ D ⊔ cone v P.ambient ∧ ¬ insert v P.lower ⊆ s) ↔
    s ∈ D ⊔ cone v P.retained
  by_cases hvs : v ∈ s
  · rw [mem_union_containing D P.ambient v hvD hvs,
      mem_union_containing D P.retained v hvD hvs,
      insert_subset_iff_erase hvl hvs, augmented_retained]
  · rw [mem_union_avoiding D P.ambient v hPD hvs,
      mem_union_avoiding D P.retained v (P.retained_le.trans hPD) hvs]
    exact ⟨fun h => h.1, fun hs => ⟨hs, fun h => hvs
      (h (Finset.mem_insert_self _ _))⟩⟩

/-- Every deletion face survives a lifted pair, not just its vertices. -/
theorem le_liftOver_retained (P : CollapsePair V) (D : PreAbstractSimplicialComplex V)
    (v : V) (hPD : P.ambient ≤ D) (hvD : Fresh v D) :
    D ≤ (Pair.liftPairOver P D v hPD hvD).retained := by
  rw [Pair.liftOver_retained]
  exact le_sup_left

theorem link_liftOver_retained (P : CollapsePair V) (D : PreAbstractSimplicialComplex V)
    (v : V) (hPD : P.ambient ≤ D) (hvD : Fresh v D) :
    link (Pair.liftPairOver P D v hPD hvD).retained v = P.retained := by
  rw [Pair.liftOver_retained]
  exact link_union_cone D P.retained v (P.retained_le.trans hPD) hvD

end Pair

namespace Sequence

/-- Replays the exact link intermediates, adjoining v to both faces at each step. -/
def liftOver {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (D : PreAbstractSimplicialComplex V) (v : V) (hMD : M ≤ D)
    (hvD : Fresh v D) : Sequence (D ⊔ cone v M) (D ⊔ cone v N) := by
  revert hMD
  induction S with
  | refl M => intro hMD; exact .refl _
  | @step P N T ih =>
      intro hMD
      let Q := Pair.liftPairOver P D v hMD hvD
      have htail := ih (P.retained_le.trans hMD)
      have htail' : Sequence Q.retained (D ⊔ cone v N) :=
        htail.cast (Pair.liftOver_retained P D v hMD hvD).symm rfl
      exact .step Q htail'

theorem pairs_liftOver_length
    {M N D : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (v : V) (hMD : M ≤ D) (hvD : Fresh v D) :
    (S.liftOver D v hMD hvD).pairs.length = S.pairs.length := by
  induction S generalizing D with
  | refl M => rfl
  | @step P N T ih =>
      simp only [Sequence.liftOver, Sequence.pairs, Sequence.pairs_cast,
        List.length_cons]
      exact congrArg Nat.succ (ih (P.retained_le.trans hMD) hvD)

theorem pairs_liftOver_forall2
    {M N D : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (v : V) (hMD : M ≤ D) (hvD : Fresh v D) :
    List.Forall₂
      (fun P Q => ∃ (hQD : Q.ambient ≤ D) (hvD' : Fresh v D),
        P = Pair.liftPairOver Q D v hQD hvD')
      (S.liftOver D v hMD hvD).pairs S.pairs := by
  induction S generalizing D with
  | refl M => simp [Sequence.liftOver, Sequence.pairs]
  | @step P N T ih =>
      simp only [Sequence.liftOver, Sequence.pairs, Sequence.pairs_cast, List.forall₂_cons]
      refine ⟨?_, ih (P.retained_le.trans hMD) hvD⟩
      exact ⟨hMD, hvD, trivial⟩

theorem frames_liftOver
    {M N D : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (v : V) (hMD : M ≤ D) (hvD : Fresh v D) :
    frames (S.liftOver D v hMD hvD) =
      (frames S).map (fun L => D ⊔ cone v L) := by
  induction S generalizing D with
  | refl M => rfl
  | @step P N T ih =>
      simp only [Sequence.liftOver, Sequence.frames, Sequence.frames_cast, List.map_cons]
      exact congrArg (List.cons _) (ih (P.retained_le.trans hMD) hvD)

theorem frames_liftOver_getD
    {M N D : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (v : V) (hMD : M ≤ D) (hvD : Fresh v D) (i : Nat) :
    (S.liftOver D v hMD hvD).frames.getD i (D ⊔ cone v M) =
      D ⊔ cone v (S.frames.getD i M) := by
  rw [frames_liftOver]
  exact List.getD_map S.frames M (fun L => D ⊔ cone v L)

private theorem frames_append_getD_lt_aux
    {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) (d : PreAbstractSimplicialComplex V)
    {i : Nat} (hi : i < S.pairs.length + 1) :
    (S.append T).frames.getD i d = S.frames.getD i d := by
  induction S generalizing i with
  | refl K =>
      have hi0 : i = 0 := by simpa only [pairs, List.length_nil, zero_add,
        Nat.lt_one_iff] using hi
      subst i
      exact frames_source_zero T d
  | @step P L S ih =>
      cases i with
      | zero => rfl
      | succ i =>
          apply ih
          simpa only [pairs, List.length_cons, Nat.succ_add,
            Nat.succ_lt_succ_iff] using hi

theorem frames_append_getD_lt
    {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) {i : Nat}
    (hi : i < S.pairs.length + 1) :
    (S.append T).frames.getD i K = S.frames.getD i K :=
  frames_append_getD_lt_aux S T K hi

end Sequence

/-- At terminal link {w}, the only v-faces are {v} and {v,w}. -/
def terminalPair (D : PreAbstractSimplicialComplex V) (v w : V)
    (hvD : Fresh v D) (hvw : v ≠ w) (hwD : ({w} : Finset V) ∈ D) :
    CollapsePair V where
  ambient := D ⊔ cone v (vertexComplex w)
  lower := {v}
  apex := w
  lower_nonempty := Finset.singleton_nonempty _
  apex_notMem := by simpa using Ne.symm hvw
  upper_mem := by
    right
    refine ⟨Finset.insert_nonempty _ _, Or.inr ?_⟩
    rw [Finset.erase_insert_of_ne (Ne.symm hvw), Finset.erase_singleton]
    rfl
  free := by
    intro s hs hstrict
    have hvs : v ∈ s := hstrict.subset (Finset.mem_singleton_self _)
    have he := (mem_union_containing D (vertexComplex w) v hvD hvs).mp hs
    rcases he with he | he
    · have hs' : s = {v} := by
        rw [← Finset.insert_erase hvs, he]
        simp
      exact (hstrict.ne hs'.symm).elim
    · change s.erase v = {w} at he
      rw [← Finset.insert_erase hvs, he]
      exact Finset.insert_comm v w ∅

theorem terminalPair_retained (D : PreAbstractSimplicialComplex V) (v w : V)
    (hvD : Fresh v D) (hvw : v ≠ w) (hwD : ({w} : Finset V) ∈ D) :
    (terminalPair D v w hvD hvw hwD).retained = D := by
  apply SetLike.coe_injective
  ext s
  change (s ∈ D ⊔ cone v (vertexComplex w) ∧ ¬ ({v} : Finset V) ⊆ s) ↔ s ∈ D
  constructor
  · rintro ⟨hs, hn⟩
    have hvs : v ∉ s := fun h => hn (Finset.singleton_subset_iff.mpr h)
    exact (mem_union_avoiding D (vertexComplex w) v
      (fun (t : Finset V) (ht : t ∈ vertexComplex w) => by
        change t = {w} at ht
        rw [ht]
        exact hwD) hvs).mp hs
  · intro hs
    exact ⟨Or.inl hs, fun h => hvD s hs (h (Finset.mem_singleton_self _))⟩

/-- Genuine collapse onto exact deletion, from a combinatorial link collapse to
an actual vertex. v≠w and the relevant edge are DERIVED, not assumed away. -/
def linkCollapseDeletion (K : PreAbstractSimplicialComplex V) (v w : V)
    (S : Sequence (link K v) (vertexComplex w)) : Sequence K (deletion K v) := by
  have hw : ({w} : Finset V) ∈ link K v := S.monotone rfl
  have hvw : v ≠ w := by simpa using hw.2.1
  have hv : ({v} : Finset V) ∈ K :=
    (K.isRelLowerSet_faces hw.2.2).2
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_nonempty _)
  let D := deletion K v
  have hwD : ({w} : Finset V) ∈ D := link_le_deletion K v hw
  let Q := terminalPair D v w (deletion_fresh K v) hvw hwD
  have last : Sequence Q.ambient D :=
    (Sequence.step Q (Sequence.refl Q.retained)).cast rfl
      (terminalPair_retained D v w (deletion_fresh K v) hvw hwD)
  have lifted := S.liftOver D v (link_le_deletion K v) (deletion_fresh K v)
  exact (lifted.append last).cast (deletion_union_link_cone K v hv) rfl

/-- Its inclusion is the actual coordinate inclusion and its homotopy fixes all
of the deletion, including disconnected components and faces with ghost labels. -/
def linkDeletionSDR (K : PreAbstractSimplicialComplex V) (v w : V)
    (S : Sequence (link K v) (vertexComplex w)) :
    RelativeSDR K (deletion K v) (deletion_le K v) :=
  (linkCollapseDeletion K v w S).realize

namespace Pair

/-- The key obstruction to a new coface: a lower face inside any cone face
would be a retained L-face, contradicting its removal. -/
theorem lower_not_subset_cone (P : CollapsePair V) (L : PreAbstractSimplicialComplex V)
    (v : V) (hL : L ≤ P.retained) (hv : Fresh v P.ambient)
    {s : Finset V} (hs : s ∈ cone v L) : ¬ P.lower ⊆ s := by
  intro hls
  have hvl : v ∉ P.lower := hv _ P.lower_mem
  have hle : P.lower ⊆ s.erase v := subset_erase_of_notMem hvl hls
  rcases hs.2 with he | he
  · exact P.lower_nonempty.ne_empty (Finset.subset_empty.mp (by simpa [he] using hle))
  · have hlL : P.lower ∈ L := (L.isRelLowerSet_faces he).2 hle P.lower_nonempty
    exact (hL hlL).2 (Finset.Subset.refl _)

/-- SAME lower and upper free pair after adjoining the retained cone. -/
def extendCone (P : CollapsePair V) (L : PreAbstractSimplicialComplex V) (v : V)
    (hL : L ≤ P.retained) (hv : Fresh v P.ambient) : CollapsePair V where
  ambient := P.ambient ⊔ cone v L
  lower := P.lower
  apex := P.apex
  lower_nonempty := P.lower_nonempty
  apex_notMem := P.apex_notMem
  upper_mem := Or.inl P.upper_mem
  free := by
    intro s hs hlt
    rcases hs with hs | hs
    · exact P.free s hs hlt
    · exact (Pair.lower_not_subset_cone P L v hL hv hs hlt.subset).elim

theorem extendCone_retained (P : CollapsePair V) (L : PreAbstractSimplicialComplex V)
    (v : V) (hL : L ≤ P.retained) (hv : Fresh v P.ambient) :
    (Pair.extendCone P L v hL hv).retained = P.retained ⊔ cone v L := by
  apply SetLike.coe_injective
  ext s
  change ((s ∈ P.ambient ∨ s ∈ cone v L) ∧ ¬ P.lower ⊆ s) ↔
    ((s ∈ P.ambient ∧ ¬ P.lower ⊆ s) ∨ s ∈ cone v L)
  constructor
  · rintro ⟨(hs | hs), hn⟩
    · exact Or.inl ⟨hs, hn⟩
    · exact Or.inr hs
  · rintro (⟨hs, hn⟩ | hs)
    · exact ⟨Or.inl hs, hn⟩
    · exact ⟨Or.inr hs, Pair.lower_not_subset_cone P L v hL hv hs⟩

end Pair

namespace Sequence

/-- A finite collapse extends over a cone on its retained complex. Each step
has the original lower/apex; its exact retained complex includes the ENTIRE cone. -/
def extendAcrossCone {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (v : V) (hv : Fresh v K) : Sequence (K ⊔ cone v L) (cone v L) := by
  revert hv
  induction S with
  | refl K =>
      intro hv
      rw [sup_eq_right.mpr (base_le_cone v K)]
      exact .refl _
  | @step P L T ih =>
      intro hv
      let Q := Pair.extendCone P L v T.monotone hv
      have hv' : Fresh v P.retained := fun s hs => hv s hs.1
      have htail := ih hv'
      have htail' : Sequence Q.retained (cone v L) :=
        htail.cast (Pair.extendCone_retained P L v T.monotone hv).symm rfl
      exact .step Q htail'

/-- Relative SDR onto the full actual cone; no point of that cone moves during
this collapse. This does not assert that its subsequent contraction fixes it. -/
def coneExtensionSDR {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (v : V) (hv : Fresh v K) :
    RelativeSDR (K ⊔ cone v L) (cone v L) le_sup_right :=
  (S.extendAcrossCone v hv).realize

end Sequence

/-- Use the existing actual cone/apex coordinate owner. -/
def selfConePair (v : V) (L : PreAbstractSimplicialComplex V) : ConePair V where
  ambient := cone v L
  cone := cone v L
  inclusion := le_rfl
  apex := v
  apex_face := apex_mem_cone v L
  cone_face := fun s hs => cone_face v hs

def conePoint (v : V) (L : PreAbstractSimplicialComplex V) : Space (cone v L) :=
  (selfConePair v L).apexPoint

/-- Contract to the existing actual apex using the original owner cone-segment
proof from the frozen owner bundle; the relative fixed set is the apex. -/
def coneContraction (v : V) (L : PreAbstractSimplicialComplex V) :
    (ContinuousMap.id (Space (cone v L))).HomotopyRel
      (ContinuousMap.const _ (conePoint v L)) {conePoint v L} where
  toHomotopy := straight _ _ (by
    intro t x
    change mix (t : ℝ) x.val (conePoint v L).val ∈ realization (cone v L)
    change (fun a => (1 - (t : ℝ)) * x.val a + (t : ℝ) *
      (selfConePair v L).apexPoint.val a) ∈ realization (selfConePair v L).cone
    exact (selfConePair v L).cone_segment x x.property (t : ℝ) t.2.1 t.2.2)
  prop' := by
    intro t x hx
    have he : x = conePoint v L := Set.mem_singleton_iff.mp hx
    subst x
    apply Subtype.ext
    funext a
    change mix t (conePoint v L).val (conePoint v L).val a = (conePoint v L).val a
    dsimp only [mix]
    ring

namespace Sequence

/-- Consequent contraction of the original union to the actual apex. Both
segments are retained on the actual included apex: the first segment is the
relative SDR on the whole cone, and the second segment uses the original
coneContraction relative to its singleton apex. No null map, contractibility,
retraction, or homotopy is an input. -/
def coneExtensionContraction {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (v : V) (hv : Fresh v K) :
    (ContinuousMap.id (Space (K ⊔ cone v L))).HomotopyRel
      (ContinuousMap.const _
        (realizationInclusion (show cone v L ≤ K ⊔ cone v L from le_sup_right)
          (conePoint v L)))
      {realizationInclusion (show cone v L ≤ K ⊔ cone v L from le_sup_right)
        (conePoint v L)} := by
  let T := S.extendAcrossCone v hv
  let D := T.realize
  let i := realizationInclusion T.monotone
  let A : (ContinuousMap.id (Space (K ⊔ cone v L))).HomotopyRel
      (i.comp D.retraction) {i (conePoint v L)} := {
    toHomotopy := D.homotopy.toHomotopy
    prop' := by
      intro t x hx
      have hx' : x = i (conePoint v L) := Set.mem_singleton_iff.mp hx
      subst x
      exact D.homotopy.eq_fst t (conePoint v L).property }
  let B : (i.comp D.retraction).HomotopyRel
      (i.comp (ContinuousMap.const _ (conePoint v L)))
      {i (conePoint v L)} := {
    toHomotopy := ((ContinuousMap.Homotopy.refl i).comp
      ((coneContraction v L).toHomotopy.compContinuousMap D.retraction)).cast
        (by ext x; rfl) (by ext x; rfl)
    prop' := by
      intro t x hx
      have hx' : x = i (conePoint v L) := Set.mem_singleton_iff.mp hx
      subst x
      have hr : D.retraction (i (conePoint v L)) = conePoint v L := by
        exact D.retraction_inclusion _
      change i ((coneContraction v L) (t,
        D.retraction (i (conePoint v L)))) =
        i (D.retraction (i (conePoint v L)))
      rw [hr]
      exact congrArg i ((coneContraction v L).eq_fst t
        (by simp)) }
  exact (A.trans B).cast (by ext x; rfl) (by ext x; rfl)

end Sequence

end D5.S3.Geometry.FiniteRelativeSimplicialCollapse

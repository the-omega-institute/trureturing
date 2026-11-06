/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Native
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Native
   mirror-E: none(waiver:original-label-two-sum-native)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Descending finite fibres emit existing native free pairs with exact evolving endpoints and ordered coverage. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Raw
import Mathlib.Data.List.Sort

/-! UNCOMPILED. All collapse data below are the existing CollapsePair/Sequence.
There is no simulated homotopy, matching theorem, or second pair datatype. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Set Finset
open scoped unitInterval ContinuousMap
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteConeCollapse FiniteSimplicialJoin
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing upper ideals is always downward closed; freeness is proved before
using it as the retained complex of an ordinary pair. -/
def cut (K : Family V) (lowers : Finset (Finset V)) : Family V where
  carrier := {s | s ∈ K ∧ ∀ a ∈ lowers, ¬ a ⊆ s}
  lower' := by
    rintro s t h ⟨hs,hnot⟩
    exact ⟨K.lower h hs,fun a ha hat => hnot a ha (hat.trans h)⟩

@[simp] theorem cut_empty (K : Family V) : cut K ∅ = K := by
  apply SetLike.ext; intro s; simp [cut]

@[simp] theorem cut_cut (K : Family V) (a b : Finset (Finset V)) :
    cut (cut K a) b = cut K (a ∪ b) := by
  apply SetLike.ext
  intro s
  change ((s ∈ K ∧ ∀ q ∈ a, ¬q ⊆ s) ∧ ∀ q ∈ b, ¬q ⊆ s) ↔
    s ∈ K ∧ ∀ q ∈ a ∪ b, ¬q ⊆ s
  simp only [Finset.mem_union]
  aesop

/-- Populate the actual native pair, using the whole current raw family. -/
def emitPair (K : Family V) (a : Finset V) (v : V) (ha : a.Nonempty)
    (hv : v ∉ a) (hu : insert v a ∈ K)
    (hf : ∀ s ∈ K, a ⊆ s → s = a ∨ s = insert v a) : CollapsePair V where
  ambient := project K
  lower := a
  apex := v
  lower_nonempty := ha
  apex_notMem := hv
  upper_mem := ⟨ha.mono (Finset.subset_insert _ _),hu⟩
  free := by
    intro s hs hsub
    exact (hf s hs.2 hsub.1).resolve_left
      (fun he => hsub.ne he.symm)

/-- The equality is literal deletion of the upper ideal of the lower face. -/
theorem emitPair_retained (K : Family V) (a : Finset V) (v : V)
    (ha : a.Nonempty) (hv : v ∉ a) (hu : insert v a ∈ K)
    (hf : ∀ s ∈ K, a ⊆ s → s = a ∨ s = insert v a) :
    (emitPair K a v ha hv hu hf).retained = project (cut K {a}) := by
  ext s
  change (s.Nonempty ∧ s ∈ K) ∧ ¬ a ⊆ s ↔
    s.Nonempty ∧ s ∈ K ∧ ∀ b ∈ ({a} : Finset (Finset V)), ¬ b ⊆ s
  simp only [Finset.mem_singleton, forall_eq]
  tauto

/-- Label-order tie break. The finite enumeration is fixed once per ambient
Fintype instance; cardinality is always the primary comparison. -/
def fibreBefore (a b : Finset V) : Prop :=
  b.card < a.card ∨ a.card = b.card ∧
    (Fintype.equivFin (Finset V) a).val ≤ (Fintype.equivFin (Finset V) b).val

private instance fibreBeforeTotal : Std.Total (fibreBefore (V := V)) :=
  ⟨by intro a b; unfold fibreBefore; omega⟩
private instance fibreBeforeTrans : IsTrans (Finset V) (fibreBefore (V := V)) :=
  ⟨by intro a b c; unfold fibreBefore; omega⟩

/-- Actual terminating merge-sort, not an assumed fibre schedule. -/
def fibres (F : Finset (Finset V)) : List (Finset V) := by
  classical
  exact F.toList.mergeSort (fun a b => fibreBefore a b)

theorem fibres_spec (F : Finset (Finset V)) :
    (fibres F).Nodup ∧ (fibres F).toFinset = F ∧
      (fibres F).Pairwise (fun a b => b.card ≤ a.card) := by
  classical
  have hp : List.Perm (fibres F) F.toList := List.mergeSort_perm _ _
  refine ⟨hp.nodup_iff.mpr F.nodup_toList, ?_, ?_⟩
  · ext s
    simpa only [List.mem_toFinset, Finset.mem_toList] using hp.mem_iff
  · exact (List.pairwise_mergeSort' (fibreBefore (V := V)) F.toList).imp
      (by intro a b h; unfold fibreBefore at h; omega)

/-- The empty projected lower is permitted only when the right fibre supplies
an actual vertex. This condition is checked on each emitted parent lower. -/
private theorem union_nonempty_right {a t : Finset V} (ht : t.Nonempty) :
    (a ∪ t).Nonempty := ht.mono Finset.subset_union_right

private theorem union_left_injective {X Y a t u : Finset V}
    (hXY : Disjoint X Y) (ha : a ⊆ X) (ht : t ⊆ Y) (hu : u ⊆ Y)
    (h : a ∪ t ⊆ a ∪ u) : t ⊆ u := by
  intro v hv
  rcases Finset.mem_union.mp (h (Finset.mem_union_right _ hv)) with hv' | hv'
  · exact False.elim (Finset.disjoint_left.mp hXY (ha hv') (ht hv))
  · exact hv'

/-- Generic rectangle construction. The coface premise refers only to faces of
its SOURCE, not to a desired collapse or endpoint. It says that every coface of
a lower fibre has one of the two original left parts and a listed right part.
The output endpoint, all current pairs, and their order are then constructed. -/
private def rectangleAux (X Y a : Finset V) (v : V)
    (hXY : Disjoint X Y) (haX : a ⊆ X) (hvX : v ∈ X) (hva : v ∉ a)
    (todo : List (Finset V)) (hnodup : todo.Nodup)
    (horder : todo.Pairwise (fun s t => t.card ≤ s.card))
    (K : Family V)
    (hsupport : ∀ t ∈ todo, t ⊆ Y)
    (hne : ∀ t ∈ todo, (a ∪ t).Nonempty)
    (hmem : ∀ t ∈ todo, a ∪ t ∈ K ∧ insert v (a ∪ t) ∈ K)
    (hcoface : ∀ t ∈ todo, ∀ s ∈ K, a ∪ t ⊆ s →
      ∃ u ∈ todo, t ⊆ u ∧ (s = a ∪ u ∨ s = insert v (a ∪ u))) :
    {S : Sequence (project K) (project (cut K (todo.map (fun t => a ∪ t)).toFinset)) //
      S.pairs.map (fun P => (P.lower,P.upper)) =
        todo.map (fun t => (a ∪ t,insert v (a ∪ t)))} := by
  classical
  cases todo with
  | nil => exact ⟨(Sequence.refl (project K)).cast rfl (by simp), by simp [Sequence.pairs_cast,Sequence.pairs]⟩
  | cons t ts =>
    have hord := List.pairwise_cons.mp horder
    have hn := List.nodup_cons.mp hnodup
    have htY := hsupport t (by simp)
    have hvt : v ∉ a ∪ t := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hva,fun hv => Finset.disjoint_left.mp hXY hvX (htY hv)⟩
    have hf : ∀ s ∈ K, a ∪ t ⊆ s →
        s = a ∪ t ∨ s = insert v (a ∪ t) := by
      intro s hs has
      obtain ⟨u,hu,htu,he⟩ := hcoface t (by simp) s hs has
      have hut : u = t := by
        rcases List.mem_cons.mp hu with rfl | hu
        · rfl
        · exact Finset.eq_of_subset_of_card_le htu (hord.1 u hu) |>.symm
      simpa [hut] using he
    let P := emitPair K (a ∪ t) v (hne t (by simp)) hvt
      (hmem t (by simp)).2 hf
    have htailmem : ∀ u ∈ ts,
        a ∪ u ∈ cut K {a ∪ t} ∧ insert v (a ∪ u) ∈ cut K {a ∪ t} := by
      intro u hu
      have hunion : ¬ a ∪ t ⊆ a ∪ u := by
        intro h
        have htu := union_left_injective hXY haX htY (hsupport u (by simp [hu])) h
        have he : t = u := Finset.eq_of_subset_of_card_le htu (hord.1 u hu)
        exact hn.1 (he.symm ▸ hu)
      have hupper : ¬ a ∪ t ⊆ insert v (a ∪ u) := by
        intro h
        apply hunion
        intro w hw
        have hwv : w ≠ v := by
          intro he
          subst w
          exact hvt hw
        exact (Finset.mem_insert.mp (h hw)).resolve_left hwv
      exact ⟨⟨(hmem u (by simp [hu])).1,by simpa using hunion⟩,
        ⟨(hmem u (by simp [hu])).2,by simpa using hupper⟩⟩
    have htailcoface : ∀ u ∈ ts, ∀ s ∈ cut K {a ∪ t}, a ∪ u ⊆ s →
        ∃ w ∈ ts, u ⊆ w ∧ (s = a ∪ w ∨ s = insert v (a ∪ w)) := by
      intro u hu s hs has
      obtain ⟨w,hw,huw,he⟩ := hcoface u (by simp [hu]) s hs.1 has
      rcases List.mem_cons.mp hw with hwt | hw
      · have hab : a ∪ t ⊆ s := by
          rcases he with hes | hes
          · rw [hes, hwt]
          · rw [hes, hwt]
            exact Finset.subset_insert _ _
        exact False.elim (hs.2 _ (by simp) hab)
      · exact ⟨w,hw,huw,he⟩
    let T := rectangleAux X Y a v hXY haX hvX hva ts hn.2 hord.2
      (cut K {a ∪ t}) (fun u hu => hsupport u (by simp [hu]))
      (fun u hu => hne u (by simp [hu])) htailmem htailcoface
    refine ⟨(Sequence.step P (T.1.cast
      (emitPair_retained K (a ∪ t) v (hne t (by simp)) hvt
        (hmem t (by simp)).2 hf).symm rfl)).cast rfl (by
          simp only [List.map_cons, List.toFinset_cons]
          rw [cut_cut]
          congr 2), ?_⟩
    simpa only [Sequence.pairs_cast,Sequence.pairs,List.map_cons,emitPair,CollapsePair.upper]
      using congrArg (List.cons (a ∪ t,insert v (a ∪ t))) T.2
termination_by todo.length

/-- Public rectangle endpoint and genuine ordered native list. -/
def rectangle (X Y a : Finset V) (v : V)
    (hXY : Disjoint X Y) (haX : a ⊆ X) (hvX : v ∈ X) (hva : v ∉ a)
    (F : Finset (Finset V)) (K : Family V)
    (hsupport : ∀ t ∈ F, t ⊆ Y)
    (hne : ∀ t ∈ F, (a ∪ t).Nonempty)
    (hmem : ∀ t ∈ F, a ∪ t ∈ K ∧ insert v (a ∪ t) ∈ K)
    (hcoface : ∀ t ∈ F, ∀ s ∈ K, a ∪ t ⊆ s →
      ∃ u ∈ F, t ⊆ u ∧ (s = a ∪ u ∨ s = insert v (a ∪ u))) :
    Sequence (project K) (project (cut K (F.image (fun t => a ∪ t)))) := by
  classical
  have hh := fibres_spec F
  have hm (t) : t ∈ fibres F ↔ t ∈ F := by
    simpa only [hh.2.1] using
      (show t ∈ fibres F ↔ t ∈ (fibres F).toFinset from List.mem_toFinset.symm)
  exact (rectangleAux X Y a v hXY haX hvX hva (fibres F) hh.1 hh.2.2 K
    (fun t ht => hsupport t ((hm t).mp ht))
    (fun t ht => hne t ((hm t).mp ht))
    (fun t ht => hmem t ((hm t).mp ht))
    (by
      intro t ht s hs has
      obtain ⟨u,hu,htu,he⟩ := hcoface t ((hm t).mp ht) s hs has
      exact ⟨u,(hm u).mpr hu,htu,he⟩)).1.cast rfl (by
        congr 2
        ext t
        simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
        exact ⟨fun ⟨u,hu,he⟩ => ⟨u,(hm u).mp hu,he⟩,
          fun ⟨u,hu,he⟩ => ⟨u,(hm u).mpr hu,he⟩⟩)

/-- The list statement refers to the real pair extraction, and contains no
external pair schedule assumption. -/
theorem rectangle_order (X Y a : Finset V) (v : V)
    (hXY : Disjoint X Y) (haX : a ⊆ X) (hvX : v ∈ X) (hva : v ∉ a)
    (F : Finset (Finset V)) (K : Family V)
    (hsupport : ∀ t ∈ F, t ⊆ Y) (hne : ∀ t ∈ F, (a ∪ t).Nonempty)
    (hmem : ∀ t ∈ F, a ∪ t ∈ K ∧ insert v (a ∪ t) ∈ K)
    (hc : ∀ t ∈ F, ∀ s ∈ K, a ∪ t ⊆ s →
      ∃ u ∈ F, t ⊆ u ∧ (s = a ∪ u ∨ s = insert v (a ∪ u))) :
    ((rectangle X Y a v hXY haX hvX hva F K hsupport hne hmem hc).pairs.map
      (fun P => (P.lower,P.upper))) =
        (fibres F).map (fun t => (a ∪ t,insert v (a ∪ t))) := by
  classical
  unfold rectangle
  rw [Sequence.pairs_cast]
  have hm (t) : t ∈ fibres F ↔ t ∈ F := by
    simpa only [(fibres_spec F).2.1] using
      (show t ∈ fibres F ↔ t ∈ (fibres F).toFinset from List.mem_toFinset.symm)
  exact (rectangleAux X Y a v hXY haX hvX hva (fibres F)
    (fibres_spec F).1 (fibres_spec F).2.2 K
    (fun t ht => hsupport t ((hm t).mp ht))
    (fun t ht => hne t ((hm t).mp ht))
    (fun t ht => hmem t ((hm t).mp ht))
    (by
      intro t ht s hs has
      obtain ⟨u,hu,htu,he⟩ := hc t ((hm t).mp ht) s hs has
      exact ⟨u,(hm u).mpr hu,htu,he⟩)).2

/-- Fixed coordinate consequence of the EXISTING Sequence homotopy. -/
theorem cut_fixed (K : Family V) (A : Finset (Finset V))
    (S : Sequence (project K) (project (cut K A))) (t : unitInterval)
    (x : Space (project K)) (hx : x.val ∈ realization (project (cut K A)))
    (v : V) : (S.collapseHomotopy (t,x)).val v = x.val v := by
  exact congrArg (fun z : Space (project K) => z.val v)
    (S.collapseHomotopy_fixed t x hx)

end D5.S3.Geometry.OriginalLabelTwoSum

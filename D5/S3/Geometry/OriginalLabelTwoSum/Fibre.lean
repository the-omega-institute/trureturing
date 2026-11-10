/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Fibre
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Fibre
   mirror-E: none(waiver:original-label-two-sum-fibre)
   anchors: [mathlib/module/Mathlib.Data.List.Forall2]
   utility: none
   digest: Native local sequences lift over literal fixed fibres using the existing coordinate homotopy. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates

/-! UNCOMPILED. The non-VOID hypothesis is explicit whenever the existing
AugmentedFace predicate reconstructs a raw family. This file never reconstructs
VOID by adjoining empty. All moves remain the existing ordinary native pairs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem aug_mono {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    nativeAug K ≤ nativeAug L := by
  intro s hs
  exact hs.elim Or.inl (fun hs => Or.inr (h hs))

private def fibreFrame (B : Family V) (a : Finset V)
    (M : PreAbstractSimplicialComplex V) : PreAbstractSimplicialComplex V :=
  project (B ⊔ rawJoin (delta a) (nativeAug M))

private theorem fibre_split {a Y x t s : Finset V} (h : Disjoint a Y)
    (hx : x ⊆ a) (ht : t ⊆ Y) (hs : a ∪ s ⊆ x ∪ t) (hsY : s ⊆ Y) :
    x = a ∧ s ⊆ t := by
  constructor
  · apply Finset.Subset.antisymm hx
    intro v hv
    rcases Finset.mem_union.mp (hs (Finset.mem_union_left _ hv)) with hvx | hvt
    · exact hvx
    · exact False.elim (Finset.disjoint_left.mp h hv (ht hvt))
  · intro v hv
    rcases Finset.mem_union.mp (hs (Finset.mem_union_right _ hv)) with hvx | hvt
    · exact False.elim (Finset.disjoint_left.mp h (hx hvx) (hsY hv))
    · exact hvt

/-- Local pair lift. `hboundary` concerns the original source, and `hbase`
identifies the base's fibre intersection. Neither premise supplies an output
collapse, output collar, or desired parent endpoint. -/
private def fibrePair (P : CollapsePair V) (B A : Family V) (a Y : Finset V)
    (hdisj : Disjoint a Y)
    (hY : ∀ s ∈ P.ambient, s ⊆ Y)
    (hboundary : ∀ x ⊂ a, ∀ t ∈ nativeAug P.ambient, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ A)
    (hA : project A ≤ P.retained) : CollapsePair V := by
  have hlY := hY P.lower P.lower_mem
  have huY := hY P.upper P.upper_mem
  have hnot : P.lower ∉ A := by
    intro ha
    have hh := hA ⟨P.lower_nonempty,ha⟩
    exact hh.2 le_rfl
  refine emitPair (B ⊔ rawJoin (delta a) (nativeAug P.ambient))
    (a ∪ P.lower) P.apex (P.lower_nonempty.mono Finset.subset_union_right) ?_ ?_ ?_
  · simp only [Finset.mem_union,not_or]
    exact ⟨fun hv => Finset.disjoint_left.mp hdisj hv
      (huY (Finset.mem_insert_self _ _)),P.apex_notMem⟩
  · right
    refine ⟨a,(by change a ⊆ a; exact le_rfl),P.upper,Or.inr P.upper_mem,?_⟩
    ext v
    simp only [Finset.mem_insert,Finset.mem_union]
    tauto
  · intro s hs hls
    rcases hs with hs | ⟨x,hx,t,ht,rfl⟩
    · exact False.elim (hnot (hbase P.lower hlY (B.lower hls hs)))
    · have htY : t ⊆ Y := ht.elim (fun he => he.symm ▸ Finset.empty_subset Y) (hY t)
      obtain ⟨rfl,hl⟩ := fibre_split hdisj hx htY hls hlY
      have htne : t.Nonempty := P.lower_nonempty.mono hl
      have htP : t ∈ P.ambient := ht.resolve_left
        (fun he => Finset.not_nonempty_empty (he ▸ htne))
      have he : t = P.lower ∨ t = P.upper := by
        by_cases he : t = P.lower
        · exact Or.inl he
        · exact Or.inr (P.free t htP
            (Finset.ssubset_iff_subset_ne.mpr ⟨hl,Ne.symm he⟩))
      rcases he with rfl | rfl
      · exact Or.inl rfl
      · right
        ext v
        simp only [CollapsePair.upper,Finset.mem_union,Finset.mem_insert]
        tauto

private theorem fibrePair_retained (P : CollapsePair V) (B A : Family V)
    (a Y : Finset V) (hd : Disjoint a Y)
    (hY : ∀ s ∈ P.ambient, s ⊆ Y)
    (hb : ∀ x ⊂ a, ∀ t ∈ nativeAug P.ambient, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ A)
    (hA : project A ≤ P.retained) :
    (fibrePair P B A a Y hd hY hb hbase hA).retained = fibreFrame B a P.retained := by
  rw [fibrePair,emitPair_retained]
  ext s
  simp only [mem_project, cut, LowerSet.mem_mk, Set.mem_setOf_eq,
    Finset.mem_singleton, forall_eq]
  change (s.Nonempty ∧ ((s ∈ B ∨ s ∈ rawJoin (delta a) (nativeAug P.ambient)) ∧
    ¬ a ∪ P.lower ⊆ s)) ↔
      s.Nonempty ∧ (s ∈ B ∨ s ∈ rawJoin (delta a) (nativeAug P.retained))
  have hlow : P.lower ∉ A := by
    intro hl
    exact (hA ⟨P.lower_nonempty,hl⟩).2 le_rfl
  constructor
  · rintro ⟨hn,(hB | ⟨x,hx,t,ht,rfl⟩),hnot⟩
    · exact ⟨hn,Or.inl hB⟩
    · by_cases hxa : x = a
      · subst x
        refine ⟨hn,Or.inr ⟨a,(by change a ⊆ a; exact le_rfl),t,?_,rfl⟩⟩
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · right
          exact ⟨ht,fun hl => hnot (Finset.union_subset_union le_rfl hl)⟩
      · exact ⟨hn,Or.inl (hb x
          (Finset.ssubset_iff_subset_ne.mpr ⟨hx,hxa⟩) t ht)⟩
  · rintro ⟨hn,hB | ⟨x,hx,t,ht,rfl⟩⟩
    · refine ⟨hn,Or.inl hB,?_⟩
      intro hl
      exact hlow (hbase P.lower (hY _ P.lower_mem) (B.lower hl hB))
    · refine ⟨hn,Or.inr ⟨x,hx,t,(aug_mono P.retained_le ht),rfl⟩,?_⟩
      intro hl
      have htY : t ⊆ Y := ht.elim (fun he => he.symm ▸ Finset.empty_subset Y)
        (fun ht => hY t ht.1)
      obtain ⟨hxa,hlt⟩ := fibre_split hd hx htY hl (hY _ P.lower_mem)
      rcases ht with rfl | ht
      · exact Finset.not_nonempty_empty (P.lower_nonempty.mono hlt)
      · exact ht.2 hlt

/-- Recursive lift of an ACTUAL local Sequence. Its fixed base is included in
every current retained complex. The endpoint is built, rather than assumed. -/
private def fibreSequence {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (B A : Family V) (a Y : Finset V) (hd : Disjoint a Y)
    (hY : ∀ s ∈ M, s ⊆ Y)
    (hb : ∀ x ⊂ a, ∀ t ∈ nativeAug M, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ A)
    (hA : project A ≤ N) : Sequence (fibreFrame B a M) (fibreFrame B a N) := by
  induction S with
  | refl M => exact Sequence.refl _
  | @step P N T ih =>
    let Q := fibrePair P B A a Y hd hY hb hbase (hA.trans T.monotone)
    have htY : ∀ s ∈ P.retained, s ⊆ Y := fun s hs => hY s hs.1
    have htb : ∀ x ⊂ a, ∀ t ∈ nativeAug P.retained, x ∪ t ∈ B :=
      fun x hx t ht => hb x hx t (aug_mono P.retained_le ht)
    exact Sequence.step Q ((ih htY htb hA).cast
      (fibrePair_retained P B A a Y hd hY hb hbase
        (hA.trans T.monotone)).symm rfl)

private theorem fibreSequence_pairs {M N : PreAbstractSimplicialComplex V}
    (S : Sequence M N) (B A : Family V) (a Y : Finset V) (hd : Disjoint a Y)
    (hY : ∀ s ∈ M, s ⊆ Y)
    (hb : ∀ x ⊂ a, ∀ t ∈ nativeAug M, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ A) (hA : project A ≤ N) :
    (fibreSequence S B A a Y hd hY hb hbase hA).pairs.map
      (fun P => (P.lower,P.upper)) =
        S.pairs.map (fun P => (a ∪ P.lower,a ∪ P.upper)) := by
  induction S with
  | refl M => rfl
  | @step P N T ih =>
    have htY : ∀ s ∈ P.retained, s ⊆ Y := fun s hs => hY s hs.1
    have htb : ∀ x ⊂ a, ∀ t ∈ nativeAug P.retained, x ∪ t ∈ B :=
      fun x hx t ht => hb x hx t (aug_mono P.retained_le ht)
    have hupper : insert P.apex (a ∪ P.lower) = a ∪ P.upper := by
      ext v; simp only [Finset.mem_insert,Finset.mem_union]; tauto
    simpa only [fibreSequence,Sequence.pairs,Sequence.pairs_cast,List.map_cons,
      fibrePair,emitPair,CollapsePair.upper,hupper] using
        congrArg (List.cons (a ∪ P.lower,a ∪ P.upper)) (ih htY htb hA)

/-- Non-VOID local sequences lift over a literal fibre. This is used for Gamma
and filling/collar schedules; all ordinary lower faces are still nonempty even
when a=empty. No homotopy or parent certificate is an input. -/
def liftFibre (M N B : Family V) (a Y : Finset V)
    (hM0 : (∅ : Finset V) ∈ M) (hN0 : (∅ : Finset V) ∈ N)
    (S : Sequence (project M) (project N)) (hd : Disjoint a Y)
    (hY : Supported Y M)
    (hb : ∀ x ⊂ a, ∀ t ∈ M, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ N) :
    Sequence (project (B ⊔ rawJoin (delta a) M))
      (project (B ⊔ rawJoin (delta a) N)) := by
  have T := fibreSequence S B N a Y hd (fun s hs => hY s hs.2)
    (by simpa only [reconstruct_nonvoid M hM0] using hb) hbase le_rfl
  exact T.cast (by simp only [fibreFrame,reconstruct_nonvoid M hM0])
    (by simp only [fibreFrame,reconstruct_nonvoid N hN0])

/-- Exact ordered coverage for the ACTUAL native fibre list, including every
pair of a supplied Gamma, filling-main or separate collar sequence. -/
theorem liftFibre_pairs (M N B : Family V) (a Y : Finset V)
    (hM0 : (∅ : Finset V) ∈ M) (hN0 : (∅ : Finset V) ∈ N)
    (S : Sequence (project M) (project N)) (hd : Disjoint a Y)
    (hY : Supported Y M) (hb : ∀ x ⊂ a, ∀ t ∈ M, x ∪ t ∈ B)
    (hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ N) :
    (liftFibre M N B a Y hM0 hN0 S hd hY hb hbase).pairs.map
      (fun P => (P.lower,P.upper)) =
        S.pairs.map (fun P => (a ∪ P.lower,a ∪ P.upper)) := by
  unfold liftFibre
  rw [Sequence.pairs_cast]
  exact fibreSequence_pairs S B N a Y hd (fun s hs => hY s hs.2)
    (by simpa only [reconstruct_nonvoid M hM0] using hb) hbase le_rfl

end D5.S3.Geometry.OriginalLabelTwoSum

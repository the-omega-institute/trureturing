/- GID: D5/S3/Geometry/FinitePrescribedPairProtection
   generality: G
   mirror-B: D5/B/S3/Geometry/FinitePrescribedPairProtection
   mirror-E: none(waiver:finite-prescribed-pair-protection)
   anchors: [mathlib/module/Mathlib.Data.List.Basic]
   utility: none
   digest: A forward scan of native pairs constructs protected replay and an original-order standalone core collapse. -/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import Mathlib.Tactic

/-! SOURCE ONLY, UNCOMPILED. Ordinary specification: independently verified
proofs03--05, released 2026-11-06. This owner does not alter the dual-word owner.
There is no supplied endpoint collapse: both native sequences are constructed.
All simplices below use the native NONEMPTY convention. In particular an empty
set of tops gives the empty native complex; no assertion identifies raw VOID
with raw UNIT. Grounds and ghost labels are unchanged throughout. -/
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Finset
namespace D5.S3.Geometry.FinitePrescribedPairProtection
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Sequence" => FiniteRelativeSimplicialCollapse.Sequence (V := V)

/-- Native nonempty faces of a finite union of full simplices. -/
def simplices (H : Finset (Finset V)) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∃ q ∈ H, s ⊆ q}
  isRelLowerSet_faces := by
    rintro s ⟨hs,q,hq,hsq⟩
    exact ⟨hs,fun t hts ht => ⟨ht,q,hq,hts.trans hsq⟩⟩

@[simp] theorem mem_simplices (H : Finset (Finset V)) (s : Finset V) :
    s ∈ simplices H ↔ s.Nonempty ∧ ∃ q ∈ H, s ⊆ q := Iff.rfl

@[simp] theorem simplices_empty : simplices (∅ : Finset (Finset V)) = ⊥ := by
  apply SetLike.coe_injective
  ext s
  change (s.Nonempty ∧ ∃ q ∈ (∅ : Finset (Finset V)), s ⊆ q) ↔ False
  simp

@[simp] theorem simplices_union (H J : Finset (Finset V)) :
    simplices (H ∪ J) = simplices H ⊔ simplices J := by
  apply SetLike.coe_injective
  ext s
  change (s.Nonempty ∧ ∃ q ∈ H ∪ J, s ⊆ q) ↔
    (s.Nonempty ∧ ∃ q ∈ H, s ⊆ q) ∨ (s.Nonempty ∧ ∃ q ∈ J, s ⊆ q)
  simp only [Finset.mem_union]
  aesop

/-- Skip precisely when an existing protected top contains the lower. -/
def blocked (H : Finset (Finset V)) (P : CollapsePair V) : Prop :=
  ∃ q ∈ H, P.lower ⊆ q

/-- The returned objects are the original native pair objects, in source order. -/
def skipped : List (CollapsePair V) → Finset (Finset V) → List (CollapsePair V)
  | [], _ => []
  | P :: ps, H => if blocked H P then P :: skipped ps (insert P.upper H)
      else skipped ps H

/-- Actual emitted subsequence, with the same forward decisions as skipped. -/
def emitted : List (CollapsePair V) → Finset (Finset V) → List (CollapsePair V)
  | [], _ => []
  | P :: ps, H => if blocked H P then emitted ps (insert P.upper H)
      else P :: emitted ps H

/-- Final accumulated tops; later decisions see all earlier skipped uppers. -/
def advance : List (CollapsePair V) → Finset (Finset V) → Finset (Finset V)
  | [], H => H
  | P :: ps, H => advance ps (if blocked H P then insert P.upper H else H)

/-- Tops contributed by the actual skipped list. -/
def skippedTops (ps : List (CollapsePair V)) (H : Finset (Finset V)) :
    Finset (Finset V) := ((skipped ps H).map CollapsePair.upper).toFinset

/-- The endpoint core is computed from the terminal base and the forward scan. -/
def core {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (H : Finset (Finset V)) : PreAbstractSimplicialComplex V :=
  L ⊔ simplices (skippedTops S.pairs H)

private theorem cofaces (P : CollapsePair V) {s : Finset V}
    (hs : s ∈ P.ambient) (hl : P.lower ⊆ s) : s = P.lower ∨ s = P.upper := by
  by_cases he : s = P.lower
  · exact Or.inl he
  · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hl,Ne.symm he⟩))

private theorem upper_closure_le (P : CollapsePair V) :
    simplices {P.upper} ≤ P.ambient := by
  rintro s ⟨hn,q,hq,hs⟩
  have : q = P.upper := by simpa using hq
  subst q
  exact (P.ambient.isRelLowerSet_faces P.upper_mem).2 hs hn

private theorem restored (P : CollapsePair V) :
    P.retained ⊔ simplices {P.upper} = P.ambient := by
  ext s
  constructor
  · rintro (hs | hs)
    · exact P.retained_le hs
    · exact upper_closure_le P hs
  · intro hs
    by_cases hl : P.lower ⊆ s
    · right
      refine ⟨(P.ambient.isRelLowerSet_faces hs).1,P.upper,by simp,?_⟩
      rcases cofaces P hs hl with rfl | rfl
      · exact Finset.subset_insert P.apex P.lower
      · exact le_rfl
    · exact Or.inl ⟨hs,hl⟩

private theorem core_refl (K : PreAbstractSimplicialComplex V) (H) :
    core (Sequence.refl K) H = K := by simp [core,skippedTops,skipped,Sequence.pairs]

private theorem core_step (P : CollapsePair V) {L} (T : Sequence P.retained L) (H) :
    core (.step P T) H = if blocked H P then
      core T (insert P.upper H) ⊔ simplices {P.upper} else core T H := by
  classical
  by_cases h : blocked H P
  · simp only [core,Sequence.pairs,skipped,if_pos h,skippedTops,
      List.map_cons,List.toFinset_cons]
    rw [show insert P.upper ((skipped T.pairs (insert P.upper H)).map
        CollapsePair.upper).toFinset =
        {P.upper} ∪ ((skipped T.pairs (insert P.upper H)).map
          CollapsePair.upper).toFinset by ext q; simp,
      simplices_union]
    ac_rfl
  · simp [core,Sequence.pairs,skipped,skippedTops,h]

/-- No future skipped upper can resurrect an earlier emitted pair: every face
of every later upper already belongs to the earlier retained base. -/
theorem future_upper_in_retained (P : CollapsePair V) {L}
    (T : Sequence P.retained L) {Q : CollapsePair V} (hQ : Q ∈ T.pairs)
    {s : Finset V} (hn : s.Nonempty) (hs : s ⊆ Q.upper) : s ∈ P.retained :=
by
  have bound : ∀ {A B : PreAbstractSimplicialComplex V} (U : Sequence A B)
      {R : CollapsePair V}, R ∈ U.pairs → R.ambient ≤ A := by
    intro A B U
    induction U with
    | refl => simp [Sequence.pairs]
    | step R U ih =>
      intro Q hQ
      change Q ∈ R :: U.pairs at hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact le_rfl
      · exact (ih hQ).trans R.retained_le
  exact bound T hQ ((Q.ambient.isRelLowerSet_faces Q.upper_mem).2 hs hn)

/-- In particular neither face of an earlier pair can reappear in the closure
of a later upper; this uses the later DOWNWARD-CLOSED base, not reverse replay. -/
theorem future_upper_cannot_resurrect (P : CollapsePair V) {L}
    (T : Sequence P.retained L) {Q : CollapsePair V} (hQ : Q ∈ T.pairs) :
    ¬P.lower ⊆ Q.upper ∧ ¬P.upper ⊆ Q.upper := by
  have hl : ¬P.lower ⊆ Q.upper := by
    intro hs
    have hp := future_upper_in_retained P T hQ P.lower_nonempty hs
    exact hp.2 le_rfl
  exact ⟨hl,fun hu => hl ((Finset.subset_insert P.apex P.lower).trans hu)⟩

/-- The computed core is a subcomplex of the original base. -/
theorem core_le {K L} (S : Sequence K L) (H) : core S H ≤ K := by
  induction S generalizing H with
  | refl K => rw [core_refl]
  | step P T ih =>
    rw [core_step]
    split_ifs
    · exact sup_le ((ih _).trans P.retained_le) (upper_closure_le P)
    · exact (ih _).trans P.retained_le

/-- Every original face under an initial protected top survives in the core.
This proves full-boundary retention without assuming an output certificate. -/
theorem core_preserves {K L} (S : Sequence K L) (H) {s : Finset V}
    (hs : s ∈ K) (hprotect : ∃ q ∈ H, s ⊆ q) : s ∈ core S H := by
  revert hs hprotect
  induction S generalizing H with
  | refl K => intro hs _; simpa [core_refl] using hs
  | step P T ih =>
    intro hs hprotect
    rw [core_step]
    by_cases hb : blocked H P
    · rw [if_pos hb]
      by_cases hl : P.lower ⊆ s
      · right
        refine ⟨(P.ambient.isRelLowerSet_faces hs).1,P.upper,by simp,?_⟩
        rcases cofaces P hs hl with rfl | rfl
        · exact Finset.subset_insert P.apex P.lower
        · exact le_rfl
      · left
        exact ih (insert P.upper H) ⟨hs,hl⟩ (by
          obtain ⟨q,hq,hsq⟩ := hprotect; exact ⟨q,mem_insert_of_mem hq,hsq⟩)
    · rw [if_neg hb]
      apply ih H
      · refine ⟨hs,?_⟩
        intro hl
        obtain ⟨q,hq,hsq⟩ := hprotect
        exact hb ⟨q,hq,hl.trans hsq⟩
      · exact hprotect

/-- EXACT endpoint as terminal faces plus the two faces of each skipped pair. -/
theorem core_exact {K L} (S : Sequence K L) (H) (s : Finset V) :
    s ∈ core S H ↔ s ∈ L ∨ ∃ P ∈ skipped S.pairs H, s = P.lower ∨ s = P.upper := by
  induction S generalizing H with
  | refl K => simp [core_refl,skipped,Sequence.pairs]
  | step P T ih =>
    rw [core_step]
    by_cases hb : blocked H P
    · rw [if_pos hb]
      simp only [Sequence.pairs,skipped,if_pos hb,List.mem_cons]
      constructor
      · rintro (hs | hs)
        · rcases (ih _).mp hs with h | ⟨Q,hQ,he⟩
          · exact Or.inl h
          · exact Or.inr ⟨Q,Or.inr hQ,he⟩
        · have hK := upper_closure_le P hs
          by_cases hl : P.lower ⊆ s
          · exact Or.inr ⟨P,Or.inl rfl,cofaces P hK hl⟩
          · have ht := core_preserves T (insert P.upper H) ⟨hK,hl⟩ (by
              obtain ⟨hn,q,hq,hsq⟩ := hs
              have : q = P.upper := by simpa using hq
              subst q; exact ⟨P.upper,by simp,hsq⟩)
            rcases (ih _).mp ht with h | ⟨Q,hQ,he⟩
            · exact Or.inl h
            · exact Or.inr ⟨Q,Or.inr hQ,he⟩
      · rintro (hs | ⟨Q,hQ,he⟩)
        · exact Or.inl ((ih _).mpr (Or.inl hs))
        · rcases hQ with hQP | hQ
          · subst Q
            right
            rcases he with rfl | rfl
            · exact ⟨P.lower_nonempty,P.upper,by simp,Finset.subset_insert P.apex P.lower⟩
            · exact ⟨P.lower_nonempty.mono (Finset.subset_insert P.apex P.lower),P.upper,by simp,le_rfl⟩
          · exact Or.inl ((ih _).mpr (Or.inr ⟨Q,hQ,he⟩))
    · simpa only [if_neg hb,Sequence.pairs,skipped] using ih H

/-- Literal equality of native face sets, without replacing closures by an
unproved facet approximation. -/
theorem core_faces_exact {K L} (S : Sequence K L) (H) :
    (core S H).faces = L.faces ∪
      {s | ∃ P ∈ skipped S.pairs H, s = P.lower ∨ s = P.upper} := by
  ext s
  exact core_exact S H s

/-- Restrict a genuine native pair to any subcomplex containing its upper. -/
def restrictPair (P : CollapsePair V) (A : PreAbstractSimplicialComplex V)
    (hA : A ≤ P.ambient) (hu : P.upper ∈ A) : CollapsePair V where
  ambient := A
  lower := P.lower
  apex := P.apex
  lower_nonempty := P.lower_nonempty
  apex_notMem := P.apex_notMem
  upper_mem := hu
  free s hs hls := P.free s (hA hs) hls

/-- Lift a pair only when no added top contains its lower. -/
def unionPair (P : CollapsePair V) (H : Finset (Finset V))
    (h : ¬ blocked H P) : CollapsePair V where
  ambient := P.ambient ⊔ simplices H
  lower := P.lower
  apex := P.apex
  lower_nonempty := P.lower_nonempty
  apex_notMem := P.apex_notMem
  upper_mem := Or.inl P.upper_mem
  free := by
    intro s hs hls
    rcases hs with hs | ⟨hn,q,hq,hsq⟩
    · exact P.free s hs hls
    · exact False.elim (h ⟨q,hq,hls.1.trans hsq⟩)

private theorem unionPair_retained (P : CollapsePair V) (H) (h : ¬blocked H P) :
    (unionPair P H h).retained = P.retained ⊔ simplices H := by
  ext s
  change (s ∈ P.ambient ∨ s ∈ simplices H) ∧ ¬P.lower ⊆ s ↔ _
  constructor
  · rintro ⟨hs,hn⟩; exact hs.elim (fun hs => Or.inl ⟨hs,hn⟩) Or.inr
  · rintro (⟨hs,hn⟩ | hs)
    · exact ⟨Or.inl hs,hn⟩
    · refine ⟨Or.inr hs,?_⟩
      rintro hl
      obtain ⟨_,q,hq,hsq⟩ := hs
      exact h ⟨q,hq,hl.trans hsq⟩

/-- The forward emitted list is an actual native sequence in the union. -/
def protectedReplay {K L} (S : Sequence K L) (H : Finset (Finset V)) :
    Sequence (K ⊔ simplices H) (core S H ⊔ simplices H) := by
  classical
  induction S generalizing H with
  | refl K => exact (Sequence.refl _).cast rfl (by rw [core_refl])
  | step P T ih =>
    by_cases hb : blocked H P
    · exact (ih (insert P.upper H)).cast (by
        rw [show insert P.upper H = H ∪ {P.upper} by ext q; simp [or_comm],
          simplices_union]
        calc
          P.retained ⊔ (simplices H ⊔ simplices {P.upper}) =
              (P.retained ⊔ simplices {P.upper}) ⊔ simplices H := by ac_rfl
          _ = P.ambient ⊔ simplices H := by rw [restored]) (by
        rw [core_step,if_pos hb]
        rw [show insert P.upper H = H ∪ {P.upper} by ext q; simp [or_comm],
          simplices_union]
        ac_rfl)
    · exact (Sequence.step (unionPair P H hb)
        ((ih H).cast (unionPair_retained P H hb).symm rfl)).cast rfl (by
          rw [core_step,if_neg hb])

/-- Exact extraction of the emitted native pairs, retaining source order. -/
theorem protectedReplay_pairs {K L} (S : Sequence K L) (H) :
    (protectedReplay S H).pairs.map (fun P => (P.lower,P.upper)) =
      (emitted S.pairs H).map (fun P => (P.lower,P.upper)) := by
  induction S generalizing H with
  | refl K => simp [protectedReplay,emitted,Sequence.pairs,Sequence.pairs_cast]
  | step P T ih =>
    by_cases hb : blocked H P
    · simp only [protectedReplay,dif_pos hb,Sequence.pairs_cast,Sequence.pairs,emitted,if_pos hb]
      exact ih (insert P.upper H)
    · simp only [protectedReplay,dif_neg hb,Sequence.pairs_cast,Sequence.pairs,emitted,if_neg hb,List.map_cons]
      exact congrArg (List.cons (P.lower,P.upper)) (ih H)

private theorem restricted_retained (P : CollapsePair V) {L}
    (T : Sequence P.retained L) (H) (hb : blocked H P) :
    (restrictPair P (core (.step P T) H) (core_le _ _) (by
      rw [core_step,if_pos hb]; right
      exact ⟨P.lower_nonempty.mono (Finset.subset_insert P.apex P.lower),P.upper,by simp,le_rfl⟩)).retained =
      core T (insert P.upper H) := by
  ext s
  change (s ∈ core (.step P T) H ∧ ¬P.lower ⊆ s) ↔ _
  rw [core_step,if_pos hb]
  constructor
  · rintro ⟨hs,hn⟩
    rcases hs with hs | hs
    · exact hs
    · exact core_preserves T (insert P.upper H) ⟨upper_closure_le P hs,hn⟩ (by
        obtain ⟨_,q,hq,hsq⟩ := hs
        have : q = P.upper := by simpa using hq
        subst q; exact ⟨P.upper,by simp,hsq⟩)
  · intro hs
    exact ⟨Or.inl hs,(core_le T _ hs).2⟩

/-- Standalone skipped replay is in ORIGINAL order, on the core ALONE. -/
def standaloneReplay {K L} (S : Sequence K L) (H : Finset (Finset V)) :
    Sequence (core S H) L := by
  classical
  induction S generalizing H with
  | refl K => exact (Sequence.refl K).cast (core_refl K H).symm rfl
  | step P T ih =>
    by_cases hb : blocked H P
    · let Q := restrictPair P (core (.step P T) H) (core_le _ _) (by
        rw [core_step,if_pos hb]; right
        exact ⟨P.lower_nonempty.mono (Finset.subset_insert P.apex P.lower),P.upper,by simp,le_rfl⟩)
      exact Sequence.step Q ((ih (insert P.upper H)).cast
        (restricted_retained P T H hb).symm rfl)
    · exact (ih H).cast (by rw [core_step,if_neg hb]) rfl

/-- Exact native extraction for the separate core list; there is no reversal. -/
theorem standaloneReplay_pairs {K L} (S : Sequence K L) (H) :
    (standaloneReplay S H).pairs.map (fun P => (P.lower,P.upper)) =
      (skipped S.pairs H).map (fun P => (P.lower,P.upper)) := by
  induction S generalizing H with
  | refl K => simp [standaloneReplay,skipped,Sequence.pairs,Sequence.pairs_cast]
  | step P T ih =>
    by_cases hb : blocked H P
    · simp only [standaloneReplay,dif_pos hb,Sequence.pairs_cast,Sequence.pairs,skipped,if_pos hb,List.map_cons]
      exact congrArg (List.cons (P.lower,P.upper)) (ih (insert P.upper H))
    · simp only [standaloneReplay,dif_neg hb,Sequence.pairs_cast,Sequence.pairs,skipped,if_neg hb]
      exact ih H

/-- A separately established terminal tail can now be appended on the core. -/
def standaloneWithTail {K L M} (S : Sequence K L) (H)
    (tail : Sequence L M) : Sequence (core S H) M :=
  (standaloneReplay S H).append tail

/-- Every emitted lower remains nonempty by the native convention. -/
theorem emitted_nonempty {K L} (S : Sequence K L) (H) :
    ∀ P ∈ emitted S.pairs H, P.lower.Nonempty := by
  intro P _; exact P.lower_nonempty

/-- Exact obstruction criterion for outside critical tops; both directions use
actual cofaces, and no boundary hypothesis is needed for this local test. -/
theorem outside_coface_criterion (P : CollapsePair V) (H)
    (hout : ∀ q ∈ H, q ∉ P.ambient) :
    (∀ s ∈ P.ambient ⊔ simplices H, P.lower ⊆ s →
      s = P.lower ∨ s = P.upper) ↔ ¬blocked H P := by
  constructor
  · intro hf hb
    obtain ⟨q,hq,hlq⟩ := hb
    have hn := P.lower_nonempty.mono hlq
    rcases hf q (Or.inr ⟨hn,q,hq,le_rfl⟩) hlq with he | he
    · exact hout q hq (he.symm ▸ P.lower_mem)
    · exact hout q hq (he.symm ▸ P.upper_mem)
  · intro h s hs hl
    rcases hs with hs | ⟨hn,q,hq,hsq⟩
    · exact cofaces P hs hl
    · exact False.elim (h ⟨q,hq,hl.trans hsq⟩)

/-- Outside tops stay absent and every nonempty proper boundary face survives.
The input family may be empty; no critical simplex is silently introduced. -/
theorem critical_boundary {K L} (S : Sequence K L) (H)
    (hout : ∀ q ∈ H, q ∉ K)
    (hbd : ∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ K) :
    (∀ q ∈ H, q ∉ core S H) ∧
      (∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ core S H) := by
  constructor
  · intro q hq hc; exact hout q hq (core_le S H hc)
  · intro q hq s hn hs
    exact core_preserves S H (hbd q hq s hn hs) ⟨q,hq,hs.1⟩

/-- The ordinary outside/full-boundary assumptions already force incomparability. -/
theorem critical_antichain (K : PreAbstractSimplicialComplex V) (H : Finset (Finset V))
    (hne : ∀ q ∈ H, q.Nonempty) (hout : ∀ q ∈ H, q ∉ K)
    (hbd : ∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ K) :
    ∀ q ∈ H, ∀ r ∈ H, q ⊆ r → q = r := by
  intro q hq r hr hqr
  by_contra he
  exact hout q hq (hbd r hr q (hne q hq)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hqr,he⟩))

/-- Explicit prefix bookkeeping for the scan, with no existential desired list. -/
theorem scan_append (xs ys : List (CollapsePair V)) (H) :
    skipped (xs ++ ys) H = skipped xs H ++ skipped ys (advance xs H) ∧
    emitted (xs ++ ys) H = emitted xs H ++ emitted ys (advance xs H) := by
  induction xs generalizing H with
  | nil => simp [skipped,emitted,advance]
  | cons P xs ih =>
    by_cases hb : blocked H P <;>
      simp [skipped,emitted,advance,hb,ih,List.cons_append]

/-- Accumulated tops are precisely original tops plus earlier skipped uppers. -/
theorem advance_exact (xs : List (CollapsePair V)) (H) :
    advance xs H = H ∪ skippedTops xs H := by
  induction xs generalizing H with
  | nil => simp [advance,skippedTops,skipped]
  | cons P xs ih =>
    by_cases hb : blocked H P <;>
      simp [advance,skippedTops,skipped,hb,ih,Finset.insert_union,
        Finset.union_insert,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]

/-- At any original cut B_i, the actual protected current ambient is exactly
B_i union R_i union the original critical simplices. This is the endpoint of
the already constructed prefix replay, whether that prefix emitted or skipped. -/
theorem prefix_invariant {K B L : PreAbstractSimplicialComplex V}
    (A : Sequence K B) (T : Sequence B L) (H) :
    core A H ⊔ simplices H = B ⊔ simplices (skippedTops A.pairs H) ⊔ simplices H ∧
    B ⊔ simplices (advance A.pairs H) = core A H ⊔ simplices H := by
  constructor
  · rfl
  · rw [advance_exact,simplices_union]
    unfold core
    ac_rfl

/-- Exact cofaces of every constructed native pair, including the lower itself. -/
theorem native_current_cofaces (P : CollapsePair V) (s : Finset V) :
    (s ∈ P.ambient ∧ P.lower ⊆ s) ↔ s = P.lower ∨ s = P.upper := by
  constructor
  · rintro ⟨hs,hl⟩; exact cofaces P hs hl
  · rintro (rfl | rfl)
    · exact ⟨P.lower_mem,le_rfl⟩
    · exact ⟨P.upper_mem,Finset.subset_insert P.apex P.lower⟩

/-- The forward decision at a cut tests exactly the original tops and EARLIER
skipped uppers; no later upper participates in the decision. -/
theorem decision_at_prefix (xs : List (CollapsePair V)) (H) (P : CollapsePair V) :
    blocked (advance xs H) P ↔
      (∃ q ∈ H, P.lower ⊆ q) ∨
        ∃ Q ∈ skipped xs H, P.lower ⊆ Q.upper := by
  rw [advance_exact]
  simp only [blocked,Finset.mem_union,skippedTops,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨q,hq,hl⟩
    rcases hq with hq | ⟨Q,hQ,rfl⟩
    · exact Or.inl ⟨q,hq,hl⟩
    · exact Or.inr ⟨Q,hQ,hl⟩
  · rintro (⟨q,hq,hl⟩ | ⟨Q,hQ,hl⟩)
    · exact ⟨q,Or.inl hq,hl⟩
    · exact ⟨Q.upper,Or.inr ⟨Q,hQ,rfl⟩,hl⟩

/-- Original zero-based indices are generated simultaneously with pair objects. -/
def skippedIndexed : List (CollapsePair V) → Finset (Finset V) → Nat →
    List (Nat × CollapsePair V)
  | [], _, _ => []
  | P :: ps, H, n => if blocked H P then
      (n,P) :: skippedIndexed ps (insert P.upper H) (n+1)
    else skippedIndexed ps H (n+1)

/-- Actual emitted indices, with the same source-index increments on skips. -/
def emittedIndexed : List (CollapsePair V) → Finset (Finset V) → Nat →
    List (Nat × CollapsePair V)
  | [], _, _ => []
  | P :: ps, H, n => if blocked H P then
      emittedIndexed ps (insert P.upper H) (n+1)
    else (n,P) :: emittedIndexed ps H (n+1)

/-- The actual skipped original indices, starting at zero. -/
def skippedIndices (ps : List (CollapsePair V)) (H : Finset (Finset V)) : List Nat :=
  (skippedIndexed ps H 0).map Prod.fst

/-- The actual emitted original indices, starting at zero. -/
def emittedIndices (ps : List (CollapsePair V)) (H : Finset (Finset V)) : List Nat :=
  (emittedIndexed ps H 0).map Prod.fst

/-- Pair projections of the indexed scan agree with the actual two sublists. -/
theorem indexed_scan (ps : List (CollapsePair V)) (H) (n : Nat) :
    (skippedIndexed ps H n).map Prod.snd = skipped ps H ∧
    (emittedIndexed ps H n).map Prod.snd = emitted ps H := by
  induction ps generalizing H n with
  | nil => simp [skippedIndexed,emittedIndexed,skipped,emitted]
  | cons P ps ih =>
    by_cases hb : blocked H P <;>
      simp [skippedIndexed,emittedIndexed,skipped,emitted,hb,ih]

/-- The generated indices are genuine original positions within the input list. -/
theorem indexed_bounds (ps : List (CollapsePair V)) (H) (n : Nat) :
    (∀ z ∈ skippedIndexed ps H n, n ≤ z.1 ∧ z.1 < n + ps.length) ∧
    (∀ z ∈ emittedIndexed ps H n, n ≤ z.1 ∧ z.1 < n + ps.length) := by
  induction ps generalizing H n with
  | nil => simp [skippedIndexed,emittedIndexed]
  | cons P ps ih =>
    by_cases hb : blocked H P
    · simp only [skippedIndexed,emittedIndexed,if_pos hb,List.length_cons,List.mem_cons]
      constructor
      · intro z hz
        rcases hz with rfl | hz
        · simp
        · have hh := (ih (insert P.upper H) (n+1)).1 z hz
          constructor <;> omega
      · intro z hz
        have hh := (ih (insert P.upper H) (n+1)).2 z hz
        constructor <;> omega
    · simp only [skippedIndexed,emittedIndexed,if_neg hb,List.length_cons,List.mem_cons]
      constructor
      · intro z hz
        have hh := (ih H (n+1)).1 z hz
        constructor <;> omega
      · intro z hz
        rcases hz with rfl | hz
        · simp
        · have hh := (ih H (n+1)).2 z hz
          constructor <;> omega

/-- Empty critical families produce the original full list and no skipped pairs. -/
theorem empty_protection (ps : List (CollapsePair V)) :
    skipped ps ∅ = [] ∧ emitted ps ∅ = ps := by
  induction ps with
  | nil => simp [skipped,emitted]
  | cons P ps ih => simp [skipped,emitted,blocked,ih]

@[simp] theorem core_empty {K L} (S : Sequence K L) : core S ∅ = L := by
  simp [core,skippedTops,(empty_protection S.pairs).1]

end D5.S3.Geometry.FinitePrescribedPairProtection

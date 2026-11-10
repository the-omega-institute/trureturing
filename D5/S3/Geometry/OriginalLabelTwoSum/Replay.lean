/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Replay
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Replay
   mirror-E: none(waiver:original-label-two-sum-replay)
   anchors: [mathlib/module/Mathlib.Data.List.Forall2]
   utility: none
   digest: Actual child free pairs are classified and replayed by the original rectangular or Gamma rules. -/
import D5.S3.Geometry.OriginalLabelTwoSum.RectangleEndpoints
import D5.S3.Geometry.OriginalLabelTwoSum.Vertical

/-! UNCOMPILED. This is collapse-only child replay. It never accepts a parent
collapse or its endpoint as a premise. The no-vertical permission is checked
against actual extracted native pairs, not a guessed child schedule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Phi applied to the literal deletion and raw link of a child. -/
def parentOf (X Y Z : Finset V) (e : V) (E C : Family V) : Family V :=
  phi X Y Z (restrict X C) (rawLink X e C) E

private theorem restrict_cut (X a : Finset V) (C : Family V) :
    restrict X (cut C {a}) = cut (restrict X C) {a} := by
  apply SetLike.ext
  intro s
  simp only [restrict,cut,LowerSet.mem_inf_iff,LowerSet.mem_mk,mem_delta,
    Finset.mem_singleton,forall_eq,Set.mem_setOf_eq]
  tauto

private theorem subset_insert_erase (e : V) (a s : Finset V) :
    a ⊆ insert e s ↔ a.erase e ⊆ s := by
  constructor
  · intro h v hv
    exact (Finset.mem_insert.mp (h (Finset.mem_of_mem_erase hv))).resolve_left
      (Finset.mem_erase.mp hv).1
  · intro h v hv
    by_cases he : v = e
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (h (Finset.mem_erase.mpr ⟨he,hv⟩)))

private theorem link_cut (X a : Finset V) (e : V) (C : Family V) :
    rawLink X e (cut C {a}) = cut (rawLink X e C) {a.erase e} := by
  apply SetLike.ext
  intro s
  simp only [rawLink,cut,LowerSet.mem_mk,Finset.mem_singleton,forall_eq,
    subset_insert_erase,Set.mem_setOf_eq]
  tauto

private theorem nativeAug_retained (P : CollapsePair V) :
    nativeAug P.retained = cut (nativeAug P.ambient) {P.lower} := by
  apply SetLike.ext
  intro s
  change AugmentedFace P.retained s ↔
    AugmentedFace P.ambient s ∧ ∀ a ∈ ({P.lower} : Finset (Finset V)), ¬ a ⊆ s
  simpa only [Finset.mem_singleton,forall_eq] using augmented_retained P s

/-- One child pair, on its actual native ambient, produces a finite native
parent sequence. Its source and target are computed Phi states. -/
def replayPair (X Y Z : Finset V) (e : V) (E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (heX : e ∉ X)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    (P : CollapsePair V)
    (hs : Supported (insert e X) (nativeAug P.ambient))
    (permission : P.apex = e →
      Sequence (project (delta Y)) (project E)) :
    Sequence (project (parentOf X Y Z e E (nativeAug P.ambient)))
      (project (parentOf X Y Z e E (nativeAug P.retained))) := by
  let C := nativeAug P.ambient
  let D := restrict X C
  let L := rawLink X e C
  have hD : Supported X D := fun _ h => h.2
  have hL : Supported X L := fun _ h => h.1
  have hLD : L ≤ D := by
    intro s hs
    exact ⟨C.lower (Finset.subset_insert e s) hs.2,hs.1⟩
  have hpC : P.lower ∈ C := Or.inr P.lower_mem
  have huC : P.upper ∈ C := Or.inr P.upper_mem
  have cofaces : ∀ s ∈ C, P.lower ⊆ s → s = P.lower ∨ s = P.upper := by
    intro s hs hls
    have hne := P.lower_nonempty.mono hls
    have hsP : s ∈ P.ambient := hs.resolve_left (fun he =>
      Finset.not_nonempty_empty (he ▸ hne))
    by_cases he : s = P.lower
    · exact Or.inl he
    · exact Or.inr (P.free s hsP
        (Finset.ssubset_iff_subset_ne.mpr ⟨hls,Ne.symm he⟩))
  have htarget : nativeAug P.retained = cut C {P.lower} := nativeAug_retained P
  by_cases heU : e ∈ P.upper
  · by_cases heS : e ∈ P.lower
    · -- Both child faces contain e; the projected lower may be empty.
      let a := P.lower.erase e
      have huE : P.apex ≠ e := fun h => P.apex_notMem (h.symm ▸ heS)
      have haX : a ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (hs _ hpC (Finset.mem_of_mem_erase hv))).resolve_left
          (Finset.mem_erase.mp hv).1
      have hvX : P.apex ∈ X :=
        (Finset.mem_insert.mp (hs _ huC (Finset.mem_insert_self _ _))).resolve_left huE
      have hva : P.apex ∉ a := fun h => P.apex_notMem (Finset.mem_of_mem_erase h)
      have haL : a ∈ L := ⟨haX,by simpa [a,Finset.insert_erase heS] using hpC⟩
      have hbL : insert P.apex a ∈ L := by
        refine ⟨Finset.insert_subset_iff.mpr ⟨hvX,haX⟩,?_⟩
        have heq : insert e (insert P.apex a) = P.upper := by
          rw [Finset.insert_comm,show insert e a = P.lower from Finset.insert_erase heS]
        rw [heq]; exact huC
      have hf : ∀ s ∈ L, a ⊆ s → s = a ∨ s = insert P.apex a := by
        intro s hsL has
        have hlow : P.lower ⊆ insert e s := by
          rw [← Finset.insert_erase heS]
          exact Finset.insert_subset_insert e has
        rcases cofaces _ hsL.2 hlow with h | h
        · left
          have hh := congrArg (fun z : Finset V => z.erase e) h
          simpa [Finset.erase_insert (show e ∉ s from fun h => heX (hsL.1 h)),a] using hh
        · right
          have hh := congrArg (fun z : Finset V => z.erase e) h
          simpa [CollapsePair.upper,Finset.erase_insert
            (show e ∉ s from fun h => heX (hsL.1 h)),Finset.erase_insert_of_ne huE,a] using hh
      have hDel : restrict X (cut C {P.lower}) = D := by
        apply SetLike.ext
        intro s
        constructor
        · exact fun h => ⟨h.1.1,h.2⟩
        · intro h
          exact ⟨⟨h.1,by
            intro q hq hqs
            have heq : q = P.lower := by simpa using hq
            subst q
            exact heX (h.2 (hqs heS))⟩,h.2⟩
      exact (linkLift X Y Z a P.apex D L E hd hz hD hL hE hLD haX hvX hva
        haL hbL hf).cast rfl (by
          rw [htarget]
          simp only [parentOf,hDel,link_cut]
          rfl)
    · -- Vertical pair: its apex is exactly e and alpha is actually nonempty.
      have hve : P.apex = e := (Finset.mem_insert.mp heU).resolve_right heS |>.symm
      have haX : P.lower ⊆ X := by
        intro v hv
        exact (Finset.mem_insert.mp (hs _ hpC hv)).resolve_left
          (fun h => heS (h ▸ hv))
      have haL : P.lower ∈ L := ⟨haX,by simpa [← hve] using huC⟩
      have maxD : ∀ s ∈ D, P.lower ⊆ s → s = P.lower := by
        intro s hsD hls
        rcases cofaces s hsD.1 hls with h | h
        · exact h
        · exact False.elim (heX (hsD.2 (h.symm ▸ heU)))
      have maxL : ∀ s ∈ L, P.lower ⊆ s → s = P.lower := by
        intro s hsL hls
        have hl : P.lower ⊆ insert e s := hls.trans (Finset.subset_insert _ _)
        have hup := (cofaces (insert e s) hsL.2 hl).resolve_left
          (fun h => heS (h ▸ Finset.mem_insert_self e s))
        have hh := congrArg (fun z : Finset V => z.erase e) hup
        simpa [CollapsePair.upper,hve,Finset.erase_insert heS,
          Finset.erase_insert (show e ∉ s from fun h => heX (hsL.1 h))] using hh
      exact (verticalGamma X Y Z P.lower D L E hd hz hD hL hE hLD haL maxD maxL
        P.lower_nonempty hE0 (permission hve)).cast rfl (by
          rw [htarget]
          simp only [parentOf,restrict_cut,link_cut,Finset.erase_eq_of_notMem heS]
          rfl)
  · -- Neither child face contains e: deletion rectangle.
    have heS : e ∉ P.lower := fun h => heU (Finset.mem_insert_of_mem h)
    have huX : P.upper ⊆ X := by
      intro v hv
      exact (Finset.mem_insert.mp (hs _ huC hv)).resolve_left
        (fun h => heU (h ▸ hv))
    have huD : P.upper ∈ D := ⟨huC,huX⟩
    have hnL : P.lower ∉ L := by
      intro hL'
      have hh := (cofaces (insert e P.lower) hL'.2 (Finset.subset_insert _ _)).resolve_left
        (fun h => heS (h ▸ Finset.mem_insert_self e P.lower))
      exact heU (hh ▸ Finset.mem_insert_self e P.lower)
    let Q := emitPair D P.lower P.apex P.lower_nonempty P.apex_notMem huD
      (fun s hs hls => cofaces s hs.1 hls)
    have hLink : rawLink X e (cut C {P.lower}) = L := by
      rw [link_cut,Finset.erase_eq_of_notMem heS]
      apply SetLike.ext
      intro s
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro q hq hqs
        have heq : q = P.lower := by simpa using hq
        subst q
        exact hnL (L.lower hqs h)
    exact (deletionLift X Y Z D L E hd hz hD hL hE Q rfl hnL).cast rfl (by
      rw [htarget]
      simp only [parentOf,restrict_cut,hLink]
      rfl)

/-- Entire native child list, with exact Gamma or actual no-vertical alternative.
The optional no-vertical case cannot manufacture a missing Gamma. -/
def replaySequence (X Y Z : Finset V) (e : V) (E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (heX : e ∉ X)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (hs : Supported (insert e X) (nativeAug M))
    (permission : Nonempty (Sequence (project (delta Y)) (project E)) ∨
      ∀ P ∈ S.pairs, P.apex ≠ e) :
    Sequence (project (parentOf X Y Z e E (nativeAug M)))
      (project (parentOf X Y Z e E (nativeAug N))) := by
  induction S with
  | refl M => exact Sequence.refl _
  | @step P N T ih =>
    let hperm : P.apex = e → Sequence (project (delta Y)) (project E) := by
      intro he
      have hg : Nonempty (Sequence (project (delta Y)) (project E)) :=
        permission.elim id (fun hn => False.elim (hn P (by simp [Sequence.pairs]) he))
      exact Classical.choice hg
    have htperm : Nonempty (Sequence (project (delta Y)) (project E)) ∨
        ∀ Q ∈ T.pairs, Q.apex ≠ e := by
      rcases permission with hg | hn
      · exact Or.inl hg
      · exact Or.inr (fun Q hQ => hn Q (by simp [Sequence.pairs,hQ]))
    have hts : Supported (insert e X) (nativeAug P.retained) := by
      intro s hss
      exact hs s (hss.elim Or.inl (fun h => Or.inr h.1))
    exact (replayPair X Y Z e E hd hz heX hE hE0 P hs hperm).append (ih hts htperm)


/-- The ordered native pair datum.  It is a projection of the existing
    `CollapsePair`; no competing pair engine is introduced. -/
def orderedPair (P : CollapsePair V) : Finset V × Finset V :=
  (P.lower, P.upper)

def orderedPairs {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : List (Finset V × Finset V) :=
  S.pairs.map orderedPair

@[simp] theorem orderedPairs_cast {K L K' L' : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K = K') (hL : L = L') :
    orderedPairs (S.cast hK hL) = orderedPairs S := by
  simp [orderedPairs]

@[simp] theorem orderedPairs_append
    {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) :
    orderedPairs (S.append T) = orderedPairs S ++ orderedPairs T := by
  simp [orderedPairs, Sequence.pairs_append, List.map_append]

/-- The right-hand Gamma chosen by the existing Prop-valued permission.  This
is a source constituent, not the list of a parent/replay output. Nonempty loses
the identity of a supplied witness, so we expose the actual choice explicitly. -/
def rightGammaPairs (Y : Finset V) (E : Family V) :
    List (Finset V × Finset V) := by
  classical
  exact if hg : Nonempty (Sequence (project (delta Y)) (project E)) then
    orderedPairs (Classical.choice hg)
  else []

/-- Replay specified solely on original lower/upper faces and a right Gamma
list. No native pair, previous certificate or target sequence is re-extracted. -/
def replayFacePairs (Y Z : Finset V) (e : V) (E : Family V)
    (P : Finset V × Finset V) (gamma : List (Finset V × Finset V)) :
    List (Finset V × Finset V) := by
  classical
  exact if e ∉ P.2 then
    (fibres (Z.powerset.filter (fun t => t ∉ E))).map
      (fun t => (P.1 ∪ t, P.2 ∪ t))
  else if e ∈ P.1 then
    (fibres (Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E))).map
      (fun t => (P.1.erase e ∪ t, P.2.erase e ∪ t))
  else gamma.map (fun Q => (P.1 ∪ Q.1, P.1 ∪ Q.2))

/-- This is the actual branch schedule for one child pair: the descending
    deletion rectangle, the descending link rectangle, the supplied Gamma
    schedule after lifting, or the excluded branch.  Every nonempty branch is
    independently specified from the original pair and finite schedule data. -/
def replayBranchPairs (X Y Z : Finset V) (e : V) (E : Family V)
    (P : CollapsePair V)
    (permission : P.apex = e → Sequence (project (delta Y)) (project E)) :
    List (Finset V × Finset V) := by
  classical
  exact if heU : e ∉ P.upper then
    (fibres (Z.powerset.filter (fun t => t ∉ E))).map
      (fun t => (P.lower ∪ t, insert P.apex (P.lower ∪ t)))
  else if heL : e ∈ P.lower then
    (fibres (Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E))).map
      (fun t => (P.lower.erase e ∪ t,
        insert P.apex (P.lower.erase e ∪ t)))
  else if heA : P.apex = e then
    (permission heA).pairs.map
      (fun Q => (P.lower ∪ Q.lower, P.lower ∪ Q.upper))
  else []

/-- Ordered pair extraction for the three actual replay constructors.  The
    proof is by the branch split already used by `replayPair`; `pairs_cast`
    removes endpoint transports, `rectangle_order` discharges the two finite
    descending enumerations, and `liftFibre_pairs` discharges Gamma. -/
theorem replayPair_orderedPairs
    (X Y Z : Finset V) (e : V) (E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (heX : e ∉ X)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    (P : CollapsePair V)
    (hs : Supported (insert e X) (nativeAug P.ambient))
    (permission : P.apex = e → Sequence (project (delta Y)) (project E)) :
    orderedPairs (replayPair X Y Z e E hd hz heX hE hE0 P hs permission) =
      replayBranchPairs X Y Z e E P permission := by
  classical
  unfold replayPair replayBranchPairs orderedPairs orderedPair
  by_cases heU : e ∈ P.upper
  · by_cases heL : e ∈ P.lower
    · simp only [dif_pos heU, if_neg (not_not.mpr heU),
        dif_neg (not_not.mpr heU), dif_pos heL, if_pos heL,
        orderedPairs, orderedPair, Sequence.pairs_cast,
        linkLift, linkRectangle, rectangle_order]
    · have heA : P.apex = e :=
        (Finset.mem_insert.mp (show e ∈ insert P.apex P.lower from heU)).resolve_right heL |>.symm
      simp only [dif_pos heU, if_neg (not_not.mpr heU),
        dif_neg (not_not.mpr heU), dif_neg heL, if_neg heL, dif_pos heA,
        orderedPairs, orderedPair, Sequence.pairs_cast,
        verticalGamma, liftFibre_pairs]
  · simp only [dif_neg heU, if_pos heU, dif_pos heU,
      orderedPairs, orderedPair, Sequence.pairs_cast,
      deletionLift, deletionRectangle, rectangle_order, emitPair]

private theorem replayBranchPairs_faces
    (X Y Z : Finset V) (e : V) (E : Family V) (P : CollapsePair V)
    (permission : P.apex = e → Sequence (project (delta Y)) (project E))
    (gamma : List (Finset V × Finset V))
    (hgamma : ∀ h : P.apex = e, orderedPairs (permission h) = gamma) :
    replayBranchPairs X Y Z e E P permission =
      replayFacePairs Y Z e E (orderedPair P) gamma := by
  classical
  have hupper (t : Finset V) :
      insert P.apex (P.lower ∪ t) = P.upper ∪ t := by
    ext v
    simp only [CollapsePair.upper, Finset.mem_insert, Finset.mem_union]
    tauto
  by_cases heU : e ∈ P.upper
  · by_cases heL : e ∈ P.lower
    · have hne : P.apex ≠ e := fun h => P.apex_notMem (h.symm ▸ heL)
      have herase (t : Finset V) :
          insert P.apex (P.lower.erase e ∪ t) = P.upper.erase e ∪ t := by
        ext v
        simp only [CollapsePair.upper, Finset.mem_insert, Finset.mem_union,
          Finset.mem_erase]
        constructor
        · rintro (rfl | hv)
          · exact Or.inl ⟨hne, Or.inl rfl⟩
          · rcases hv with hv | hv
            · exact Or.inl ⟨hv.1, Or.inr hv.2⟩
            · exact Or.inr hv
        · rintro (⟨hv, ha | hl⟩ | ht)
          · exact Or.inl ha
          · exact Or.inr (Or.inl ⟨hv, hl⟩)
          · exact Or.inr (Or.inr ht)
      simp only [replayBranchPairs, replayFacePairs, orderedPair, heU, heL,
        not_true_eq_false, not_false_eq_true, if_false, if_true, dite_false, dite_true]
      apply congrArg (fun f => List.map f _)
      funext t
      exact Prod.ext rfl (herase t)
    · have heA : P.apex = e :=
        (Finset.mem_insert.mp (show e ∈ insert P.apex P.lower from heU)).resolve_right heL |>.symm
      simp only [replayBranchPairs, replayFacePairs, orderedPair,
        heU, heL, not_true_eq_false, not_false_eq_true, if_false, if_true, dite_false, dite_true,
        dif_neg (not_not.mpr heU), dif_neg heL, dif_pos heA]
      rw [← hgamma heA]
      simp only [orderedPairs, orderedPair, List.map_map]
      rfl
  · simp only [replayBranchPairs, replayFacePairs, orderedPair, heU,
      not_false_eq_true, if_true, dite_true]
    apply congrArg (fun f => List.map f _)
    funext t
    exact Prod.ext rfl (hupper t)

/-- The complete replay list is a flat map on the ORIGINAL child faces. The
right Gamma is the same classical choice as in the constructor. Membership is
used only for the real head/tail pairs in the no-vertical alternative. -/
theorem replaySequence_orderedPairs
    (X Y Z : Finset V) (e : V) (E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (heX : e ∉ X)
    (hE : Supported Y E) (hE0 : (∅ : Finset V) ∈ E)
    {M N : PreAbstractSimplicialComplex V} (S : Sequence M N)
    (hs : Supported (insert e X) (nativeAug M))
    (permission : Nonempty (Sequence (project (delta Y)) (project E)) ∨
      ∀ P ∈ S.pairs, P.apex ≠ e) :
    orderedPairs (replaySequence X Y Z e E hd hz heX hE hE0 S hs permission) =
      S.pairs.flatMap (fun P =>
        replayFacePairs Y Z e E (orderedPair P) (rightGammaPairs Y E)) := by
  classical
  induction S with
  | refl M => rfl
  | @step P N T ih =>
    have htail : Supported (insert e X) (nativeAug P.retained) := by
      intro s hP
      exact hs s (hP.elim Or.inl (fun h => Or.inr h.1))
    let hperm : P.apex = e → Sequence (project (delta Y)) (project E) := by
      intro h
      have hg : Nonempty (Sequence (project (delta Y)) (project E)) :=
        permission.elim id (fun hn => False.elim (hn P (by simp [Sequence.pairs]) h))
      exact Classical.choice hg
    have htailperm : Nonempty (Sequence (project (delta Y)) (project E)) ∨
        ∀ Q ∈ T.pairs, Q.apex ≠ e :=
      permission.elim Or.inl
        (fun hn => Or.inr (fun Q hQ => hn Q (by simp [Sequence.pairs, hQ])))
    have hgamma : ∀ h : P.apex = e,
        orderedPairs (hperm h) = rightGammaPairs Y E := by
      intro h
      dsimp only [hperm]
      rcases permission with hg | hn
      · change orderedPairs (Classical.choice hg) = rightGammaPairs Y E
        simp only [rightGammaPairs, dif_pos hg]
      · exact False.elim (hn P (by simp [Sequence.pairs]) h)
    change orderedPairs ((replayPair X Y Z e E hd hz heX hE hE0 P hs hperm).append
      (replaySequence X Y Z e E hd hz heX hE hE0 T htail htailperm)) = _
    rw [orderedPairs_append, replayPair_orderedPairs,
      replayBranchPairs_faces X Y Z e E P hperm (rightGammaPairs Y E) hgamma,
      ih htail htailperm] <;> rfl

end D5.S3.Geometry.OriginalLabelTwoSum

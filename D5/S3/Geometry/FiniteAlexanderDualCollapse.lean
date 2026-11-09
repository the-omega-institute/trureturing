/- GID: D5/S3/Geometry/FiniteAlexanderDualCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteAlexanderDualCollapse
   mirror-E: none(waiver:finite-alexander-dual-collapse)
   anchors: [mathlib/module/Mathlib.Data.List.Forall2, mathlib/module/Mathlib.Data.Fintype.EquivFin]
   utility: none
   digest: Fixed labeled complements reverse free pairs and compute a one-critical-face cell attachment. -/
/- UNCOMPILED SOURCE ATTEMPT. No elaboration, kernel, axiom or acceptance claim.
   Imports include the two released UNCOMPILED owner drafts. -/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import Mathlib.Data.List.Forall2
import Mathlib.Data.Fintype.EquivFin

/-!
The ground is an explicit finset W inside the unchanged finite coordinate type V.
Every primal face is supported on W; a cone apex is outside W. Ghosts remain in W.
`dual` is the NONEMPTY skeleton of the complement formula. Its augmented meaning
is asserted ONLY through `dual_augmented` on the proper domain. In particular no
void dual is represented as `AugmentedFace bottom`. There is no resizing of V.

The only collapse-sequence owner is FiniteRelativeSimplicialCollapse.Sequence.
The certificate contains finite combinatorial data, never desired maps or sphere
conclusions. The final disk-collar/sphere argument is a separate typed obligation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteAlexanderDualCollapse
open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All faces, including their ghost ambient coordinates, use the fixed ground. -/
def Supported (W : Finset V) (K : PreAbstractSimplicialComplex V) : Prop :=
  ∀ s ∈ K, s ⊆ W

/-- Full ground absent from the AUGMENTED face family; false when W is empty. -/
def Proper (W : Finset V) (K : PreAbstractSimplicialComplex V) : Prop :=
  ¬ AugmentedFace K W

private theorem supported_mono {W : Finset V} {K L : PreAbstractSimplicialComplex V}
    (hW : Supported W K) (h : L ≤ K) : Supported W L :=
  fun s hs => hW s (h hs)

private theorem proper_mono {W : Finset V} {K L : PreAbstractSimplicialComplex V}
    (hW : Proper W K) (h : L ≤ K) : Proper W L := by
  rintro (he | hm)
  · exact hW (Or.inl he)
  · exact hW (Or.inr (h hm))

private theorem augmented_mono {K L : PreAbstractSimplicialComplex V} (h : K ≤ L)
    {s : Finset V} (hs : AugmentedFace K s) : AugmentedFace L s := by
  rcases hs with he | hm
  · exact Or.inl he
  · exact Or.inr (h hm)

private theorem augmented_of_nonempty {K : PreAbstractSimplicialComplex V}
    {s : Finset V} (hs : s.Nonempty) : AugmentedFace K s ↔ s ∈ K := by
  exact ⟨fun h => h.resolve_left hs.ne_empty, Or.inr⟩

private theorem complement_cross {W s t : Finset V} (hs : s ⊆ W) (ht : t ⊆ W) :
    W \ t ⊆ s ↔ W \ s ⊆ t := by
  constructor
  · intro h
    have hh := Finset.sdiff_subset_sdiff_right W h
    simpa only [Finset.sdiff_sdiff_eq_self ht] using hh
  · intro h
    have hh := Finset.sdiff_subset_sdiff_right W h
    simpa only [Finset.sdiff_sdiff_eq_self hs] using hh

/-- Native nonempty faces of the fixed-ground complement formula. The augmented
bridge requires Proper; outside that domain this definition is only a skeleton. -/
def dual (W : Finset V) (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ⊆ W ∧ ¬ AugmentedFace K (W \ s)}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsW, hn⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, hts.trans hsW, fun h => hn
      (augmented_downward h (Finset.sdiff_subset_sdiff_right W hts))⟩

private theorem dual_supported (W : Finset V) (K : PreAbstractSimplicialComplex V) :
    Supported W (dual W K) := fun _ hs => hs.2.1

/-- The total augmented bridge on the proper domain, including s=empty. -/
theorem dual_augmented (W : Finset V) (K : PreAbstractSimplicialComplex V)
    (hp : Proper W K) (s : Finset V) :
    AugmentedFace (dual W K) s ↔ s ⊆ W ∧ ¬ AugmentedFace K (W \ s) := by
  constructor
  · rintro (rfl | hs)
    · exact ⟨empty_subset _, by simpa only [Proper, Finset.sdiff_empty] using hp⟩
    · exact hs.2
  · rintro ⟨hsW, hn⟩
    by_cases hs : s = ∅
    · exact Or.inl hs
    · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr hs, hsW, hn⟩

/-- No relabeling or deletion of ghost coordinates occurs under duality. -/
theorem dual_antitone (W : Finset V) {K L : PreAbstractSimplicialComplex V}
    (h : K ≤ L) : dual W L ≤ dual W K := by
  rintro s ⟨hs, hsW, hn⟩
  exact ⟨hs, hsW, fun hm => hn (augmented_mono h hm)⟩

private theorem dual_proper {W : Finset V} {K : PreAbstractSimplicialComplex V}
    (hp : Proper W K) : Proper W (dual W K) := by
  rw [Proper, dual_augmented W K hp W]
  simp [AugmentedFace]

/-- Double duality for a supported, nonvoid proper augmented primal family. -/
theorem dual_involutive (W : Finset V) (K : PreAbstractSimplicialComplex V)
    (hW : Supported W K) (hp : Proper W K) : dual W (dual W K) = K := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, hsW, hn⟩
    have hout := (dual_augmented W (dual W K) (dual_proper hp) s).mp
      (Or.inr ⟨hs, hsW, hn⟩)
    have hh := dual_augmented W K hp (W \ s)
    rw [Finset.sdiff_sdiff_eq_self hsW] at hh
    have ha : AugmentedFace K s := by
      by_contra h
      exact hout.2 (hh.mpr ⟨Finset.sdiff_subset, h⟩)
    exact (augmented_of_nonempty hs).mp ha
  · intro hs
    have hsW := hW s hs
    refine ⟨(K.isRelLowerSet_faces hs).1, hsW, ?_⟩
    intro hd
    have hh := (dual_augmented W K hp (W \ s)).mp hd
    rw [Finset.sdiff_sdiff_eq_self hsW] at hh
    exact hh.2 (Or.inr hs)

private theorem augmented_retained_exact (P : CollapsePair V) (s : Finset V) :
    AugmentedFace P.retained s ↔
      AugmentedFace P.ambient s ∧ s ≠ P.lower ∧ s ≠ P.upper := by
  by_cases hs : s = ∅
  · subst s
    simp [AugmentedFace, P.lower_nonempty.ne_empty.symm,
      (Finset.insert_nonempty P.apex P.lower).ne_empty.symm]
  · rw [augmented_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hs),
      augmented_of_nonempty (Finset.nonempty_iff_ne_empty.mpr hs)]
    exact P.mem_retained_iff s

private theorem complement_upper (W : Finset V) (P : CollapsePair V)
    (hW : P.upper ⊆ W) : insert P.apex (W \ P.upper) = W \ P.lower := by
  ext v
  have haW : P.apex ∈ W := hW (by simp [CollapsePair.upper])
  simp only [Finset.mem_insert, Finset.mem_sdiff, CollapsePair.upper]
  by_cases hv : v = P.apex
  · subst v
    simp [haW, P.apex_notMem]
  · simp [hv]

private theorem reverse_lower_nonempty (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hp : Proper W D) (P : CollapsePair V) (hP : P.ambient ≤ D) :
    (W \ P.upper).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro h
  exact hp (augmented_downward (Or.inr (hP P.upper_mem)) h)

/-- The actual reversed pair has lower W\\upper, apex unchanged, ambient the
exact retained primal dual. Properness supplies its nonempty lower face. -/
def reversePair (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) (P : CollapsePair V)
    (hP : P.ambient ≤ D) : CollapsePair V where
  ambient := dual W P.retained
  lower := W \ P.upper
  apex := P.apex
  lower_nonempty := reverse_lower_nonempty W D hp P hP
  apex_notMem := by simp [CollapsePair.upper]
  upper_mem := by
    rw [complement_upper W P (hW _ (hP P.upper_mem))]
    refine ⟨?_, Finset.sdiff_subset, ?_⟩
    · exact (reverse_lower_nonempty W D hp P hP).mono
        (Finset.sdiff_subset_sdiff_right W (Finset.subset_insert _ _))
    · rw [Finset.sdiff_sdiff_eq_self (hW _ (hP P.lower_mem))]
      intro h
      have hn := (augmented_retained P P.lower).mp h
      exact hn.2 (Finset.Subset.refl _)
  free := by
    intro s hs hlt
    have hsW : s ⊆ W := hs.2.1
    have hc : W \ s ⊆ P.upper := by
      apply (complement_cross hsW (hW _ (hP P.upper_mem))).mp
      exact hlt.subset
    have hm : AugmentedFace P.ambient (W \ s) :=
      augmented_downward (Or.inr P.upper_mem) hc
    have he : W \ s = P.lower ∨ W \ s = P.upper := by
      by_contra hn
      exact hs.2.2 ((augmented_retained_exact P _).mpr
        ⟨hm, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩)
    rcases he with he | he
    · have he' : s = W \ P.lower := by
        have := congrArg (fun t => W \ t) he
        simpa only [Finset.sdiff_sdiff_eq_self hsW] using this
      exact he'.trans (complement_upper W P (hW _ (hP P.upper_mem))).symm
    · have he' : s = W \ P.upper := by
        have := congrArg (fun t => W \ t) he
        simpa only [Finset.sdiff_sdiff_eq_self hsW] using this
      exact (hlt.ne he'.symm).elim

/-- Exact retained endpoint, as an equality of native complexes on V. -/
theorem reversePair_retained (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) (P : CollapsePair V)
    (hP : P.ambient ≤ D) : (reversePair W D hW hp P hP).retained = dual W P.ambient := by
  apply SetLike.coe_injective
  ext s
  change ((s.Nonempty ∧ s ⊆ W ∧ ¬ AugmentedFace P.retained (W \ s)) ∧
    ¬ W \ P.upper ⊆ s) ↔
    (s.Nonempty ∧ s ⊆ W ∧ ¬ AugmentedFace P.ambient (W \ s))
  constructor
  · rintro ⟨⟨hs, hsW, hn⟩, hf⟩
    refine ⟨hs, hsW, ?_⟩
    intro hm
    have hls : P.lower ⊆ W \ s := by
      by_contra h
      exact hn ((augmented_retained P _).mpr ⟨hm, h⟩)
    have hc : W \ s ⊆ P.upper := by
      rcases hm with he | hm
      · rw [he]; exact empty_subset _
      · by_cases he : W \ s = P.lower
        · rw [he]; exact subset_insert _ _
        · rw [P.free _ hm (Finset.ssubset_iff_subset_ne.mpr ⟨hls, Ne.symm he⟩)]
    apply hf
    have hh := Finset.sdiff_subset_sdiff_right W hc
    simpa only [Finset.sdiff_sdiff_eq_self hsW] using hh
  · rintro ⟨hs, hsW, hn⟩
    refine ⟨⟨hs, hsW, fun h => hn (augmented_mono P.retained_le h)⟩, ?_⟩
    intro hsub
    have hc : W \ s ⊆ P.upper :=
      (complement_cross hsW (hW _ (hP P.upper_mem))).mp hsub
    exact hn (augmented_downward (Or.inr P.upper_mem) hc)

/-- Relation arguments are SOURCE FIRST, OUTPUT SECOND. Forall₂ below explicitly
swaps its output-first list arguments. Endpoint and pair labels are all retained. -/
def ReversePairSpec (W : Finset V) (source output : CollapsePair V) : Prop :=
  output.ambient = dual W source.retained ∧
  output.retained = dual W source.ambient ∧
  output.lower = W \ source.upper ∧ output.upper = W \ source.lower ∧
  output.apex = source.apex ∧
  output.lower.Nonempty ∧ 1 ≤ output.lower.card ∧
  output.upper.card = output.lower.card + 1 ∧
  output.lower.card = W.card - source.upper.card ∧
  (∀ s, AugmentedFace output.ambient s ↔
    s ⊆ W ∧ ¬ AugmentedFace source.retained (W \ s)) ∧
  (∀ s, AugmentedFace output.retained s ↔
    s ⊆ W ∧ ¬ AugmentedFace source.ambient (W \ s))

private theorem reversePair_spec (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) (P : CollapsePair V)
    (hP : P.ambient ≤ D) : ReversePairSpec W P (reversePair W D hW hp P hP) := by
  refine ⟨rfl, reversePair_retained W D hW hp P hP, rfl,
    complement_upper W P (hW _ (hP P.upper_mem)), rfl,
    (reversePair W D hW hp P hP).lower_nonempty,
    (by have h := Finset.card_pos.mpr (reversePair W D hW hp P hP).lower_nonempty; omega),
    Finset.card_insert_of_notMem (reversePair W D hW hp P hP).apex_notMem,
    Finset.card_sdiff_of_subset (hW _ (hP P.upper_mem)),
    dual_augmented W P.retained (proper_mono hp (P.retained_le.trans hP)), ?_⟩
  intro s
  rw [reversePair_retained W D hW hp P hP]
  exact dual_augmented W P.ambient (proper_mono hp hP) s

private def reverseOne (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) (P : CollapsePair V)
    (hP : P.ambient ≤ D) : Sequence (dual W P.retained) (dual W P.ambient) :=
  (Sequence.step (reversePair W D hW hp P hP) (Sequence.refl _)).cast rfl
    (reversePair_retained W D hW hp P hP)

/-- Recursion returns finite computed owner data and reverses the order of pairs. -/
def reverseSequence (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K ≤ D) : Sequence (dual W L) (dual W K) := by
  revert hK
  induction S with
  | refl K => intro hK; exact .refl _
  | @step P L T ih =>
      intro hK
      exact (ih (P.retained_le.trans hK)).append (reverseOne W D hW hp P hK)

private theorem pairs_append_exact {K L M : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) : (S.append T).pairs = S.pairs ++ T.pairs := by
  exact Sequence.pairs_append S T

private theorem frames_append_one {K : PreAbstractSimplicialComplex V}
    (P : CollapsePair V) (S : Sequence K P.ambient) :
    (S.append (Sequence.step P (Sequence.refl _))).frames =
      S.frames ++ [P.retained] := by
  have h : ∀ {A B C : PreAbstractSimplicialComplex V}
      (U : Sequence A B) (T : Sequence B C),
      (U.append T).frames = U.frames ++ T.frames.tail := by
    intro A B C U T
    induction U with
    | refl A => cases T <;> rfl
    | step Q U ih => simp only [Sequence.append, Sequence.frames, ih, List.cons_append]
  simpa only [Sequence.frames, List.tail_cons, List.tail_nil] using
    h S (Sequence.step P (Sequence.refl _))

/-- Every reversed ordered pair has the exact complement labels and endpoints. -/
theorem reverseSequence_pairs (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K ≤ D) :
    List.Forall₂ (fun output source => ReversePairSpec W source output)
      (reverseSequence W D hW hp S hK).pairs S.pairs.reverse := by
  revert hK
  induction S with
  | refl K => intro hK; exact .nil
  | @step P L T ih =>
      intro hK
      simp only [reverseSequence, pairs_append_exact, reverseOne, Sequence.pairs_cast,
        Sequence.pairs, List.reverse_cons]
      apply List.rel_append (ih (P.retained_le.trans hK))
      exact .cons (reversePair_spec W D hW hp P hK) .nil

private theorem append_cast_right {K L M M' : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (T : Sequence L M) (h : M = M') :
    S.append (T.cast rfl h) = (S.append T).cast rfl h := by
  subst M'
  rfl

/-- All intermediate complexes are literally duals of the reversed original
frames. This includes both endpoints and has no default-frame ambiguity. -/
theorem reverseSequence_frames (W : Finset V) (D : PreAbstractSimplicialComplex V)
    (hW : Supported W D) (hp : Proper W D) {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hK : K ≤ D) :
    (reverseSequence W D hW hp S hK).frames = S.frames.reverse.map (dual W) := by
  revert hK
  induction S with
  | refl K => intro hK; rfl
  | @step P L T ih =>
      intro hK
      change ((reverseSequence W D hW hp T (P.retained_le.trans hK)).append
        (reverseOne W D hW hp P hK)).frames = _
      unfold reverseOne
      rw [append_cast_right, Sequence.frames_cast]
      calc
        _ = (reverseSequence W D hW hp T (P.retained_le.trans hK)).frames ++
            [(reversePair W D hW hp P hK).retained] :=
          frames_append_one (reversePair W D hW hp P hK)
            (reverseSequence W D hW hp T (P.retained_le.trans hK))
        _ = _ := by
          rw [reversePair_retained, ih (P.retained_le.trans hK)]
          simp [Sequence.frames, List.reverse_cons, List.map_append]

/-- Lift over a cone on ANY retained subcomplex. The existing owner operation
extendAcrossCone is the special case B=L; its pair constructor is reused here. -/
def extendOverRetainedCone {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (B : PreAbstractSimplicialComplex V) (hB : B ≤ L) (a : V) (ha : Fresh a K) :
    Sequence (K ⊔ cone a B) (L ⊔ cone a B) := by
  revert hB ha
  induction S with
  | refl K => intro hB ha; exact .refl _
  | @step P L T ih =>
      intro hB ha
      let R := Pair.extendCone P B a (hB.trans T.monotone) ha
      have ht := ih hB (fun s hs => ha s hs.1)
      exact .step R (ht.cast (Pair.extendCone_retained P B a
        (hB.trans T.monotone) ha).symm rfl)

/-- Deleting a maximal face is downward closed. Maximality, not just membership,
is used to prevent a surviving face from having the deleted face as a subface. -/
def removeMax (Q : PreAbstractSimplicialComplex V) (sigma : Finset V)
    (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ Q ∧ s ≠ sigma}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hn⟩
    refine ⟨(Q.isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    refine ⟨(Q.isRelLowerSet_faces hs).2 hts ht, ?_⟩
    intro he
    exact hn (hmax s hs (he ▸ hts))

private theorem removeMax_le (Q : PreAbstractSimplicialComplex V) (sigma : Finset V)
    (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma) : removeMax Q sigma hmax ≤ Q :=
  fun _ hs => hs.1

/-- Empty augmented face survives; deleting the empty face is excluded. -/
theorem removeMax_augmented (Q : PreAbstractSimplicialComplex V) (sigma : Finset V)
    (hsigma : sigma.Nonempty) (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma)
    (s : Finset V) :
    AugmentedFace (removeMax Q sigma hmax) s ↔ AugmentedFace Q s ∧ s ≠ sigma := by
  constructor
  · rintro (rfl | ⟨hs, hn⟩)
    · exact ⟨Or.inl rfl, hsigma.ne_empty.symm⟩
    · exact ⟨Or.inr hs, hn⟩
  · rintro ⟨(he | hm), hn⟩
    · exact Or.inl he
    · exact Or.inr ⟨hm, hn⟩

/-- Full coordinate simplex; empty face exists only in AugmentedFace. -/
def simplex (lambda : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ⊆ lambda}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsl⟩
    exact ⟨hs, fun t hts ht => ⟨ht, hts.trans hsl⟩⟩

/-- Entire boundary, including the augmented empty face for a singleton lambda.
For lambda empty this native skeleton is empty; we use it only with lambda nonempty. -/
def boundary (lambda : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ⊂ lambda}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsl⟩
    refine ⟨hs, ?_⟩
    intro t hts ht
    exact ⟨ht, Finset.ssubset_iff_subset_ne.mpr
      ⟨hts.trans hsl.subset, fun he => hsl.not_ge (he ▸ hts)⟩⟩

private theorem sigma_subset_complement {W sigma s : Finset V}
    (hsigma : sigma ⊆ W) (hs : s ⊆ W \ sigma) : sigma ⊆ W \ s := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨hsigma hv, ?_⟩
  intro hvs
  exact (Finset.mem_sdiff.mp (hs hvs)).2 hv

private theorem maximal_complement_not_face (W : Finset V)
    (Q : PreAbstractSimplicialComplex V) (sigma : Finset V)
    (hsigma : sigma.Nonempty) (hsW : sigma ⊆ W)
    (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma)
    {s : Finset V} (hs : s ⊂ W \ sigma) : ¬ AugmentedFace Q (W \ s) := by
  intro hm
  have hsub := sigma_subset_complement hsW hs.subset
  have hne : (W \ s).Nonempty := hsigma.mono hsub
  have he := hmax _ ((augmented_of_nonempty hne).mp hm) hsub
  have he' : s = W \ sigma := by
    have hh := congrArg (fun t => W \ t) he
    simpa only [Finset.sdiff_sdiff_eq_self (hs.subset.trans Finset.sdiff_subset)] using hh
  exact hs.ne he'

/-- The critical deletion adds the FULL complementary simplex in the dual. -/
theorem critical_dual_union (W : Finset V) (Q : PreAbstractSimplicialComplex V)
    (hW : Supported W Q) (sigma : Finset V) (hsigma : sigma.Nonempty)
    (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma) (hsQ : sigma ∈ Q) :
    dual W (removeMax Q sigma hmax) = dual W Q ⊔ simplex (W \ sigma) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hs, hsW, hn⟩
    by_cases hm : AugmentedFace Q (W \ s)
    · right
      have he : W \ s = sigma := by
        by_contra he
        exact hn ((removeMax_augmented Q sigma hsigma hmax _).mpr ⟨hm, he⟩)
      have he' : s = W \ sigma := by
        have hh := congrArg (fun t => W \ t) he
        simpa only [Finset.sdiff_sdiff_eq_self hsW] using hh
      exact ⟨hs, by rw [he']⟩
    · exact Or.inl ⟨hs, hsW, hm⟩
  · rintro (hs | hs)
    · exact (dual_antitone W (removeMax_le Q sigma hmax)) hs
    · refine ⟨hs.1, hs.2.trans Finset.sdiff_subset, ?_⟩
      intro hm
      have hm' := (removeMax_augmented Q sigma hsigma hmax _).mp hm
      have hsub := sigma_subset_complement (hW _ hsQ) hs.2
      have hne : (W \ s).Nonempty := hsigma.mono hsub
      exact hm'.2 (hmax _ ((augmented_of_nonempty hne).mp hm'.1) hsub)

/-- Its overlap with the old dual is exactly the entire complementary boundary. -/
theorem critical_dual_intersection (W : Finset V) (Q : PreAbstractSimplicialComplex V)
    (hW : Supported W Q) (sigma : Finset V) (hsigma : sigma.Nonempty)
    (hmax : ∀ t ∈ Q, sigma ⊆ t → t = sigma) (hsQ : sigma ∈ Q) :
    dual W Q ⊓ simplex (W \ sigma) = boundary (W \ sigma) := by
  apply SetLike.coe_injective
  ext s
  constructor
  · rintro ⟨hd, hs⟩
    refine ⟨hs.1, Finset.ssubset_iff_subset_ne.mpr ⟨hs.2, ?_⟩⟩
    intro he
    apply hd.2.2
    rw [he, Finset.sdiff_sdiff_eq_self (hW _ hsQ)]
    exact Or.inr hsQ
  · rintro ⟨hs, hsl⟩
    exact ⟨⟨hs, hsl.subset.trans Finset.sdiff_subset,
      maximal_complement_not_face W Q sigma hsigma (hW _ hsQ) hmax hsl⟩,
      ⟨hs, hsl.subset⟩⟩

private theorem boundary_augmented (lambda : Finset V) (hl : lambda.Nonempty)
    (s : Finset V) : AugmentedFace (boundary lambda) s ↔ s ⊂ lambda := by
  constructor
  · rintro (rfl | hs)
    · exact Finset.ssubset_iff_subset_ne.mpr ⟨empty_subset _, hl.ne_empty.symm⟩
    · exact hs.2
  · intro hs
    by_cases he : s = ∅
    · exact Or.inl he
    · exact Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr he, hs⟩

/-- Finite, computable membership table: no face is omitted from the fixed W. -/
def dualTable (W : Finset V) (faces : Finset (Finset V)) : Finset (Finset V) :=
  W.powerset.filter (fun s => W \ s ∉ faces)

/-- A finite output with a total exact augmented-to-native bridge. It is used only
on the proper domain; full-simplex void duals are never re-augmented. -/
structure FiniteDualData (W : Finset V) (K : PreAbstractSimplicialComplex V)
    (hp : Proper W K) where
  faces : Finset (Finset V)
  exact_faces : ∀ s, s ∈ faces ↔ AugmentedFace (dual W K) s
  reconstruct : Supported W K → dual W (dual W K) = K

private def finiteDualData (W : Finset V) (K : PreAbstractSimplicialComplex V)
    (hp : Proper W K) (faces : Finset (Finset V))
    (hfaces : ∀ s, s ∈ faces ↔ AugmentedFace K s) : FiniteDualData W K hp where
  faces := dualTable W faces
  exact_faces := by
    intro s
    rw [dual_augmented W K hp]
    simp only [dualTable, Finset.mem_filter, Finset.mem_powerset, hfaces]
  reconstruct := fun hW => dual_involutive W K hW hp

/-- Purely finite certificate. The two sequences are DATA, and the critical
maximal-face deletion is separate from the ordinary nonempty-lower collapse lists.
E<=D is derived below rather than supplied a second time. -/
structure Certificate (V : Type*) [Fintype V] [DecidableEq V] where
  W : Finset V
  D : PreAbstractSimplicialComplex V
  E : PreAbstractSimplicialComplex V
  Q : PreAbstractSimplicialComplex V
  Dfaces : Finset (Finset V)
  Efaces : Finset (Finset V)
  Qfaces : Finset (Finset V)
  Dfaces_exact : ∀ s, s ∈ Dfaces ↔ AugmentedFace D s
  Efaces_exact : ∀ s, s ∈ Efaces ↔ AugmentedFace E s
  Qfaces_exact : ∀ s, s ∈ Qfaces ↔ AugmentedFace Q s
  supported_D : Supported W D
  proper_D : Proper W D
  first : Sequence D Q
  sigma : Finset V
  sigma_nonempty : sigma.Nonempty
  sigma_mem : sigma ∈ Q
  sigma_maximal : ∀ t ∈ Q, sigma ⊆ t → t = sigma
  sigma_not_E : sigma ∉ E
  second : Sequence (removeMax Q sigma sigma_maximal) E
  a : V
  a_not_W : a ∉ W

namespace Certificate
variable (c : Certificate V)

abbrev Qprime : PreAbstractSimplicialComplex V :=
  removeMax c.Q c.sigma c.sigma_maximal
abbrev lambda : Finset V := c.W \ c.sigma
abbrev d : ℕ := c.lambda.card - 1
abbrev Dstar : PreAbstractSimplicialComplex V := dual c.W c.D
abbrev Estar : PreAbstractSimplicialComplex V := dual c.W c.E
abbrev Qstar : PreAbstractSimplicialComplex V := dual c.W c.Q
abbrev QprimeStar : PreAbstractSimplicialComplex V := dual c.W c.Qprime
abbrev C : PreAbstractSimplicialComplex V := cone c.a c.Dstar
abbrev K : PreAbstractSimplicialComplex V := c.Estar ⊔ c.C
abbrev X : PreAbstractSimplicialComplex V := c.QprimeStar ⊔ c.C
abbrev P : PreAbstractSimplicialComplex V := c.Qstar ⊔ c.C

private theorem Q_le_D : c.Q ≤ c.D := c.first.monotone
private theorem Qprime_le_D : c.Qprime ≤ c.D :=
  (removeMax_le c.Q c.sigma c.sigma_maximal).trans c.Q_le_D
private theorem E_le_D : c.E ≤ c.D := c.second.monotone.trans c.Qprime_le_D
private theorem supported_Q : Supported c.W c.Q := supported_mono c.supported_D c.Q_le_D
private theorem fresh_dual (T : PreAbstractSimplicialComplex V) : Fresh c.a (dual c.W T) := by
  intro s hs ha
  exact c.a_not_W (dual_supported c.W T s hs ha)

/-- Nonempty complementary face and exact arithmetic, without negative dimensions
or silently truncated identities. The disjoint split uses the original W. -/
theorem arithmetic :
    c.lambda.Nonempty ∧ Disjoint c.sigma c.lambda ∧ c.sigma ∪ c.lambda = c.W ∧
    c.W.card = c.sigma.card + c.lambda.card ∧ 2 ≤ c.W.card ∧
    c.d + 1 = c.lambda.card ∧ c.d = c.W.card - c.sigma.card - 1 := by
  have hsW : c.sigma ⊆ c.W := c.supported_Q _ c.sigma_mem
  have hl : c.lambda.Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact c.proper_D (augmented_downward (Or.inr (c.Q_le_D c.sigma_mem)) h)
  have hc := Finset.card_sdiff_add_card_eq_card hsW
  have hcLambda : c.lambda.card + c.sigma.card = c.W.card := hc
  have hsc : 0 < c.sigma.card := Finset.card_pos.mpr c.sigma_nonempty
  have hlc : 0 < c.lambda.card := Finset.card_pos.mpr hl
  refine ⟨hl, Finset.disjoint_sdiff, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_sdiff_of_subset hsW
  · change c.W.card = c.sigma.card + (c.W \ c.sigma).card
    omega
  · omega
  · change c.lambda.card - 1 + 1 = c.lambda.card
    omega
  · change c.lambda.card - 1 = c.W.card - c.sigma.card - 1
    change (c.W \ c.sigma).card + c.sigma.card = c.W.card at hc
    omega

/-- Finite critical deletion table; empty stays because sigma is nonempty. -/
def QprimeFaces : Finset (Finset V) := c.Qfaces.erase c.sigma

private theorem QprimeFaces_exact (s : Finset V) :
    s ∈ c.QprimeFaces ↔ AugmentedFace c.Qprime s := by
  rw [removeMax_augmented c.Q c.sigma c.sigma_nonempty c.sigma_maximal s]
  simp only [QprimeFaces, Finset.mem_erase, c.Qfaces_exact]
  exact and_comm

/-- Actual finite computed dual membership tables, all on the original W. -/
def dualData :
    FiniteDualData c.W c.D c.proper_D ×
    FiniteDualData c.W c.E (proper_mono c.proper_D c.E_le_D) ×
    FiniteDualData c.W c.Q (proper_mono c.proper_D c.Q_le_D) ×
    FiniteDualData c.W c.Qprime (proper_mono c.proper_D c.Qprime_le_D) :=
  ⟨finiteDualData c.W c.D c.proper_D c.Dfaces c.Dfaces_exact,
   finiteDualData c.W c.E (proper_mono c.proper_D c.E_le_D) c.Efaces c.Efaces_exact,
   finiteDualData c.W c.Q (proper_mono c.proper_D c.Q_le_D) c.Qfaces c.Qfaces_exact,
   finiteDualData c.W c.Qprime (proper_mono c.proper_D c.Qprime_le_D)
     c.QprimeFaces c.QprimeFaces_exact⟩

/-- Only a coordinate ordering for the complementary disk; it does not change
any primal/dual ground or erase ghost labels from a complement. -/
def lambdaCoordinates : c.lambda ≃ Fin c.lambda.card := c.lambda.equivFin

/-- The primal second list, reversed and complemented, computes E* -> Q'*. -/
def firstDual : Sequence c.Estar c.QprimeStar :=
  reverseSequence c.W c.D c.supported_D c.proper_D c.second c.Qprime_le_D

/-- The first primal list gives Q* -> D*, independently of the attached disk. -/
def secondDual : Sequence c.Qstar c.Dstar :=
  reverseSequence c.W c.D c.supported_D c.proper_D c.first le_rfl

/-- Adding the cone on D* to the first dual list fixes that ENTIRE cone. -/
def reduction : Sequence c.K c.X :=
  extendOverRetainedCone c.firstDual c.Dstar
    (dual_antitone c.W c.Qprime_le_D) c.a (c.fresh_dual c.E)

/-- This collapse is of P alone. It is never performed inside X. -/
def collapseP : Sequence c.P c.C :=
  c.secondDual.extendAcrossCone c.a (c.fresh_dual c.Q)

/-- Actual coordinate inclusion j:D* -> E*, not a substituted null map. -/
def j : C(Space c.Dstar, Space c.Estar) := realizationInclusion (dual_antitone c.W c.E_le_D)

/-- Computed SDRs expose the existing owner's actual maps, rather than taking
retractions, homotopies or a topological outcome as certificate fields. -/
def reductionSDR : RelativeSDR c.K c.X c.reduction.monotone := c.reduction.realize

def pSDR : RelativeSDR c.P c.C c.collapseP.monotone := c.collapseP.realize

/-- Computed contraction of P, using the original cone coordinate owner.
The returned homotopy is relative to the actual included cone apex. -/
def pContraction : (ContinuousMap.id (Space c.P)).HomotopyRel
    (ContinuousMap.const _
      (realizationInclusion (show c.C ≤ c.P from le_sup_right) (conePoint c.a c.Dstar)))
    {realizationInclusion (show c.C ≤ c.P from le_sup_right)
      (conePoint c.a c.Dstar)} :=
  c.secondDual.coneExtensionContraction c.a (c.fresh_dual c.Q)

/-- Pointwise fixed-apex law for the actual pContraction. -/
theorem pContraction_fixed_apex (t : I) :
    c.pContraction (t,
      realizationInclusion (show c.C ≤ c.P from le_sup_right)
        (conePoint c.a c.Dstar)) =
      realizationInclusion (show c.C ≤ c.P from le_sup_right)
        (conePoint c.a c.Dstar) :=
  c.pContraction.eq_fst t (by simp)

/-- Exact cell union after the first relative reduction. -/
theorem cell_decomposition : c.X = c.P ⊔ simplex c.lambda := by
  have h := critical_dual_union c.W c.Q c.supported_Q c.sigma
    c.sigma_nonempty c.sigma_maximal c.sigma_mem
  change dual c.W c.Qprime ⊔ c.C = (dual c.W c.Q ⊔ c.C) ⊔ simplex c.lambda
  rw [h]
  exact sup_right_comm _ _ _

private theorem cone_overlap (s : Finset V) (hc : s ∈ c.C) (hs : s ∈ simplex c.lambda) :
    s ∈ c.Qstar := by
  have ha : c.a ∉ s := fun h => c.a_not_W (hs.2.trans Finset.sdiff_subset h)
  have hd : AugmentedFace c.Dstar s := by
    simpa only [Finset.erase_eq_of_notMem ha] using hc.2
  have hd' : s ∈ c.Dstar := (augmented_of_nonempty hs.1).mp hd
  exact (dual_antitone c.W c.Q_le_D) hd'

/-- The cone introduces no extra disk intersection: full boundary, also when
lambda has one label (ordinary boundary empty, augmented boundary {empty}). -/
theorem cell_intersection :
    c.P ⊓ simplex c.lambda = boundary c.lambda ∧
    (∀ s, AugmentedFace (boundary c.lambda) s ↔ s ⊂ c.lambda) ∧
    (c.lambda.card = 1 → boundary c.lambda = ⊥) := by
  refine ⟨?_, (fun s => boundary_augmented c.lambda c.arithmetic.1 s), ?_⟩
  · have h := critical_dual_intersection c.W c.Q c.supported_Q c.sigma
      c.sigma_nonempty c.sigma_maximal c.sigma_mem
    apply SetLike.coe_injective
    ext s
    constructor
    · rintro ⟨(hs | hs), hl⟩
      · have hm : s ∈ c.Qstar ⊓ simplex c.lambda := ⟨hs, hl⟩
        rw [h] at hm
        exact hm
      · have hm : s ∈ c.Qstar ⊓ simplex c.lambda := ⟨c.cone_overlap s hs hl, hl⟩
        rw [h] at hm
        exact hm
    · intro hs
      have hm : s ∈ c.Qstar ⊓ simplex c.lambda := by rw [h]; exact hs
      exact ⟨Or.inl hm.1, hm.2⟩
  · intro hm
    apply SetLike.coe_injective
    ext s
    constructor
    · intro hs
      have hc := Finset.card_lt_card hs.2
      have hp := Finset.card_pos.mpr hs.1
      omega
    · intro hs
      exact hs.elim

/-- Lambda is an actual nonempty E* face, even if D* or Q* has no ordinary point. -/
theorem complementary_face : c.lambda ∈ c.Estar := by
  refine ⟨c.arithmetic.1, Finset.sdiff_subset, ?_⟩
  rw [Finset.sdiff_sdiff_eq_self (c.supported_Q _ c.sigma_mem)]
  exact fun h => c.sigma_not_E ((augmented_of_nonempty c.sigma_nonempty).mp h)

/- The ordinary Euclidean sphere and based sphere constructions remain outside
   this finite certificate source. Their exact missing endpoint work is recorded
   in the implementation envelope; no obligation definition is retained here. -/

end Certificate
end D5.S3.Geometry.FiniteAlexanderDualCollapse

/- GID: D5/S3/Geometry/FiniteMatchingCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteMatchingCollapse
   mirror-E: none(waiver:finite-matching-collapse-extraction)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Finite acyclic face matchings construct native collapse sequences to saturated subcomplexes. -/
import D5.S3.Geometry.FiniteAcyclicFaceMatching

/-! UNCOMPILED. Strong induction removes a proved free source pair from the
actual evolving complex. The finite matching and target saturation are purely
combinatorial hypotheses. Sequence, CollapsePair and RelativeSDR retain their
existing native owners. -/

noncomputable section
open Set Finset

namespace D5.S3.Geometry.FiniteMatchingCollapse

open FiniteAcyclicFaceMatching FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse
open FiniteVertexDominationCollapse (faceSet mem_faceSet)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replay an arbitrary native sequence by deleting its actual pair prefix. -/
theorem frame_mem {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (i : Nat) (hi : i ≤ S.pairs.length) (s : Finset V) :
    s ∈ S.frames.getD i L ↔ s ∈ K ∧
      ∀ P ∈ S.pairs.take i, s ≠ P.lower ∧ s ≠ P.upper := by
  induction S generalizing i with
  | refl K =>
      have hi0 : i = 0 := by simpa [Sequence.pairs] using hi
      subst i
      simp [Sequence.frames, Sequence.pairs]
  | step P T ih =>
      cases i with
      | zero => simp [Sequence.frames, Sequence.pairs]
      | succ i =>
          have hi' : i ≤ T.pairs.length := by simpa [Sequence.pairs] using hi
          change s ∈ T.frames.getD i L ↔ s ∈ P.ambient ∧
            ∀ Q ∈ P :: T.pairs.take i, s ≠ Q.lower ∧ s ≠ Q.upper
          rw [ih i hi', P.mem_retained_iff]
          constructor
          · rintro ⟨⟨hs, hl, hu⟩, htail⟩
            exact ⟨hs, fun Q hQ => (List.mem_cons.mp hQ).elim
              (fun he => he ▸ ⟨hl, hu⟩) (fun h => htail Q h)⟩
          · rintro ⟨hs, hQ⟩
            exact ⟨⟨hs, (hQ P (by simp)).1, (hQ P (by simp)).2⟩,
              fun Q h => hQ Q (List.mem_cons_of_mem P h)⟩

theorem frames_terminal {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : S.frames.getD S.pairs.length L = L := by
  induction S with
  | refl K => rfl
  | step P T ih => exact ih

theorem elementary_face_count (P : CollapsePair V) :
    (faceSet P.ambient).card = (faceSet P.retained).card + 2 := by
  classical
  have hne : P.lower ≠ P.upper := by
    intro h
    exact P.apex_notMem (h.symm ▸ Finset.mem_insert_self _ _)
  have hl : P.lower ∉ faceSet P.retained := by
    simp only [mem_faceSet, P.mem_retained_iff]
    exact fun h => h.2.1 rfl
  have hu : P.upper ∉ faceSet P.retained := by
    simp only [mem_faceSet, P.mem_retained_iff]
    exact fun h => h.2.2 rfl
  have heq : faceSet P.ambient = insert P.lower (insert P.upper (faceSet P.retained)) := by
    ext s
    simp only [mem_faceSet, Finset.mem_insert, P.mem_retained_iff]
    constructor
    · intro hs
      by_cases hsl : s = P.lower
      · exact Or.inl hsl
      · by_cases hsu : s = P.upper
        · exact Or.inr (Or.inl hsu)
        · exact Or.inr (Or.inr ⟨hs, hsl, hsu⟩)
    · rintro (rfl | rfl | ⟨hs, _, _⟩)
      · exact P.lower_mem
      · exact P.upper_mem
      · exact hs
  rw [heq, Finset.card_insert_of_notMem (by simp [hne, hl]),
    Finset.card_insert_of_notMem hu]
  omega

/-- Every actual step removes two distinct nonempty faces. -/
theorem sequence_face_count {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) :
    (faceSet K).card = (faceSet L).card + 2 * S.pairs.length := by
  induction S with
  | refl K => simp [Sequence.pairs]
  | step P T ih =>
      rw [elementary_face_count P, ih]
      simp [Sequence.pairs, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pair_ambient_le_source {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (P : CollapsePair V) (hP : P ∈ S.pairs) : P.ambient ≤ K := by
  revert hP
  induction S with
  | refl K => intro hP; simp [Sequence.pairs] at hP
  | step Q T ih =>
      intro hP
      rcases List.mem_cons.mp hP with rfl | hP
      · exact le_rfl
      · exact (ih hP).trans Q.retained_le

theorem sequence_lowers_nodup {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : (S.pairs.map CollapsePair.lower).Nodup := by
  induction S with
  | refl K => simp [Sequence.pairs]
  | step P T ih =>
      change (P.lower :: T.pairs.map CollapsePair.lower).Nodup
      apply List.nodup_cons.mpr
      refine ⟨?_, ih⟩
      intro hm
      obtain ⟨Q, hQ, heq⟩ := List.mem_map.mp hm
      have hret : Q.lower ∈ P.retained := pair_ambient_le_source T Q hQ Q.lower_mem
      have hh := (P.mem_retained_iff Q.lower).mp hret
      exact hh.2.1 heq

theorem matching_pair_occurs {K L T : PreAbstractSimplicialComplex V}
    (M : Pairing K) (S : Sequence L T)
    (hS : ∀ P ∈ S.pairs, (P.lower, P.apex) ∈ M.pairs)
    (e : Finset V × V) (he : e ∈ M.pairs) (hl : e.1 ∈ L) :
    (∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ T := by
  classical
  constructor
  · rintro ⟨P, hP, hPe⟩ ht
    have hret := S.final_le_each_retained hP ht
    have hlP : e.1 = P.lower := (congrArg Prod.fst hPe).symm
    exact ((P.mem_retained_iff e.1).mp hret).2.1 hlP
  · intro ht
    by_contra hnone
    apply ht
    have hf := frame_mem S S.pairs.length le_rfl e.1
    rw [frames_terminal S, List.take_length] at hf
    apply hf.mpr ⟨hl, ?_⟩
    intro P hP
    have hPe := hS P hP
    have hsep : ¬ Incident e.1 (P.lower, P.apex) := by
      intro hi
      have heq := M.disjoint e he (P.lower, P.apex) hPe e.1 (Or.inl rfl) hi
      exact hnone ⟨P, hP, heq.symm⟩
    exact ⟨fun h => hsep (Or.inl h), fun h => hsep (Or.inr h)⟩

theorem frames_supported {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (W : Finset V) (hW : ∀ s ∈ K, s ⊆ W)
    (J : PreAbstractSimplicialComplex V) (hJ : J ∈ S.frames) :
    ∀ s ∈ J, s ⊆ W :=
  fun s hs => hW s (S.frames_le_source J hJ hs)

namespace Pairing

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

private theorem source_retained_target {L T : PreAbstractSimplicialComplex V}
    (hLK : L ≤ K) (hTL : T ≤ L) (hL : M.Saturated L)
    (e : Finset V × V) (he : e ∈ M.pairs) (hlL : e.1 ∈ L)
    (hlT : e.1 ∉ T) (hs : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) :
    T ≤ (M.sourcePair hLK hTL hL e he hlL hlT hs).retained := by
  intro s hsT
  refine ⟨hTL hsT, ?_⟩
  intro hls
  exact hlT ((T.isRelLowerSet_faces hsT).2 hls (M.lower_nonempty e he))

private theorem source_retained_saturated {L T : PreAbstractSimplicialComplex V}
    (hLK : L ≤ K) (hTL : T ≤ L) (hL : M.Saturated L)
    (e : Finset V × V) (he : e ∈ M.pairs) (hlL : e.1 ∈ L)
    (hlT : e.1 ∉ T) (hs : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) :
    M.Saturated (M.sourcePair hLK hTL hL e he hlL hlT hs).retained := by
  let P := M.sourcePair hLK hTL hL e he hlL hlT hs
  intro f hf
  by_cases hef : e = f
  · subst f
    simp only [P.mem_retained_iff]
    constructor <;> intro h
    · exact (h.2.1 rfl).elim
    · exact (h.2.2 rfl).elim
  · have hsep : ∀ s, Incident s f → s ≠ e.1 ∧ s ≠ upper e := by
      intro s hsf
      constructor
      · intro hse
        exact hef (M.disjoint e he f hf s (Or.inl hse) hsf)
      · intro hse
        exact hef (M.disjoint e he f hf s (Or.inr hse) hsf)
    rw [P.mem_retained_iff, P.mem_retained_iff]
    change (f.1 ∈ L ∧ f.1 ≠ e.1 ∧ f.1 ≠ upper e) ↔
      (upper f ∈ L ∧ upper f ≠ e.1 ∧ upper f ≠ upper e)
    exact ⟨fun h => ⟨(hL f hf).mp h.1, hsep _ (Or.inr rfl)⟩,
      fun h => ⟨(hL f hf).mpr h.1, hsep _ (Or.inl rfl)⟩⟩

/-- Actual finite extraction, including its integration invariant: every pair
in the native sequence is one of the original matching pairs. -/
theorem sequence_exists (hacyc : M.IsAcyclic)
    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)
    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)
    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) :
    ∃ S : Sequence L T, ∀ P ∈ S.pairs,
      (P.lower, P.apex) ∈ M.pairs := by
  classical
  have aux : ∀ n : Nat, ∀ L : PreAbstractSimplicialComplex V,
      (faceSet L).card = n → L ≤ K → T ≤ L → M.Saturated L →
      (∀ s ∈ L, M.Unmatched s → s ∈ T) → ∃ S : Sequence L T, ∀ P ∈ S.pairs, (P.lower, P.apex) ∈ M.pairs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro L hn hLK hTL hL hcritL
        by_cases hLT : L = T
        · subst L
          exact ⟨.refl T, by simp [Sequence.pairs]⟩
        · obtain ⟨e, he, hlL, hlT, hs⟩ := M.source_lower hacyc hLK hTL hL hT
            hcritL hLT
          let P := M.sourcePair hLK hTL hL e he hlL hlT hs
          have hpT : T ≤ P.retained := M.source_retained_target hLK hTL hL e he hlL hlT hs
          have hpS : M.Saturated P.retained :=
            M.source_retained_saturated hLK hTL hL e he hlL hlT hs
          have hsmall : (faceSet P.retained).card < n := by
            have hc := elementary_face_count P
            change (faceSet L).card = _ at hc
            omega
          obtain ⟨S, hS⟩ := ih _ hsmall P.retained rfl
            (P.retained_le.trans hLK) hpT hpS
            (fun s hs hu => hcritL s (P.retained_le hs) hu)
          refine ⟨.step P S, ?_⟩
          intro Q hQ
          rcases List.mem_cons.mp hQ with rfl | hQ
          · exact he
          · exact hS Q hQ
  exact aux _ L rfl hLK hTL hL hcrit

/-- A definite finite native sequence, chosen from the construction above. -/
def collapseBetween (hacyc : M.IsAcyclic)
    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)
    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)
    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) : Sequence L T :=
  (M.sequence_exists hacyc T hTK hT L hLK hTL hL hcrit).choose

theorem collapseBetween_pairs (hacyc : M.IsAcyclic)
    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)
    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)
    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) (P : CollapsePair V)
    (hP : P ∈ (M.collapseBetween hacyc T hTK hT L hLK hTL hL hcrit).pairs) :
    (P.lower, P.apex) ∈ M.pairs :=
  (M.sequence_exists hacyc T hTK hT L hLK hTL hL hcrit).choose_spec P hP

/-- Native original-coordinate SDR, fixing ALL of the target. -/
def sdrBetween (hacyc : M.IsAcyclic)
    (T : PreAbstractSimplicialComplex V) (hTK : T ≤ K) (hT : M.Saturated T)
    (L : PreAbstractSimplicialComplex V) (hLK : L ≤ K) (hTL : T ≤ L)
    (hL : M.Saturated L) (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T) : RelativeSDR L T hTL :=
  (M.collapseBetween hacyc T hTK hT L hLK hTL hL hcrit).realize

end Pairing
end D5.S3.Geometry.FiniteMatchingCollapse

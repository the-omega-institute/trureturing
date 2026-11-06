/- GID: D5/S3/Geometry/FiniteVertexDominationCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteVertexDominationCollapse
   mirror-E: none(waiver:original-label-elementary-domination)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: A dominated vertex admits a complete original-label finite free-face deletion certificate. -/
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/- SOURCE ATTEMPT — UNCOMPILED. No kernel, axioms, Scribe/Reg, admission, or
   publication result is claimed. Input hashes and additive integration are
   recorded in the companion JSON, outside this canonical seven-line header. -/

/-!
The finite pairing proof is the classical dominated-vertex collapse: remove
faces containing v and omitting u in decreasing cardinality, pairing each with
its u-extension. The ordinary proof reused here is the released CLI79532
verification, constructive_restricted_result.K_elementary_fold and
actual_Ind_F_certificate.graph_fold (2026-11-05); no novelty is claimed.

All complexes and pairs stay on V, including its ghost labels. Every lower
face is nonempty. The recursion proves freeness in the ACTUAL retained complex;
it neither postulates a matching nor transports one through a homeomorphism.
The resulting SDR is the native elementary-sequence SDR. It is not asserted
to be the simultaneous coordinate-transfer homotopy of the existing graph
fold library. Nothing here supplies the universal root-K or sphere/collar
obligations of the broader geometry project.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset Topology
open scoped unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteVertexDominationCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation FiniteElementaryCollapse
open FiniteRelativeSimplicialCollapse FiniteGraphVertexSubstitution

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A face-extension hypothesis, with no collapse or topological data. -/
def Extends (K : PreAbstractSimplicialComplex V) (u v : V) : Prop :=
  ∀ s ∈ K, v ∈ s → insert u s ∈ K

/-- Exactly the possible lower faces, not including an augmented empty face. -/
def badFaces (K : PreAbstractSimplicialComplex V) (u v : V) : Finset (Finset V) :=
  by classical exact Finset.univ.filter fun s => s ∈ K ∧ v ∈ s ∧ u ∉ s

@[simp] theorem mem_badFaces (K : PreAbstractSimplicialComplex V) (u v : V)
    (s : Finset V) : s ∈ badFaces K u v ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s := by
  classical
  simp [badFaces]

/-- The literal finite face family. Empty faces contribute no count. -/
def faceSet (K : PreAbstractSimplicialComplex V) : Finset (Finset V) :=
  by classical exact Finset.univ.filter fun s => s ∈ K

@[simp] theorem mem_faceSet (K : PreAbstractSimplicialComplex V) (s : Finset V) :
    s ∈ faceSet K ↔ s ∈ K := by
  classical
  simp [faceSet]

/-- No candidate lower face is exactly the ghost-v case, even if u is a ghost. -/
theorem badFaces_empty_iff (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) : badFaces K u v = ∅ ↔ Fresh v K := by
  classical
  constructor
  · intro he s hs hv
    have hsing : ({v} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hs).2 (by simpa using hv) (Finset.singleton_nonempty v)
    have hb : ({v} : Finset V) ∈ badFaces K u v :=
      (mem_badFaces K u v _).2 ⟨hsing, by simp, by simpa using huv⟩
    rw [he] at hb
    exact Finset.notMem_empty _ hb
  · intro hf
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hh := (mem_badFaces K u v s).1 hs
    exact hf s hh.1 hh.2.1

private theorem deletion_eq_of_fresh (K : PreAbstractSimplicialComplex V)
    (v : V) (hf : Fresh v K) : deletion K v = K := by
  apply le_antisymm (deletion_le K v)
  intro s hs
  exact ⟨hs, hf s hs⟩

/-- Select one maximum-cardinality lower face in the CURRENT complex and prove
its actual unique-strict-coface condition. This is the essential free-pair step. -/
private def maximalPair (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V)
    (hs : s ∈ badFaces K u v)
    (hmax : ∀ t ∈ badFaces K u v, t.card ≤ s.card) : CollapsePair V where
  ambient := K
  lower := s
  apex := u
  lower_nonempty := ⟨v, ((mem_badFaces K u v s).1 hs).2.1⟩
  apex_notMem := ((mem_badFaces K u v s).1 hs).2.2
  upper_mem := hExt s ((mem_badFaces K u v s).1 hs).1
    ((mem_badFaces K u v s).1 hs).2.1
  free := by
    intro t ht hst
    have hsk := (mem_badFaces K u v s).1 hs
    have hvt : v ∈ t := hst.subset hsk.2.1
    by_cases hut : u ∈ t
    · have hvr : v ∈ t.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, hvt⟩
      have hrk : t.erase u ∈ K := (K.isRelLowerSet_faces ht).2
        (Finset.erase_subset _ _) ⟨v, hvr⟩
      have hrbad : t.erase u ∈ badFaces K u v :=
        (mem_badFaces K u v _).2 ⟨hrk, hvr, Finset.notMem_erase _ _⟩
      have hsr : s ⊆ t.erase u := by
        intro a ha
        exact Finset.mem_erase.mpr ⟨fun hau => hsk.2.2 (hau ▸ ha), hst.subset ha⟩
      have hr : t.erase u = s :=
        (Finset.eq_of_subset_of_card_le hsr (hmax _ hrbad)).symm
      calc
        t = insert u (t.erase u) := (Finset.insert_erase hut).symm
        _ = insert u s := congrArg (insert u) hr
    · have htbad : t ∈ badFaces K u v :=
        (mem_badFaces K u v t).2 ⟨ht, hvt, hut⟩
      exact (not_lt_of_ge (hmax t htbad) (Finset.card_lt_card hst)).elim

private theorem maximalPair_extends (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V)
    (hs : s ∈ badFaces K u v)
    (hmax : ∀ t ∈ badFaces K u v, t.card ≤ s.card) :
    Extends (maximalPair K u v huv hExt s hs hmax).retained u v := by
  intro t ht hv
  refine ⟨hExt t ht.1 hv, ?_⟩
  intro hsi
  apply ht.2
  intro a ha
  rcases Finset.mem_insert.mp (hsi ha) with hau | hat
  · exact (((mem_badFaces K u v s).1 hs).2.2 (hau ▸ ha)).elim
  · exact hat

private theorem maximalPair_deletion (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V)
    (hs : s ∈ badFaces K u v)
    (hmax : ∀ t ∈ badFaces K u v, t.card ≤ s.card) :
    deletion (maximalPair K u v huv hExt s hs hmax).retained v = deletion K v := by
  apply le_antisymm
  · intro t ht
    exact ⟨ht.1.1, ht.2⟩
  · intro t ht
    refine ⟨⟨ht.1, ?_⟩, ht.2⟩
    intro hst
    exact ht.2 (hst ((mem_badFaces K u v s).1 hs).2.1)

private theorem maximalPair_badFaces (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V)
    (hs : s ∈ badFaces K u v)
    (hmax : ∀ t ∈ badFaces K u v, t.card ≤ s.card) :
    badFaces (maximalPair K u v huv hExt s hs hmax).retained u v =
      (badFaces K u v).erase s := by
  classical
  let P := maximalPair K u v huv hExt s hs hmax
  ext t
  constructor
  · intro ht
    have hh := (mem_badFaces P.retained u v t).1 ht
    refine Finset.mem_erase.mpr ⟨?_, (mem_badFaces K u v t).2
      ⟨hh.1.1, hh.2.1, hh.2.2⟩⟩
    intro hts
    apply hh.1.2
    change s ⊆ t
    rw [hts]
  · intro ht
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp ht
    have hh := (mem_badFaces K u v t).1 hb
    apply (mem_badFaces P.retained u v t).2
    refine ⟨(P.mem_retained_iff t).2 ⟨hh.1, hne, ?_⟩, hh.2.1, hh.2.2⟩
    intro htu
    apply hh.2.2
    rw [htu]
    exact Finset.mem_insert_self _ _

/-- Existence is proved by strong induction on the actual number of remaining
lower faces. The output includes the ordered complete, duplicate-free list. -/
private theorem exists_sequence (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    ∃ S : Sequence K (deletion K v),
      (∀ P ∈ S.pairs, P.apex = u ∧ v ∈ P.lower) ∧
      (S.pairs.map CollapsePair.lower).Nodup ∧
      (∀ s, s ∈ S.pairs.map CollapsePair.lower ↔ s ∈ badFaces K u v) ∧
      (S.pairs.map CollapsePair.lower).Pairwise (fun s t => t.card ≤ s.card) := by
  classical
  have aux : ∀ n : Nat, ∀ M : PreAbstractSimplicialComplex V,
      (badFaces M u v).card = n → Extends M u v →
      ∃ S : Sequence M (deletion M v),
        (∀ P ∈ S.pairs, P.apex = u ∧ v ∈ P.lower) ∧
        (S.pairs.map CollapsePair.lower).Nodup ∧
        (∀ s, s ∈ S.pairs.map CollapsePair.lower ↔ s ∈ badFaces M u v) ∧
        (S.pairs.map CollapsePair.lower).Pairwise (fun s t => t.card ≤ s.card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro M hn hext
      by_cases he : badFaces M u v = ∅
      · have hd : M = deletion M v :=
          (deletion_eq_of_fresh M v ((badFaces_empty_iff M u v huv).1 he)).symm
        refine ⟨(Sequence.refl M).cast rfl hd, ?_, ?_, ?_, ?_⟩
        · simp [Sequence.pairs]
        · simp [Sequence.pairs]
        · intro s
          simp [Sequence.pairs, he]
        · simp [Sequence.pairs]
      · obtain ⟨s, hs, hmax⟩ :=
          Finset.exists_max_image (badFaces M u v) Finset.card
            (Finset.nonempty_iff_ne_empty.mpr he)
        let P := maximalPair M u v huv hext s hs hmax
        have hbad : badFaces P.retained u v = (badFaces M u v).erase s :=
          maximalPair_badFaces M u v huv hext s hs hmax
        have hsmall : (badFaces P.retained u v).card < n := by
          rw [hbad, ← hn]
          exact Finset.card_erase_lt_of_mem hs
        obtain ⟨T, hTapex, hTnodup, hTmem, hTorder⟩ := ih _ hsmall P.retained rfl
          (maximalPair_extends M u v huv hext s hs hmax)
        let S : Sequence M (deletion M v) := (Sequence.step P T).cast rfl
          (maximalPair_deletion M u v huv hext s hs hmax)
        have hSpairs : S.pairs = P :: T.pairs := by
          simp only [S, Sequence.pairs_cast, Sequence.pairs]
        refine ⟨S, ?_, ?_, ?_, ?_⟩
        · intro Q hQ
          rw [hSpairs] at hQ
          rcases List.mem_cons.mp hQ with rfl | hQ
          · exact ⟨rfl, ((mem_badFaces M u v s).1 hs).2.1⟩
          · exact hTapex Q hQ
        · rw [hSpairs, List.map_cons, List.nodup_cons]
          refine ⟨?_, hTnodup⟩
          intro hmem
          have hh := hTmem s |>.1 hmem
          rw [hbad] at hh
          exact (Finset.mem_erase.mp hh).1 rfl
        · intro t
          rw [hSpairs, List.map_cons, List.mem_cons, hTmem, hbad]
          change (t = s ∨ t ∈ (badFaces M u v).erase s) ↔ t ∈ badFaces M u v
          constructor
          · rintro (rfl | ht)
            · exact hs
            · exact (Finset.mem_erase.mp ht).2
          · intro ht
            by_cases hts : t = s
            · exact Or.inl hts
            · exact Or.inr (Finset.mem_erase.mpr ⟨hts, ht⟩)
        · rw [hSpairs, List.map_cons, List.pairwise_cons]
          refine ⟨?_, hTorder⟩
          intro t ht
          have hh := hTmem t |>.1 ht
          rw [hbad] at hh
          exact hmax t (Finset.mem_erase.mp hh).2
  exact aux (badFaces K u v).card K rfl hExt

/-- The constructed genuine elementary collapse on the ORIGINAL finite type. -/
def sequence (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) : Sequence K (deletion K v) :=
  Classical.choose (exists_sequence K u v huv hExt)

private theorem sequence_spec (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (∀ P ∈ (sequence K u v huv hExt).pairs, P.apex = u ∧ v ∈ P.lower) ∧
    ((sequence K u v huv hExt).pairs.map CollapsePair.lower).Nodup ∧
    (∀ s, s ∈ (sequence K u v huv hExt).pairs.map CollapsePair.lower ↔
      s ∈ badFaces K u v) ∧
    ((sequence K u v huv hExt).pairs.map CollapsePair.lower).Pairwise
      (fun s t => t.card ≤ s.card) :=
  Classical.choose_spec (exists_sequence K u v huv hExt)

/-- Complete lower-face list, in removal order, with no repeated face. -/
def orderedLowers (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V) :=
  (sequence K u v huv hExt).pairs.map CollapsePair.lower

/-- Complete literal (lower,upper) data, in the same order as Sequence.pairs. -/
def orderedPairs (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) : List (Finset V × Finset V) :=
  (sequence K u v huv hExt).pairs.map fun P => (P.lower, P.upper)

theorem sequence_pair_spec (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)
    (hP : P ∈ (sequence K u v huv hExt).pairs) :
    P.lower.Nonempty ∧ v ∈ P.lower ∧ u ∉ P.lower ∧
      P.apex = u ∧ P.upper = insert u P.lower := by
  have hh := (sequence_spec K u v huv hExt).1 P hP
  refine ⟨P.lower_nonempty, hh.2, ?_, hh.1, ?_⟩
  · simpa only [hh.1] using P.apex_notMem
  · simp only [CollapsePair.upper, hh.1]

theorem orderedLowers_nodup (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (orderedLowers K u v huv hExt).Nodup :=
  (sequence_spec K u v huv hExt).2.1

/-- Every original relevant face appears once; no current-frame assumption is
silently inserted into this public completeness statement. -/
theorem orderedLowers_mem (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (s : Finset V) :
    s ∈ orderedLowers K u v huv hExt ↔ s ∈ K ∧ v ∈ s ∧ u ∉ s :=
  ((sequence_spec K u v huv hExt).2.2.1 s).trans (mem_badFaces K u v s)

theorem orderedLowers_decreasing (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (orderedLowers K u v huv hExt).Pairwise (fun s t => t.card ≤ s.card) :=
  (sequence_spec K u v huv hExt).2.2.2

theorem orderedPairs_eq (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    orderedPairs K u v huv hExt =
      (orderedLowers K u v huv hExt).map (fun s => (s, insert u s)) := by
  unfold orderedPairs orderedLowers
  rw [List.map_map]
  apply List.map_congr_left
  intro P hP
  have hh := sequence_pair_spec K u v huv hExt P hP
  exact Prod.ext rfl hh.2.2.2.2

theorem orderedPairs_nodup (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (orderedPairs K u v huv hExt).Nodup := by
  rw [orderedPairs_eq]
  exact List.Nodup.map (fun a b h => congrArg Prod.fst h)
    (orderedLowers_nodup K u v huv hExt)

/-- Exact complete pair data: upper faces are not independently chosen. -/
theorem orderedPairs_mem (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (a b : Finset V) :
    (a, b) ∈ orderedPairs K u v huv hExt ↔
      a ∈ K ∧ v ∈ a ∧ u ∉ a ∧ b = insert u a := by
  rw [orderedPairs_eq]
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := List.mem_map.mp h
    have hsa : s = a := congrArg Prod.fst he
    subst s
    have hb : insert u a = b := congrArg Prod.snd he
    have hh := (orderedLowers_mem K u v huv hExt a).1 hs
    exact ⟨hh.1, hh.2.1, hh.2.2, hb.symm⟩
  · rintro ⟨ha, hv, hu, rfl⟩
    exact List.mem_map.mpr ⟨a, (orderedLowers_mem K u v huv hExt a).2
      ⟨ha, hv, hu⟩, rfl⟩

theorem sequence_length (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (sequence K u v huv hExt).pairs.length = (badFaces K u v).card := by
  classical
  have he : (orderedLowers K u v huv hExt).toFinset = badFaces K u v := by
    ext s
    simp only [List.mem_toFinset, orderedLowers_mem, mem_badFaces]
  have hc := List.toFinset_card_of_nodup (orderedLowers_nodup K u v huv hExt)
  rw [he] at hc
  simpa only [orderedLowers, List.length_map] using hc.symm

/-- Native deletion-fixedness at EVERY free-pair stage. -/
theorem deletion_le_each_retained (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (P : CollapsePair V)
    (hP : P ∈ (sequence K u v huv hExt).pairs) : deletion K v ≤ P.retained :=
  (sequence K u v huv hExt).final_le_each_retained hP

private theorem sequence_frames_terminal {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) : S.frames.getD S.pairs.length L = L := by
  induction S with
  | refl K => rfl
  | @step P N T ih =>
      simpa only [Sequence.frames, Sequence.pairs, List.length_cons, List.getD_cons_succ] using ih

/-- Exact replay of any native sequence as deletion of the indicated prefix.
This is a theorem about faces in the actual evolving complexes. -/
private theorem sequence_frame_mem {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (i : Nat) (hi : i ≤ S.pairs.length) (s : Finset V) :
    s ∈ S.frames.getD i L ↔ s ∈ K ∧
      ∀ P ∈ S.pairs.take i, s ≠ P.lower ∧ s ≠ P.upper := by
  induction S generalizing i with
  | refl K =>
      have hi0 : i = 0 := by simpa only [Sequence.pairs, List.length_nil, Nat.le_zero] using hi
      subst i
      simp [Sequence.frames, Sequence.pairs]
  | @step P N T ih =>
      cases i with
      | zero => simp [Sequence.frames, Sequence.pairs]
      | succ i =>
          have hi' : i ≤ T.pairs.length := by
            simpa only [Sequence.pairs, List.length_cons, Nat.succ_le_succ_iff] using hi
          change s ∈ T.frames.getD i N ↔ s ∈ P.ambient ∧
            ∀ Q ∈ P :: T.pairs.take i, s ≠ Q.lower ∧ s ≠ Q.upper
          rw [ih i hi', P.mem_retained_iff]
          constructor
          · rintro ⟨⟨hs, hl, hu⟩, htail⟩
            refine ⟨hs, ?_⟩
            intro Q hQ
            rcases List.mem_cons.mp hQ with rfl | hQ
            · exact ⟨hl, hu⟩
            · exact htail Q hQ
          · rintro ⟨hs, hQ⟩
            have hp := hQ P (by simp)
            exact ⟨⟨hs, hp.1, hp.2⟩, fun Q hmem => hQ Q (List.mem_cons_of_mem P hmem)⟩

theorem frames_length (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (sequence K u v huv hExt).frames.length = (badFaces K u v).card + 1 := by
  rw [Sequence.frames_length, sequence_length]

theorem frames_initial (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (sequence K u v huv hExt).frames.getD 0 (deletion K v) = K :=
  (sequence K u v huv hExt).frames_source_zero _

theorem frames_terminal (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (sequence K u v huv hExt).frames.getD (badFaces K u v).card (deletion K v) =
      deletion K v := by
  rw [← sequence_length K u v huv hExt]
  exact sequence_frames_terminal _

theorem frame_mem_iff (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (i : Nat)
    (hi : i ≤ (badFaces K u v).card) (s : Finset V) :
    s ∈ (sequence K u v huv hExt).frames.getD i (deletion K v) ↔
      s ∈ K ∧ ∀ P ∈ (sequence K u v huv hExt).pairs.take i,
        s ≠ P.lower ∧ s ≠ P.upper := by
  apply sequence_frame_mem
  simpa only [sequence_length] using hi

private theorem pair_faceSet (P : CollapsePair V) :
    faceSet P.retained = ((faceSet P.ambient).erase P.lower).erase P.upper := by
  classical
  ext s
  simp only [mem_faceSet, P.mem_retained_iff, Finset.mem_erase]
  tauto

private theorem pair_faceCount (P : CollapsePair V) :
    (faceSet P.ambient).card = (faceSet P.retained).card + 2 := by
  classical
  have hne : P.upper ≠ P.lower := by
    intro he
    exact P.apex_notMem (he ▸ Finset.mem_insert_self P.apex P.lower)
  have hl : P.lower ∈ faceSet P.ambient := (mem_faceSet _ _).2 P.lower_mem
  have hu : P.upper ∈ (faceSet P.ambient).erase P.lower :=
    Finset.mem_erase.mpr ⟨hne, (mem_faceSet _ _).2 P.upper_mem⟩
  have hc1 := Finset.card_erase_add_one hl
  have hc2 := Finset.card_erase_add_one hu
  rw [← pair_faceSet] at hc2
  omega

private theorem sequence_faceCount {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) :
    (faceSet K).card = (faceSet L).card + 2 * S.pairs.length := by
  induction S with
  | refl K => simp [Sequence.pairs]
  | step P T ih =>
      have hp := pair_faceCount P
      simp only [Sequence.pairs, List.length_cons]
      omega

/-- Exactly two distinct nonempty original faces disappear per lower face. -/
theorem face_count (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (faceSet K).card = (faceSet (deletion K v)).card + 2 * (badFaces K u v).card := by
  have hh := sequence_faceCount (sequence K u v huv hExt)
  simpa only [sequence_length] using hh

/-- If v is a ghost, the chosen certificate has no pairs, not a spurious
empty-lower elementary collapse. No realization point is chosen. -/
theorem ghost_pairs (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :
    (sequence K u v huv hExt).pairs = [] := by
  apply List.length_eq_zero_iff.mp
  rw [sequence_length, (badFaces_empty_iff K u v huv).2 hf]
  rfl

private theorem sequence_frames_of_nil {K L : PreAbstractSimplicialComplex V}
    (S : Sequence K L) (hp : S.pairs = []) : S.frames = [K] := by
  cases S with
  | refl K => rfl
  | step P T => simp [Sequence.pairs] at hp

theorem ghost_frames (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (hf : Fresh v K) :
    (sequence K u v huv hExt).frames = [K] := by
  exact sequence_frames_of_nil _ (ghost_pairs K u v huv hExt hf)

/-- Native SDR, with the literal inclusion of the entire deletion. -/
def sdr (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    RelativeSDR K (deletion K v) (deletion_le K v) :=
  (sequence K u v huv hExt).realize

/-- Explicitly expose the retraction used by the elementary sequence. -/
def retraction (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) : C(Space K, Space (deletion K v)) :=
  (sdr K u v huv hExt).retraction

theorem retraction_inclusion (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (y : Space (deletion K v)) :
    retraction K u v huv hExt (realizationInclusion (deletion_le K v) y) = y :=
  (sdr K u v huv hExt).retraction_inclusion y

def collapseHomotopy (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) :
    (ContinuousMap.id (Space K)).HomotopyRel
      ((realizationInclusion (deletion_le K v)).comp (retraction K u v huv hExt))
      {x | x.val ∈ realization (deletion K v)} :=
  (sdr K u v huv hExt).homotopy

/-- The fixed set is the FULL realization, not only the retained vertices. -/
theorem collapseHomotopy_fixed (K : PreAbstractSimplicialComplex V) (u v : V)
    (huv : u ≠ v) (hExt : Extends K u v) (t : I) (x : Space K)
    (hx : x.val ∈ realization (deletion K v)) :
    collapseHomotopy K u v huv hExt (t, x) = x :=
  (collapseHomotopy K u v huv hExt).eq_fst t hx

/-- Original coordinates are literally unchanged by the inclusion. -/
theorem inclusion_coordinates (K : PreAbstractSimplicialComplex V) (v : V)
    (y : Space (deletion K v)) :
    (realizationInclusion (deletion_le K v) y).val = y.val := rfl

/-- The original deleted label remains in V, with coordinate zero. -/
theorem deletion_coordinate_zero (K : PreAbstractSimplicialComplex V) (v : V)
    (y : Space (deletion K v)) : y.val v = 0 := by
  obtain ⟨s, hs, hy⟩ := (realization_mem_iff (deletion K v) y.val).1 y.property
  exact hy.2.2 v hs.2

/-- Legality of all ground coordinates, including every excluded ghost label. -/
theorem restricted_coordinate_zero (G : SimpleGraph V) (p : V → Prop)
    (x : Space (restricted G p)) (a : V) (ha : ¬ p a) : x.val a = 0 := by
  obtain ⟨s, hs, hx⟩ := (realization_mem_iff (restricted G p) x.val).1 x.property
  exact hx.2.2 a (fun has => ha (hs.2.2 a has))

/-- The allowed-ground version of open-neighborhood domination. Only allowed
neighbors need satisfy the containment; the survivor must itself be allowed. -/
theorem graph_extends (G : SimpleGraph V) (p : V → Prop) (u v : V)
    (huv : u ≠ v) (hpu : p u)
    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :
    Extends (restricted G p) u v := by
  intro s hs hv
  refine ⟨Finset.insert_nonempty u s, ?_, ?_⟩
  · intro a ha b hb hab hadj
    rcases Finset.mem_insert.mp ha with hau | haS
    · rcases Finset.mem_insert.mp hb with hbu | hbS
      · exact G.loopless.irrefl u (by simpa only [hau, hbu] using hadj)
      · have hvb : G.Adj v b := hdom b (hs.2.2 b hbS) (by simpa only [hau] using hadj)
        exact hs.2.1 hv hbS (G.ne_of_adj hvb) hvb
    · rcases Finset.mem_insert.mp hb with hbu | hbS
      · have hva : G.Adj v a := hdom a (hs.2.2 a haS) (by simpa only [hbu] using hadj.symm)
        exact hs.2.1 hv haS (G.ne_of_adj hva) hva
      · exact hs.2.1 haS hbS hab hadj
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hpu
    · exact hs.2.2 a ha

/-- Exact equality on V, with every excluded/ghost label still in the type. -/
theorem restricted_deletion (G : SimpleGraph V) (p : V → Prop) (v : V) :
    deletion (restricted G p) v = restricted G (fun a => p a ∧ a ≠ v) := by
  apply le_antisymm
  · rintro s ⟨⟨hn, hi, hp⟩, hv⟩
    refine ⟨hn, hi, ?_⟩
    intro a ha
    exact ⟨hp a ha, fun hav => hv (hav ▸ ha)⟩
  · rintro s ⟨hn, hi, hp⟩
    refine ⟨⟨hn, hi, fun a ha => (hp a ha).1⟩, ?_⟩
    intro hv
    exact (hp v hv).2 rfl

/-- Graph consumer with the literal native deletion endpoint, not an induced
subtype and not a homotopy-equivalent substitute. -/
def graphSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)
    (huv : u ≠ v) (hpu : p u)
    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :
    Sequence (restricted G p) (deletion (restricted G p) v) :=
  sequence (restricted G p) u v huv (graph_extends G p u v huv hpu hdom)

/-- The same certificate viewed at the exactly equal restricted-ground target. -/
def graphRestrictedSequence (G : SimpleGraph V) (p : V → Prop) (u v : V)
    (huv : u ≠ v) (hpu : p u)
    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :
    Sequence (restricted G p) (restricted G (fun a => p a ∧ a ≠ v)) :=
  (graphSequence G p u v huv hpu hdom).cast rfl (restricted_deletion G p v)

/-- Whole-deletion fixedness for the actual original-label graph realization. -/
def graphSDR (G : SimpleGraph V) (p : V → Prop) (u v : V)
    (huv : u ≠ v) (hpu : p u)
    (hdom : ∀ a, p a → G.Adj u a → G.Adj v a) :
    RelativeSDR (restricted G p) (deletion (restricted G p) v)
      (deletion_le (restricted G p) v) :=
  (graphSequence G p u v huv hpu hdom).realize

/-- For ordinary independent faces, the neighbourhood-set hypothesis directly
constructs the elementary certificate. The existing coordinate fold remains a separate library result; no duplicate
transfer theorem or equality between its homotopy and this one is introduced. -/
def independenceSequence (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hdom : G.neighborSet u ⊆ G.neighborSet v) :
    Sequence (independenceComplex G).toPreAbstractSimplicialComplex
      (deletion (independenceComplex G).toPreAbstractSimplicialComplex v) := by
  have he : Extends (independenceComplex G).toPreAbstractSimplicialComplex u v := by
    rw [← unrestricted G]
    exact graph_extends G (fun _ => True) u v huv trivial (fun a _ ha => hdom ha)
  exact sequence _ u v huv he

/-- Ordinary independent faces have the same literal restriction endpoint. -/
theorem independence_deletion (G : SimpleGraph V) (v : V) :
    deletion (independenceComplex G).toPreAbstractSimplicialComplex v =
      restricted G (fun a => a ≠ v) := by
  rw [← unrestricted G, restricted_deletion]
  ext s
  simp [restricted]

end D5.S3.Geometry.FiniteVertexDominationCollapse

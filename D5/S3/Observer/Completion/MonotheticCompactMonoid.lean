/- GID: D5/S3/Observer/Completion/MonotheticCompactMonoid
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/MonotheticCompactMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The tail of a compact monothetic additive monoid is its minimal ideal group. -/

import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Data.ENat.Basic

open Set Topology

namespace D5.S3.Observer.Completion.MonotheticCompactMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
  [ContinuousAdd M] [CompactSpace M] [T2Space M]

def tail (a : M) (N : ℕ) : Set M :=
  closure (range fun n : ℕ => (N + n) • a)

def core (a : M) : Set M := ⋂ N : ℕ, tail a N

private theorem tail_eq_range (a : M) (hd : DenseRange fun n : ℕ => n • a) (N : ℕ) :
    tail a N = range (fun x : M => N • a + x) := by
  have hc : Continuous (fun x : M => N • a + x) := continuous_const.add continuous_id
  have h := hc.isClosedMap.closure_image_eq_of_continuous hc
    (range fun n : ℕ => n • a)
  rw [hd.closure_range, image_univ, ← Set.range_comp] at h
  simpa only [tail, Function.comp_def, add_nsmul] using h

private theorem tail_succ_subset (a : M) (N : ℕ) : tail a (N + 1) ⊆ tail a N := by
  apply closure_mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n + 1, by dsimp; congr 1; omega⟩

private theorem core_nonempty (a : M) : (core a).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (tail a) (tail_succ_subset a)
  · intro N
    exact ⟨N • a, subset_closure ⟨0, by simp⟩⟩
  · exact isClosed_closure.isCompact
  · intro N; exact isClosed_closure

private theorem core_closed (a : M) : IsClosed (core a) :=
  isClosed_iInter fun _ => isClosed_closure

private theorem add_mem_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (x : M) {y : M} (hy : y ∈ core a) : x + y ∈ core a := by
  apply mem_iInter.mpr
  intro N
  have hyN := mem_iInter.mp hy N
  rw [tail_eq_range a hd N] at hyN ⊢
  obtain ⟨z, rfl⟩ := hyN
  exact ⟨x + z, by dsimp; ac_rfl⟩

private theorem tail_succ_eq_image (a : M) (hd : DenseRange fun n : ℕ => n • a) (N : ℕ) :
    tail a (N + 1) = (fun y => a + y) '' tail a N := by
  rw [tail_eq_range a hd (N + 1), tail_eq_range a hd N, ← Set.range_comp]
  congr 1
  funext x
  simp only [Function.comp_def, add_nsmul, one_nsmul]
  ac_rfl

private theorem generator_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, a + z = y := by
  let F : ℕ → Set M := fun N => tail a N ∩ {z | a + z = y}
  have hFclosed (N : ℕ) : IsClosed (F N) :=
    isClosed_closure.inter (isClosed_eq (continuous_const.add continuous_id) continuous_const)
  have hFne (N : ℕ) : (F N).Nonempty := by
    have hN := mem_iInter.mp hy (N + 1)
    rw [tail_succ_eq_image a hd N] at hN
    obtain ⟨z, hz, he⟩ := hN
    exact ⟨z, hz, he⟩
  have hFmono (N : ℕ) : F (N + 1) ⊆ F N :=
    inter_subset_inter_left _ (tail_succ_subset a N)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hFmono hFne (hFclosed 0).isCompact hFclosed
  refine ⟨z, mem_iInter.mpr (fun N => (mem_iInter.mp hz N).1), ?_⟩
  exact (mem_iInter.mp hz 0).2

private theorem natural_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (n : ℕ) {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, n • a + z = y := by
  induction n generalizing y with
  | zero => exact ⟨y, hy, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, he⟩ := generator_surjective_on_core a hd hy
    obtain ⟨z, hz, hz'⟩ := ih hw
    refine ⟨z, hz, ?_⟩
    rw [succ_nsmul', add_assoc, hz', he]

private theorem translation_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (x : M) {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, x + z = y := by
  let F : Set (M × M) := {p | p.2 ∈ core a ∧ p.1 + p.2 = y}
  have hF : IsClosed F := (core_closed a).preimage continuous_snd |>.inter
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)
  have hproj : IsClosed (Prod.fst '' F) := isClosedMap_fst_of_compactSpace F hF
  have hnat (n : ℕ) : n • a ∈ Prod.fst '' F := by
    obtain ⟨z, hz, he⟩ := natural_surjective_on_core a hd n hy
    exact ⟨(n • a, z), ⟨hz, he⟩, rfl⟩
  have hx : x ∈ Prod.fst '' F := hd.induction_on x hproj hnat
  obtain ⟨⟨_, z⟩, ⟨hz, he⟩, rfl⟩ := hx
  exact ⟨z, hz, he⟩

private theorem translation_image_core (a : M) (hd : DenseRange fun n : ℕ => n • a) (x : M) :
    (fun z => x + z) '' core a = core a := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact add_mem_core a hd x hz
  · intro y hy
    exact translation_surjective_on_core a hd x hy

private theorem core_has_identity (a : M) (hd : DenseRange fun n : ℕ => n • a) :
    ∃ e ∈ core a, ∀ z ∈ core a, e + z = z := by
  obtain ⟨b, hb⟩ := core_nonempty a
  obtain ⟨e, he, hbe⟩ := translation_surjective_on_core a hd b hb
  refine ⟨e, he, ?_⟩
  intro z hz
  obtain ⟨c, hc, hbc⟩ := translation_surjective_on_core a hd b hz
  calc
    e + z = e + (b + c) := congrArg (e + ·) hbc.symm
    _ = (b + e) + c := by ac_rfl
    _ = z := by rw [hbe, hbc]

end D5.S3.Observer.Completion.MonotheticCompactMonoid

/- GID: D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/CompleteRootSupergraphExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An exhaustive ray catalogue with one six-vertex canonical block and a disjoint bipartite remainder excludes two mutually unbiased completion contexts. -/

import D5.S3.Quantum.Tomography.RankOneContextCommutator

/- Reuse audit (2026-09-05): uses RankOneContext, overlap, normalized
   rank-one idempotence, Matrix.trace, Finset.image and finite-cardinality
   equality. No new Hadamard, unitary, graph, ray-equivalence, or affinity
   definition is introduced. The analytic root-cover and interval-to-Lean
   transfer remain explicit obligations: this theorem does not trust JSON,
   external checker verdicts, hashes, or the cardinality of a sampled set.
-/

open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.CompleteRootSupergraphExclusion

open Matrix
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private theorem two_other_indices (i : Fin 6) :
    ∃ j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases i
  · exact ⟨1, 2, by decide⟩
  · exact ⟨0, 2, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨0, 1, by decide⟩

private theorem clique_image_eq_canonical
    {κ : Type*} [DecidableEq κ]
    (canonical : Finset κ) (hcard : canonical.card = 6)
    (color : κ → Bool) (c : Fin 6 → κ) (hinj : Function.Injective c)
    (hedge : ∀ i j, i ≠ j →
      (c i ∈ canonical ∧ c j ∈ canonical) ∨
      (c i ∉ canonical ∧ c j ∉ canonical ∧ color (c i) ≠ color (c j))) :
    Finset.univ.image c = canonical := by
  have hmem (i : Fin 6) : c i ∈ canonical := by
    by_contra hi
    obtain ⟨j, k, hij, hik, hjk⟩ := two_other_indices i
    have hij' := (hedge i j hij).resolve_left (fun h ↦ hi h.1)
    have hik' := (hedge i k hik).resolve_left (fun h ↦ hi h.1)
    have hjk' := (hedge j k hjk).resolve_left (fun h ↦ hij'.2.1 h.1)
    cases hci : color (c i) <;> cases hcj : color (c j) <;>
      cases hck : color (c k) <;> simp_all
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact hmem i
  · rw [Finset.card_image_of_injective _ hinj]
    simp [hcard]

private theorem context_labels_injective
    {κ : Type*}
    (P : κ → Matrix (Fin 6) (Fin 6) ℂ)
    (C : RankOneContext 6) (c : Fin 6 → κ)
    (hc : ∀ i, C.projector i = P (c i))
    (horth : ∀ i j, i ≠ j → overlap C C i j = 0) :
    Function.Injective c := by
  intro i j hij
  by_contra hne
  have hzero := horth i j hne
  have hproj : C.projector i = C.projector j := by
    rw [hc i, hc j, hij]
  unfold overlap at hzero
  rw [← hproj, (C.rankOne i).2.1, (C.rankOne i).2.2.1] at hzero
  norm_num at hzero

/-- A complete root catalogue whose orthogonality supergraph consists of a
six-element canonical block and a disjoint bipartite remainder cannot contain
two mutually unbiased complete rank-one contexts.

`hCoverC` and `hCoverD` quantify over every projector of the actual contexts.
They must come from an exhaustive analytic root-cover theorem, not merely
from existence of sixty isolated roots. Exact edges need not persist: only
the stated one-sided implication from zero overlap to an allowed edge is used.
The conclusion is on the existing context and overlap API. -/
theorem no_mutually_unbiased_completions_of_complete_root_supergraph
    {κ : Type*} [DecidableEq κ]
    (P : κ → Matrix (Fin 6) (Fin 6) ℂ)
    (canonical : Finset κ) (hcard : canonical.card = 6)
    (color : κ → Bool)
    (hgraph : ∀ k l, k ≠ l → (trace (P k * P l)).re = 0 →
      (k ∈ canonical ∧ l ∈ canonical) ∨
      (k ∉ canonical ∧ l ∉ canonical ∧ color k ≠ color l))
    (C D : RankOneContext 6)
    (hCoverC : ∀ i, ∃ k, C.projector i = P k)
    (hCoverD : ∀ i, ∃ k, D.projector i = P k)
    (hOrthoC : ∀ i j, i ≠ j → overlap C C i j = 0)
    (hOrthoD : ∀ i j, i ≠ j → overlap D D i j = 0) :
    ¬ (∀ i j, overlap C D i j = (6 : ℝ)⁻¹) := by
  classical
  choose c hc using hCoverC
  choose d hd using hCoverD
  have hci := context_labels_injective P C c hc hOrthoC
  have hdi := context_labels_injective P D d hd hOrthoD
  have hCImage : Finset.univ.image c = canonical := by
    apply clique_image_eq_canonical canonical hcard color c hci
    intro i j hij
    have hz := hOrthoC i j hij
    unfold overlap at hz
    rw [hc i, hc j] at hz
    exact hgraph (c i) (c j) (hci.ne hij) hz
  have hDImage : Finset.univ.image d = canonical := by
    apply clique_image_eq_canonical canonical hcard color d hdi
    intro i j hij
    have hz := hOrthoD i j hij
    unfold overlap at hz
    rw [hd i, hd j] at hz
    exact hgraph (d i) (d j) (hdi.ne hij) hz
  have hmem : d 0 ∈ Finset.univ.image c := by
    rw [hCImage, ← hDImage]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  have hshared : C.projector i = D.projector 0 := by
    rw [hc i, hd 0, hi]
  intro hMUB
  have hbad := hMUB i 0
  unfold overlap at hbad
  rw [← hshared, (C.rankOne i).2.1, (C.rankOne i).2.2.1] at hbad
  norm_num at hbad

#print axioms no_mutually_unbiased_completions_of_complete_root_supergraph

end D5.S3.Quantum.Tomography.CompleteRootSupergraphExclusion

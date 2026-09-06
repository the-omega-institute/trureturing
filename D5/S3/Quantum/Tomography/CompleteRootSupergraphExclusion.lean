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


/-- Quantitative tube variant: a tube may be empty or contain several roots.
If two points in one tube have overlap at least mu, different tube labels with
small overlap satisfy the canonical-block/bipartite supergraph, and each of
two six-frames has within-frame overlaps below eta <= mu, some cross-frame
overlap is at least mu. Root existence and uniqueness are unnecessary.

This strengthens the exact catalogue consumer above without replacing it.
The matrices may be actual context projectors or normalized outer products of
approximate frames. All geometric inequalities remain explicit proof inputs. -/
theorem six_frames_have_large_cross_overlap_of_root_tube_cover
    {κ : Type*} [DecidableEq κ]
    (tube : κ → Set (Matrix (Fin 6) (Fin 6) ℂ))
    (canonical : Finset κ) (hcard : canonical.card = 6) (color : κ → Bool)
    (η μ : ℝ) (hημ : η ≤ μ)
    (hSame : ∀ k P ∈ tube k, ∀ Q ∈ tube k, μ ≤ (trace (P * Q)).re)
    (hGraph : ∀ k l, k ≠ l → ∀ P ∈ tube k, ∀ Q ∈ tube l,
      (trace (P * Q)).re < η →
      (k ∈ canonical ∧ l ∈ canonical) ∨
      (k ∉ canonical ∧ l ∉ canonical ∧ color k ≠ color l))
    (C D : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
    (hCoverC : ∀ i, ∃ k, C i ∈ tube k)
    (hCoverD : ∀ i, ∃ k, D i ∈ tube k)
    (hSmallC : ∀ i j, i ≠ j → (trace (C i * C j)).re < η)
    (hSmallD : ∀ i j, i ≠ j → (trace (D i * D j)).re < η) :
    ∃ i j, μ ≤ (trace (C i * D j)).re := by
  classical
  choose c hc using hCoverC
  choose d hd using hCoverD
  have hInjective (V : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
      (v : Fin 6 → κ) (hv : ∀ i, V i ∈ tube (v i))
      (hSmall : ∀ i j, i ≠ j → (trace (V i * V j)).re < η) :
      Function.Injective v := by
    intro i j hij
    by_contra hne
    have hmem : V j ∈ tube (v i) := by rw [hij]; exact hv j
    have hlo := hSame (v i) (V i) (hv i) (V j) hmem
    have hhi := hSmall i j hne
    exact (not_lt_of_ge (le_trans hημ hlo)) hhi
  have hci := hInjective C c hc hSmallC
  have hdi := hInjective D d hd hSmallD
  have hCImage : Finset.univ.image c = canonical := by
    apply clique_image_eq_canonical canonical hcard color c hci
    intro i j hij
    exact hGraph (c i) (c j) (hci.ne hij) (C i) (hc i) (C j) (hc j)
      (hSmallC i j hij)
  have hDImage : Finset.univ.image d = canonical := by
    apply clique_image_eq_canonical canonical hcard color d hdi
    intro i j hij
    exact hGraph (d i) (d j) (hdi.ne hij) (D i) (hd i) (D j) (hd j)
      (hSmallD i j hij)
  have hmem : d 0 ∈ Finset.univ.image c := by
    rw [hCImage, ← hDImage]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, 0, hSame (c i) (C i) (hc i) (D 0) ?_⟩
  rw [hi]
  exact hd 0

#print axioms six_frames_have_large_cross_overlap_of_root_tube_cover

/-- A two-relation tube certificate excludes two approximately mutually
unbiased six-frames. The orthogonality supergraph may contain many six-cliques.
For each possible first clique, its common unbiased-neighbor graph needs only
five colors, so it cannot contain the second six-clique.

The graph relations are one-sided enclosures of actual overlaps on whole tubes.
Tubes need not be disjoint, nonempty, or contain a unique root. The finite
coloring hypothesis must be proved for every first clique; an external JSON
verdict is not a proof of that hypothesis. -/
theorem two_relation_tube_certificate_forces_cross_unbiasedness_error
    {κ : Type*}
    (tube : κ → Set (Matrix (Fin 6) (Fin 6) ℂ))
    (orthogonalCandidate unbiasedCandidate : κ → κ → Prop)
    (η μ τ : ℝ) (hημ : η ≤ μ)
    (hSame : ∀ k P ∈ tube k, ∀ Q ∈ tube k, μ ≤ (trace (P * Q)).re)
    (hOrth : ∀ k l, k ≠ l → ∀ P ∈ tube k, ∀ Q ∈ tube l,
      (trace (P * Q)).re < η → orthogonalCandidate k l)
    (hUnbiased : ∀ k l, ∀ P ∈ tube k, ∀ Q ∈ tube l,
      |(trace (P * Q)).re - (1 / 6 : ℝ)| < τ → unbiasedCandidate k l)
    (hColor : ∀ c : Fin 6 → κ, Function.Injective c →
      (∀ i j, i ≠ j → orthogonalCandidate (c i) (c j)) →
      ∃ color : κ → Fin 5,
        ∀ k l, k ≠ l →
          (∀ i, unbiasedCandidate (c i) k) →
          (∀ i, unbiasedCandidate (c i) l) →
          orthogonalCandidate k l → color k ≠ color l)
    (C D : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
    (hCoverC : ∀ i, ∃ k, C i ∈ tube k)
    (hCoverD : ∀ i, ∃ k, D i ∈ tube k)
    (hSmallC : ∀ i j, i ≠ j → (trace (C i * C j)).re < η)
    (hSmallD : ∀ i j, i ≠ j → (trace (D i * D j)).re < η) :
    ∃ i j, τ ≤ |(trace (C i * D j)).re - (1 / 6 : ℝ)| := by
  classical
  choose c hc using hCoverC
  choose d hd using hCoverD
  have hInj (V : Fin 6 → Matrix (Fin 6) (Fin 6) ℂ)
      (v : Fin 6 → κ) (hv : ∀ i, V i ∈ tube (v i))
      (hSmall : ∀ i j, i ≠ j → (trace (V i * V j)).re < η) :
      Function.Injective v := by
    intro i j hij
    by_contra hne
    have hmem : V j ∈ tube (v i) := by rw [hij]; exact hv j
    have hlo := hSame (v i) (V i) (hv i) (V j) hmem
    exact (not_lt_of_ge (le_trans hημ hlo)) (hSmall i j hne)
  have hci := hInj C c hc hSmallC
  have hdi := hInj D d hd hSmallD
  have hCliqueC : ∀ i j, i ≠ j → orthogonalCandidate (c i) (c j) := by
    intro i j hij
    exact hOrth (c i) (c j) (hci.ne hij) (C i) (hc i) (C j) (hc j)
      (hSmallC i j hij)
  obtain ⟨color, hcolor⟩ := hColor c hci hCliqueC
  by_contra hNo
  have hClose (i j : Fin 6) : |(trace (C i * D j)).re - (1 / 6 : ℝ)| < τ := by
    exact lt_of_not_ge (fun h ↦ hNo ⟨i, j, h⟩)
  have hPartner (j : Fin 6) : ∀ i, unbiasedCandidate (c i) (d j) := by
    intro i
    exact hUnbiased (c i) (d j) (C i) (hc i) (D j) (hd j) (hClose i j)
  have hColorInj : Function.Injective (fun j : Fin 6 ↦ color (d j)) := by
    intro i j hij
    by_contra hne
    have hEdge := hOrth (d i) (d j) (hdi.ne hne)
      (D i) (hd i) (D j) (hd j) (hSmallD i j hne)
    exact hcolor (d i) (d j) (hdi.ne hne) (hPartner i) (hPartner j) hEdge hij
  have hcard := Fintype.card_le_of_injective (fun j : Fin 6 ↦ color (d j)) hColorInj
  norm_num at hcard

#print axioms two_relation_tube_certificate_forces_cross_unbiasedness_error

end D5.S3.Quantum.Tomography.CompleteRootSupergraphExclusion

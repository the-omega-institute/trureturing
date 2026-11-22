/- GID: D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/DirectSumCircuitTorsion
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral cycle joins and signed circuit restrictions for a matroid direct sum. -/

module

public import D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
public import Mathlib.Combinatorics.Matroid.Sum

/-! # Joint circuit restrictions of a direct sum -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.DirectSumCircuitTorsion

variable {V : Type*} {M N : Matroid V} {K I : Set V}

private lemma contract_disjointSum_left (h : Disjoint M.E N.E) (hI : M.IsBasis I K) :
    (M.disjointSum N h) ／ K =
      (M ／ K).disjointSum N (h.mono_left (by rw [Matroid.contract_ground]; exact Set.sdiff_subset)) := by
  have hK := hI.subset_ground
  have hIN : Disjoint I N.E := h.mono_left hI.indep.subset_ground
  have hKN : Disjoint K N.E := h.mono_left hK
  have hsum : (M.disjointSum N h).IsBasis I K := by
    rw [Matroid.disjointSum_isBasis_iff, Set.inter_eq_left.2 hI.indep.subset_ground,
      Set.inter_eq_left.2 hK, Set.disjoint_iff_inter_eq_empty.mp hIN,
      Set.disjoint_iff_inter_eq_empty.mp hKN]
    exact ⟨hI, by simp, hI.subset, hK.trans Set.subset_union_left⟩
  apply Matroid.ext_indep
  · rw [Matroid.contract_ground, Matroid.disjointSum_ground_eq,
      Matroid.disjointSum_ground_eq, Matroid.contract_ground]
    ext x
    have hx : x ∈ K → x ∉ N.E := fun hxK hxN => Set.disjoint_left.mp hKN hxK hxN
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  intro J hJ
  have hJ' : J ⊆ (M.E ∪ N.E) \ K := by
    simpa only [Matroid.contract_ground, Matroid.disjointSum_ground_eq] using hJ
  have hKJ : Disjoint K J := Set.disjoint_left.2 fun _ hxK hxJ => (hJ' hxJ).2 hxK
  have hKMJ : Disjoint K (J ∩ M.E) := hKJ.mono_right Set.inter_subset_left
  have hJM : J ∩ (M.E \ K) = J ∩ M.E := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, (hJ' hx.1).2⟩⟩
  have hsub : J ⊆ (M.E \ K) ∪ N.E := by
    intro x hx
    rcases (hJ' hx).1 with hxM | hxN
    · exact Or.inl ⟨hxM, (hJ' hx).2⟩
    · exact Or.inr hxN
  have hsub' : J ∪ I ⊆ M.E ∪ N.E :=
    Set.union_subset (fun _ hx => (hJ' hx).1) (hI.indep.subset_ground.trans Set.subset_union_left)
  simp only [hsum.contract_indep_iff, Matroid.disjointSum_indep_iff,
    Matroid.contract_ground, hI.contract_indep_iff, Set.union_inter_distrib_right,
    Set.inter_eq_left.2 hI.indep.subset_ground, Set.disjoint_iff_inter_eq_empty.mp hIN,
    Set.union_empty, hKMJ, hKJ, hsub, hsub', hJM, and_true]

end D5.S3.Combinatorics.Matroids.DirectSumCircuitTorsion

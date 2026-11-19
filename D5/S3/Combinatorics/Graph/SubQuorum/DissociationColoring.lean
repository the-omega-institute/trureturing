/- GID: D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/DissociationColoring
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Injective support colorings are exactly dissociation selections. -/

import D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting
import Mathlib.Data.Finset.Lattice.Fold

/-! The reduction beta two at most psi square is attributed to Sahbi in the
received representative-packing source. These are the actual canonical partial
colorings: uncolored vertices and unused color labels contribute no palette size.
The theorem includes the empty graph. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.DissociationColoring
open DoubleStarGrafting StarFormingDissociationRefutation

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- For a coloring injective on its actual support, the majority condition says
exactly that every colored vertex has at most one colored neighbor. -/
theorem injective_support_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Option C) (hi : Set.InjOn c (coloredSupport c Finset.univ)) :
    IsSubQuorum G c ↔ IsKIndependent G 2 (coloredSupport c Finset.univ) := by
  classical
  have hs (v : V) (hv : c v ≠ none) :
      ((Finset.univ.filter (G.Adj v)).filter (fun w => c w = c v)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw he
    have hwc : c w ≠ none := by rw [he]; exact hv
    have heq := hi (by simp [coloredSupport,hwc]) (by simp [coloredSupport,hv]) he
    exact G.irrefl (heq ▸ (Finset.mem_filter.mp hw).2)
  have hc (v : V) :
      ((Finset.univ.filter (G.Adj v)).filter (fun w => c w ≠ none)) =
        (coloredSupport c Finset.univ).filter (G.Adj v) := by
    ext w
    simp [coloredSupport,and_comm]
  have hn (v : V) :
      @Finset.filter V (G.Adj v) (fun _ => Classical.propDecidable _) Finset.univ =
        Finset.univ.filter (G.Adj v) := by ext w; simp
  constructor
  · intro h v hv
    have hv' : c v ≠ none := (Finset.mem_filter.mp hv).2
    have hh := h v hv'
    rw [hn,hs v hv',hc] at hh
    simp only [Finset.card_empty] at hh
    omega
  · intro h v hv
    have hh := h v (by simp [coloredSupport,hv])
    change 2 * (1 + _) ≥ 1 + _
    rw [hn,hs v hv,hc]
    simp only [Finset.card_empty]
    omega

/-- Give each vertex of an actual dissociation selection its own natural color. -/
noncomputable def distinctColoring (S : Finset V) (v : V) : Option ℕ :=
  if v ∈ S then some ((Fintype.equivFin V v).val) else none

/-- The construction preserves the support exactly, including an empty selection. -/
theorem distinct_support (S : Finset V) :
    coloredSupport (distinctColoring S) Finset.univ = S := by
  classical
  ext v
  simp [coloredSupport,distinctColoring]

/-- Color names are injective on the selected vertices. -/
theorem distinct_injective (S : Finset V) :
    Set.InjOn (distinctColoring S) (coloredSupport (distinctColoring S) Finset.univ) := by
  classical
  rw [distinct_support]
  intro v hv w hw he
  simp only [Finset.mem_coe] at hv hw
  have he' : (Fintype.equivFin V v).val = (Fintype.equivFin V w).val := by
    simpa [distinctColoring,hv,hw] using he
  exact (Fintype.equivFin V).injective (Fin.ext he')

/-- The represented color count is the size of the selected set. -/
theorem distinct_palette (S : Finset V) :
    (palette (distinctColoring S) Finset.univ).card = S.card := by
  classical
  unfold palette
  rw [Finset.card_image_of_injOn (distinct_injective S),distinct_support]

/-- The complete lower comparison uses an actual attained dissociation maximum. -/
theorem beta_le_psiSq (G : SimpleGraph V) [DecidableRel G.Adj] :
    beta G 2 ≤ psiSq G := by
  classical
  have hnonempty : (Finset.univ.powerset.filter (IsKIndependent G 2)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    simp [IsKIndependent]
  obtain ⟨S, hmem, hmax⟩ :=
    Finset.exists_mem_eq_sup _ hnonempty Finset.card
  have hS := (Finset.mem_filter.mp hmem).2
  have hc : S.card = beta G 2 := hmax.symm
  have hi : IsSubQuorum G (distinctColoring S) :=
    (injective_support_iff G (distinctColoring S) (distinct_injective S)).mpr
      (by simpa only [distinct_support] using hS)
  rw [← hc, ← distinct_palette S]
  apply Nat.le_findGreatest
  · exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (by simp))
  · exact ⟨distinctColoring S, hi, rfl⟩

end D5.S3.Combinatorics.Graph.SubQuorum.DissociationColoring

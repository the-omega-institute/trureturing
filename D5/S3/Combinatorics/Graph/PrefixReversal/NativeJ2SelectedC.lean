/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual c edge of the same frame inventory witness has a selected terminal label. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SelectedC

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open private raw_a_cut_labels up_down from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open private cutGenerator_native from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreEdgeClassification
open private c_ne_native edge_generator_unique from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open private relabel_selected from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport

private theorem deleted_finish_selected {m : ℕ} (hm : 5 ≤ m)
    (z g : Configuration m) (hg : g = a m ∨ g = b m)
    (hd : F2DeletedEdge m s(z, z * g)) :
    (z * g) (Fin.last m) ∈ ({0, Fin.last m} : Finset (Fin (m + 1))) := by
  classical
  rcases hg with rfl | rfl
  · rcases Sym2.eq_iff.mp (raw_a_cut_labels hm z hd) with ⟨_, he⟩ | ⟨_, he⟩
    all_goals simp [he]
  · rcases (native_f2_b_cut_classification (by omega : 4 ≤ m) z).mp hd with
      ⟨_, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩
    all_goals simpa only [Equiv.Perm.mul_apply, b_last, he] using
      (show z (Fin.last m) ∈ ({0, Fin.last m} : Finset (Fin (m + 1))) by simp [he])

private theorem c_last (m : ℕ) : c m (Fin.last m) = Fin.last m := by
  apply Fin.ext
  simp only [c_apply, Fin.val_last, if_neg (by omega : ¬ m < m - 1)]

/-- Both endpoints of every literal T or E seam carry an actual selected
label. The conclusion follows from its own indexed deleted native edge. -/
theorem native_f2_seam_selected_terminal {m : ℕ} (hm : 5 ≤ m)
    (e : Sym2 (Configuration m)) (he : F2Seam m e)
    (x : Configuration m) (hx : x ∈ e) :
    x (Fin.last m) ∈ ({0, Fin.last m} : Finset (Fin (m + 1))) := by
  classical
  have seam_endpoint (z : Configuration m)
      (hz : z (Fin.last m) ∈ ({0, Fin.last m} : Finset (Fin (m + 1))))
      (hx : x ∈ s(z, z * c m)) :
      x (Fin.last m) ∈ ({0, Fin.last m} : Finset (Fin (m + 1))) := by
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hz
    · simpa only [Equiv.Perm.mul_apply, c_last] using hz
  rcases he with ⟨p, he⟩ | ⟨j, i, he⟩
  · apply seam_endpoint (cutStart p * cutGenerator p)
    · exact deleted_finish_selected hm _ _ (cutGenerator_native p) (Or.inl ⟨p, rfl⟩)
    · simpa only [he] using hx
  · apply seam_endpoint (gapAnchor (contactAnchor j) i * b m)
    · exact deleted_finish_selected hm _ _ (Or.inr rfl) (Or.inr ⟨j, i, rfl⟩)
    · simpa only [he] using hx

/-- The exact supplied frame walk supplies the edge membership. Its
inventory earns the selected terminal condition without choosing a new
cycle or requiring a selected-c certificate from the caller. -/
theorem native_j2_frame_c_selected {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2)
    {base : {v : Configuration m // FrameDomain F v}}
    (w : (domainGraph (FrameDomain F)).Walk base base)
    (hinv : ∀ e : Sym2 (Configuration m),
      e ∈ w.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m (Sym2.map (undoRelabel F) e) ∧
        ¬ F2DeletedEdge m (Sym2.map (undoRelabel F) e)) ∨
        F2Seam m (Sym2.map (undoRelabel F) e))
    (x y : {v : Configuration m // FrameDomain F v})
    (hy : y.val = x.val * c m) (he : s(x,y) ∈ w.edges) :
    x.val (Fin.last m) ∈ F.selected.toFinset := by
  classical
  have hraw : Sym2.map (undoRelabel F) s(x.val, y.val) =
      s(undoRelabel F x.val, undoRelabel F x.val * c m) := by
    simp only [hy, Sym2.map_mk, undoRelabel, mul_assoc]
  have hedge := (hinv s(x.val, y.val)).mp
    (List.mem_map.mpr ⟨s(x,y), he, rfl⟩)
  rw [hraw] at hedge
  have hseam : F2Seam m s(undoRelabel F x.val, undoRelabel F x.val * c m) := by
    rcases hedge with ⟨hn, _⟩ | hs
    · obtain ⟨z, g, _, hg, heq⟩ :=
        (native_f2_native_edge_catalog (by omega : 4 ≤ m) _).mp hn
      exact (c_ne_native (by omega : 4 ≤ m) g hg
        (edge_generator_unique _ _ (c m) g (c_sq m) heq)).elim
    · exact hs
  have hlabel := native_f2_seam_selected_terminal hm _ hseam
    (undoRelabel F x.val) (Sym2.mem_mk_left _ _)
  rw [← relabel_selected hm F]
  apply Finset.mem_image.mpr
  refine ⟨(undoRelabel F x.val) (Fin.last m), hlabel, ?_⟩
  exact congrArg (fun z : Configuration m => z (Fin.last m)) (up_down F x.val)

#print axioms native_f2_seam_selected_terminal
#print axioms native_j2_frame_c_selected

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SelectedC

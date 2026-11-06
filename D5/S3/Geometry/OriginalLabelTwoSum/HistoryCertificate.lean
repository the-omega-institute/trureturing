/- GID: D5/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/HistoryCertificate
   mirror-E: none(waiver:physical-history-strong-extraction)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Actual mixed-history roots contain a singleton and yield their computed strong main and separate-core sequences. -/
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryRecursion

/-! SOURCE_ONLY_UNCOMPILED. The nondegeneracy argument concerns the literal
augmented root, before project. It retains the full ambient type V, all old
ghosts and every actual physical chord index. No classification, local leaf,
Output, Certificate or collapse supplier is an input of the history results.

The strong branch below is the exact allCornersOutput branch at empty masks.
Equality transport changes neither its critical data nor its ordered native
main and C-ALONE sequences. Existing Sequence geometry consumes those fields
directly; this module adds no application or homotopy wrapper and asserts no
sphere equivalence. All elaboration, kernel, Scribe, Reg and delivery checks
remain pending. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryCertificate
open OriginalLabelTwoSum HistoryCorners HistoryLeafCap PhysicalHistory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every prescribed actual history has a genuine singleton in its raw root.
At an attachment, an old retained label outside the deleted port is outside
the fresh ground supporting an actual surviving right physical row. -/
theorem root_has_singleton {n : Nat} {G : Type} {g : GraphData G V}
    (h : MixedHistory n G g) : ∃ x : V, ({x} : Finset V) ∈ g.rows.root := by
  cases h with
  | seed f =>
      refine ⟨f 0, ?_⟩
      rw [seed_root]
      exact Or.inl (Or.inl (show ({f 0} : Finset V) ⊆ {f 0} from le_rfl))
  | @attach n G g old i =>
      have hcard := mixed_ground_card old
      have herase := Finset.card_erase_add_one i.retained
      have hold : (g.ground.erase i.e).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hold
      let d : Fin i.width := ⟨1, by have := i.atLeastThree; omega⟩
      have hd : d ≠ AllMWheel.interfaceRow i.width i.atLeastThree := by
        intro heq
        have hv := congrArg Fin.val heq
        change 1 = 0 at hv
        omega
      let c := (physicalWheelStep_chords g i).symm (.inr ⟨d, hd⟩)
      have hrow : (physicalWheelStep g i).data.rows.row c ⊆
          (AllMWheel.ground i.width).image i.labels := by
        change (physicalWheelStep g i).data.rows.row
          ((physicalWheelStep_chords g i).symm (.inr ⟨d, hd⟩)) ⊆ _
        rw [physicalWheelStep_rows_right]
        exact Finset.image_subset_image
          ((AllMWheel.rimRows i.width (by have := i.atLeastThree; omega)).row_supported d)
      have hxrow : x ∉ (physicalWheelStep g i).data.rows.row c := by
        intro hxc
        exact Finset.disjoint_left.mp i.fresh (Finset.mem_of_mem_erase hx) (hrow hxc)
      refine ⟨x, c, Finset.singleton_subset_iff.mpr ?_⟩
      refine Finset.mem_sdiff.mpr ⟨?_, hxrow⟩
      change x ∈ g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels
      exact Finset.mem_union_left _ hx

private theorem empty_corner {G : Type} (g : GraphData G V) :
    corner g.ground ∅ ∅ g.rows.root = g.rows.root := by
  apply SetLike.ext
  intro s
  change (s ⊆ HistoryCorners.residual g.ground ∅ ∅ ∧ s ∪ ∅ ∈ g.rows.root) ↔ s ∈ g.rows.root
  simp only [HistoryCorners.residual, Finset.union_empty, Finset.sdiff_empty]
  exact ⟨fun hs => hs.2, fun hs => ⟨g.rows.root_supported s hs, hs⟩⟩

private def strongOfSingleton {W : Finset V} {K : Family V}
    (o : Output W K) (has : ∃ x : V, ({x} : Finset V) ∈ K) : Certificate W K := by
  cases o with
  | void he =>
      apply False.elim
      obtain ⟨x, hx⟩ := has
      rw [he] at hx
      exact hx
  | unit he =>
      apply False.elim
      obtain ⟨x, hx⟩ := has
      rw [he] at hx
      change ({x} : Finset V) ⊆ ∅ at hx
      exact Finset.notMem_empty x (hx (Finset.mem_singleton_self x))
  | strong c => exact c

/-- Construct the strong certificate on the ACTUAL uncornered root. The only
input is the prescribed history. Its main list starts at project g.rows.root;
its separate list starts at project core ALONE and ends at its own actual
coordinate vertex. Every critical absence, proper boundary and antichain
condition is inherited from this exact computed strong branch. -/
def certificate {n : Nat} {G : Type} {g : GraphData G V}
    (h : MixedHistory n G g) : Certificate g.ground g.rows.root := by
  have o := HistoryRecursion.allCornersOutput h ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) (by simp)
  have hground : HistoryCorners.residual g.ground ∅ ∅ = g.ground := by
    simp only [HistoryCorners.residual, Finset.union_empty, Finset.sdiff_empty]
  rw [hground, empty_corner g] at o
  exact strongOfSingleton o (root_has_singleton h)

end D5.S3.Geometry.OriginalLabelTwoSum.HistoryCertificate

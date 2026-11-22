/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularComplement
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularComplement
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDimension]
   utility: none
   digest: Countably many smooth sets of codimension two leave a path-connected complement. -/
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The endpoints of segments passing through the excluded sets lie in
cones of dimension strictly below the ambient dimension. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularComplement

open Set
open scoped Convex ENNReal

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

private def cone (D : ℕ → Set H) (g : ℕ → H → E) (x : E) : Set E :=
  ⋃ k, (fun p : H × ℝ => p.2 • (g k p.1 - x) + x) '' (D k ×ˢ (univ : Set ℝ))

omit [FiniteDimensional ℝ E] in
private theorem cone_dim {D : ℕ → Set H} {g : ℕ → H → E}
    (hg : ∀ k, DifferentiableOn ℝ (g k) (D k)) (x : E) :
    dimH (cone D g x) ≤ Module.finrank ℝ H + 1 := by
  rw [cone, dimH_iUnion]
  apply iSup_le
  intro k
  have hcomp : DifferentiableOn ℝ (fun p : H × ℝ => g k p.1) (D k ×ˢ (univ : Set ℝ)) :=
    (hg k).comp differentiable_fst.differentiableOn (fun _ hp => hp.1)
  have hdiff : DifferentiableOn ℝ (fun p : H × ℝ => p.2 • (g k p.1 - x) + x)
      (D k ×ˢ (univ : Set ℝ)) :=
    (differentiable_snd.differentiableOn.smul (hcomp.sub_const x)).add_const x
  calc
    _ ≤ dimH (D k ×ˢ (univ : Set ℝ)) := hdiff.dimH_image_le
    _ ≤ dimH (univ : Set (H × ℝ)) := dimH_mono (subset_univ _)
    _ = _ := by
      rw [Real.dimH_univ_eq_finrank, Module.finrank_prod, Module.finrank_self, Nat.cast_add,
        Nat.cast_one]

private theorem segment_avoids {D : ℕ → Set H} {g : ℕ → H → E} {B : Set E}
    (hB : B ⊆ ⋃ k, g k '' D k) {x c : E} (hx : x ∉ B) (hc : c ∉ cone D g x) :
    segment ℝ x c ⊆ Bᶜ := by
  intro z hz hzB
  obtain ⟨t, _, rfl⟩ := segment_eq_image_lineMap ℝ x c ▸ hz
  have ht : t ≠ 0 := by
    intro h
    subst t
    exact hx (by simpa using hzB)
  obtain ⟨k, u, hu, he⟩ := mem_iUnion.mp (hB hzB)
  apply hc
  refine mem_iUnion.mpr ⟨k, ⟨(u, t⁻¹), ⟨hu, mem_univ _⟩, ?_⟩⟩
  change t⁻¹ • (g k u - x) + x = c
  rw [he, AffineMap.lineMap_apply_module', add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ ht, one_smul, sub_add_cancel]

/-- A set covered by countably many differentiable images of dimension at
least two below the ambient dimension has a path-connected complement. -/
theorem isPathConnected_compl_of_smooth_cover (B : Set E) (D : ℕ → Set H)
    (g : ℕ → H → E) (hg : ∀ k, DifferentiableOn ℝ (g k) (D k))
    (hB : B ⊆ ⋃ k, g k '' D k)
    (hcodim : Module.finrank ℝ H + 1 < Module.finrank ℝ E) :
    IsPathConnected Bᶜ := by
  have hlt : ((Module.finrank ℝ H : ℕ) : ℝ≥0∞) + 1 < Module.finrank ℝ E := by
    exact_mod_cast hcodim
  have hdim : dimH B < Module.finrank ℝ E := by
    apply (dimH_mono hB).trans_lt
    rw [dimH_iUnion]
    refine (iSup_le fun k => (hg k).dimH_image_le.trans
      ((dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank H))).trans_lt ?_
    exact (Nat.cast_lt.2 (Nat.lt_of_succ_lt hcodim))
  obtain ⟨x, hx⟩ := (dense_compl_of_dimH_lt_finrank hdim).nonempty
  refine ⟨x, hx, fun y hy => ?_⟩
  have hC : dimH (cone D g x ∪ cone D g y) < Module.finrank ℝ E := by
    rw [dimH_union]
    exact (sup_le (cone_dim hg x) (cone_dim hg y)).trans_lt hlt
  obtain ⟨c, hc⟩ := (dense_compl_of_dimH_lt_finrank hC).nonempty
  have hxc : segment ℝ x c ⊆ Bᶜ := segment_avoids hB hx (fun h => hc (Or.inl h))
  have hyc : segment ℝ y c ⊆ Bᶜ := segment_avoids hB hy (fun h => hc (Or.inr h))
  have join (a : E) (hs : segment ℝ a c ⊆ Bᶜ) : JoinedIn Bᶜ a c :=
    (((convex_segment a c).isPathConnected ⟨a, left_mem_segment ..⟩).joinedIn
      a (left_mem_segment ..) c (right_mem_segment ..)).mono hs
  exact (join x hxc).trans (join y hyc).symm

end D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularComplement

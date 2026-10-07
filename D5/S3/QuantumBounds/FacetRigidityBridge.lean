/- GID: D5/S3/QuantumBounds/FacetRigidityBridge
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/FacetRigidityBridge
   mirror-E: none(waiver:non-computational-content)
   anchors: []
   utility: none
   digest: Rigidity of saturating generators gives an exposed face of affine codimension one. -/
/-
proof_shape: rigidity_facet_bridge: content; face_convexHull: content.
proof_shape: vectorSpan_convexHull: bind-only (consumer: rigidity_facet_bridge).
proof_shape: annihilator_vectorSpan: bind-only (consumer: rigidity_facet_bridge).
escape_witness: face_convexHull, and the annihilator decomposition in rigidity_facet_bridge.
admission_basis: escape-witness
Utility: general convex geometry, without enumeration, checker, numeric reduction or instance.
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
open scoped BigOperators
open Set

namespace D5.S3.QuantumBounds.FacetRigidityBridge
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- proof_shape: bind-only; consumer: rigidity_facet_bridge. -/
private theorem vectorSpan_convexHull (s : Set E) :
    vectorSpan ℝ (convexHull ℝ s) = vectorSpan ℝ s := by
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

/-- proof_shape: content; consumer: rigidity_facet_bridge. -/
private theorem face_convexHull (s : Set E) (I : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hv : ∀ z ∈ s, b ≤ I z) (o : E) (ho : o ∈ s) (hIo : I o = b) :
    {p ∈ convexHull ℝ s | I p = b} = convexHull ℝ {z ∈ s | I z = b} := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨hp, hIp⟩
    obtain ⟨ι, inst, w, z, hw, hsum, hz, hrep⟩ := mem_convexHull_iff_exists_fintype.mp hp
    let _ := inst
    have hIsum : ∑ i, w i * I (z i) = b := by
      rw [← hrep] at hIp
      simpa using hIp
    have hzero : ∑ i, w i * (I (z i) - b) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hIsum, hsum, one_mul, sub_self]
    have hnonneg (i : ι) : 0 ≤ w i * (I (z i) - b) :=
      mul_nonneg (hw i) (sub_nonneg.mpr (hv _ (hz i)))
    have hactive (i : ι) (hi : 0 < w i) : I (z i) = b := by
      have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hzero i
        (Finset.mem_univ i)
      have hh := (mul_eq_zero.mp he).resolve_left (ne_of_gt hi)
      exact sub_eq_zero.mp hh
    let z' : ι → E := fun i => if 0 < w i then z i else o
    refine mem_convexHull_of_exists_fintype w z' hw hsum ?_ ?_
    · intro i
      dsimp [z']
      split_ifs with hi
      · exact ⟨hz i, hactive i hi⟩
      · exact ⟨ho, hIo⟩
    · calc ∑ i, w i • z' i = ∑ i, w i • z i := by
             apply Finset.sum_congr rfl
             intro i _
             dsimp [z']
             split_ifs with hi
             · rfl
             · have hi0 : w i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
               simp [hi0]
           _ = p := hrep
  · refine convexHull_min ?_ ?_
    · rintro z ⟨hz, hIz⟩
      exact ⟨subset_convexHull ℝ s hz, hIz⟩
    · exact (convex_convexHull ℝ s).inter ((convex_singleton b).linear_preimage I)

/-- proof_shape: bind-only; consumer: rigidity_facet_bridge. -/
private theorem annihilator_vectorSpan (s : Set E) (o : E) (ho : o ∈ s)
    (ell : E →ₗ[ℝ] ℝ) :
    ell ∈ (vectorSpan ℝ s).dualAnnihilator ↔ ∀ z ∈ s, ell z = ell o := by
  constructor
  · intro h z hz
    have he := (Submodule.mem_dualAnnihilator ell).mp h (z - o)
      (vsub_mem_vectorSpan ℝ hz ho)
    simpa [map_sub, sub_eq_zero] using he
  · intro h
    apply (Submodule.mem_dualAnnihilator ell).mpr
    have hle : vectorSpan ℝ s ≤ LinearMap.ker ell := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ ho]
      apply Submodule.span_le.mpr
      rintro z ⟨p, hp, rfl⟩
      change ell (p - o) = 0
      simp only [map_sub, h p hp, sub_self]
    intro z hz
    exact hle hz

variable [FiniteDimensional ℝ E]

theorem rigidity_facet_bridge (s : Set E) (I n : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hv : ∀ z ∈ s, b ≤ I z)
    (hn : ∀ z ∈ s, n z = 1)
    (o : E) (ho : o ∈ s) (hIo : I o = b)
    (t : E) (ht : t ∈ s) (hIt : I t ≠ b)
    (hR : ∀ ell : E →ₗ[ℝ] ℝ,
      (∀ z ∈ s, I z = b → ell z = 0) →
      ∃ lam : ℝ, ∀ z ∈ s, ell z = lam * (I z - b)) :
    Module.finrank ℝ (vectorSpan ℝ {p ∈ convexHull ℝ s | I p = b}) + 1 =
      Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ s)) := by
  rw [face_convexHull s I b hv o ho hIo, vectorSpan_convexHull, vectorSpan_convexHull]
  let W := vectorSpan ℝ s
  let U := vectorSpan ℝ {z ∈ s | I z = b}
  have hUo : o ∈ {z ∈ s | I z = b} := ⟨ho, hIo⟩
  have hW : I ∉ W.dualAnnihilator := by
    intro hi
    have hh := (annihilator_vectorSpan s o ho I).mp hi t ht
    exact hIt (hh.trans hIo)
  have eqann : U.dualAnnihilator = W.dualAnnihilator ⊔ Submodule.span ℝ {I} := by
    apply le_antisymm
    · intro ell hell
      have heq := (annihilator_vectorSpan _ o hUo ell).mp hell
      let ell0 := ell - (ell o) • n
      obtain ⟨lam, hlam⟩ := hR ell0 (by
        intro z hz hIz
        have hh := heq z ⟨hz, hIz⟩
        simp [ell0, hh, hn z hz])
      have hdiff : ell - lam • I ∈ W.dualAnnihilator := by
        apply (annihilator_vectorSpan s o ho _).mpr
        intro z hz
        have h := hlam z hz
        simp only [ell0, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hn z hz] at h
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hIo]
        linarith
      exact Submodule.mem_sup.mpr ⟨ell - lam • I, hdiff, lam • I,
        Submodule.smul_mem _ lam (Submodule.mem_span_singleton_self I), sub_add_cancel ell (lam •
          I)⟩
    · apply sup_le
      · intro ell hell
        apply (annihilator_vectorSpan _ o hUo ell).mpr
        intro z hz
        exact (annihilator_vectorSpan s o ho ell).mp hell z hz.1
      · apply Submodule.span_le.mpr
        intro ell hell
        have he : ell = I := Set.mem_singleton_iff.mp hell
        subst ell
        apply (annihilator_vectorSpan _ o hUo I).mpr
        intro z hz
        exact hz.2.trans hIo.symm
  have hdim := Submodule.finrank_sup_span_singleton hW
  rw [← eqann] at hdim
  have hWdim := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hUdim := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  change Module.finrank ℝ U + 1 = Module.finrank ℝ W
  apply Nat.add_right_cancel (m := Module.finrank ℝ W.dualAnnihilator)
  calc (Module.finrank ℝ U + 1) + Module.finrank ℝ W.dualAnnihilator =
      Module.finrank ℝ U + (Module.finrank ℝ W.dualAnnihilator + 1) := by ring
    _ = Module.finrank ℝ U + Module.finrank ℝ U.dualAnnihilator := by rw [hdim]
    _ = Module.finrank ℝ W + Module.finrank ℝ W.dualAnnihilator := hUdim.trans hWdim.symm

end D5.S3.QuantumBounds.FacetRigidityBridge

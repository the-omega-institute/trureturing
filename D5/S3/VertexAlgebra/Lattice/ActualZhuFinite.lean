/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuFinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuFinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-definite lattice full actual Zhu additive quotient is finite-dimensional. -/

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Fedor K. Popov
Modified source: the circle absorption and degree induction adapt
VOA.Modularity.ZhuAlgebraFinite from Lean_VOA commit
013a799ca834a8a6b3afa8129e3e522025b3f45c to the original actual lattice carrier.
The fixed-energy C2 projection expands both unrestricted input states.
proof_shape: positive_definite_zhu_quotient_finite: content
admission_basis: escape-witness
escape_witness: fixed-energy projection of full C2 into homogeneous pairs and
strict lower-energy absorption by the complete actual circle sum.
-/

import D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite
import D5.S3.VertexAlgebra.Lattice.NormFourZhuFinite
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading

/-! Finite homogeneous lifts, fixed-energy C2 projection, and strict circle descent
on the original full lattice carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuFinite

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy
open scoped BigOperators VertexOperator

noncomputable section

/-- The full actual Zhu O-space; the second state is unrestricted. -/
def zhuO (D : LatticeData) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ (n : ℕ) (a b : Carrier D),
    a ∈ grade D (n : ℤ) ∧ z = NormFourZhuFinite.circle D n a b}

private def homogeneousC2 (D : LatticeData) (N : ℕ) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ (p q : ℕ) (a b : Carrier D),
    a ∈ grade D (p : ℤ) ∧ b ∈ grade D (q : ℤ) ∧ p + q + 1 = N ∧
    z = mu D a (-2) b}

private theorem projection_c2 (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ)
    (z : Carrier D) (hz : z ∈ ActualC2.C2 D) :
    gradeProjection D (N : ℤ) z ∈ homogeneousC2 D N := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl⟩ := hz
    have hexpand : mu D a (-2) b =
        ∑ p ∈ stateEnergies D a, ∑ q ∈ stateEnergies D b,
          mu D (gradeProjection D p a) (-2) (gradeProjection D q b) := by
      conv_lhs => rw [← sum_gradeProjections D a, ← sum_gradeProjections D b]
      simp only [mu, map_sum, Finset.sum_apply, LinearMap.sum_apply]
      exact Finset.sum_comm
    rw [hexpand, map_sum]
    apply Submodule.sum_mem
    intro p hp
    rw [map_sum]
    apply Submodule.sum_mem
    intro q hq
    have hp0 := stateEnergies_nonneg hD a p hp
    have hq0 := stateEnergies_nonneg hD b q hq
    have hpcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp0
    have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq0
    have hm := positive_actual_mode_grade D hD p q (-2)
      (gradeProjection D p a) (gradeProjection D q b)
      (gradeProjection_mem D p a) (gradeProjection_mem D q b)
    change mu D _ (-2) _ ∈ grade D (p + q - (-2) - 1) at hm
    by_cases he : p + q - (-2) - 1 = (N : ℤ)
    · rw [he] at hm
      rw [gradeProjection_eq_self_of_mem_grade D _ _ hm]
      exact Submodule.subset_span ⟨p.toNat, q.toNat,
        gradeProjection D p a, gradeProjection D q b,
        by simpa only [hpcast] using gradeProjection_mem D p a,
        by simpa only [hqcast] using gradeProjection_mem D q b,
        by omega, rfl⟩
    · rw [gradeProjection_zero_of_mem_grade_ne D _ _ he _ hm]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (homogeneousC2 D N).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (homogeneousC2 D N).smul_mem c ih

private theorem finite_homogeneous_representatives (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    [Module.Finite ℂ (Carrier D ⧸ ActualC2.C2 D)] :
    ∃ S : Finset (Carrier D),
      (∀ s ∈ S, ∃ n : ℕ, s ∈ grade D (n : ℤ)) ∧
      Submodule.span ℂ (S : Set (Carrier D)) ⊔ ActualC2.C2 D = ⊤ := by
  classical
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin (R := ℂ) (M := Carrier D ⧸ ActualC2.C2 D)
  choose r hr using fun i : Fin k => (ActualC2.C2 D).mkQ_surjective (f i)
  let S : Finset (Carrier D) := Finset.univ.biUnion fun i : Fin k =>
    (stateEnergies D (r i)).image fun n => gradeProjection D n (r i)
  have hR : Submodule.span ℂ (Set.range r) ⊔ ActualC2.C2 D = ⊤ := by
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span]
    have he : (ActualC2.C2 D).mkQ '' Set.range r = Set.range f := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hr i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨r i, ⟨i, rfl⟩, hr i⟩
    rw [he, hf]
  have hRS : Submodule.span ℂ (Set.range r) ≤ Submodule.span ℂ (S : Set (Carrier D)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← sum_gradeProjections D (r i)]
    apply Submodule.sum_mem
    intro n hn
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  refine ⟨S, ?_, top_unique ?_⟩
  · intro s hs
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨n.toNat, ?_⟩
    simpa only [Int.toNat_of_nonneg (stateEnergies_nonneg hD (r i) n hn)] using
      gradeProjection_mem D n (r i)
  · rw [← hR]
    exact sup_le_sup_right hRS _

private theorem projection_span (D : LatticeData) (S : Finset (Carrier D))
    (hS : ∀ s ∈ S, ∃ n : ℕ, s ∈ grade D (n : ℤ))
    (N : ℕ) (v : Carrier D) (hv : v ∈ Submodule.span ℂ (S : Set (Carrier D))) :
    gradeProjection D (N : ℤ) v ∈ Submodule.span ℂ (S : Set (Carrier D)) := by
  classical
  induction hv using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨n, hn⟩ := hS s hs
    by_cases he : (n : ℤ) = (N : ℤ)
    · rw [he] at hn
      rw [gradeProjection_eq_self_of_mem_grade D _ _ hn]
      exact Submodule.subset_span hs
    · rw [gradeProjection_zero_of_mem_grade_ne D _ _ he _ hn]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

private theorem homogeneous_spanning (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (S : Finset (Carrier D))
    (hS : ∀ s ∈ S, ∃ n : ℕ, s ∈ grade D (n : ℤ))
    (htop : Submodule.span ℂ (S : Set (Carrier D)) ⊔ ActualC2.C2 D = ⊤)
    (N : ℕ) (v : Carrier D) (hv : v ∈ grade D (N : ℤ)) :
    v ∈ Submodule.span ℂ (S : Set (Carrier D)) ⊔ homogeneousC2 D N := by
  have hmem : v ∈ Submodule.span ℂ (S : Set (Carrier D)) ⊔ ActualC2.C2 D := by
    rw [htop]; trivial
  obtain ⟨s, hs, z, hz, he⟩ := Submodule.mem_sup.mp hmem
  have he' := congrArg (gradeProjection D (N : ℤ)) he
  rw [map_add, gradeProjection_eq_self_of_mem_grade D _ _ hv] at he'
  exact Submodule.mem_sup.mpr ⟨_, projection_span D S hS N s hs,
    _, projection_c2 D hD N z hz, he'⟩

private theorem circle_absorption (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (T : Submodule ℂ (Carrier D)) (hO : zhuO D ≤ T)
    (N : ℕ) (ih : ∀ j < N, grade D (j : ℤ) ≤ T) : homogeneousC2 D N ≤ T := by
  classical
  apply Submodule.span_le.mpr
  rintro z ⟨p, q, a, b, ha, hb, hpq, rfl⟩
  change mu D a (-2) b ∈ T
  let correction : Carrier D := ∑ k ∈ Finset.range p,
    (p.choose (k + 1) : ℂ) • mu D a ((k : ℤ) - 1) b
  have hc : NormFourZhuFinite.circle D p a b = mu D a (-2) b + correction := by
    unfold NormFourZhuFinite.circle
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, Nat.cast_zero, zero_sub]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    push_cast
    ring
  have hcircle : NormFourZhuFinite.circle D p a b ∈ T :=
    hO (Submodule.subset_span ⟨p, a, b, ha, rfl⟩)
  have hcorr : correction ∈ T := by
    apply Submodule.sum_mem
    intro k hk
    apply T.smul_mem
    have hk' : k < p := Finset.mem_range.mp hk
    have hm := positive_actual_mode_grade D hD (p : ℤ) (q : ℤ) ((k : ℤ) - 1) a b ha hb
    have he : (p : ℤ) + (q : ℤ) - ((k : ℤ) - 1) - 1 = ((N - (k + 1) : ℕ) : ℤ) := by
      omega
    rw [he] at hm
    exact ih (N - (k + 1)) (by omega) hm
  simpa only [hc, add_sub_cancel_right] using T.sub_mem hcircle hcorr

/-- Finite-dimensionality of the full actual Zhu additive quotient. This
asserts no quotient multiplication, rationality, or analytic CFT property. -/
theorem positive_definite_zhu_quotient_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FiniteDimensional ℂ (Carrier D ⧸ zhuO D) := by
  classical
  have := ActualC2Cofinite.positive_definite_c2_cofinite D hD
  obtain ⟨S, hS, htop⟩ := finite_homogeneous_representatives D hD
  let T := Submodule.span ℂ (S : Set (Carrier D)) ⊔ zhuO D
  have hgrade : ∀ N : ℕ, grade D (N : ℤ) ≤ T := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      exact (fun v hv => (sup_le le_sup_left
        (circle_absorption D hD T le_sup_right N ih))
        (homogeneous_spanning D hD S hS htop N v hv))
  have hT : T = ⊤ := by
    apply top_unique
    intro v hv
    rw [← sum_gradeProjections D v]
    apply Submodule.sum_mem
    intro n hn
    have hn0 := stateEnergies_nonneg hD v n hn
    have hg : gradeProjection D n v ∈ grade D (n.toNat : ℤ) := by
      simpa only [Int.toNat_of_nonneg hn0] using gradeProjection_mem D n v
    exact hgrade n.toNat hg
  have hmap : (Submodule.span ℂ (S : Set (Carrier D))).map (zhuO D).mkQ = ⊤ := by
    rw [Submodule.map_mkQ_eq_top, sup_comm]
    exact hT
  apply Module.Finite.of_fg_top
  rw [← hmap]
  exact (Submodule.fg_span S.finite_toSet).map _

end
end D5.S3.VertexAlgebra.Lattice.ActualZhuFinite

#print axioms D5.S3.VertexAlgebra.Lattice.ActualZhuFinite.positive_definite_zhu_quotient_finite

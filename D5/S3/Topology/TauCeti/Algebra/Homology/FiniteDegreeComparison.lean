/- GID: D5/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison
   generality: G
   mirror-B: D5/B/S3/Topology/TauCeti/Algebra/Homology/FiniteDegreeComparison
   mirror-E: none(waiver:abstract-finite-degree-comparison)
   anchors: []
   utility: none
   digest: Triangular column homology bounds compare native total homology in finite degrees. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The natural-number total symmetry instance is adapted from
TauCetiProject/TauCeti revision 289eb81f25e69d47485b9ab90980e873372581d4,
TauCeti/Algebra/Homology/ComplexShape/Signs.lean.
Modifications: private instance in the receiving namespace; only the consumed
symmetry instance is retained. The full Apache-2.0 license is in
docs/reports/licenses/tauceti-sphere-port-LICENSE.txt.
-/

import D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Finite-degree comparison of first-quadrant total complexes -/

noncomputable section
open CategoryTheory Limits HomologicalComplex
universe v u

namespace HomologicalComplex₂

/-- The signed interchange of the two natural-number directions. -/
private instance finiteDegreeTotalSymmetry :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, Nat.add_mul, one_mul, pow_add]
    ac_rfl
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one]

variable {C : Type u} [Category.{v} C] [Abelian C]

open HomologicalComplex.HomologySequence ComplexShape in
/-- Row homology comparison in the triangle below Q, with epimorphisms on its boundary. -/
private lemma finite_degree_comparison_rows (Q : ℕ) :
    ∀ {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)} (φ : K ⟶ L),
      (∀ p q, p + q < Q →
        IsIso (homologyMap (((eval C _ q).mapHomologicalComplex _).map φ) p)) →
      (∀ p q, p + q = Q →
        Epi (homologyMap (((eval C _ q).mapHomologicalComplex _).map φ) p)) →
      (∀ n < Q, IsIso (homologyMap (total.map φ (ComplexShape.down ℕ)) n)) ∧
        Epi (homologyMap (total.map φ (ComplexShape.down ℕ)) Q) := by
  induction Q with
  | zero =>
    intro K L φ hIso hEpi
    refine ⟨fun n hn ↦ (Nat.not_lt_zero n hn).elim, ?_⟩
    exact epi_homologyMap_τ₂ (rowZeroShortComplexMap φ) (rowZeroShortComplex_shortExact K)
      (rowZeroShortComplex_shortExact L) 0 (hEpi 0 0 rfl)
      ((extend_exactAt _ _ 0 fun _ ↦ by simp [embeddingDownNatSucc]).isZero_homology.epi _)
      (fun j hj ↦ by simp at hj)
  | succ Q ih =>
    intro K L φ hIso hEpi
    obtain ⟨ihIso, ihEpi⟩ := ih (rowsSuccMap φ)
      (fun p q hpq ↦ hIso p (q + 1) (by omega))
      (fun p q hpq ↦ hEpi p (q + 1) (by omega))
    have hepi (n : ℕ) (hn : n ≤ Q) :
        Epi (homologyMap (total.map (rowsSuccMap φ) (ComplexShape.down ℕ)) n) := by
      rcases hn.lt_or_eq with hn | rfl
      · have := ihIso n hn
        infer_instance
      · exact ihEpi
    refine ⟨fun n hn ↦ ?_, ?_⟩
    · refine isIso_homologyMap_τ₂ (rowZeroShortComplexMap φ)
        (rowZeroShortComplex_shortExact K) (rowZeroShortComplex_shortExact L) n ?_
        (hIso n 0 (by omega)) ?_ ?_
      · rintro i rfl
        exact (epi_homologyMap_extendMap_iff _ (show embeddingDownNatSucc.f n = n + 1 from rfl)).2
          (hepi n (by omega))
      · rcases n with _ | n
        · exact isIso_homologyMap_extendMap_of_forall_ne _ fun _ ↦ by
            simp [embeddingDownNatSucc]
        · have := ihIso n (by omega)
          rw [← quasiIsoAt_iff_isIso_homologyMap] at this ⊢
          exact (quasiIsoAt_extendMap_iff _ embeddingDownNatSucc rfl).2 this
      · intro j hj
        have : IsIso (homologyMap (rowZeroShortComplexMap φ).τ₁ j) :=
          hIso j 0 (by simp at hj; omega)
        infer_instance
    · refine epi_homologyMap_τ₂ (rowZeroShortComplexMap φ)
        (rowZeroShortComplex_shortExact K) (rowZeroShortComplex_shortExact L) (Q + 1)
        (hEpi (Q + 1) 0 (by omega))
        ((epi_homologyMap_extendMap_iff _
          (show embeddingDownNatSucc.f Q = Q + 1 from rfl)).2 ihEpi) ?_
      intro j hj
      have : IsIso (homologyMap (rowZeroShortComplexMap φ).τ₁ j) :=
        hIso j 0 (by simp at hj; omega)
      infer_instance

variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the signed symmetry for the actual total map. -/
private lemma finite_degree_comparison_flip_naturality (φ : K ⟶ L) :
    let ψ : K.flip ⟶ L.flip := (flipFunctor C _ _).map φ
    total.map ψ (ComplexShape.down ℕ) ≫
        (L.totalFlipIso (ComplexShape.down ℕ)).hom =
      (K.totalFlipIso (ComplexShape.down ℕ)).hom ≫ total.map φ (ComplexShape.down ℕ) := by
  dsimp only
  ext n q p h
  dsimp only [HomologicalComplex.comp_f]
  simp only [ιTotal_map_assoc, ιTotal_totalFlipIso_f_hom,
    ιTotal_totalFlipIso_f_hom_assoc, Linear.units_smul_comp, Linear.comp_units_smul,
    ιTotal_map, flipFunctor_map_f_f]

/-- Triangular comparison of actual column homology gives isomorphisms on total homology
through degree k and an epimorphism in degree k+1. -/
theorem finite_degree_comparison_total_map (k : ℕ) (φ : K ⟶ L)
    (hIso : ∀ p q : ℕ, p + q ≤ k → IsIso (homologyMap (φ.f p) q))
    (hEpi : ∀ p q : ℕ, p + q = k + 1 → Epi (homologyMap (φ.f p) q)) :
    (∀ n : ℕ, n ≤ k → IsIso (homologyMap (total.map φ (ComplexShape.down ℕ)) n)) ∧
      Epi (homologyMap (total.map φ (ComplexShape.down ℕ)) (k + 1)) := by
  let ψ : K.flip ⟶ L.flip := (flipFunctor C _ _).map φ
  obtain ⟨hI, hE⟩ := finite_degree_comparison_rows (k + 1) ψ
    (fun q p hpq ↦ hIso p q (by omega))
    (fun q p hpq ↦ hEpi p q (by omega))
  have hnat : total.map ψ (ComplexShape.down ℕ) ≫
      (L.totalFlipIso (ComplexShape.down ℕ)).hom =
      (K.totalFlipIso (ComplexShape.down ℕ)).hom ≫ total.map φ (ComplexShape.down ℕ) :=
    finite_degree_comparison_flip_naturality φ
  have hmap : total.map φ (ComplexShape.down ℕ) =
      (K.totalFlipIso (ComplexShape.down ℕ)).inv ≫
        total.map ψ (ComplexShape.down ℕ) ≫
          (L.totalFlipIso (ComplexShape.down ℕ)).hom := by
    rw [hnat, Iso.inv_hom_id_assoc]
  constructor
  · intro n hn
    have := hI n (by omega)
    rw [hmap]
    simp only [homologyMap_comp]
    infer_instance
  · rw [hmap]
    simp only [homologyMap_comp]
    have := hE
    infer_instance

end HomologicalComplex₂

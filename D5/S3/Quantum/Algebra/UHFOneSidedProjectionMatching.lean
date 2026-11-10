/- GID: D5/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UHFOneSidedProjectionMatching
   mirror-E: none(waiver:intrinsic-algebraic-supplier)
   anchors: []
   utility: none
   digest: Finite-stage localization and one-sided matching of actual completed algebra projections. -/

import D5.S3.Quantum.Analysis.RussoDye
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

namespace D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching

open scoped Matrix.Norms.L2Operator
open Matrix

variable {C : Type*} [CStarAlgebra C]

/-- Actual unital full-matrix ranges, increasing and norm dense in the completed algebra.
No growth, parity, trace, localization, or matching condition is part of these data. -/
structure FullMatrixModel (C : Type*) [CStarAlgebra C] where
  size : ℕ → ℕ
  embed : (n : ℕ) → Matrix (Fin (size n)) (Fin (size n)) ℂ →⋆ₐ[ℂ] C
  injective : ∀ n, Function.Injective (embed n)
  increasing : ∀ n N, n ≤ N → Set.range (embed n) ⊆ Set.range (embed N)
  dense : Dense (⋃ n, Set.range (embed n))

private theorem close_projections_unitary {p q : C}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hclose : ‖p - q‖ < 1) :
    ∃ u : unitary C, (u : C) * p * star (u : C) = q := by
  let _ := CStarAlgebra.spectralOrder C
  let _ := CStarAlgebra.spectralOrderedRing C
  let x := q * p + (1 - q) * (1 - p)
  have hpp := hp.isIdempotentElem.eq
  have hqq := hq.isIdempotentElem.eq
  have hs : p + p - 1 ∈ unitary C := by
    apply Unitary.mem_iff.mpr
    simp only [star_sub, star_add, hp.isSelfAdjoint.star_eq, star_one]
    constructor <;> noncomm_ring [hpp]
  have hx : IsUnit x := by
    have he : 1 - x = (p - q) * (p + p - 1) := by
      dsimp [x]
      noncomm_ring [hpp]
    have hn : ‖1 - x‖ < 1 := by
      rw [he, CStarRing.norm_mul_coe_unitary (p - q) ⟨_, hs⟩]
      exact hclose
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  have hxp : x * p = q * x := by dsimp [x]; noncomm_ring [hpp, hqq]
  have hxx : star x * x = 1 - (p - q) * (p - q) := by
    dsimp [x]
    simp only [star_add, star_mul, star_sub, star_one,
      hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    noncomm_ring [hpp, hqq]
  have hcomm : Commute (star x * x) p := by
    rw [hxx]
    show (1 - (p - q) * (p - q)) * p = p * (1 - (p - q) * (p - q))
    noncomm_ring [hpp, hqq]
  have ha : Commute (CFC.abs x) p := by
    exact hcomm.cfcₙ_nnreal NNReal.sqrt
  obtain ⟨u, hu, hxu⟩ :=
    D5.S3.Quantum.Analysis.RussoDye.exists_mem_unitary_eq_mul_cfcAbs hx
  have hau : IsUnit (CFC.abs x) :=
    isUnit_mul_self_iff.mp (CFC.abs_mul_abs x ▸ hx.star.mul hx)
  have hup : u * p = q * u := by
    apply hau.mul_left_inj.mp
    calc u * p * CFC.abs x = u * CFC.abs x * p := by rw [mul_assoc, ha.eq, ← mul_assoc]
      _ = q * u * CFC.abs x := by simpa only [hxu, mul_assoc] using hxp
  refine ⟨⟨u, hu⟩, ?_⟩
  change u * p * star u = q
  rw [hup, mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one]

end D5.S3.Quantum.Algebra.UHFOneSidedProjectionMatching

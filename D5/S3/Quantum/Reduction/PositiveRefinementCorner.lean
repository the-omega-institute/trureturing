/- GID: D5/S3/Quantum/Reduction/PositiveRefinementCorner
   generality: I
   mirror-B: D5/B/S3/Quantum/Reduction/PositiveRefinementCorner
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Positive maps dominated by projection compression are scalar on the whole supported matrix corner. -/

import D5.S3.Quantum.Reduction.PositiveRefinementRigidity
import D5.S3.Quantum.Lieb.PositiveMapJensen
import Mathlib.Analysis.CStarAlgebra.Projection

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Reduction.PositiveRefinementRigidity
open D5.S3.Quantum.Lieb.PositiveMapJensen
namespace D5.S3.Quantum.Reduction.PositiveRefinementCorner
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem projection_frame (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    ∃ r : ℕ, ∃ V : Matrix n (Fin r) ℂ, Vᴴ * V = 1 ∧ V * Vᴴ = P := by
  classical
  have hp : P.IsHermitian := hP
  let U : Matrix n n ℂ := hp.eigenvectorUnitary
  let s := {i : n // hp.eigenvalues i = 1}
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let V : Matrix n (Fin (Fintype.card s)) ℂ := fun i j => U i (e j).val
  have heigen (i : n) : hp.eigenvalues i = 0 ∨ hp.eigenvalues i = 1 := by
    have hs := (isStarProjection_iff_spectrum_subset_and_isSelfAdjoint.mp
      (show IsStarProjection P from ⟨hPP, hP⟩)).1 (hp.eigenvalues_mem_spectrum_real i)
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hs
  have hu : Uᴴ * U = 1 := hp.eigenvectorUnitary.2.1
  have hspec : P = U * diagonal (fun i => (hp.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hp.spectral_theorem
  refine ⟨Fintype.card s, V, ?_, ?_⟩
  · ext i j
    have h := congrArg (fun M : Matrix n n ℂ => M (e i).val (e j).val) hu
    simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, e.injective.eq_iff, Subtype.val_injective.eq_iff] using h
  · ext i j
    calc
      (V * Vᴴ) i j = ∑ k : s, U i k.val * star (U j k.val) := by
        simpa only [V, Matrix.mul_apply, Matrix.conjTranspose_apply] using
          e.sum_comp (fun k : s => U i k.val * star (U j k.val))
      _ = ∑ k : n, (hp.eigenvalues k : ℂ) * (U i k * star (U j k)) := by
        apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
        · intro k hk
          have hn : hp.eigenvalues k ≠ 1 := by
            intro h
            exact hk ⟨⟨k, h⟩, rfl⟩
          rw [(heigen k).resolve_right hn]
          simp
        · intro k
          simp only [k.property, Complex.ofReal_one, one_mul]
      _ = (U * diagonal (fun k => (hp.eigenvalues k : ℂ)) * Uᴴ) i j := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = P i j := congrArg (fun M : Matrix n n ℂ => M i j) hspec.symm

/-- Positivity-only domination by compression to any Hermitian projection
forces one scalar on the entire corner; the zero corner is included. -/
theorem corner_dominated_scalar
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ P * X * P) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ X, Φ X = (c : ℂ) • (P * X * P) := by
  classical
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have hzero : Φ (1 - P) = 0 := by
    have hQ := hproj.one_sub.nonneg.posSemidef
    apply le_antisymm
    · have h := hdom (1 - P) hQ
      simpa only [mul_sub, mul_one, hPP, sub_self, zero_mul] using h
    · exact (hpos _ hQ).nonneg
  have hin := positive_map_projection_compression Φ hpos P hP hPP hzero
  let out : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := {
    toFun X := P * Φ X * P
    map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hout : out = Φ := by
    apply eq_of_projection_eq
    intro Q hQ hQQ
    have hq : IsStarProjection Q := ⟨hQQ, hQ⟩
    have hle : Φ Q ≤ P := by
      have hc := congruence_mono (sub_nonneg.mp hq.one_sub.nonneg) P
      have hc' : P * Q * P ≤ P := by simpa only [hP, mul_one, hPP] using hc
      exact (hdom Q hq.nonneg.posSemidef).trans hc'
    obtain ⟨hr, hl⟩ := hproj.mul_right_and_mul_left_of_nonneg_of_le
      (hpos Q hq.nonneg.posSemidef).nonneg hle
    exact (congrArg (fun M => M * P) hl).trans hr
  obtain ⟨r, V, hV, hVP⟩ := projection_frame P hP hPP
  by_cases hr : r = 0
  · subst r
    have hp0 : P = 0 := by rw [← hVP]; ext i j; simp [Matrix.mul_apply]
    refine ⟨0, le_rfl, zero_le_one, ?_⟩
    have heq : Φ = 0 := by
      apply eq_of_projection_eq
      intro Q hQ hQQ
      have hq : Q.PosSemidef := by
        simpa only [hQ, hQQ] using posSemidef_conjTranspose_mul_self Q
      change Φ Q = 0
      exact le_antisymm (by simpa only [hp0, zero_mul, mul_zero] using hdom Q hq)
        (hpos Q hq).nonneg
    intro X
    simp [heq]
  have hPV : P * V = V := by rw [← hVP, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hVP' : Vᴴ * P = Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hPV
  let T : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ := {
    toFun X := Vᴴ * Φ (V * X * Vᴴ) * V
    map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hTpos (X : Matrix (Fin r) (Fin r) ℂ) (hX : X.PosSemidef) : (T X).PosSemidef :=
    (hpos _ (hX.mul_mul_conjTranspose_same V)).conjTranspose_mul_mul_same V
  have hTdom (X : Matrix (Fin r) (Fin r) ℂ) (hX : X.PosSemidef) : T X ≤ X := by
    have hc := congruence_mono (hdom _ (hX.mul_mul_conjTranspose_same V)) V
    change T X ≤ Vᴴ * (P * (V * X * Vᴴ) * P) * V at hc
    have he : Vᴴ * (P * (V * X * Vᴴ) * P) * V = X := by
      calc
        _ = (Vᴴ * P * V) * X * (Vᴴ * P * V) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hVP', hV, one_mul, mul_one]
    simpa only [he] using hc
  obtain ⟨c, hc, hc', hT⟩ := identity_dominated_scalar T hTpos hTdom
    (⟨0, Nat.pos_of_ne_zero hr⟩ : Fin r)
  refine ⟨c, hc, hc', ?_⟩
  intro X
  have houtX : P * Φ X * P = Φ X := LinearMap.congr_fun hout X
  have hTX : T (Vᴴ * X * V) = Vᴴ * Φ X * V := by
    change Vᴴ * Φ (V * (Vᴴ * X * V) * Vᴴ) * V = _
    have he : V * (Vᴴ * X * V) * Vᴴ = P * X * P := by
      rw [← hVP]
      simp only [Matrix.mul_assoc]
    rw [he, hin X]
  calc
    Φ X = V * (Vᴴ * Φ X * V) * Vᴴ := by
      calc
        _ = P * Φ X * P := houtX.symm
        _ = _ := by rw [← hVP]; simp only [Matrix.mul_assoc]
    _ = V * T (Vᴴ * X * V) * Vᴴ := by rw [hTX]
    _ = (c : ℂ) • (P * X * P) := by
      rw [hT]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← hVP]
      simp only [Matrix.mul_assoc]

#print axioms corner_dominated_scalar
end D5.S3.Quantum.Reduction.PositiveRefinementCorner

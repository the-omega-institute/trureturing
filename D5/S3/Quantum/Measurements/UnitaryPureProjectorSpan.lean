/- GID: D5/S3/Quantum/Measurements/UnitaryPureProjectorSpan
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/UnitaryPureProjectorSpan
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complex linear matrix maps agree when they agree on every unitary pure projector. -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Unitary pure projectors determine complex linear maps on all matrices. -/

open scoped BigOperators Matrix

noncomputable section

namespace D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem unitary_pure_ext {d : ℕ} [NeZero d]
    (f g : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ u : Matrix.unitaryGroup (Fin d) ℂ,
      f (u.1 * Matrix.single 0 0 1 * u.1ᴴ) =
        g (u.1 * Matrix.single 0 0 1 * u.1ᴴ)) : f = g := by
  have hs (u : Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
      f (u.1 * Matrix.single i i 1 * u.1ᴴ) =
        g (u.1 * Matrix.single i i 1 * u.1ᴴ) := by
    let p := (Equiv.swap (0 : Fin d) i).permMatrix ℂ
    have hp : p ∈ Matrix.unitaryGroup (Fin d) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      simp [p, Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
    let v : Matrix.unitaryGroup (Fin d) ℂ := u * ⟨p, hp⟩
    have hsingle : p * Matrix.single 0 0 1 * pᴴ = Matrix.single i i 1 := by
      dsimp [p]
      rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
        PEquiv.mul_toMatrix_toPEquiv]
      ext a b
      simp only [Matrix.submatrix_apply, Function.id_def, Equiv.swap_inv,
        Equiv.symm_swap, Matrix.single]
      have ha : (0 : Fin d) = (Equiv.swap 0 i) a ↔ i = a := by
        constructor
        · intro hzero
          simpa using congrArg (Equiv.swap (0 : Fin d) i) hzero
        · intro hai
          rw [← hai]
          simp
      have hb : (0 : Fin d) = (Equiv.swap 0 i) b ↔ i = b := by
        constructor
        · intro hzero
          simpa using congrArg (Equiv.swap (0 : Fin d) i) hzero
        · intro hbi
          rw [← hbi]
          simp
      change (if 0 = (Equiv.swap 0 i) a ∧ 0 = (Equiv.swap 0 i) b then (1 : ℂ) else 0) =
        if i = a ∧ i = b then 1 else 0
      simp only [ha, hb]
    have hv : v.1 * Matrix.single 0 0 1 * v.1ᴴ =
        u.1 * Matrix.single i i 1 * u.1ᴴ := by
      change (u.1 * p) * Matrix.single 0 0 1 * (u.1 * p)ᴴ = _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc p (Matrix.single 0 0 1),
        ← Matrix.mul_assoc (p * Matrix.single 0 0 1), hsingle]
    simpa only [hv] using h v
  have hh (x : Matrix (Fin d) (Fin d) ℂ) (hx : x.IsHermitian) : f x = g x := by
    let u := hx.eigenvectorUnitary
    have hdec : x = ∑ i, (hx.eigenvalues i : ℂ) •
        ((u : Matrix (Fin d) (Fin d) ℂ) * Matrix.single i i 1 *
          (u : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
      conv_lhs => rw [hx.spectral_theorem, Unitary.conjStarAlgAut_apply]
      rw [← Matrix.sum_single_eq_diagonal]
      simp only [Function.comp_apply, Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi : Matrix.single i i (RCLike.ofReal (hx.eigenvalues i) : ℂ) =
          (hx.eigenvalues i : ℂ) • Matrix.single i i 1 := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
        simp
      rw [hi, Matrix.mul_smul, Matrix.smul_mul]
      simp [u, Matrix.star_eq_conjTranspose]
    rw [hdec, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, map_smul, hs u i]
  apply LinearMap.ext
  intro x
  rw [← realPart_add_I_smul_imaginaryPart x, map_add, map_add,
    map_smul, map_smul, hh _ (realPart x).2, hh _ (imaginaryPart x).2]

theorem trace_one_sandwich {d : ℕ} (p x : Matrix (Fin d) (Fin d) ℂ)
    (hpp : p * p = p) (htr : p.trace = 1) :
    p * x * p = (p * x).trace • p := by
  let f := Matrix.toLin' p
  have hf : IsIdempotentElem f := by
    change f * f = f
    simpa only [f, Module.End.mul_eq_comp, ← Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hpp
  have hdim : Module.finrank ℂ (LinearMap.range f) = 1 := by
    have ht := ((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hf).trace
    rw [Matrix.trace_toLin'_eq, htr] at ht
    exact_mod_cast ht.symm
  let t : LinearMap.range f →ₗ[ℂ] LinearMap.range f :=
    (f.rangeRestrict.comp (Matrix.toLin' x)).comp (LinearMap.range f).subtype
  obtain ⟨c, hc, hu⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim t
  have hmat : p * x * p = c • p := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun z : LinearMap.range f => (z : Fin d → ℂ))
      (LinearMap.congr_fun hc (f.rangeRestrict v))
    change f ((Matrix.toLin' x) (f v)) = c • f v at hv
    simpa only [f, Matrix.toLin'_mul_apply, map_smul, LinearMap.smul_apply] using hv
  have hcval : c = (p * x).trace := by
    have ht := congrArg Matrix.trace hmat
    rw [Matrix.trace_smul, htr, smul_eq_mul, mul_one,
      Matrix.trace_mul_cycle, hpp] at ht
    exact ht.symm
  simpa only [hcval] using hmat

end D5.S3.Quantum.Measurements.UnitaryPureProjectorSpan

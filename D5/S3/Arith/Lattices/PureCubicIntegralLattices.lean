/- GID: D5/S3/Arith/Lattices/PureCubicIntegralLattices
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicIntegralLattices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two integral bases of rational pure-cubic lattices have explicit trace discriminants. -/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicIntegralLattices

open Polynomial Module
open scoped Matrix

/-- The displayed triples are integral rational bases with discriminants
`-27(mn)^2` and `-3(mn)^2`. The theorem does not identify the full ring of
integers or its field discriminant. -/
theorem integral_cubic_lattices
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((m * n ^ 2 : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k) :
    IsIntegral ℤ pb.gen ∧
    IsIntegral ℤ (pb.gen ^ 2 / (n : K)) ∧
    IsIntegral ℤ
      ((1 + (c : K) * pb.gen +
        (v : K) * (pb.gen ^ 2 / (n : K))) / 3) ∧
    ∃ b1 b2 : Basis (Fin 3) ℚ K,
      (b1 : Fin 3 → K) = ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)] ∧
      (b2 : Fin 3 → K) =
        ![(1 : K), pb.gen,
          (1 + (c : K) * pb.gen +
            (v : K) * (pb.gen ^ 2 / (n : K))) / 3] ∧
      Algebra.discr ℚ b1 = -27 * ((m * n : ℤ) : ℚ) ^ 2 ∧
      Algebra.discr ℚ b2 = -3 * ((m * n : ℤ) : ℚ) ^ 2 := by
  letI : Module.Finite ℚ K := pb.finite
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
  have hbetaCube :
      (pb.gen ^ 2 / (n : K)) ^ 3 = ((m ^ 2 * n : ℤ) : K) := by
    calc
      (pb.gen ^ 2 / (n : K)) ^ 3 = (pb.gen ^ 3) ^ 2 / (n : K) ^ 3 := by ring
      _ = ((m ^ 2 * n : ℤ) : K) := by
        rw [hroot]
        field_simp [hnK]
        push_cast
        ring
  have hAlpha : IsIntegral ℤ pb.gen := by
    apply IsIntegral.of_pow (n := 3) (by norm_num)
    rw [hroot]
    exact isIntegral_algebraMap
  have hBeta : IsIntegral ℤ (pb.gen ^ 2 / (n : K)) := by
    apply IsIntegral.of_pow (n := 3) (by norm_num)
    rw [hbetaCube]
    exact isIntegral_algebraMap
  let t : K := (c : K) * pb.gen
  have ht : t ^ 3 = 1 + 9 * (a : K) := by
    calc
      t ^ 3 = (c : K) ^ 3 * pb.gen ^ 3 := by dsimp [t]; ring
      _ = ((c ^ 3 * m * n ^ 2 : ℤ) : K) := by rw [hroot]; push_cast; ring
      _ = 1 + 9 * (a : K) := by rw [hcubic]; push_cast; ring
  have hEta : IsIntegral ℤ ((1 + t + t ^ 2) / 3) := by
    let u : K := (1 + t + t ^ 2) / 3
    let q : Polynomial ℤ := X ^ 2 + C (3 * a) * X + C (3 * a ^ 2)
    let p : Polynomial ℤ := X ^ 3 - q
    have hq : q.degree < 3 := by
      dsimp [q]
      compute_degree <;> norm_num
    have hp : p.Monic := by
      dsimp [p]
      exact monic_X_pow_sub hq
    have hfactor :
        (27 : K) * (u ^ 3 - u ^ 2 - 3 * (a : K) * u - 3 * (a : K) ^ 2) =
          (t ^ 3 - (1 + 9 * (a : K))) *
            (t ^ 3 + 3 * t ^ 2 + 3 * t + 2 + 9 * (a : K)) := by
      dsimp [u]
      field_simp
      ring
    have hu : u ^ 3 - u ^ 2 - 3 * (a : K) * u - 3 * (a : K) ^ 2 = 0 := by
      rw [ht, sub_self, zero_mul] at hfactor
      exact (mul_eq_zero.mp hfactor).resolve_left (by norm_num : (27 : K) ≠ 0)
    refine ⟨p, hp, ?_⟩
    change p.eval₂ (Int.castRingHom K) u = 0
    have heval : p.eval₂ (Int.castRingHom K) u =
        u ^ 3 - u ^ 2 - 3 * (a : K) * u - 3 * (a : K) ^ 2 := by
      simp only [p, q, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow,
        eval₂_X, eval₂_C, Int.coe_castRingHom]
      push_cast
      ring
    rw [heval]
    exact hu
  have hcvK : (c : K) ^ 2 * (n : K) = (v : K) + 3 * (k : K) := by
    exact_mod_cast hcv
  have hgammaEq :
      (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3 =
        (1 + t + t ^ 2) / 3 - (k : K) * (pb.gen ^ 2 / (n : K)) := by
    dsimp [t]
    field_simp [hnK]
    linear_combination -(pb.gen ^ 2) * hcvK
  have hGamma : IsIntegral ℤ
      ((1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3) := by
    rw [hgammaEq]
    exact hEta.sub (isIntegral_algebraMap.mul hBeta)

  have hdiscPowerGeneric (d : ℤ) (hd : pb.gen ^ 3 = (d : K)) :
      Algebra.discr ℚ pb.basis = -27 * (d : ℚ) ^ 2 := by
    have hpolyEval :
        aeval pb.gen ((X : Polynomial ℚ) ^ 3 - C (d : ℚ)) = 0 := by
      simpa using sub_eq_zero.mpr hd
    have hdegree :
        (((X : Polynomial ℚ) ^ 3 - C (d : ℚ))).degree ≤
          (minpoly ℚ pb.gen).degree := by
      rw [degree_X_pow_sub_C (by norm_num : 0 < 3),
        degree_eq_natDegree (minpoly.ne_zero pb.isIntegral_gen),
        pb.natDegree_minpoly, h3]
    have hmin : minpoly ℚ pb.gen = (X : Polynomial ℚ) ^ 3 - C (d : ℚ) :=
      (minpoly.unique_of_degree_le_degree_minpoly ℚ pb.gen
        (monic_X_pow_sub_C (d : ℚ) (by norm_num : 3 ≠ 0))
        hpolyEval hdegree).symm
    have hnorm : Algebra.norm ℚ pb.gen = (d : ℚ) := by
      rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hmin, h3]
      simp <;> norm_num
    have hderiv :
        ((X : Polynomial ℚ) ^ 3 - C (d : ℚ)).derivative = C 3 * X ^ 2 := by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow]
      norm_num
    rw [Algebra.discr_powerBasis_eq_norm, hmin, hderiv]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [Algebra.norm_algebraMap, hnorm, pb.finrank, h3]
    norm_num
  have hdiscPower : Algebra.discr ℚ pb.basis =
      -27 * (((m * n ^ 2 : ℤ) : ℚ)) ^ 2 :=
    hdiscPowerGeneric (m * n ^ 2) hroot

  let b : Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr h3)
  have hb (i : Fin 3) : b i = pb.gen ^ (i : ℕ) := by
    simp [b, Basis.reindex_apply, pb.basis_eq_pow]
  have hdiscB : Algebra.discr ℚ b = Algebra.discr ℚ pb.basis := by
    simpa [b, Basis.coe_reindex] using
      Algebra.discr_reindex ℚ pb.basis (finCongr h3)
  let P1 : Matrix (Fin 3) (Fin 3) ℚ :=
    !![1, 0, 0; 0, 1, 0; 0, 0, (n : ℚ)⁻¹]
  have hvec1 : P1.map (algebraMap ℚ K) *ᵥ b =
      ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)] := by
    funext i
    fin_cases i <;>
      simp [P1, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hb, div_eq_mul_inv] <;> ring
  have hdet1 : P1.det = (n : ℚ)⁻¹ := by
    simp [P1, Matrix.det_fin_three]
  have hdisc1 : Algebra.discr ℚ
      ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)] =
        -27 * ((m * n : ℤ) : ℚ) ^ 2 := by
    rw [← hvec1, Algebra.discr_of_matrix_mulVec, hdiscB, hdiscPower, hdet1]
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp
    push_cast
    ring
  let P2 : Matrix (Fin 3) (Fin 3) ℚ :=
    !![1, 0, 0; 0, 1, 0; 1 / 3, (c : ℚ) / 3, (v : ℚ) / (3 * (n : ℚ))]
  have hvec2 : P2.map (algebraMap ℚ K) *ᵥ b =
      ![(1 : K), pb.gen,
        (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3] := by
    funext i
    fin_cases i <;>
      simp [P2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hb, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv] <;> ring
  have hdet2 : P2.det = (v : ℚ) / (3 * (n : ℚ)) := by
    simp [P2, Matrix.det_fin_three]
  have hdisc2 : Algebra.discr ℚ
      ![(1 : K), pb.gen,
        (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3] =
        -3 * ((m * n : ℤ) : ℚ) ^ 2 := by
    rw [← hvec2, Algebra.discr_of_matrix_mulVec, hdiscB, hdiscPower, hdet2]
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hvq : (v : ℚ) ^ 2 = 1 := by
      rcases hv with hv | hv <;> rw [hv] <;> norm_num
    push_cast
    rw [div_pow, hvq]
    field_simp [hnq]
    ring

  let v1 : Fin 3 → K := ![(1 : K), pb.gen, pb.gen ^ 2 / (n : K)]
  let v2 : Fin 3 → K :=
    ![(1 : K), pb.gen,
      (1 + (c : K) * pb.gen + (v : K) * (pb.gen ^ 2 / (n : K))) / 3]
  have hmn : ((m * n : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast mul_ne_zero hm hn
  have hli1 : LinearIndependent ℚ v1 := by
    by_contra h
    have hz := Algebra.discr_zero_of_not_linearIndependent ℚ h
    rw [show Algebra.discr ℚ v1 = -27 * ((m * n : ℤ) : ℚ) ^ 2 from hdisc1] at hz
    exact (mul_ne_zero (by norm_num : (-27 : ℚ) ≠ 0) (pow_ne_zero 2 hmn)) hz
  have hli2 : LinearIndependent ℚ v2 := by
    by_contra h
    have hz := Algebra.discr_zero_of_not_linearIndependent ℚ h
    rw [show Algebra.discr ℚ v2 = -3 * ((m * n : ℤ) : ℚ) ^ 2 from hdisc2] at hz
    exact (mul_ne_zero (by norm_num : (-3 : ℚ) ≠ 0) (pow_ne_zero 2 hmn)) hz
  have hcard : Fintype.card (Fin 3) = finrank ℚ K := by
    rw [pb.finrank, h3]
    rfl
  let b1 : Basis (Fin 3) ℚ K :=
    basisOfLinearIndependentOfCardEqFinrank' v1 hli1 hcard
  let b2 : Basis (Fin 3) ℚ K :=
    basisOfLinearIndependentOfCardEqFinrank' v2 hli2 hcard
  refine ⟨hAlpha, hBeta, hGamma, b1, b2, ?_, ?_, ?_, ?_⟩
  · simpa [b1, v1] using coe_basisOfLinearIndependentOfCardEqFinrank' v1 hli1 hcard
  · simpa [b2, v2] using coe_basisOfLinearIndependentOfCardEqFinrank' v2 hli2 hcard
  · simpa [b1, v1] using hdisc1
  · simpa [b2, v2] using hdisc2

#print axioms integral_cubic_lattices

end D5.S3.Arith.Lattices.PureCubicIntegralLattices

/- GID: D5/S3/Arith/Lattices/PureCubicThreeSaturation
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicThreeSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace integrality forces three-saturation of the pure cubic suborder. -/

import D5.S3.Arith.Lattices.PureCubicSuborder
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicThreeSaturation

open Polynomial

/-- Multiplication by three does not add integral elements to the displayed cubic order. -/
theorem pure_cubic_three_saturation
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3) (a : ℤ)
    (hroot : pb.gen ^ 3 = ((1 + 9 * a : ℤ) : K))
    (z : K) (hzint : IsIntegral ℤ z)
    (h3z : ∃ u v w : ℤ,
      (3 : K) * z = (u : K) + (v : K) * pb.gen +
        (w : K) * ((1 + pb.gen + pb.gen ^ 2) / 3)) :
    ∃ u v w : ℤ,
      z = (u : K) + (v : K) * pb.gen +
        (w : K) * ((1 + pb.gen + pb.gen ^ 2) / 3) := by
  letI : Module.Finite ℚ K := pb.finite
  have hmin : minpoly ℚ pb.gen =
      (Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C ((1 + 9 * a : ℤ) : ℚ) := by
    have heval : Polynomial.aeval pb.gen
        ((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C ((1 + 9 * a : ℤ) : ℚ)) = 0 := by
      simpa using sub_eq_zero.mpr hroot
    have hdegree :
        (((Polynomial.X : Polynomial ℚ) ^ 3 -
          Polynomial.C ((1 + 9 * a : ℤ) : ℚ))).degree ≤
          (minpoly ℚ pb.gen).degree := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 3),
        Polynomial.degree_eq_natDegree (minpoly.ne_zero pb.isIntegral_gen),
        pb.natDegree_minpoly, h3]
    exact (minpoly.unique_of_degree_le_degree_minpoly ℚ pb.gen
      (Polynomial.monic_X_pow_sub_C _ (by norm_num : 3 ≠ 0))
      heval hdegree).symm
  have htraceGen : Algebra.trace ℚ K pb.gen = 0 := by
    rw [pb.trace_gen_eq_nextCoeff_minpoly, hmin]
    simp only [Polynomial.nextCoeff, Polynomial.natDegree_X_pow_sub_C]
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  have hmat : Algebra.leftMulMatrix pb.basis pb.gen =
      Matrix.of (fun i j : Fin pb.dim =>
        if (j : ℕ) + 1 = pb.dim then
          -(((Polynomial.X : Polynomial ℚ) ^ 3 -
            Polynomial.C ((1 + 9 * a : ℤ) : ℚ)).coeff (i : ℕ))
        else if (i : ℕ) = j + 1 then 1 else 0) := by
    rw [pb.leftMulMatrix, pb.minpolyGen_eq, hmin]
  have htr0 : Algebra.trace ℚ K pb.gen = 0 := htraceGen
  have htr2 : Algebra.trace ℚ K (pb.gen ^ 2) = 0 := by
    rw [Algebra.trace_eq_matrix_trace pb.basis, map_pow, hmat]
    rw [h3]
    norm_num [Matrix.trace, Matrix.diag, pow_two, Matrix.mul_apply, Matrix.of_apply,
      Fin.sum_univ_three, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_one, Polynomial.coeff_C] <;> simp
  let beta : K := (1 + pb.gen + pb.gen ^ 2) / 3
  have htraceScalar (r : ℚ) : Algebra.trace ℚ K (algebraMap ℚ K r) = 3 * r := by
    rw [Algebra.trace_algebraMap_of_basis pb.basis]
    simp [Fintype.card_fin, h3]
  have htraceMul (r : ℚ) (x : K) :
      Algebra.trace ℚ K ((algebraMap ℚ K r) * x) =
        r * Algebra.trace ℚ K x := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htraceIntMul (r : ℤ) (x : K) :
      Algebra.trace ℚ K ((r : K) * x) =
        (r : ℚ) * Algebra.trace ℚ K x := by
    simpa using htraceMul (r : ℚ) x
  have htraceIntScalar (r : ℤ) :
      Algebra.trace ℚ K (r : K) = 3 * (r : ℚ) := by
    simpa using htraceScalar (r : ℚ)
  have htraceBeta : Algebra.trace ℚ K beta = 1 := by
    have hbeq : (3 : ℚ) • beta = 1 + pb.gen + pb.gen ^ 2 := by
      dsimp [beta]
      rw [Algebra.smul_def]
      field_simp
      simp only [map_ofNat]
      ring
    have ht := congrArg (Algebra.trace ℚ K) hbeq
    simp only [map_smul, map_add] at ht
    have htr1 : Algebra.trace ℚ K (1 : K) = 3 := by
      simpa using htraceScalar 1
    rw [htr1, htr0, htr2] at ht
    norm_num at ht
    exact ht
  have htraceInt (x : K) (hx : IsIntegral ℤ x) :
      ∃ t : ℤ, (t : ℚ) = Algebra.trace ℚ K x := by
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hx)
  obtain ⟨u, v, w, h3z⟩ := h3z
  have htrace3z :
      3 * Algebra.trace ℚ K z = 3 * (u : ℚ) + (w : ℚ) := by
    have ht := congrArg (Algebra.trace ℚ K) h3z
    simp only [map_add] at ht
    change Algebra.trace ℚ K ((3 : K) * z) =
      Algebra.trace ℚ K (u : K) +
        Algebra.trace ℚ K ((v : K) * pb.gen) +
        Algebra.trace ℚ K ((w : K) * beta) at ht
    have htraceThree : Algebra.trace ℚ K ((3 : K) * z) =
        3 * Algebra.trace ℚ K z := by simpa using htraceMul 3 z
    rw [htraceThree, htraceIntScalar u,
      htraceIntMul v pb.gen, htraceIntMul w beta, htr0, htraceBeta] at ht
    norm_num at ht
    exact ht
  obtain ⟨t, ht⟩ := htraceInt z hzint
  have hw : (3 : ℤ) ∣ w := by
    have h : 3 * t = 3 * u + w := by
      have hq : ((3 * t : ℤ) : ℚ) = ((3 * u + w : ℤ) : ℚ) := by
        exact_mod_cast ht.symm ▸ htrace3z
      exact_mod_cast hq
    omega
  obtain ⟨k, hk⟩ := hw
  let z1 : K := z - (k : K) * beta
  have hbetaInt : IsIntegral ℤ beta := by
    obtain ⟨_, _, _, A, hA, hAint, _⟩ :=
      D5.S3.Arith.Lattices.PureCubicSuborder.pure_cubic_suborder pb h3 a hroot
    apply hAint
    apply (hA beta).mpr
    refine ⟨0, 0, 1, ?_⟩
    simp [beta]
  have hz1int : IsIntegral ℤ z1 := by
    exact hzint.sub ((isIntegral_algebraMap : IsIntegral ℤ (k : K)).mul hbetaInt)
  have h3z1 : (3 : K) * z1 = (u : K) + (v : K) * pb.gen := by
    dsimp [z1]
    calc
      (3 : K) * (z - (k : K) * beta) =
          (3 : K) * z - (3 : K) * ((k : K) * beta) := by ring
      _ = (u : K) + (v : K) * pb.gen := by
        rw [h3z, hk]
        change (u : K) + (v : K) * pb.gen + ((3 * k : ℤ) : K) * beta -
          (3 : K) * ((k : K) * beta) = (u : K) + (v : K) * pb.gen
        push_cast
        ring
  have h9z1 : (9 : K) * z1 ^ 2 =
      ((u : K) + (v : K) * pb.gen) ^ 2 := by
    calc
      (9 : K) * z1 ^ 2 = ((3 : K) * z1) ^ 2 := by ring
      _ = _ := congrArg (fun x : K => x ^ 2) h3z1
  have hsqexpand : ((u : K) + (v : K) * pb.gen) ^ 2 =
      ((u ^ 2 : ℤ) : K) + ((2 * u * v : ℤ) : K) * pb.gen +
        ((v ^ 2 : ℤ) : K) * pb.gen ^ 2 := by
    push_cast
    ring
  have htrace9 : 9 * Algebra.trace ℚ K (z1 ^ 2) =
      3 * (u : ℚ) ^ 2 := by
    have ht := congrArg (Algebra.trace ℚ K) h9z1
    rw [hsqexpand] at ht
    simp only [map_add] at ht
    have hleft : Algebra.trace ℚ K ((9 : K) * z1 ^ 2) =
        9 * Algebra.trace ℚ K (z1 ^ 2) := by simpa using htraceMul 9 (z1 ^ 2)
    rw [hleft, htraceIntScalar (u ^ 2), htraceIntMul (2 * u * v) pb.gen,
      htraceIntMul (v ^ 2) (pb.gen ^ 2), htr0, htr2] at ht
    norm_num at ht
    simpa [Int.cast_pow] using ht
  obtain ⟨t1, ht1⟩ := htraceInt (z1 ^ 2) (hz1int.pow 2)
  have hu : (3 : ℤ) ∣ u := by
    have hq : ((9 * t1 : ℤ) : ℚ) = ((3 * u ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast ht1.symm ▸ htrace9
    have hi : 9 * t1 = 3 * u ^ 2 := by exact_mod_cast hq
    have hsqdiv : (3 : ℤ) ∣ u ^ 2 := by
      refine ⟨t1, ?_⟩
      omega
    exact (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hsqdiv
  obtain ⟨l, hl⟩ := hu
  let z2 : K := z1 - (l : K)
  have hz2int : IsIntegral ℤ z2 := by
    exact hz1int.sub (isIntegral_algebraMap : IsIntegral ℤ (l : K))
  have h3z2 : (3 : K) * z2 = (v : K) * pb.gen := by
    dsimp [z2]
    calc
      (3 : K) * (z1 - (l : K)) = (3 : K) * z1 - (3 : K) * (l : K) := by ring
      _ = (v : K) * pb.gen := by
        rw [h3z1, hl]
        push_cast
        ring
  have h27z2 : (27 : K) * z2 ^ 3 =
      ((v ^ 3 * (1 + 9 * a) : ℤ) : K) := by
    calc
      (27 : K) * z2 ^ 3 = ((3 : K) * z2) ^ 3 := by ring
      _ = ((v : K) * pb.gen) ^ 3 := congrArg (fun x : K => x ^ 3) h3z2
      _ = ((v ^ 3 * (1 + 9 * a) : ℤ) : K) := by
        rw [mul_pow, hroot]
        push_cast
        ring
  have htrace27 : 27 * Algebra.trace ℚ K (z2 ^ 3) =
      3 * (((v ^ 3 * (1 + 9 * a) : ℤ) : ℚ)) := by
    have ht := congrArg (Algebra.trace ℚ K) h27z2
    have hleft : Algebra.trace ℚ K ((27 : K) * z2 ^ 3) =
        27 * Algebra.trace ℚ K (z2 ^ 3) := by simpa using htraceMul 27 (z2 ^ 3)
    rw [hleft, htraceIntScalar] at ht
    exact ht
  obtain ⟨t2, ht2⟩ := htraceInt (z2 ^ 3) (hz2int.pow 3)
  have hv : (3 : ℤ) ∣ v := by
    have hq : ((27 * t2 : ℤ) : ℚ) =
        ((3 * (v ^ 3 * (1 + 9 * a)) : ℤ) : ℚ) := by
      exact_mod_cast ht2.symm ▸ htrace27
    have hi : 27 * t2 = 3 * (v ^ 3 * (1 + 9 * a)) := by
      exact_mod_cast hq
    have hprod : (3 : ℤ) ∣ v ^ 3 * (1 + 9 * a) := by
      refine ⟨3 * t2, ?_⟩
      omega
    have hnotB : ¬(3 : ℤ) ∣ 1 + 9 * a := by
      intro h
      obtain ⟨r, hr⟩ := h
      omega
    have hp : Prime (3 : ℤ) := by norm_num
    exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hprod).resolve_right hnotB)
  obtain ⟨m, hm⟩ := hv
  refine ⟨l, m, k, ?_⟩
  have hleft : (3 : K) * z =
      (3 : K) * ((l : K) + (m : K) * pb.gen + (k : K) * beta) := by
    rw [h3z, hl, hm, hk]
    change ((3 * l : ℤ) : K) + ((3 * m : ℤ) : K) * pb.gen +
      ((3 * k : ℤ) : K) * beta =
      (3 : K) * ((l : K) + (m : K) * pb.gen + (k : K) * beta)
    push_cast
    ring
  exact (mul_left_cancel₀ (by norm_num : (3 : K) ≠ 0) hleft)

#print axioms pure_cubic_three_saturation

end D5.S3.Arith.Lattices.PureCubicThreeSaturation

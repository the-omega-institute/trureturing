/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicCoefficientIdentity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicCoefficientIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial class membership, residue cancellation and signed sewing combine to prove the original all-index coefficient recurrences, with no correspondence certificate as an input.. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicFinitePrincipalParts
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicUnsewnCurrent
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicFiniteClass
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicResidues
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicSewingBridge
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Intervals

/-!
UNCOMPILED LEAN SOURCE PROPOSAL. No elaboration, kernel, native or official
acceptance is claimed. All six imported cubic suppliers are themselves
uncompiled proposals; their immutable source hashes are in result.json.
The finite-class supplier's degree proof at lines 316-317 passes a maximum
bound where degree_mul_le requires a sum bound, detailed in result.json.
Its unchanged source is an upstream integration blocker.

The private argument below is finite binomial inversion, followed by actual
zero-residue reconstruction. It is applied separately to the literal TT and
UT coefficients. No sewing, residue, finite-class or recurrence certificate
is an input of the public theorem. The external root equation is retained in
the exact original statement, although the algebra uses only b != 0.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicResidues

private abbrev inversionRoot : PowerSeries ℂ :=
  PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)

private lemma inversion_root_half : inversionRoot * halfSeries = 1 := by
  have hhalf : halfSeries = PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) := by
    ext j
    simp only [halfSeries, PowerSeries.coeff_mk,
      PowerSeries.binomialSeries_coeff, halfBinomial_choose]
  rw [hhalf, inversionRoot, ← PowerSeries.binomialSeries_add,
    show (1 / 2 : ℂ) + -1 / 2 = 0 by norm_num,
    PowerSeries.binomialSeries_zero]

/- Multiplication by one monomial makes the truncation length N-j.
This coefficient proof includes coefficients at and above N. -/
private lemma inversion_trunc_monomial (N j : ℕ) (hj : j < N)
    (c : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.trunc N (PowerSeries.monomial j c * f) =
      Polynomial.monomial j c * PowerSeries.trunc (N - j) f := by
  ext m
  rw [PowerSeries.coeff_trunc, PowerSeries.monomial_eq_C_mul_X_pow,
    mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hjm : j ≤ m
  · simp only [if_pos hjm, PowerSeries.coeff_trunc]
    by_cases hm : m < N
    · rw [if_pos hm, if_pos (by omega : m - j < N - j)]
    · rw [if_neg hm, if_neg (by omega : ¬m - j < N - j), mul_zero]
  · simp only [if_neg hjm, mul_zero, ite_self]

/- Equation (59): y_j is the actual coefficient of H*P. Each finite current
numerator is exactly sum_{k <= N-1-j} choose(1/2,k) X^k, by its definition
as a truncation. No principal-part or reconstruction premise is used. -/
private lemma finite_binomial_inversion (N : ℕ) (p : Polynomial ℂ)
    (hp : p.degree < N) :
    p = ∑ j ∈ Finset.range N,
      Polynomial.monomial j (PowerSeries.coeff j
        (halfSeries * (p : PowerSeries ℂ))) *
          finiteCurrentNumerator (N - 1 - j) := by
  classical
  have htrunc : PowerSeries.trunc N (p : PowerSeries ℂ) = p := by
    ext m
    rw [PowerSeries.coeff_trunc, Polynomial.coeff_coe]
    by_cases hm : m < N
    · rw [if_pos hm]
    · rw [if_neg hm]
      exact ((Polynomial.degree_lt_iff_coeff_zero p N).mp hp m
        (le_of_not_gt hm)).symm
  have hinverse : PowerSeries.trunc N
      (inversionRoot * (halfSeries * (p : PowerSeries ℂ))) = p := by
    rw [← mul_assoc, inversion_root_half, one_mul, htrunc]
  calc
    p = PowerSeries.trunc N
        (inversionRoot * (halfSeries * (p : PowerSeries ℂ))) := hinverse.symm
    _ = PowerSeries.trunc N (inversionRoot *
        (PowerSeries.trunc N (halfSeries * (p : PowerSeries ℂ)) :
          PowerSeries ℂ)) := (PowerSeries.trunc_mul_trunc _ _).symm
    _ = ∑ j ∈ Finset.range N, PowerSeries.trunc N
        (PowerSeries.monomial j (PowerSeries.coeff j
          (halfSeries * (p : PowerSeries ℂ))) * inversionRoot) := by
      rw [PowerSeries.trunc_apply N (halfSeries * (p : PowerSeries ℂ)),
        Finset.Nat.Ico_zero_eq_range]
      change PowerSeries.trunc N (inversionRoot *
        Polynomial.coeToPowerSeries.ringHom (∑ j ∈ Finset.range N,
          Polynomial.monomial j (PowerSeries.coeff j
            (halfSeries * (p : PowerSeries ℂ))))) = _
      rw [map_sum, Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_monomial]
      rw [mul_comm]
    _ = ∑ j ∈ Finset.range N,
        Polynomial.monomial j (PowerSeries.coeff j
          (halfSeries * (p : PowerSeries ℂ))) *
            finiteCurrentNumerator (N - 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      rw [inversion_trunc_monomial N j hjN]
      have hlength : N - j = (N - 1 - j) + 1 := by omega
      rw [hlength]

/- Equation (60). The only generic hypotheses are a finite polynomial
representation and its actual Laurent residue. Both are discharged from
the literal kernels at each of the two calls in the final theorem. -/
private lemma finite_binomial_reconstruction (N : ℕ) (hN : 1 ≤ N)
    (p : Polynomial ℂ) (hp : p.degree < N) (K : LaurentSeries ℂ)
    (hK : K = HahnSeries.single (-(N : ℤ)) (1 : ℂ) *
      (halfSeries : LaurentSeries ℂ) * (p : LaurentSeries ℂ))
    (hres : K.coeff (-1) = 0) :
    K = ∑ t ∈ Finset.Icc 1 (N - 1),
      HahnSeries.C (K.coeff (-(t : ℤ) - 1) / (t : ℂ)) *
        finiteCurrentLaurent t := by
  classical
  let ι : Polynomial ℂ →+* LaurentSeries ℂ :=
    (HahnSeries.ofPowerSeries ℤ ℂ).comp Polynomial.coeToPowerSeries.ringHom
  let y : ℕ → ℂ := fun j =>
    PowerSeries.coeff j (halfSeries * (p : PowerSeries ℂ))
  have hcast (q : Polynomial ℂ) : (q : LaurentSeries ℂ) = ι q := by
    first
    | rfl
    | simpa only [ι, RingHom.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply] using (RatFunc.coe_coe q).symm
  have hKι : K = HahnSeries.single (-(N : ℤ)) (1 : ℂ) *
      (halfSeries : LaurentSeries ℂ) * ι p := by
    simpa only [hcast p] using hK
  have hKseries : K = HahnSeries.single (-(N : ℤ)) (1 : ℂ) *
      ((halfSeries * (p : PowerSeries ℂ) : PowerSeries ℂ) :
        LaurentSeries ℂ) := by
    rw [PowerSeries.coe_mul]
    exact hKι.trans (mul_assoc _ _ _)
  have hcoeff (j : ℕ) : K.coeff ((j : ℤ) - N) = y j := by
    rw [hKseries, HahnSeries.coeff_single_mul, one_mul,
      show ((j : ℤ) - N) - (-(N : ℤ)) = (j : ℤ) by omega,
      LaurentSeries.coeff_coe_powerSeries]
  have hyzero : y (N - 1) = 0 := by
    rw [← hcoeff, show ((N - 1 : ℕ) : ℤ) - N = -1 by omega, hres]
  have hmono (j : ℕ) (c : ℂ) :
      ι (Polynomial.monomial j c) = HahnSeries.single (j : ℤ) c := by
    change (HahnSeries.ofPowerSeries ℤ ℂ)
      (Polynomial.monomial j c : PowerSeries ℂ) = _
    rw [Polynomial.coe_monomial, PowerSeries.monomial_eq_C_mul_X_pow,
      map_mul, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
    simp [HahnSeries.C_apply, HahnSeries.single_mul_single]
  have hinv : p = ∑ j ∈ Finset.range N,
      Polynomial.monomial j (y j) * finiteCurrentNumerator (N - 1 - j) :=
    finite_binomial_inversion N p hp
  have hP : ι p = ∑ j ∈ Finset.range N,
      ι (Polynomial.monomial j (y j)) * ι (finiteCurrentNumerator (N - 1 - j)) := by
    rw [hinv, map_sum]
    simp only [map_mul]
  let F : ℕ → LaurentSeries ℂ := fun j =>
    HahnSeries.single (-(N : ℤ)) (1 : ℂ) * (halfSeries : LaurentSeries ℂ) *
      ι (Polynomial.monomial j (y j)) * ι (finiteCurrentNumerator (N - 1 - j))
  have hsum : K = ∑ j ∈ Finset.range N, F j := by
    rw [hKι, hP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [F]
    ring
  have hlast : F (N - 1) = 0 := by
    simp [F, hyzero]
  have hshort : K = ∑ j ∈ Finset.range (N - 1), F j := by
    rw [hsum, show Finset.range N = Finset.range ((N - 1) + 1) by
      congr 1 <;> omega, Finset.sum_range_succ, hlast, add_zero]
  conv_lhs => rw [hshort]
  refine Finset.sum_bij (fun j _ => N - 1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    have hjN : j < N - 1 := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj k hk heq
    have hjN : j < N - 1 := Finset.mem_range.mp hj
    have hkN : k < N - 1 := Finset.mem_range.mp hk
    omega
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, htN⟩
    refine ⟨N - 1 - t, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    have hjN : j < N - 1 := Finset.mem_range.mp hj
    let t := N - 1 - j
    have ht : 0 < t := by dsimp only [t]; omega
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    have hexp : -(N : ℤ) + (j : ℤ) = -(t : ℤ) - 1 := by
      dsimp only [t]
      omega
    have hc : K.coeff (-(t : ℤ) - 1) = y j := by
      have he : (j : ℤ) - N = -(t : ℤ) - 1 := by
        dsimp only [t]
        omega
      simpa only [he] using hcoeff j
    change F j = HahnSeries.C (K.coeff (-(t : ℤ) - 1) / (t : ℂ)) *
      finiteCurrentLaurent t
    rw [hc]
    calc
      F j = (HahnSeries.single (-(N : ℤ)) (1 : ℂ) *
          ι (Polynomial.monomial j (y j))) *
          (ι (finiteCurrentNumerator t) * (halfSeries : LaurentSeries ℂ)) := by
        dsimp only [F, t]
        ring
      _ = HahnSeries.single (-(t : ℤ) - 1) (y j) *
          (ι (finiteCurrentNumerator t) * (halfSeries : LaurentSeries ℂ)) := by
        rw [hmono, HahnSeries.single_mul_single, hexp, one_mul]
      _ = HahnSeries.single (-(t : ℤ) - 1) (y j) *
          (((finiteCurrentNumerator t : PowerSeries ℂ) * halfSeries :
            PowerSeries ℂ) : LaurentSeries ℂ) := by
        rw [PowerSeries.coe_mul]
      _ = HahnSeries.C (y j / (t : ℂ)) * finiteCurrentLaurent t := by
        rw [finiteCurrentLaurent, HahnSeries.C_apply, ← mul_assoc,
          HahnSeries.single_mul_single, zero_add, div_mul_cancel₀ _ ht0]

/- Extract the whole regular tail, with the original order pairScalar s t.
This is the same finite inversion, not a second uniqueness assumption. -/
private lemma reconstructed_regular_coefficient (N : ℕ) (hN : 1 ≤ N)
    (p : Polynomial ℂ) (hp : p.degree < N) (K : LaurentSeries ℂ)
    (hK : K = HahnSeries.single (-(N : ℤ)) (1 : ℂ) *
      (halfSeries : LaurentSeries ℂ) * (p : LaurentSeries ℂ))
    (hres : K.coeff (-1) = 0) (s : ℕ) (hs : 0 < s) :
    K.coeff ((s : ℤ) - 1) = ∑ t ∈ Finset.Icc 1 (N - 1),
      pairScalar s t / (t : ℂ) * K.coeff (-(t : ℤ) - 1) := by
  conv_lhs => rw [finite_binomial_reconstruction N hN p hp K hK hres]
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
    finite_current_regular_coeff t s hs]
  have hpair : pairScalar t s = pairScalar s t := by
    unfold pairScalar
    rw [add_comm (t : ℂ) (s : ℂ)]
    ring
  rw [hpair]
  ring

/-- Both exact signed original TT/UT recurrences, at every natural degree
and positive mode, on the original literal cubic kernels and current row.
SOURCE ONLY: the proof and all six suppliers remain UNCOMPILED. -/
theorem cubic_original_coefficient_identity : CubicOriginalCoefficientIdentity := by
  intro b hb hb0 _hroot s d hs
  by_cases hsd : s ≤ d
  · constructor
    · rw [if_pos hsd]
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = s + n := ⟨d - s, by omega⟩
      simp only [Nat.add_sub_cancel_left]
      rw [cubic_tt_signed_sewing b hb hb0 s hs n]
      by_cases hn : n = 0
      · subst n
        simp [cubic_ut_degree_zero]
      · obtain ⟨p, hp, hK⟩ := cubicUT_finite_class b hb hb0 n (by omega)
        have hK' : PowerSeries.coeff n (cubicUTSeries b hb) =
            HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (1 : ℂ) *
              (halfSeries : LaurentSeries ℂ) * (p : LaurentSeries ℂ) := by
          simpa only [Nat.cast_add, Nat.cast_one, neg_add] using hK
        have hregular := reconstructed_regular_coefficient (n + 1) (by omega)
          p hp (PowerSeries.coeff n (cubicUTSeries b hb)) hK'
          (cubicUT_residue_zero b hb hb0 n) s hs
        simp only [Nat.add_sub_cancel] at hregular
        rw [hregular]
    · rw [if_pos hsd]
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = s + n := ⟨d - s, by omega⟩
      simp only [Nat.add_sub_cancel_left]
      rw [cubic_ut_signed_sewing b hb hb0 s hs n]
      by_cases hn : n = 0
      · subst n
        simp [cubic_tt_degree_zero_currentRow b hb hb0 s hs]
      · have hne : s + n ≠ s := by omega
        rw [if_neg hne]
        simp only [neg_zero, zero_sub]
        obtain ⟨p, hp, hK⟩ := cubicTT_finite_class b hb hb0 n (by omega)
        have hregular := reconstructed_regular_coefficient n (by omega)
          p hp (PowerSeries.coeff n (cubicTTSeries b hb)) hK
          (cubicTT_residue_zero b hb hb0 n) s hs
        rw [hregular]
        congr 1
        have hext := Finset.sum_Icc_succ_top (a := 1) (b := n - 1)
          (by omega : 1 ≤ (n - 1) + 1)
          (fun t => pairScalar s t / (t : ℂ) *
            negativeCoefficient (cubicTTSeries b hb) t n)
        rw [show n - 1 + 1 = n by omega,
          cubic_tt_pole_bound b hb hb0 n n (le_refl n), mul_zero, add_zero] at hext
        exact hext.symm
  · simp only [if_neg hsd]
    exact ⟨cubic_tt_pole_bound b hb hb0 s d (by omega),
      cubic_ut_pole_bound b hb hb0 s d (by omega)⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

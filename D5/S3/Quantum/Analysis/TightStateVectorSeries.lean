/- GID: D5/S3/Quantum/Analysis/TightStateVectorSeries
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TightStateVectorSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-rank tightness of a positive normalized functional gives one countable vector family representing every bounded operator. -/
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic

open Filter Topology InnerProductSpace
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Analysis.TightStateVectorSeries

theorem positive_functional_vector_series_of_finite_rank_tightness
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)
    (hφone : φ 1 = 1)
    (E : ℕ → (H →L[ℂ] H))
    (hE : ∀ j, IsStarProjection (E j))
    (hEfinite : ∀ j, FiniteDimensional ℂ (E j).range)
    (htight :
      Tendsto (fun j => (φ (1 - E j)).re)
        atTop (𝓝 0)) :
    ∃ u : ℕ → H,
      HasSum (fun k => ‖u k‖ ^ 2) 1 ∧
      ∀ S : H →L[ℂ] H,
        HasSum
          (fun k => inner ℂ (u k) (S (u k)))
          (φ S) := by
  classical
  let Op := H →L[ℂ] H

  -- These estimates apply to every positive normalized functional.
  -- The pre-GNS multiplication estimate is used only on the left.
  have hbasic
      (f : Op →ₚ[ℂ] ℂ)
      (hfone : f 1 = 1) :
      (∀ A : Op, ‖f A‖ ≤ ‖A‖) ∧
      (∀ P S : Op,
        IsStarProjection P →
        ‖f S - f (P * S * P)‖ ≤
          2 * ‖S‖ * Real.sqrt (f (1 - P)).re) := by
    let q : Op → ℝ := fun A => ‖f.toPreGNS A‖

    have hqnonneg (A : Op) : 0 ≤ q A :=
      norm_nonneg _

    have hqone : q (1 : Op) = 1 := by
      change Real.sqrt (f (star (1 : Op) * 1)).re = 1
      simp [hfone]

    have hleft (A B : Op) :
        q (A * B) ≤ ‖A‖ * q B := by
      have hL : ‖f.leftMulMapPreGNS A‖ ≤ ‖A‖ := by
        unfold PositiveLinearMap.leftMulMapPreGNS
        exact LinearMap.mkContinuous_norm_le _
          (norm_nonneg A) _
      change
        ‖(f.leftMulMapPreGNS A) (f.toPreGNS B)‖ ≤
          ‖A‖ * ‖f.toPreGNS B‖
      exact
        ((f.leftMulMapPreGNS A).le_opNorm
          (f.toPreGNS B)).trans
          (mul_le_mul_of_nonneg_right hL
            (norm_nonneg _))

    have hqbound (A : Op) : q A ≤ ‖A‖ := by
      simpa only [mul_one, hqone] using
        hleft A (1 : Op)

    have hCS (A B : Op) :
        ‖f (star A * B)‖ ≤ q A * q B := by
      simpa only
        [PositiveLinearMap.preGNS_inner_def,
         PositiveLinearMap.ofPreGNS_toPreGNS]
        using
          (norm_inner_le_norm
            (𝕜 := ℂ) (f.toPreGNS A) (f.toPreGNS B))

    have hqprojection
        (P : Op) (hP : IsStarProjection P) :
        q P = Real.sqrt (f P).re := by
      change Real.sqrt (f (star P * P)).re =
        Real.sqrt (f P).re
      rw [hP.isSelfAdjoint.star_eq,
        hP.isIdempotentElem.eq]

    have hprojection
        (P : Op) (hP : IsStarProjection P) :
        q P ≤ 1 :=
      (hqbound P).trans (IsStarProjection.norm_le P hP)

    constructor
    · intro A
      calc
        ‖f A‖ ≤ q (1 : Op) * q A := by
          simpa only [star_one, one_mul] using
            hCS (1 : Op) A
        _ = q A := by rw [hqone, one_mul]
        _ ≤ ‖A‖ := hqbound A
    · intro P S hP
      let a : Op := 1 - P
      have ha : IsStarProjection a := hP.one_sub

      have hsplit :
          S - P * S * P = a * S + P * S * a := by
        dsimp only [a]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel

      have hfirst :
          ‖f (a * S)‖ ≤ ‖S‖ * q a := by
        calc
          _ ≤ q a * q S := by
            simpa only [ha.isSelfAdjoint.star_eq]
              using hCS a S
          _ ≤ q a * ‖S‖ :=
            mul_le_mul_of_nonneg_left
              (hqbound S) (hqnonneg a)
          _ = ‖S‖ * q a := mul_comm _ _

      have hSP : q (star S * P) ≤ ‖S‖ := by
        calc
          _ ≤ ‖star S‖ * q P := hleft (star S) P
          _ ≤ ‖star S‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (hprojection P hP) (norm_nonneg _)
          _ = ‖S‖ := by
            simpa only [mul_one] using (norm_star S)

      have hsecond :
          ‖f (P * S * a)‖ ≤ ‖S‖ * q a := by
        calc
          _ ≤ q (star S * P) * q a := by
            have hstarP : star P = P := hP.isSelfAdjoint.star_eq
            simpa only [star_mul, star_star, hstarP]
              using hCS (star S * P) a
          _ ≤ ‖S‖ * q a :=
            mul_le_mul_of_nonneg_right hSP (hqnonneg a)

      calc
        ‖f S - f (P * S * P)‖ =
            ‖f (a * S) + f (P * S * a)‖ := by
          rw [← map_sub, hsplit, map_add]
        _ ≤ ‖f (a * S)‖ + ‖f (P * S * a)‖ :=
          norm_add_le _ _
        _ ≤ ‖S‖ * q a + ‖S‖ * q a :=
          add_le_add hfirst hsecond
        _ = 2 * ‖S‖ * q (1 - P) := by
          dsimp only [a]
          ring
        _ = 2 * ‖S‖ *
            Real.sqrt (f (1 - P)).re := by
          rw [hqprojection (1 - P) hP.one_sub]

  have hφbound : ∀ A : Op, ‖φ.toLinearMap A‖ ≤ ‖A‖ := by
    intro A
    simpa only [PositiveLinearMap.coe_toLinearMap] using (hbasic φ hφone).1 A

  -- B v u = φ(rankOne u v).
  -- Riesz gives <ρ v,u> = B v u.
  let φL : Op →L[ℂ] ℂ :=
    φ.toLinearMap.mkContinuous 1
      (fun A => by
        simpa only [one_mul] using hφbound A)

  let B : H →L⋆[ℂ] H →L[ℂ] ℂ :=
    (ContinuousLinearMap.compL ℂ H Op ℂ φL).comp
      (rankOne ℂ).flip

  let ρ : Op := continuousLinearMapOfBilin B

  have hρleft (v u : H) :
      inner ℂ (ρ v) u = φ (rankOne ℂ u v) := by
    change
      inner ℂ (continuousLinearMapOfBilin B v) u =
        B v u
    exact continuousLinearMapOfBilin_apply B v u

  have hρright (u v : H) :
      inner ℂ u (ρ v) = φ (rankOne ℂ v u) := by
    calc
      inner ℂ u (ρ v) =
          star (inner ℂ (ρ v) u) := by
        simpa only [Complex.star_def] using
          (inner_conj_symm (𝕜 := ℂ) u (ρ v)).symm
      _ = star (φ (rankOne ℂ u v)) := by
        rw [hρleft]
      _ = φ (rankOne ℂ v u) := by
        rw [← map_star φ,
          ContinuousLinearMap.star_eq_adjoint,
          adjoint_rankOne]

  have hρpositive : ρ.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff_complex ρ).2
    intro x
    rw [hρleft]
    have hx : 0 ≤ φ (rankOne ℂ x x) :=
      φ.map_nonneg
        ((ContinuousLinearMap.nonneg_iff_isPositive
          (rankOne ℂ x x)).2
          (isPositive_rankOne_self x))
    exact
      ⟨Complex.conj_eq_iff_re.mp hx.star_eq,
       (Complex.nonneg_iff.mp hx).1⟩

  have hρ : 0 ≤ ρ :=
    (ContinuousLinearMap.nonneg_iff_isPositive ρ).2
      hρpositive

  let T : Op := CFC.sqrt ρ

  have hTnonneg : 0 ≤ T := CFC.sqrt_nonneg ρ

  have hTsym : T.toLinearMap.IsSymmetric :=
    hTnonneg.isSelfAdjoint.isSymmetric

  have hTsquare (x : H) : T (T x) = ρ x := by
    have h := congrArg (fun A : Op => A x)
      (CFC.sqrt_mul_sqrt_self ρ hρ)
    simpa only [T, ContinuousLinearMap.mul_apply] using h

  have hdiagonal (x : H) :
      ‖T x‖ ^ 2 = (φ (rankOne ℂ x x)).re := by
    calc
      ‖T x‖ ^ 2 =
          (inner ℂ (T x) (T x)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (T x)).symm
      _ = (inner ℂ x (T (T x))).re :=
        congrArg Complex.re (hTsym x (T x))
      _ = (inner ℂ x (ρ x)).re := by
        rw [hTsquare]
      _ = (φ (rankOne ℂ x x)).re := by
        rw [hρright]

  -- An arbitrary Hilbert basis is sufficient. Countability of the
  -- nonzero constructed vectors will follow from summability.
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let v : w → H := fun i => T (b i)

  have hfiniteProjection (s : Finset w) :
      IsStarProjection
        (∑ i ∈ s, rankOne ℂ (b i) (b i)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (IsStarProjection.zero Op : IsStarProjection (0 : Op))
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        apply
          (isStarProjection_rankOne_self
            (b.orthonormal.norm_eq_one a)).add ih
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hai : a ≠ i := by
          intro h
          exact ha (h ▸ hi)
        simp only
          [ContinuousLinearMap.mul_def,
           rankOne_comp_rankOne,
           b.orthonormal.inner_eq_zero hai,
           zero_smul]

  have hfiniteMass (s : Finset w) :
      ∑ i ∈ s, ‖v i‖ ^ 2 ≤ 1 := by
    let P : Op := ∑ i ∈ s, rankOne ℂ (b i) (b i)
    have hP : IsStarProjection P := hfiniteProjection s

    have hsum :
        ∑ i ∈ s, ‖v i‖ ^ 2 = (φ P).re := by
      dsimp only [P, v]
      simp only [map_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hdiagonal (b i)

    rw [hsum]
    have hn :=
      (Complex.nonneg_iff.mp
        (φ.map_nonneg hP.one_sub.nonneg)).1
    simpa only
      [map_sub, hφone, Complex.sub_re,
       Complex.one_re, sub_nonneg]
      using hn

  have hmassSummable :
      Summable (fun i : w => ‖v i‖ ^ 2) :=
    summable_of_sum_le
      (fun i => sq_nonneg ‖v i‖) hfiniteMass

  let m : ℝ := ∑' i : w, ‖v i‖ ^ 2

  have hmUpper : m ≤ 1 :=
    Real.tsum_le_of_sum_le
      (fun i => sq_nonneg ‖v i‖) hfiniteMass

  have htermBound (S : Op) (i : w) :
      ‖inner ℂ (v i) (S (v i))‖ ≤
        ‖S‖ * ‖v i‖ ^ 2 := by
    calc
      _ ≤ ‖v i‖ * ‖S (v i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖v i‖ * (‖S‖ * ‖v i‖) :=
        mul_le_mul_of_nonneg_left
          (S.le_opNorm (v i)) (norm_nonneg _)
      _ = ‖S‖ * ‖v i‖ ^ 2 := by ring

  have hseries (S : Op) :
      Summable (fun i : w =>
        inner ℂ (v i) (S (v i))) :=
    (hmassSummable.mul_left ‖S‖).of_norm_bounded
      (htermBound S)

  -- Construct the vector-sum functional before proving its mass is one.
  let ψL : Op →ₗ[ℂ] ℂ :=
    { toFun := fun S =>
        ∑' i : w, inner ℂ (v i) (S (v i))
      map_add' := fun A C => by
        simpa only
          [ContinuousLinearMap.add_apply, inner_add_right]
          using (hseries A).tsum_add (hseries C)
      map_smul' := fun c A => by
        simpa only [ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply]
          using (hseries A).tsum_const_smul c }

  have hψnonneg (S : Op) (hS : 0 ≤ S) :
      0 ≤ ψL S := by
    have hpositive : S.IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive S).1 hS
    have hterm (i : w) :
        0 ≤ inner ℂ (v i) (S (v i)) :=
      hpositive.inner_nonneg_right (v i)
    apply Complex.nonneg_iff.mpr
    constructor
    · change
        0 ≤ Complex.reCLM
          (∑' i : w, inner ℂ (v i) (S (v i)))
      rw [Complex.reCLM.map_tsum (hseries S)]
      exact tsum_nonneg
        (fun i => (Complex.nonneg_iff.mp (hterm i)).1)
    · change
        0 = Complex.imCLM
          (∑' i : w, inner ℂ (v i) (S (v i)))
      rw [Complex.imCLM.map_tsum (hseries S)]
      have him (i : w) :
          (inner ℂ (v i) (S (v i))).im = 0 :=
        (Complex.nonneg_iff.mp (hterm i)).2.symm
      have hzfun :
          (fun i : w => Complex.imCLM (inner ℂ (v i) (S (v i)))) =
            (fun _ : w => 0) := by
        funext i
        simpa only [Complex.imCLM_apply] using him i
      rw [hzfun, tsum_zero]

  let ψ : Op →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ψL hψnonneg

  have hψoneMass : ψ 1 = (m : ℂ) := by
    change
      (∑' i : w, inner ℂ (v i) (v i)) = (m : ℂ)
    calc
      _ = ∑' i : w, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
        apply tsum_congr
        intro i
        rw [inner_self_eq_norm_sq_to_K]
        norm_num
      _ = (m : ℂ) :=
        by
          dsimp only [m]
          exact (Complex.ofReal_tsum (fun i : w => ‖v i‖ ^ 2)).symm

  -- Parseval fixes the rank-one orientation:
  -- ψ(rankOne x y) = <T y,T x> = <y,ρ x>.
  have hψrankOne (x y : H) :
      ψ (rankOne ℂ x y) = φ (rankOne ℂ x y) := by
    have hterm (i : w) :
        inner ℂ (v i) (rankOne ℂ x y (v i)) =
          inner ℂ (T y) (b i) *
            inner ℂ (b i) (T x) := by
      dsimp only [v]
      rw [inner_right_rankOne_apply]
      have hx := hTsym.apply_clm (b i) x
      have hy := hTsym.apply_clm y (b i)
      rw [hx, ← hy]
      ring

    have hsum :
        HasSum
          (fun i : w =>
            inner ℂ (v i) (rankOne ℂ x y (v i)))
          (inner ℂ (T y) (T x)) :=
      (b.hasSum_inner_mul_inner (T y) (T x)).congr_fun
        hterm

    change
      (∑' i : w,
        inner ℂ (v i) (rankOne ℂ x y (v i))) =
        φ (rankOne ℂ x y)
    calc
      _ = inner ℂ (T y) (T x) := hsum.tsum_eq
      _ = inner ℂ y (T (T x)) := hTsym y (T x)
      _ = inner ℂ y (ρ x) := by rw [hTsquare]
      _ = φ (rankOne ℂ x y) := hρright y x

  -- Expand the actual finite-dimensional range of P.
  -- This includes range dimension zero.
  have hfiniteCompression
      (P : Op)
      (hP : IsStarProjection P)
      (hfinite : FiniteDimensional ℂ P.range)
      (S : Op) :
      ψ (P * S * P) = φ (P * S * P) := by
    let R : Submodule ℂ H := P.range
    letI : FiniteDimensional ℂ R := hfinite

    have hsym :
        P.toLinearMap.IsSymmetricProjection := by
      have hid : IsIdempotentElem P.toLinearMap := by
        change P.toLinearMap * P.toLinearMap = P.toLinearMap
        ext x
        exact congrArg (fun A : Op => A x) hP.isIdempotentElem
      exact ⟨hid, hP.isSelfAdjoint.isSymmetric⟩

    obtain ⟨hR, hPeq⟩ :=
      (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range
        (p := P.toLinearMap)).mp hsym

    letI : R.HasOrthogonalProjection := hR
    let e := stdOrthonormalBasis ℂ R

    have hPstar : P = R.starProjection := by
      ext x
      exact congrArg
        (fun A : H →ₗ[ℂ] H => A x) hPeq

    have hPsum :
        P =
          ∑ i : Fin (Module.finrank ℂ R),
            rankOne ℂ (e i : H) (e i : H) :=
      hPstar.trans e.starProjection_eq_sum_rankOne

    have hcompressed :
        P * S * P =
          ∑ i : Fin (Module.finrank ℂ R),
            rankOne ℂ
              (P (S (e i : H))) (e i : H) := by
      calc
        P * S * P =
            P * S *
              (∑ i : Fin (Module.finrank ℂ R),
                rankOne ℂ (e i : H) (e i : H)) :=
          congrArg (fun A : Op => P * S * A) hPsum
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ext x
          simp [ContinuousLinearMap.mul_def, rankOne_apply]

    rw [hcompressed, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hψrankOne _ _

  have hψE (j : ℕ) : ψ (E j) = φ (E j) := by
    simpa only [mul_one, (hE j).isIdempotentElem.eq]
      using hfiniteCompression
        (E j) (hE j) (hEfinite j) (1 : Op)

  -- Tightness supplies the missing lower bound on total mass.
  have hφE :
      Tendsto (fun j => (φ (E j)).re)
        atTop (𝓝 1) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (𝓝 1)).sub htight
    simpa only
      [map_sub, hφone, Complex.sub_re,
       Complex.one_re, sub_sub_cancel, sub_zero]
      using h

  have hmLower (j : ℕ) : (φ (E j)).re ≤ m := by
    have hn :=
      (Complex.nonneg_iff.mp
        (ψ.map_nonneg (hE j).one_sub.nonneg)).1
    simpa only
      [map_sub, hψoneMass, Complex.sub_re,
       Complex.ofReal_re, hψE j, sub_nonneg]
      using hn

  have hmEq : m = 1 :=
    le_antisymm hmUpper (le_of_tendsto' hφE hmLower)

  have hmass : HasSum (fun i : w => ‖v i‖ ^ 2) 1 := by
    rw [← hmEq]
    exact hmassSummable.hasSum

  have hψone : ψ 1 = 1 := by
    rw [hψoneMass, hmEq, Complex.ofReal_one]

  have htail (j : ℕ) :
      ψ (1 - E j) = φ (1 - E j) := by
    rw [map_sub, map_sub, hψone, hφone, hψE j]

  -- Both compression errors tend to zero under the original φ.
  have hagree (S : Op) : ψ S = φ S := by
    have hbound (j : ℕ) :
        ‖φ S - ψ S‖ ≤
          4 * ‖S‖ * Real.sqrt (φ (1 - E j)).re := by
      let C : Op := E j * S * E j
      have hC : ψ C = φ C :=
        hfiniteCompression
          (E j) (hE j) (hEfinite j) S

      have hφ :=
        (hbasic φ hφone).2 (E j) S (hE j)
      have hψ :=
        (hbasic ψ hψone).2 (E j) S (hE j)
      rw [htail j] at hψ

      calc
        ‖φ S - ψ S‖ ≤
            ‖φ S - φ C‖ + ‖φ C - ψ S‖ := by
          rw [← sub_add_sub_cancel (φ S) (φ C) (ψ S)]
          exact norm_add_le _ _
        _ = ‖φ S - φ C‖ + ‖ψ C - ψ S‖ := by
          rw [← hC]
        _ = ‖φ S - φ C‖ + ‖ψ S - ψ C‖ := by
          rw [norm_sub_rev (ψ C) (ψ S)]
        _ ≤
            2 * ‖S‖ * Real.sqrt (φ (1 - E j)).re +
            2 * ‖S‖ * Real.sqrt (φ (1 - E j)).re :=
          add_le_add hφ hψ
        _ = 4 * ‖S‖ *
            Real.sqrt (φ (1 - E j)).re := by ring

    have hlimit :
        Tendsto
          (fun j =>
            4 * ‖S‖ * Real.sqrt (φ (1 - E j)).re)
          atTop (𝓝 0) := by
      have hsqrt :=
        Real.continuous_sqrt.continuousAt.tendsto.comp htight
      simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => 4 * ‖S‖)
            atTop (𝓝 (4 * ‖S‖))).mul hsqrt

    have hzero :
        Tendsto (fun _ : ℕ => ‖φ S - ψ S‖)
          atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) hbound hlimit

    have hn : ‖φ S - ψ S‖ = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hzero

    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

  have hfull (S : Op) :
      HasSum
        (fun i : w => inner ℂ (v i) (S (v i)))
        (φ S) := by
    rw [← hagree S]
    exact (hseries S).hasSum

  -- Restrict to the countable support and extend by zero.
  -- No equivalence between the whole basis and ℕ is assumed.
  let a : Set w := Function.support v

  have haCountable : a.Countable := by
    have heq :
        Function.support (fun i : w => ‖v i‖ ^ 2) = a := by
      ext i
      simp [a, Function.mem_support]
    rw [← heq]
    exact hmassSummable.countable_support

  letI : Countable a := haCountable.to_subtype
  letI : Encodable a := Encodable.ofCountable a

  let f : a → ℕ := Encodable.encode
  have hf : Function.Injective f := Encodable.encode_injective

  let u : ℕ → H :=
    Function.extend f (fun i : a => v i.1) 0

  have hindex
      {K : Type}
      [AddCommMonoid K]
      [TopologicalSpace K]
      (F : H → K)
      (hF : F 0 = 0)
      (z : K)
      (hs : HasSum (fun i : w => F (v i)) z) :
      HasSum (fun k : ℕ => F (u k)) z := by
    have hsupport :
        Function.support (fun i : w => F (v i)) ⊆ a := by
      intro i hi
      change v i ≠ 0
      intro hv
      apply (Function.mem_support.mp hi)
      rw [hv, hF]

    have hrestrict :
        HasSum (fun i : a => F (v i.1)) z :=
      (hasSum_subtype_iff_of_support_subset hsupport).2 hs

    have hext :
        HasSum
          (Function.extend f (fun i : a => F (v i.1)) 0)
          z :=
      (hasSum_extend_zero hf).2 hrestrict

    apply hext.congr_fun
    intro k
    by_cases hk : ∃ i : a, f i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [u, hf.extend_apply]
    · have hu : u k = 0 :=
        Function.extend_apply' _ _ _ hk
      have he :
          Function.extend f
            (fun i : a => F (v i.1)) 0 k = 0 :=
        Function.extend_apply' _ _ _ hk
      rw [hu, he, hF]

  refine ⟨u, ?_, ?_⟩
  · exact hindex (fun x : H => ‖x‖ ^ 2)
      (show ‖(0 : H)‖ ^ 2 = (0 : ℝ) by norm_num [norm_zero])
      (1 : ℝ) hmass
  · intro S
    exact hindex (fun x : H => inner ℂ x (S x))
      (show inner ℂ (0 : H) (S 0) = (0 : ℂ) by simp) (φ S) (hfull S)

end D5.S3.Quantum.Analysis.TightStateVectorSeries

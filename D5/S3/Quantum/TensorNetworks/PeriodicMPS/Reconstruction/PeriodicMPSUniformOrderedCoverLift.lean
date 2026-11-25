/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Every surviving common native cofactor divisor lifts to a height-one prime with zero root contraction. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbient
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformOrderedCoverNative
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformOrderedCoverLift

open MvPolynomial
open PeriodicMPSUniformSpecialDivisorExclusion
  (Variable AmbientPolynomials ambientGuard spectralCoefficients nativeSliceSubstitution)
open PeriodicMPSUniformSpecialSpectralBases
  (quartic transferPolynomial eval_discriminant)
open PeriodicMPSUniformSpectralRadicalAlgebra
open PeriodicMPSUniformVerticalAmbient
open PeriodicMPSUniformVerticalPrimeExclusion (Roots rootSum)
open PeriodicMPSUniformGuardZeroDimension (NativePolynomials nativeSliceEquiv nativeSliceEquiv_apply)
open PeriodicMPSUniformGuardedCriticalDimension
  (nativeCofactor dimH_guarded_criticalCoordinates_le)
open PeriodicMPSUniformGraphRecovery (criticalCoordinates)
open SevenSitePhysicalRankBridge (align)
open SevenSitePhysicalRankAssembly (alignedSlice asOrdinary)
open PeriodicMPSUniformMovingFrame (half imaginary)

open private spectralA spectralB spectralC normalizedA normalizedB normalizedC
  sumUnit sumUnit_val orderedChart_isDomain from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbient
open private quartic_natDegree from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialSpectralBases
open private nativeCartesian from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients

noncomputable section

/-- Coefficients of the four ordered simple roots of the literal trace-one quartic. -/
theorem exists_ordered_roots (a b c : ℂ) (hc : c ≠ 0) (hs : (quartic a b c).Separable) :
    ∃ z : Fin 4 → ℂ, Function.Injective z ∧ (∀ i, z i ≠ 0) ∧
      (∑ i, z i) = 1 ∧ elementaryA (z 0) (z 1) (z 2) (z 3) = a ∧
      elementaryB (z 0) (z 1) (z 2) (z 3) = b ∧
      elementaryC (z 0) (z 1) (z 2) (z 3) = c := by
  classical
  let P := quartic a b c
  have hmonic : P.Monic := by
    change (quartic a b c).leadingCoeff = 1
    rw [Polynomial.leadingCoeff, quartic_natDegree]
    norm_num [quartic, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  have hsplit : P.Splits := IsAlgClosed.splits _
  let roots := P.roots.toFinset
  have hnodup : P.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : roots.card = 4 := by
    dsimp [roots]
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots]
    exact quartic_natDegree _ _ _
  let e := (roots.equivFinOfCardEq hcard).symm
  let z : Fin 4 → ℂ := fun i => (e i : ℂ)
  have hinj : Function.Injective z := fun _ _ h => e.injective (Subtype.ext h)
  have hnz (i : Fin 4) : z i ≠ 0 := by
    have hm : z i ∈ P.roots := Multiset.mem_toFinset.mp (e i).property
    intro hz
    rw [hz, Polynomial.mem_roots hmonic.ne_zero] at hm
    exact hc (by simpa [Polynomial.IsRoot, P, quartic] using hm)
  have hprod : P = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
    rw [hsplit.eq_prod_roots_of_monic hmonic]
    rw [Fintype.prod_equiv e _ (fun t => Polynomial.X - Polynomial.C (t : ℂ)) (fun _ => rfl),
      Finset.prod_coe_sort roots (fun t : ℂ => Polynomial.X - Polynomial.C t)]
    simp only [Finset.prod, roots, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hexp : (∏ i, (Polynomial.X - Polynomial.C (z i))) =
      Polynomial.X ^ 4 - Polynomial.C (∑ i, z i) * Polynomial.X ^ 3 +
      Polynomial.C (elementaryA (z 0) (z 1) (z 2) (z 3)) * Polynomial.X ^ 2 -
      Polynomial.C (elementaryB (z 0) (z 1) (z 2) (z 3)) * Polynomial.X +
      Polynomial.C (elementaryC (z 0) (z 1) (z 2) (z 3)) := by
    simp only [Fin.prod_univ_four, Fin.sum_univ_four, elementaryA, elementaryB,
      elementaryC, map_add, map_mul]
    ring
  have h := hprod.trans hexp
  rw [Fin.sum_univ_four] at h
  refine ⟨z, hinj, hnz, ?_, ?_, ?_, ?_⟩
  · rw [Fin.sum_univ_four]
    have h3 := congrArg (fun p : Polynomial ℂ => p.coeff 3) h
    simp only [P, quartic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] at h3
    norm_num at h3
    linear_combination h3
  · have h2 := congrArg (fun p : Polynomial ℂ => p.coeff 2) h
    simp only [P, quartic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] at h2
    norm_num at h2
    simpa using h2.symm
  · have h1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    simp only [P, quartic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] at h1
    norm_num at h1
    simpa using h1.symm
  · have h0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
    simp only [P, quartic, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C] at h0
    norm_num at h0
    simpa using h0.symm

private def orderedVariables : Variable → OrderedChart
  | none => algebraMap (ParameterRing SpectralBase) OrderedChart ↑(parameterK (R := SpectralBase))
  | some .d => (radicalPoint orderedParameters).toCoordinates.d
  | some .db => (radicalPoint orderedParameters).toCoordinates.db
  | some .e => (radicalPoint orderedParameters).toCoordinates.e
  | some .eb => (radicalPoint orderedParameters).toCoordinates.eb

/-- The map from the independent determinant coordinates to the ordered chart. -/
def ambientToOrdered : AmbientPolynomials →ₐ[ℂ] OrderedChart := aeval orderedVariables

private theorem eval_spectralGuard {z : Fin 4 → ℂ}
    (hz : Function.Injective z) (hnz : ∀ i, z i ≠ 0) (hs : (∑ i, z i) = 1)
    (hgap : elementaryC (z 0) (z 1) (z 2) (z 3) -
      elementaryB (z 0) (z 1) (z 2) (z 3) ^ 2 ≠ 0) :
    eval z spectralGuard ≠ 0 := by
  have hdiff (i j : Fin 4) (h : i ≠ j) : z i - z j ≠ 0 := sub_ne_zero.mpr (hz.ne h)
  have hs' : eval z rootSum = 1 := by simpa [rootSum] using hs
  have hg : eval z spectralGap ≠ 0 := by
    simpa [spectralGap, spectralB, spectralC, hs', elementaryB, elementaryC] using hgap
  simp only [spectralGuard, map_mul, map_prod, eval_X, hs', one_mul]
  refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hnz i) ?_) hg
  simp only [simpleRoots, map_mul, map_sub, eval_X, mul_ne_zero_iff]
  exact ⟨⟨⟨⟨⟨hdiff 0 1 (by decide), hdiff 0 2 (by decide)⟩, hdiff 0 3 (by decide)⟩,
    hdiff 1 2 (by decide)⟩, hdiff 1 3 (by decide)⟩, hdiff 2 3 (by decide)⟩

/-- Every complex point on the guard open lifts through the actual determinant equations. -/
theorem exists_ordered_point (x : Variable → ℂ) (hg : eval x coverGuard ≠ 0) :
    ∃ F : OrderedChart →ₐ[ℂ] ℂ, F.comp ambientToOrdered = aeval x := by
  rw [eval_coverGuard] at hg
  simp only [mul_ne_zero_iff] at hg
  obtain ⟨⟨⟨⟨hU, hk⟩, hgap⟩, hc⟩, hdisc⟩ := hg
  rw [eval_discriminant] at hdisc
  let a := spectralCoefficients x 0
  let b := spectralCoefficients x 1
  let c := spectralCoefficients x 2
  have hsep : (quartic a b c).Separable := by
    by_contra h
    exact hdisc (Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (fun hz => by
        change quartic a b c = 0 at hz
        have hd := quartic_natDegree a b c
        rw [hz, Polynomial.natDegree_zero] at hd
        omega), h⟩)
  obtain ⟨z, hzinj, hroots, hsum, ha, hb, hconst⟩ := exists_ordered_roots a b c hc hsep
  let g : SpectralBase →+* ℂ := IsLocalization.Away.lift spectralGuard (g := eval z)
    (isUnit_iff_ne_zero.mpr (eval_spectralGuard hzinj hroots hsum (by rwa [hb, hconst])))
  have hg (p : Roots) : g (spectralClass p) = eval z p := IsLocalization.Away.lift_eq _ _ _
  have h1 : g (↑sumUnit : SpectralBase) = 1 := by
    rw [sumUnit_val, hg]
    simpa [rootSum] using hsum
  have hinv : g (↑sumUnit⁻¹ : SpectralBase) = 1 := by
    have h := map_mul g (↑sumUnit : SpectralBase) (↑sumUnit⁻¹ : SpectralBase)
    rw [Units.mul_inv, map_one, h1, one_mul] at h
    exact h.symm
  have hA : g normalizedA = a := by
    simpa [normalizedA, hg, hinv, spectralA, elementaryA] using ha
  have hB : g normalizedB = b := by
    simpa [normalizedB, hg, hinv, spectralB, elementaryB] using hb
  have hC : g normalizedC = c := by
    simpa [normalizedC, hg, hinv, spectralC, elementaryC] using hconst
  let U := Units.mk0 _ (mul_ne_zero hU.1 hU.2)
  let k := Units.mk0 _ hk
  let base := parameterEval g U k
  let : Algebra (ParameterRing SpectralBase) ℂ := base.toAlgebra
  have hbaseA : base orderedParameters.a = a := (parameterEval_constant _ _ _ _).trans hA
  have hbaseB : base orderedParameters.b = b := (parameterEval_constant _ _ _ _).trans hB
  have hbaseC : base orderedParameters.c = c := (parameterEval_constant _ _ _ _).trans hC
  have hbaseU : base ↑orderedParameters.U = U := parameterEval_U _ _ _
  have hbaseK : base ↑orderedParameters.k = k := parameterEval_k _ _ _
  let q : CoordinateFiber (orderedParameters.map (algebraMap (ParameterRing SpectralBase) ℂ)) :=
    { d := x (some .d)
      db := x (some .db)
      e := x (some .e)
      eb := x (some .eb)
      prod_eq := by change _ = base ↑orderedParameters.U; rw [hbaseU]; rfl
      coeff_a := by
        change _ - 2 * (base ↑orderedParameters.U + _) - (base ↑orderedParameters.k) ^ 2 =
          base orderedParameters.a
        rw [hbaseU, hbaseK, hbaseA]
        rfl
      coeff_b := by
        change base ↑orderedParameters.U - _ = base orderedParameters.b
        rw [hbaseU, hbaseB]
        rfl
      coeff_c := by
        change (base orderedParameters.b) ^ 2 +
          (base ↑orderedParameters.k) ^ 2 * _ * _ = base orderedParameters.c
        rw [hbaseB, hbaseK, hbaseC]
        rfl }
  let F := radicalLift q.toRadical
  have hF : (radicalPoint orderedParameters).toCoordinates.postcompose F = q := by
    rw [← RadicalFiber.toCoordinates_postcompose, radicalPoint_postcompose_lift,
      CoordinateFiber.toRadical_toCoordinates]
  let L : OrderedChart →ₐ[ℂ] ℂ :=
    { F.toRingHom with
      commutes' := fun r => by
        change F (rootToChart (C r)) = r
        change F (algebraMap (ParameterRing SpectralBase) OrderedChart
          (parameterConstant (spectralClass (C r)))) = r
        rw [AlgHom.commutes]
        change base (parameterConstant (spectralClass (C r))) = r
        simp [base, hg] }
  refine ⟨L, ?_⟩
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, ambientToOrdered, aeval_X]
  change F (orderedVariables i) = x i
  rcases i with _ | i
  · change F (algebraMap (ParameterRing SpectralBase) OrderedChart
      ↑(parameterK (R := SpectralBase))) = _
    rw [AlgHom.commutes]
    exact hbaseK
  · cases i
    · exact congrArg CoordinateFiber.d hF
    · exact congrArg CoordinateFiber.db hF
    · exact congrArg CoordinateFiber.e hF
    · exact congrArg CoordinateFiber.eb hF

/-- The guard-open point lifts detect every nonzero ambient polynomial. -/
theorem ambientToOrdered_injective : Function.Injective ambientToOrdered := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm _ bot_le
  intro p hp
  have hz : ambientToOrdered p = 0 := hp
  have hp' : p * coverGuard = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases h : eval x coverGuard = 0
    · rw [h, mul_zero]
    · obtain ⟨F, hF⟩ := exists_ordered_point x h
      have hx : eval x p = 0 := by
        rw [← MvPolynomial.aeval_eq_eval, ← hF, AlgHom.comp_apply, hz, map_zero]
      rw [hx, zero_mul]
  exact Ideal.mem_bot.mpr ((mul_eq_zero.mp hp').resolve_right coverGuard_ne_zero)

private theorem exists_zero_avoiding {r g : AmbientPolynomials} (hr : Irreducible r)
    (hg : ¬ r ∣ g) : ∃ x : Variable → ℂ, eval x r = 0 ∧ eval x g ≠ 0 := by
  classical
  let : Fintype Determinant := Fintype.ofList [.d, .db, .e, .eb] (by
    intro i
    cases i <;> simp)
  let I : Ideal AmbientPolynomials := Ideal.span {r}
  let : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hr.prime
  have hn : g ∉ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    rwa [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus, Ideal.mem_span_singleton]
  rw [mem_vanishingIdeal_iff] at hn
  push Not at hn
  obtain ⟨x, hx, hne⟩ := hn
  exact ⟨x, hx r (Ideal.subset_span (Set.mem_singleton r)), hne⟩

/-- A divisor meeting the guard open maps to a nonunit in the ordered chart. -/
theorem ambientToOrdered_not_isUnit {r : AmbientPolynomials} (hr : Irreducible r)
    (hg : ¬ r ∣ coverGuard) : ¬ IsUnit (ambientToOrdered r) := by
  obtain ⟨x, hx, hguard⟩ := exists_zero_avoiding hr hg
  obtain ⟨F, hF⟩ := exists_ordered_point x hguard
  intro h
  have he : F (ambientToOrdered r) = 0 :=
    (DFunLike.congr_fun hF r).trans hx
  exact not_isUnit_zero (he ▸ h.map F.toRingHom)

private theorem spectralGuard_ne_zero : spectralGuard ≠ 0 := by
  have hx : ∃ x : Variable → ℂ, eval x coverGuard ≠ 0 := by
    by_contra! h
    apply coverGuard_ne_zero
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    exact h x
  obtain ⟨x, hx⟩ := hx
  obtain ⟨F, _⟩ := exists_ordered_point x hx
  have hu : IsUnit (rootToChart spectralGuard) :=
    (IsLocalization.Away.algebraMap_isUnit (S := SpectralBase) spectralGuard).map
      ((algebraMap (ParameterRing SpectralBase) OrderedChart).comp parameterConstant)
  intro h
  have hz : rootToChart spectralGuard = 0 := (congrArg rootToChart h).trans (map_zero _)
  exact not_isUnit_zero ((congrArg F hz |>.trans (map_zero F)) ▸ hu.map F.toRingHom)

private theorem orderedChart_isNoetherianRing : IsNoetherianRing OrderedChart := by
  let : IsNoetherianRing SpectralBase :=
    IsLocalization.isNoetherianRing (Submonoid.powers spectralGuard) SpectralBase inferInstance
  let : IsNoetherianRing (ParameterRing SpectralBase) :=
    IsLocalization.isNoetherianRing (Submonoid.powers (parameterGuard SpectralBase))
      (ParameterRing SpectralBase) inferInstance
  infer_instance

private theorem comap_radical_span_ordered {r : AmbientPolynomials} (hr : Irreducible r)
    (hg : ¬ r ∣ coverGuard) :
    (Ideal.span {ambientToOrdered r}).radical.comap ambientToOrdered.toRingHom =
      Ideal.span {r} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.le_radical
    (Ideal.subset_span (Set.mem_singleton _))))
  intro p hp
  rw [Ideal.mem_span_singleton]
  by_contra h
  have hg' : ¬ r ∣ coverGuard * p := fun hmul => (hr.prime.dvd_mul.mp hmul).elim hg h
  obtain ⟨x, hrx, hx⟩ := exists_zero_avoiding hr hg'
  rw [map_mul, mul_ne_zero_iff] at hx
  obtain ⟨F, hF⟩ := exists_ordered_point x hx.1
  have hle : Ideal.span {ambientToOrdered r} ≤ RingHom.ker F.toRingHom :=
    (Ideal.span_singleton_le_iff_mem _).mpr ((DFunLike.congr_fun hF r).trans hrx)
  have hprime : (RingHom.ker F.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hp' : ambientToOrdered p ∈ (Ideal.span {ambientToOrdered r}).radical := hp
  exact hx.2 ((DFunLike.congr_fun hF p).symm.trans
    (RingHom.mem_ker.mp (hprime.radical_le_iff.mpr hle hp')))

/-- A height-one ambient divisor meeting the guard open has a height-one prime above it. -/
theorem exists_ordered_heightOne_over {r : AmbientPolynomials} (hr : Irreducible r)
    (hg : ¬ r ∣ coverGuard) :
    ∃ P : Ideal OrderedChart, P.IsPrime ∧ P.height = 1 ∧
      P.comap ambientToOrdered.toRingHom = Ideal.span {r} := by
  let : IsDomain OrderedChart := orderedChart_isDomain spectralGuard_ne_zero
  let : IsNoetherianRing OrderedChart := orderedChart_isNoetherianRing
  let I : Ideal OrderedChart := Ideal.span {ambientToOrdered r}
  let J : Ideal AmbientPolynomials := Ideal.span {r}
  have hJ : J.IsPrime := Ideal.isPrime_span_singleton_of_prime hr.prime
  have hcomap : (I.comap ambientToOrdered.toRingHom).radical = J := by
    rw [← Ideal.comap_radical]
    exact comap_radical_span_ordered hr hg
  have hmin : J ∈ (I.comap ambientToOrdered.toRingHom).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hcomap]
    exact ⟨⟨hJ, le_rfl⟩, fun _ hQ hQJ => hQ.2⟩
  obtain ⟨P, hP, hcontract⟩ := Ideal.exists_minimalPrimes_comap_eq
    ambientToOrdered.toRingHom J hmin
  have hn : ambientToOrdered r ≠ 0 := fun h =>
    hr.ne_zero (ambientToOrdered_injective (h.trans (map_zero _).symm))
  have hi : I.height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hn) (ambientToOrdered_not_isUnit hr hg)
  refine ⟨P, hP.isPrime, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I P hP) ?_, hcontract⟩
  rw [← hi]
  exact Ideal.height_mono hP.le

/-- Cartesian substitution followed by the ambient map is evaluation on the ordered slice. -/
theorem ambientToOrdered_native :
    ambientToOrdered.toRingHom.comp nativeSliceSubstitution = (aeval orderedSlice).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [nativeSliceSubstitution]
  · intro i
    fin_cases i <;>
      simp [ambientToOrdered, nativeSliceSubstitution, nativeCartesian, orderedSlice, cartesian,
        orderedVariables, half, imaginary]

/-- The native cofactors lift to a height-one prime with the exact ambient contraction. -/
theorem exists_ordered_heightOne_of_nativeCofactors (m : ℕ) {r : NativePolynomials}
    (hr : Irreducible r) (hguard : ¬ r ∣ nativeCoverGuard)
    (hcof : ∀ i : Fin 10, r ∣ nativeCofactor m i) :
    ∃ P : Ideal OrderedChart, P.IsPrime ∧ P.height = 1 ∧
      P.comap (aeval orderedSlice).toRingHom = Ideal.span {r} ∧
      ∀ i : Fin 10, orderedCofactor m i ∈ P := by
  have hir : Irreducible (nativeSliceEquiv r) := hr.map nativeSliceEquiv
  have hg : ¬ nativeSliceEquiv r ∣ coverGuard := by
    intro h
    apply hguard
    exact (map_dvd_iff nativeSliceEquiv).mp (by simpa only [nativeCoverGuard, RingEquiv.apply_symm_apply] using h)
  obtain ⟨P, hP, hp, hcontract⟩ := exists_ordered_heightOne_over hir hg
  have hc : P.comap (aeval orderedSlice).toRingHom = Ideal.span {r} := by
    rw [← ambientToOrdered_native, ← Ideal.comap_comap, hcontract]
    ext x
    change nativeSliceEquiv x ∈ Ideal.span {nativeSliceEquiv r} ↔ _
    simp only [Ideal.mem_span_singleton]
    exact map_dvd_iff nativeSliceEquiv
  refine ⟨P, hP, hp, hc, fun i => ?_⟩
  change nativeCofactor m i ∈ P.comap (aeval orderedSlice).toRingHom
  rw [hc, Ideal.mem_span_singleton]
  exact hcof i

/-- The simple nonzero spectral cover already captures every native height-one
cofactor divisor that survives localization at the basic guard. -/
theorem exists_ordered_heightOne_of_basicGuard {m : ℕ} (hm : 5 ≤ m)
    {r : NativePolynomials} (hr : Irreducible r)
    (hbasic : ¬ nativeSliceEquiv r ∣ ambientGuard)
    (hcof : ∀ i : Fin 10, r ∣ nativeCofactor m i) :
    ∃ P : Ideal OrderedChart, P.IsPrime ∧ P.height = 1 ∧
      P.comap (aeval orderedSlice).toRingHom = Ideal.span {r} ∧
      ∀ i : Fin 10, orderedCofactor m i ∈ P := by
  apply exists_ordered_heightOne_of_nativeCofactors m hr _ hcof
  intro h
  have he : nativeSliceEquiv r ∣ coverGuard := by
    simpa [nativeCoverGuard] using map_dvd nativeSliceEquiv h
  have hp := (hr.map nativeSliceEquiv).prime
  rcases hp.dvd_mul.mp he with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact hbasic h
    · exact native_commonDivisor_avoids_special hm hr hbasic hcof .zeroRoot h
  · exact native_commonDivisor_avoids_special hm hr hbasic hcof .repeatedRoot h

/-- The checked vertical theorem forces the lifted height-one cofactor prime
to have zero contraction to the homogeneous root ring. -/
theorem exists_horizontal_heightOne_of_basicGuard {m : ℕ} (hm : 5 ≤ m)
    {r : NativePolynomials} (hr : Irreducible r)
    (hbasic : ¬ nativeSliceEquiv r ∣ ambientGuard)
    (hcof : ∀ i : Fin 10, r ∣ nativeCofactor m i) :
    ∃ P : Ideal OrderedChart, P.IsPrime ∧ P.height = 1 ∧
      P.comap (aeval orderedSlice).toRingHom = Ideal.span {r} ∧
      P.comap rootToChart = ⊥ ∧ ∀ i : Fin 10, orderedCofactor m i ∈ P := by
  obtain ⟨P, hP, hheight, hcontract, hcof⟩ :=
    exists_ordered_heightOne_of_basicGuard hm hr hbasic hcof
  let := hP
  refine ⟨P, hP, hheight, hcontract, ?_, hcof⟩
  by_contra hv
  exact no_vertical_prime (by omega) P hheight hv hcof

/-- This is the horizontal input needed by the native codimension criterion. -/
theorem native_commonDivisor_dvd_basicGuard_of_no_horizontal {m : ℕ} (hm : 5 ≤ m)
    (horiz : ∀ P : Ideal OrderedChart, P.IsPrime → P.height = 1 →
      P.comap rootToChart = ⊥ → (∀ i : Fin 10, orderedCofactor m i ∈ P) → False)
    {r : NativePolynomials} (hr : Irreducible r)
    (hcof : ∀ i : Fin 10, r ∣ nativeCofactor m i) :
    r ∣ nativeSliceEquiv.symm ambientGuard := by
  by_contra h
  have hbasic : ¬ nativeSliceEquiv r ∣ ambientGuard := by
    intro hd
    exact h ((map_dvd_iff nativeSliceEquiv).mp (by simpa only [RingEquiv.apply_symm_apply] using hd))
  obtain ⟨P, hp, hh, _, hroot, hm'⟩ := exists_horizontal_heightOne_of_basicGuard hm hr hbasic hcof
  exact horiz P hp hh hroot hm'

/-- The inherited horizontal criterion yields the six-dimensional bound on
the native basic guard open. -/
theorem dimH_guarded_criticalCoordinates_le_of_no_horizontal {m : ℕ} (hm : 5 ≤ m)
    (horiz : ∀ P : Ideal OrderedChart, P.IsPrime → P.height = 1 →
      P.comap rootToChart = ⊥ → (∀ i : Fin 10, orderedCofactor m i ∈ P) → False) :
    dimH {u ∈ criticalCoordinates m | (align (asOrdinary u)).2.2.2 ≠ 0 ∧
      eval (fun i => (alignedSlice (asOrdinary u) i : ℂ))
        (nativeSliceEquiv.symm ambientGuard) ≠ 0} ≤ 6 :=
  dimH_guarded_criticalCoordinates_le m (nativeCofactorIdeal_ne_bot hm)
    (fun _ hr hcof => native_commonDivisor_dvd_basicGuard_of_no_horizontal hm horiz hr hcof)

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformOrderedCoverLift

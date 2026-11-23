/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCurrentRegression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-puncture fixed-charge Wick jet in modes one and zero. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent


/-! Two independent current occurrences at the first physical puncture. -/

open Filter Complex
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCurrentRegression

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open FourPoint.OriginalFourMActualChart
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalEntry physicalMean)
open OriginalFourMChartProduct (chartTau chartPeriod)
open OriginalFourMOccupationTransport
open OriginalFourMPhysicalCovariance (jac slotCorrection physical_covariance_swap relative)
open OriginalFourMSignedOverlap (chartCovariance chosenChartSource legSign)
open OriginalFourMSpatialWick
  (spatialCoefficient spatialCoefficient_split_marks spatialCoefficient_const_mul)
open OriginalFourMInverseJets
open OriginalChargedRowSource
open NativeAffineExternalCoefficient (jetOccupation coordinateJet)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMSlitMean (coefficient_congr)
open HalfFock.OriginalHalfCurrentTransport (contractionScalar)
open private take from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialTaylor
open private mark_jet_eq_moment from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick

private theorem two_occurrence_moment {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (mu : I → ℂ) (hA : ∀ i j, A i j = A j i) (i j : I) :
    affineMoment A mu (Finsupp.single j 1 + Finsupp.single i 1) =
      mu i * mu j + A i j := by
  classical
  have hs : affineMoment A mu (Finsupp.single j 1) = mu j := by
    rw [← zero_add (Finsupp.single j 1), affineMoment_step A mu hA]
    simp [affineMoment_zero]
  rw [affineMoment_step A mu hA, hs]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [affineMoment_zero]
  · intro k _ hk
    simp [Finsupp.single_eq_of_ne hk]
  · simp

private theorem coefficient_zero (f : ℂ → ℂ) : coefficient 0 f = f 0 := by
  simp [coefficient]

private theorem coefficient_const_mul (n : ℕ) (a : ℂ) (f : ℂ → ℂ) :
    coefficient n (fun u => a * f u) = a * coefficient n f := by
  simp only [coefficient, iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem contraction_one_zero : contractionScalar 1 0 = (3 / 16 : ℂ) := by
  have h := Ring.choose_smul_choose (3 / 2 : ℂ) (n := 2) (k := 1) (by decide)
  norm_num [nsmul_eq_mul, Ring.choose_one_right] at h
  norm_num [contractionScalar, Finset.sum_range_succ, Ring.choose_zero_right]
  linear_combination h / 4

set_option backward.isDefEq.respectTransparency false in
private theorem physical_two_mark_jet (D : LatticeData) (i : Fin D.rank)
    (upperA : Bool) (x : ℝ) (q : Charge D) :
    spatialCoefficient (Sum.elim ![1, 0] (fun _ => 1))
      ([Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1] : List (Fin 2 ⊕ Fin 2))
      (physicalChargeSummand D (fun _ => .P) (fun _ => i) upperA .A x q) 0 =
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA .A x *
        (bilinear D q q : ℂ) / 2) *
      coefficient 1 (fun u =>
        physicalMean D q upperA .A x (fun _ : Fin 2 => .P) (fun _ => i) 0 u *
        physicalMean D q upperA .A x (fun _ : Fin 2 => .P) (fun _ => i) 1 0 +
        physicalEntry D upperA .A x (fun _ : Fin 2 => .P) (fun _ => i) 0 1 u 0) := by
  let l : List (Fin 2) := [0, 1]
  let mu := physicalMean D q upperA .A x (fun _ : Fin 2 => .P) (fun _ => i)
  let A := physicalEntry D upperA .A x (fun _ : Fin 2 => .P) (fun _ => i)
  let P := Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA .A x *
    (bilinear D q q : ℂ) / 2)
  let G := physicalChargeSummand D (fun _ : Fin 2 => .P) (fun _ => i) upperA .A x q
  change spatialCoefficient _ (l.map Sum.inr ++ l.map Sum.inl) G 0 = _
  rw [spatialCoefficient_split_marks _ l (by decide : l.Nodup)]
  have hf : (fun u : Fin 2 → ℂ => coordinateJet l (fun v => G (Sum.elim u v)) 0) =
      fun u => P * (mu 0 (u 0) * mu 1 (u 1) + A 0 1 (u 0) (u 1)) := by
    funext u
    let K : Matrix (Fin 2) (Fin 2) ℂ := fun a b => A a b (u a) (u b)
    let m : Fin 2 → ℂ := fun a => mu a (u a)
    have hs (a b : Fin 2) : K a b = K b a := by
      change (D.G i i : ℂ) *
        OriginalFourMPhysicalCovariance.physicalCovariance upperA .A x .P .P (u a) (u b) =
        (D.G i i : ℂ) *
        OriginalFourMPhysicalCovariance.physicalCovariance upperA .A x .P .P (u b) (u a)
      rw [physical_covariance_swap upperA .A x .P .P (u a) (u b)]
    have hm := mark_jet_eq_moment D (fun _ => .P) (fun _ => i) upperA .A x q l u
    simp only [relative, mul_one] at hm
    change coordinateJet l (fun v => G (Sum.elim u v)) 0 =
      P * affineMoment K m (jetOccupation l) at hm
    have hl : jetOccupation l =
        Finsupp.single (1 : Fin 2) 1 + Finsupp.single (0 : Fin 2) 1 := by
      simp [l, jetOccupation]
    rw [hm, hl, two_occurrence_moment K m hs]
  rw [hf, spatialCoefficient_const_mul]
  simp only [l, spatialCoefficient, take, coefficient_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rfl


open OriginalFourMSectorContinuation (slitChargeTerm slitMatrix slitLinear)
open OriginalGaussianSourceRestriction
  (fourSupport CompactExternal compactExternal externalOccupation)
open OriginalNormalRowSource (restricted)
open FactorialFockMetric (weight)
open OriginalFourMSlitMean
  (slitMean slitCovariance slitMeanEntry slitCovarianceEntry slitCovarianceEntry_eq_native)
open OriginalFourMSignedOverlap (chosen_chart_source_eq_native chart_covariance_eq_native)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open D5.S3.Analytic.OriginalSlitNome (slitNome rank24Determinant)
open OriginalGaussianExternalBlocks (External explicitEffectiveKernel externalFreeEntry)
open OriginalGaussianExternalEquations (literal_symmetry)
open LatticeTwistedGroundRealization.SignQuotient

open private leg from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSectorContinuation

private theorem slit_matrix_symm (D : LatticeData) {Y : Type*} (e : Y → External D)
    {t : ℂ} (ht : ‖t‖ < 1) (a b : Y ⊕ Y) : slitMatrix D e t a b = slitMatrix D e t b a := by
  let w := t ^ (1 / 2 : ℂ)
  have hw2 : w ^ 2 = t := by dsimp [w]; rw [← Complex.cpow_mul_nat]; norm_num
  have hw : ‖w‖ < 1 := by
    have h := congrArg norm hw2
    rw [norm_pow] at h
    nlinarith [norm_nonneg w]
  have he (a b : Y ⊕ Y) : slitMatrix D e t a b = explicitEffectiveKernel D e w a b := by
    rw [← hw2]
    cases a <;> cases b <;>
      exact slitCovarianceEntry_eq_native D e _ _ _ _ hw
  rw [he, he]
  have hfree (a b : External D) : externalFreeEntry D a b = externalFreeEntry D b a := by
    by_cases h : a.2.2 = b.2.2 <;> simp [externalFreeEntry, h, eq_comm]
  have hJ (a b : External D) :
      OriginalGaussianExternalResolvent.externalJ a.1 a.2.2 b.1 b.2.2 w =
        OriginalGaussianExternalResolvent.externalJ b.1 b.2.2 a.1 a.2.2 w :=
    literal_symmetry false a.1 b.1 a.2.2 b.2.2 hw
  let M (a b : Y) := gramComplex D (e a).2.1 (e b).2.1 *
    (externalFreeEntry D (e a) (e b) +
      OriginalGaussianExternalResolvent.externalJ (e a).1 (e a).2.2 (e b).1 (e b).2.2 w)
  have hM (a b : Y) : M a b = M b a := by
    dsimp only [M]
    rw [hfree (e a) (e b), hJ (e a) (e b)]
    simp only [gramComplex, Matrix.map_apply, D.symmetric (e a).2.1 (e b).2.1]
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hM a b
    | inr b => rfl
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b => exact hM a b

private def nativeMean (D : LatticeData) (i : Fin D.rank) (q : Charge D) (t u : ℂ) : ℂ :=
  -(bilinear D (unitCharge D i) q : ℂ) * slitMean false u t / slitPeriod t

private def nativePair (D : LatticeData) (i : Fin D.rank) (q : Charge D) (t u : ℂ) : ℂ :=
  nativeMean D i q t u * nativeMean D i q t 0 +
    (D.G i i : ℂ) * slitCovariance false false false false u 0 t

set_option backward.isDefEq.respectTransparency false in
private theorem coefficient_native_pair (D : LatticeData) (i : Fin D.rank) (q : Charge D)
    {t : ℂ} (ht : ‖t‖ < 1) (m : ℕ) :
    rank24Determinant t * slitNome t ^ (chargeEnergy D q).toNat *
      coefficient m (nativePair D i q t) =
    (if m = 0 then 2 else 1) *
      slitChargeTerm D (Finsupp.single (i,m) 1 + Finsupp.single (i,0) 1) 0 0 0 q t := by
  classical
  let d : Exponent D := Finsupp.single (i,m) 1 + Finsupp.single (i,0) 1
  let F := fourSupport D d 0 0 0
  let e := compactExternal D F
  have hm : (i,m) ∈ F := by
    change (i,m) ∈ d.support ∪ _ ∪ _ ∪ _
    simp [d, Finsupp.mem_support_iff]
  have h0 : (i,0) ∈ F := by
    change (i,0) ∈ d.support ∪ _ ∪ _ ∪ _
    simp [d, Finsupp.mem_support_iff]
  let a : CompactExternal D F ⊕ CompactExternal D F := .inl (.inl ⟨(i,m), hm⟩)
  let b : CompactExternal D F ⊕ CompactExternal D F := .inl (.inl ⟨(i,0), h0⟩)
  let A : Matrix (CompactExternal D F ⊕ CompactExternal D F)
      (CompactExternal D F ⊕ CompactExternal D F) ℂ := slitMatrix D e t
  let mu : (CompactExternal D F ⊕ CompactExternal D F) → ℂ :=
    fun k => (bilinear D (unitCharge D (Sum.elim e e k).2.1) q : ℂ) * slitLinear D e t k
  have hd : externalOccupation D F d 0 0 0 = Finsupp.single b 1 + Finsupp.single a 1 := by
    apply Finsupp.ext
    intro j
    rcases j with (⟨j, hj⟩ | j) | (j | j)
    · change d j = (Finsupp.single b 1 + Finsupp.single a 1 :
        (CompactExternal D F ⊕ CompactExternal D F) →₀ ℕ) (Sum.inl (Sum.inl ⟨j, hj⟩))
      simp only [d, Finsupp.add_apply, Finsupp.single_apply, a, b, Sum.inl.injEq, Subtype.mk.injEq]
      exact add_comm _ _
    all_goals
      simp only [externalOccupation, Finsupp.sumElim_inl, Finsupp.sumElim_inr, restricted,
        Finsupp.comapDomain_zero, Finsupp.zero_apply, Finsupp.add_apply, Finsupp.single_apply,
        a, b, Sum.inl.injEq, reduceCtorEq, ite_false, zero_add]
  have hw : (weight (Finsupp.single b 1 + Finsupp.single a 1) : ℂ) =
      if m = 0 then 2 else 1 := by
    by_cases h : m = 0
    · subst m
      have hab : a = b := rfl
      rw [hab, ← Finsupp.single_add]
      simp [weight, Finsupp.prod_single_index]
    · have hab : a ≠ b := by
        intro hh
        exact h (congrArg (fun j => (Sum.elim e e j).2.2) hh)
      rw [ite_eq_right h]
      have hs : Disjoint (Finsupp.single b (1 : ℕ)).support (Finsupp.single a (1 : ℕ)).support := by
        simp [Ne.symm hab]
      rw [weight, Finsupp.prod_add_index_of_disjoint hs]
      simp [Finsupp.prod_single_index]
  have hslit : t ∈ D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.slitDomain :=
    D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.ball_subset_slitDomain
      (mem_ball_zero_iff.mpr ht)
  have hμ : AnalyticAt ℂ (nativeMean D i q t) 0 := by
    have hf : AnalyticAt ℂ (fun u => slitMean false u t) 0 :=
      (OriginalFourMSlitMean.slitMean_joint_analytic false hslit).fun_comp_of_eq
        (f := fun u : ℂ => (u,t)) (analyticAt_id.prod analyticAt_const) rfl
    exact (analyticAt_const.mul hf).div_const
  have hK : AnalyticAt ℂ (fun u => (D.G i i : ℂ) *
      slitCovariance false false false false u 0 t) 0 := by
    refine analyticAt_const.mul
      ((OriginalFourMSlitMean.slitCovariance_joint_analytic false false false false hslit).fun_comp_of_eq
        (f := fun u : ℂ => (u, (0, t))) (analyticAt_id.prod analyticAt_const) rfl)
  have hk (k : ℕ) : coefficient k (nativeMean D i q t) =
      (bilinear D (unitCharge D i) q : ℂ) * slitMeanEntry false false k t := by
    unfold nativeMean slitMeanEntry
    have he (u : ℂ) : -(bilinear D (unitCharge D i) q : ℂ) * slitMean false u t / slitPeriod t =
        (bilinear D (unitCharge D i) q : ℂ) * (-legSign false * slitMean false u t / slitPeriod t) := by
      simp [legSign]
      ring
    simp_rw [he, coefficient_const_mul]
  have hpair : coefficient m (nativePair D i q t) = mu a * mu b + A a b := by
    have hprod : AnalyticAt ℂ (fun u => nativeMean D i q t u * nativeMean D i q t 0) 0 :=
      hμ.mul analyticAt_const
    have hp : coefficient m (fun u => nativeMean D i q t u * nativeMean D i q t 0) =
        coefficient m (nativeMean D i q t) * nativeMean D i q t 0 := by
      simp only [coefficient, iteratedDeriv_mul_const_field, div_mul_eq_mul_div]
    unfold nativePair coefficient
    rw [iteratedDeriv_fun_add hprod.contDiffAt hK.contDiffAt, add_div]
    change coefficient m (fun u => nativeMean D i q t u * nativeMean D i q t 0) +
      coefficient m (fun u => (D.G i i : ℂ) * slitCovariance false false false false u 0 t) = _
    rw [hp, ← coefficient_zero (nativeMean D i q t), hk, hk]
    simp [mu, A, a, b, e, slitMatrix, slitLinear, slitCovarianceEntry, coefficient_zero,
      leg, compactExternal, gramComplex]
  rw [hpair, ← two_occurrence_moment A mu (slit_matrix_symm D e ht), affineMoment_coefficient, hw]
  change _ = _ * (rank24Determinant t * slitNome t ^ (chargeEnergy D q).toNat *
    affineCoefficient A mu (externalOccupation D F d 0 0 0))
  rw [hd]
  ring

open private chartA_radius chartA_nome chart_charge from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private freeCorrection from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance

set_option backward.isDefEq.respectTransparency false in
/-- The first higher mode and the lowest mode at the same puncture give the
literal fixed-charge Wick coefficient, with the repeated-mode Fock factorial. -/
theorem chartA_same_puncture_modes_one_zero_fixed_charge
    (D : LatticeData) (i : Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (hx : 1 / 2 < x) (hx1 : x < 1) :
    let t := parameter .A (x : ℂ)
    let lam := scale .A x .P
    let F := fun d => slitChargeTerm D d 0 0 0 q t
    let d10 : Exponent D := Finsupp.single (i, 1) 1 + Finsupp.single (i, 0) 1
    let d00 : Exponent D := Finsupp.single (i, 0) 2
    (chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim ![1,0] (fun _ => 1))
        ([Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1] : List (Fin 2 ⊕ Fin 2))
        (physicalChargeSummand D (fun _ => .P) (fun _ => i) upperA .A x q) 0 =
      ((1 - t) ^ (3 : ℕ) / lam ^ (2 : ℕ)) *
        (F d10 - 3 * F d00 + (3 / 16 : ℂ) * (D.G i i : ℂ) * F 0) := by
  dsimp only
  let t := parameter .A (x : ℂ)
  let f := nativePair D i q t
  let v := rawLocal .A x .P
  let J := jac .A x .P
  let rho := scaleRoot .A x .P
  let lam := scale .A x .P
  let C := fun u => -(slotCorrection .A x .P .P u 0 / (J u * J 0))
  let mu := physicalMean D q upperA .A x (fun _ : Fin 2 => .P) (fun _ => i)
  let A := physicalEntry D upperA .A x (fun _ : Fin 2 => .P) (fun _ => i)
  have hx0 : 0 < x := by linarith
  have ht : ‖t‖ < 1 := chartA_radius hx hx1
  have hslit := D5.S3.Analytic.OriginalHalfBinomialSlitPeriod.ball_subset_slitDomain
    (mem_ball_zero_iff.mpr ht)
  have hv0 : v 0 = 0 := by simp [v, rawLocal]
  have hJ0 : J 0 = rho := by simp [J, jac, halfJacobian, inverseRoot_zero, rho]
  have hrho : rho ^ 2 = lam := (chosen_roots hx0 hx1 .A .P).1
  have heta : loweringParameter .A .P = 1 := rfl
  have hv : AnalyticAt ℂ v 0 := rawLocal_analytic hx0 hx1 .A .P
  have hp : chartPeriod upperA .A x = slitPeriod t := rfl
  have hnear : Tendsto v (𝓝 0) (𝓝 0) := by
    have h : Tendsto v (𝓝 0) (𝓝 (v 0)) := hv.continuousAt
    rwa [hv0] at h
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖v u‖ + ‖t‖ < 1 := hnear.eventually
    ((isOpen_lt (continuous_norm.add continuous_const) continuous_const).mem_nhds (by simpa using ht))
  have hm := chosen_chart_source_eq_native hx0 hx1 .A (Or.inl rfl) false ht
  have hmu : mu 0 =ᶠ[𝓝 0] fun u => nativeMean D i q t (v u) / J u := by
    filter_upwards [hnear.eventually hm, hsmall] with u hu hsmallu
    have hs := hu.trans (OriginalFourMSlitMean.slitMean_eq_sourceMode false hsmallu).symm
    change _ = _
    simp only [mu, physicalMean, physicalSource, flags, legSign, hp, nativeMean, J, jac, v]
    rw [hs]
    simp only [Bool.false_eq_true, ite_false, one_mul]
    dsimp only [v]
    ring
  have hmu0 : mu 1 0 = nativeMean D i q t 0 / rho := by
    have h := hmu.eq_of_nhds
    rw [hv0, hJ0] at h
    exact h
  have hcov := chart_covariance_eq_native hx0 hx1 upperA .A (Or.inl rfl) false false false false ht
  have hxy : Tendsto (fun u : ℂ => (v u, (0 : ℂ))) (𝓝 0) (𝓝 (0, 0)) :=
    hnear.prodMk_nhds tendsto_const_nhds
  have hA : (fun u => A 0 1 u 0) =ᶠ[𝓝 0] fun u =>
      (D.G i i : ℂ) * (slitCovariance false false false false (v u) 0 t / (J u * rho) + C u) := by
    filter_upwards [hxy.eventually hcov, hsmall] with u hu hsmallu
    have hs := hu.trans (OriginalFourMSlitMean.slitCovariance_eq_native false false false false
      hsmallu (by simpa using ht)).symm
    change (D.G i i : ℂ) *
        ((chartCovariance upperA .A x false false false false (v u) (v 0) -
          slotCorrection .A x .P .P u 0) / (J u * J 0)) = _
    dsimp only [C]
    rw [hv0, hJ0, hs, sub_div]
    ring
  have he : (fun u => mu 0 u * mu 1 0 + A 0 1 u 0) =ᶠ[𝓝 0] fun u =>
      rho⁻¹ * (f (v u) / J u) + (D.G i i : ℂ) * C u := by
    filter_upwards [hmu, hA] with u hmu' hA'
    rw [hmu', hmu0, hA']
    simp only [f, nativePair, div_eq_mul_inv, mul_inv]
    ring
  have hmuA : AnalyticAt ℂ (nativeMean D i q t) 0 := by
    have hf : AnalyticAt ℂ (fun u => slitMean false u t) 0 :=
      (OriginalFourMSlitMean.slitMean_joint_analytic false hslit).fun_comp_of_eq
        (f := fun u : ℂ => (u,t)) (analyticAt_id.prod analyticAt_const) rfl
    exact (analyticAt_const.mul hf).div_const
  have hKA : AnalyticAt ℂ (fun u => slitCovariance false false false false u 0 t) 0 :=
    (OriginalFourMSlitMean.slitCovariance_joint_analytic false false false false hslit).fun_comp_of_eq
      (f := fun u : ℂ => (u,(0,t))) (analyticAt_id.prod analyticAt_const) rfl
  have hf : AnalyticAt ℂ f 0 :=
    (hmuA.mul analyticAt_const).add (analyticAt_const.mul hKA)
  have hroot : AnalyticAt ℂ (inverseRoot .A x .P) 0 := inverseRoot_analytic hx0 hx1 .A .P
  have hJ : AnalyticAt ℂ J 0 := analyticAt_const.div (hroot.pow 3) (by simp [inverseRoot_zero])
  have hJn : J 0 ≠ 0 := hJ0 ▸ root_ne hx0 hx1 .A .P
  have hJf : AnalyticAt ℂ (fun u => rho⁻¹ * (f (v u) / J u)) 0 :=
    analyticAt_const.mul ((hf.fun_comp_of_eq hv hv0).div hJ hJn)
  have hC : AnalyticAt ℂ C 0 := by
    have hfree : AnalyticAt ℂ (fun u => slotCorrection .A x .P .P u 0) 0 := by
      simp only [slotCorrection, true_and, ite_true, freeCorrection, inverseRoot_zero, mul_one]
      exact (analyticAt_const.mul (analyticAt_const.add hroot)).div
        ((analyticAt_const.mul hroot).mul ((hroot.add analyticAt_const).pow 2))
        (by norm_num [inverseRoot_zero])
    exact (hfree.div (hJ.mul analyticAt_const) (mul_ne_zero hJn hJn)).neg
  have hc : coefficient 1 C = lam⁻¹ ^ 2 * (3 / 16 : ℂ) := by
    have h := coefficient_neg_slotCorrection_div_jac hx0 hx1 .A .P 1 0
    rw [coefficient_zero, contraction_one_zero, heta] at h
    simpa [C, J, lam, div_eq_mul_inv, mul_pow] using h
  have hcomp := coefficient_comp_rawLocal_div_halfJacobian hf hx0 hx1 .A .P 1
  change coefficient 1 (fun u => f (v u) / J u) = _ at hcomp
  have hcomp' : coefficient 1 (fun u => f (v u) / J u) =
      rho⁻¹ * lam⁻¹ * (coefficient 1 f - (3 / 2 : ℂ) * coefficient 0 f) := by
    rw [hcomp, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [heta, rho, lam, Ring.choose_one_right, Ring.choose_zero_right]
    ring
  have hjet : coefficient 1 (fun u => mu 0 u * mu 1 0 + A 0 1 u 0) =
      lam⁻¹ ^ 2 * (coefficient 1 f - (3 / 2 : ℂ) * coefficient 0 f +
        (3 / 16 : ℂ) * (D.G i i : ℂ)) := by
    rw [coefficient_congr he]
    have hCG : AnalyticAt ℂ (fun u => (D.G i i : ℂ) * C u) 0 := analyticAt_const.mul hC
    have ha : coefficient 1 (fun u => rho⁻¹ * (f (v u) / J u) + (D.G i i : ℂ) * C u) =
        coefficient 1 (fun u => rho⁻¹ * (f (v u) / J u)) +
          coefficient 1 (fun u => (D.G i i : ℂ) * C u) := by
      unfold coefficient
      rw [iteratedDeriv_fun_add hJf.contDiffAt hCG.contDiffAt, add_div]
    rw [ha, coefficient_const_mul, coefficient_const_mul, hcomp', hc, ← hrho]
    simp only [inv_pow]
    ring
  rw [physical_two_mark_jet D i upperA x q, chart_charge D q hq upperA .A x
    (chartA_nome upperA hx0 hx1), hjet]
  have h0 := coefficient_native_pair D i q ht 0
  have h1 := coefficient_native_pair D i q ht 1
  norm_num at h0 h1
  rw [← Finsupp.single_add] at h0
  have hVac : slitChargeTerm D 0 0 0 0 q t =
      rank24Determinant t * slitNome t ^ (chargeEnergy D q).toNat := by
    unfold slitChargeTerm
    dsimp only
    rw [show externalOccupation D (fourSupport D 0 0 0 0) 0 0 0 0 = 0 by
      ext (⟨a | a⟩ | ⟨a | a⟩) <;> simp [externalOccupation, restricted]]
    let e := compactExternal D (fourSupport D 0 0 0 0)
    have hh := affineMoment_coefficient (slitMatrix D e t)
      (fun k => (bilinear D (unitCharge D (Sum.elim e e k).2.1) q : ℂ) * slitLinear D e t k) 0
    simp only [affineMoment_zero, weight, Finsupp.prod_zero_index, Nat.cast_one, one_mul] at hh
    rw [← hh, mul_one]
  change _ = _ * (slitChargeTerm D _ 0 0 0 q t - 3 * slitChargeTerm D _ 0 0 0 q t + _)
  have h0' : slitChargeTerm D (Finsupp.single (i, 0) 2) 0 0 0 q t =
      (rank24Determinant t * slitNome t ^ (chargeEnergy D q).toNat * coefficient 0 f) / 2 := by
    change _ = (rank24Determinant t * slitNome t ^ (chargeEnergy D q).toNat *
      coefficient 0 (nativePair D i q t)) / 2
    rw [h0]
    ring
  rw [← h1, h0', hVac, hp, rank24Determinant]
  have ht1 : 1 - t ≠ 0 := fun heq => by
    have : t = 1 := (sub_eq_zero.mp heq).symm
    simp [this] at ht
  field_simp [ht1]
  ring


open OriginalFourMChargeCoset (oscillatorLower)
open HalfFock.OriginalHalfCurrentTransport
  (normalOrder creationPart contraction lowering_normal_order_word)
open private vacuum vacuumProjection vacuumProjection_apply from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

set_option backward.isDefEq.respectTransparency false in
/-- The actual lowering flow on the repeated-colour word of modes one and zero
has one shorter creation term and one vacuum contraction. -/
theorem lowering_modes_one_zero (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (n : ℕ) :
    (n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n)
      (MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)) =
    if n = 0 then MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)
    else if n = 1 then (3 / 2 : ℂ) • (MvPolynomial.X (i, 0) ^ 2)
    else if n = 2 then ((3 / 16 : ℂ) * (D.G i i : ℂ)) • 1
    else 0 := by
  let V (j : ℕ) : Module.End ℂ (Oscillator D) := LinearMap.mulLeft ℂ (MvPolynomial.X (i, j) : Oscillator D)
  let Q : Module.End ℂ (Oscillator D) := vacuumProjection D
  have hz : creationPart D (i, 0) = PowerSeries.C (V 0) := by
    apply PowerSeries.ext
    intro k
    rw [creationPart, PowerSeries.coeff_mk, PowerSeries.coeff_C]
    cases k with
    | zero => simpa using (current_negative D i 0 : current D i (-(0 : ℕ) - 1) = V 0)
    | succ k => simp
  have ho : creationPart D (i, 1) =
      PowerSeries.C (V 1) + PowerSeries.monomial 1 ((3 / 2 : ℂ) • V 0) := by
    apply PowerSeries.ext
    intro k
    rw [creationPart, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C,
      PowerSeries.coeff_monomial]
    rcases k with _ | _ | k
    · norm_num [Ring.choose_zero_right, show current D i (-2) = V 1 from current_negative D i 1]
    · norm_num [Ring.choose_one_right, show current D i (-1) = V 0 from current_negative D i 0]
    · simp
  have hnil : normalOrder D [] = PowerSeries.C Q := by rw [normalOrder, vacuum]
  have hshort : normalOrder D [(i, 0)] = PowerSeries.C (V 0 * Q) := by
    rw [normalOrder, hz, hnil, map_mul]
    simp
  have hpair : normalOrder D [(i, 1), (i, 0)] =
      (PowerSeries.C (V 1) + PowerSeries.monomial 1 ((3 / 2 : ℂ) • V 0)) *
        PowerSeries.C (V 0 * Q) +
        PowerSeries.monomial 2 (((3 / 16 : ℂ) * (D.G i i : ℂ)) • (1 : Module.End ℂ (Oscillator D))) *
          PowerSeries.C Q := by
    rw [normalOrder, ho, hshort]
    simp [contraction, contraction_one_zero, hnil, mul_comm (D.G i i : ℂ) (3 / 16)]
  have h := lowering_normal_order_word D hu [(i, 1), (i, 0)] n
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [h, hpair]
  rw [map_add, PowerSeries.coeff_mul_C, map_add, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_C, PowerSeries.coeff_monomial, PowerSeries.coeff_monomial]
  rcases n with _ | _ | _ | n <;>
    simp [V, Q, Module.End.mul_apply, LinearMap.mulLeft_apply,
      vacuumProjection_apply, LinearMap.smul_apply, pow_two]


set_option backward.isDefEq.respectTransparency false in
/-- The two higher-current marks read the finite inverse lowering flow through
the original compact occupations and factorial Fock metric. -/
theorem chartA_same_puncture_modes_one_zero_lowering
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) (q : Charge D)
    (hq : 0 ≤ chargeEnergy D q) (upperA : Bool) {x : ℝ} (hx : 1 / 2 < x) (hx1 : x < 1) :
    let t := parameter .A (x : ℂ)
    let lam := scale .A x .P
    let P : Oscillator D := MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)
    let T := ∑ k ∈ Finset.range 4, ((-1 : ℂ) ^ k / (k.factorial : ℂ)) •
      (oscillatorLower D ^ k) P
    (chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
      spatialCoefficient (Sum.elim ![1, 0] (fun _ => 1))
        ([Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1] : List (Fin 2 ⊕ Fin 2))
        (physicalChargeSummand D (fun _ => .P) (fun _ => i) upperA .A x q) 0 =
      ((1 - t) ^ (3 : ℕ) / lam ^ (2 : ℕ)) *
        ∑ d ∈ T.support, T.coeff d * (weight d : ℂ) * slitChargeTerm D d 0 0 0 q t := by
  intro t lam P T
  let b := MvPolynomial.basisMonomials (Index D) ℂ
  let F (d : Exponent D) := slitChargeTerm D d 0 0 0 q t
  let L : Oscillator D →ₗ[ℂ] ℂ := b.constr ℂ (fun d => (weight d : ℂ) * F d)
  have hcoeff : (∑ d ∈ T.support, T.coeff d * (weight d : ℂ) * F d) = L T := by
    rw [show L T = _ from b.constr_apply ℂ _ T]
    change _ = ∑ d ∈ T.support, T.coeff d • ((weight d : ℂ) * F d)
    simp only [smul_eq_mul, mul_assoc]
  have hT : T = P - (3 / 2 : ℂ) • (MvPolynomial.X (i, 0) ^ 2) +
      ((3 / 16 : ℂ) * (D.G i i : ℂ)) • 1 := by
    unfold T
    simp_rw [div_eq_mul_inv, mul_smul]
    simp_rw [show ∀ k, (↑k.factorial : ℂ)⁻¹ • (oscillatorLower D ^ k) P = _ from
      lowering_modes_one_zero D hu i]
    norm_num [Finset.sum_range_succ, sub_eq_add_neg, neg_smul]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    dsimp only [P]
    module
  let a : Exponent D := Finsupp.single (i, 1) 1
  let d : Exponent D := Finsupp.single (i, 0) 1
  have ha : P = b (a + d) := by
    change MvPolynomial.monomial a (1 : ℂ) * MvPolynomial.monomial d 1 =
      MvPolynomial.monomial (a + d) 1
    rw [MvPolynomial.monomial_mul_monomial, mul_one]
  have hd : (MvPolynomial.X (i, 0) ^ 2 : Oscillator D) = b (d + d) := by
    rw [pow_two]
    change MvPolynomial.monomial d (1 : ℂ) * MvPolynomial.monomial d 1 =
      MvPolynomial.monomial (d + d) 1
    rw [MvPolynomial.monomial_mul_monomial, mul_one]
  have hw : weight (a + d) = 1 := by
    rw [show a + d = a + Finsupp.single (i, 0) 1 by rfl, FactorialFockMetric.weight_add_single]
    simp [a, weight, Finsupp.prod_single_index]
  have hw' : weight (d + d) = 2 := by
    rw [show d + d = d + Finsupp.single (i, 0) 1 by rfl, FactorialFockMetric.weight_add_single]
    simp [d, weight, Finsupp.prod_single_index]
  have hL (e : Exponent D) : L (b e) = (weight e : ℂ) * F e :=
    b.constr_basis ℂ _ e
  change _ = _ * ∑ d ∈ T.support, T.coeff d * (weight d : ℂ) * F d
  rw [hcoeff, hT, map_add, map_sub, map_smul, map_smul, ha, hd, show (1 : Oscillator D) = b 0 by rfl,
    hL, hL, hL, hw, hw']
  have h := chartA_same_puncture_modes_one_zero_fixed_charge D i q hq upperA hx hx1
  change _ = _ * (F (a + d) - 3 * F (Finsupp.single (i, 0) 2) +
    (3 / 16 : ℂ) * (D.G i i : ℂ) * F 0) at h
  rw [h, show d + d = Finsupp.single (i, 0) 2 by
    dsimp only [d]
    rw [← Finsupp.single_add]]
  simp [weight, smul_eq_mul]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCurrentRegression

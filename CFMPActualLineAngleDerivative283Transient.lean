import CFMPFiniteExceptionMonotone282Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine sourceCosine_continuousAt)
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualExtendedAngle268Transient
open CFMPActualAnalyticDiscriminant280Transient
open CFMPActualGlobalHessian260Transient (angleVector angleVector_hasFDerivAt angleVector_direction_actual)
open CFMPActualPhysicalHessian258Transient (physicalHessian_posDef)
open CFMPActualCompactHessian261Transient (physicalQuadratic physicalQuadratic_dotProduct)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Genuine Sector positive_classification)
open private delta square_gap denominator_pos denominator_sq raw_quotient from
  D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPActualLineAngleDerivative283Transient

def directionAngle (a b : Lengths) (t : ℝ) : ℝ :=
  sourceDifferential (AffineMap.lineMap a b t) (b-a)

theorem directionAngle_hasDerivAt_genuine (a b : Lengths) (t : ℝ)
    (ht : genuine (AffineMap.lineMap a b t)) :
    HasDerivAt (directionAngle a b)
      (physicalQuadratic wholeFamily (AffineMap.lineMap a b t) (b-a)) t := by
  let p := AffineMap.lineMap a b t
  let v := b-a
  let L : Lengths →L[ℝ] ℝ :=
    ∑ q : Fin 6, v q • (ContinuousLinearMap.proj q : Lengths →L[ℝ] ℝ)
  have hd := L.hasFDerivAt.comp_hasDerivAt t
    ((angleVector_hasFDerivAt p ht).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap)
  change HasDerivAt (fun s => L (angleVector (AffineMap.lineMap a b s)))
    (L (fderiv ℝ angleVector p v)) t at hd
  have heq : (fun s => L (angleVector (AffineMap.lineMap a b s))) = directionAngle a b := by
    funext s
    simp [L,v,angleVector,directionAngle,sourceDifferential_apply,mul_comm]
  have hval : L (fderiv ℝ angleVector p v) = physicalQuadratic wholeFamily p v := by
    simp only [L,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul]
    simp_rw [angleVector_direction_actual wholeFamily wholeFamily_realized p ht v]
    simp only [physicalQuadratic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [heq,hval] at hd
  exact hd

/-- Strictly positive original discriminant puts a positive length point
inside one flat sector, so the actual covector is locally constant there. -/
theorem positive_discriminant_flat_eventually (p : Lengths)
    (hp : p ∈ positiveLengths) (hd : 0 < discriminant p) :
    ∃ k : Fin 3, ∀ᶠ q in 𝓝 p, sourceDifferential q = flatDifferential k := by
  let x : Fin 6 → ℝ := fun j => Real.cosh (p j)
  have hx (j : Fin 6) : 1 < x j := Real.one_lt_cosh.mpr (hp j).ne'
  have hng : ¬ Genuine x := by
    intro hg
    have hn := (genuine_iff_discriminant_neg p hp).mp ⟨hp,hg⟩
    exact (not_lt_of_gt hd) hn
  obtain ⟨k,hk,_⟩ := (positive_classification x hx).2.1.resolve_left hng
  have hstrict : sourceCosine p (k.castAdd 3) < -1 := by
    change D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rawCos x (k.castAdd 3) < -1
    have hden := denominator_pos x hx (k.castAdd 3)
    have hs := denominator_sq x hx (k.castAdd 3)
    have hg := square_gap x (k.castAdd 3)
    have hfactor : 0 < x (k.castAdd 3)^2 - 1 := by nlinarith [hx (k.castAdd 3)]
    have hgap : 0 < (x (k.castAdd 3)^2 - 1) * delta x := mul_pos hfactor hd
    change D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rawCos x (k.castAdd 3) ≤ -1 at hk
    rw [raw_quotient,div_le_iff₀ hden] at hk
    rw [raw_quotient,div_lt_iff₀ hden]
    nlinarith
  have he := (sourceCosine_continuousAt p hp (k.castAdd 3)).eventually (Iio_mem_nhds hstrict)
  refine ⟨k,?_⟩
  filter_upwards [positiveLengths_open.mem_nhds hp,he] with q hq hcos
  exact sourceDifferential_eq_flat q hq k hcos.le

/-- Away from the original discriminant-zero set, the actual angle-direction
field has a nonnegative derivative: the physical positive Hessian on the
genuine side, and zero in a strict flat interior. -/
theorem directionAngle_nonneg_derivative (a b : Lengths) (t : ℝ)
    (hp : AffineMap.lineMap a b t ∈ positiveLengths)
    (hd : lineDiscriminant a b t ≠ 0) :
    ∃ d : ℝ, HasDerivAt (directionAngle a b) d t ∧ 0 ≤ d := by
  let p := AffineMap.lineMap a b t
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hg : genuine p := (genuine_iff_discriminant_neg p hp).mpr hneg
    refine ⟨physicalQuadratic wholeFamily p (b-a),
      directionAngle_hasDerivAt_genuine a b t hg,?_⟩
    rw [physicalQuadratic_dotProduct]
    simpa using ((physicalHessian_posDef wholeFamily wholeFamily_realized p hg).posSemidef.dotProduct_mulVec_nonneg (b-a))
  · obtain ⟨k,hk⟩ := positive_discriminant_flat_eventually p hp hpos
    have hline : ∀ᶠ s in 𝓝 t,
        directionAngle a b s = flatDifferential k (b-a) := by
      filter_upwards [AffineMap.lineMap_continuous.continuousAt.eventually hk] with s hs
      exact congrArg (fun L : Lengths →L[ℝ] ℝ => L (b-a)) hs
    exact ⟨0,(hasDerivAt_const t (flatDifferential k (b-a))).congr_of_eventuallyEq hline,
      le_refl 0⟩

end CFMPActualLineAngleDerivative283Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualLineAngleDerivative283Transient.directionAngle_hasDerivAt_genuine,
      ``CFMPActualLineAngleDerivative283Transient.positive_discriminant_flat_eventually,
      ``CFMPActualLineAngleDerivative283Transient.directionAngle_nonneg_derivative] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP283 actual direction-angle derivative absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP283 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP283 CHECKED {name} axioms={axioms}"

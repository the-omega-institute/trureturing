import D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
import Reg.Support.SingleDependentReadout

/-! The original dependent source family and its three scalar nested observations. -/
set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped VertexOperator BigOperators
noncomputable section

abbrev Parameters := Reg.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.Parameters

structure Input (p : Parameters) where
  K : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor p.D p.hu
  phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  H₁ : ℕ
  H₂ : ℕ
  H₃ : ℕ
  j : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ × ℂ × ℂ)

def observed (p : Parameters) (u : Input p) : ℂ × ℂ × ℂ :=
  (u.phi (((qField (u.gamma + 1) u.r u.H₁
      (targetSlice p.D p.hu (neutralMode p.D p.i u.d p.a) (u.gamma + 1))
      (targetSlice p.D p.hu p.b u.delta))[[u.n]]) u.x),
   u.phi (((qField 1 (u.d - u.j) u.H₂ (targetCurrent p.D p.hu p.i)
      (qField u.gamma (u.r + u.j) u.K (targetSlice p.D p.hu p.a u.gamma)
        (targetSlice p.D p.hu p.b u.delta)))[[u.n]]) u.x),
   u.phi (((qField u.gamma (u.d + u.r - u.j) u.H₃ (targetSlice p.D p.hu p.a u.gamma)
      (targetSlice p.D p.hu (neutralMode p.D p.i u.j p.b) (u.delta + 1)))[[u.n]]) u.x))

def actual : Realization signature := realize signature (fun _ p u =>
  (nestedLeftReadout (u.gamma + 1) 1 u.d u.r u.n (vectorFrequencyBound p.D p.a + 1) u.H₁
      (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a u.gamma)
      (targetSlice p.D p.hu p.b u.delta) u.x (rationalTripleReadout p.D p.a p.b u.K u.P),
   nestedRightReadout 1 u.gamma (u.r + u.j) (u.d - u.j) u.n u.K u.H₂
      (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a u.gamma)
      (targetSlice p.D p.hu p.b u.delta) u.x (rationalTripleReadout p.D p.a p.b u.K u.P),
   nestedRightReadout u.gamma 1 u.j (u.d + u.r - u.j) u.n
      (vectorFrequencyBound p.D p.b + 1) u.H₃
      (targetSlice p.D p.hu p.a u.gamma) (targetCurrent p.D p.hu p.i)
      (targetSlice p.D p.hu p.b u.delta) u.x
      (swapCurrentSourceReadout (rationalTripleReadout p.D p.a p.b u.K u.P))))
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => (1, 1, 1))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor p.D p.hu)
      (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ q ∈ labelledPairs 3, (threeOrders p.D p.a p.b K q : ℤ)) - d - r - n - 3
          then phi (actualNumerator p.D p.hu p.i p.a p.b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          observed p ⟨K, gamma, delta, d, r, n, x, phi, P, H₁, H₂, H₃, j⟩ =
            R.readout () p ⟨K, gamma, delta, d, r, n, x, phi, P, H₁, H₂, H₃, j⟩

theorem source_bridge : (type_of% (@actual_nested_ordered_readouts)) ↔ arena.Law actual := by
  constructor
  · intro h p
    obtain ⟨K, hp⟩ := h p.D p.hu p.i p.a p.b
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, ?_⟩
    intro H₁ H₂ H₃ j
    obtain ⟨first, second, third⟩ := observations H₁ H₂ H₃ j
    exact Prod.ext first (Prod.ext second third)
  · intro h D hu i a b
    obtain ⟨K, hp⟩ := h ⟨D, hu, i, a, b⟩
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, ?_⟩
    intro H₁ H₂ H₃ j
    have h := observations H₁ H₂ H₃ j
    exact ⟨congrArg Prod.fst h, congrArg (fun t => t.2.1) h,
      congrArg (fun t => t.2.2) h⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_nested_ordered_readouts)

private def witness : Parameters :=
  ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
    Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
    ⟨0, by decide⟩, 0, 0⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨K, hp⟩ := law witness
  obtain ⟨P, _, observations⟩ := hp 0 0 0 0 0 0 0
  have bad := congrArg Prod.fst (observations 0 0 0 0)
  have impossible : (0 : ℂ) = 1 := by simpa [observed, rejected, realize] using bad
  exact zero_ne_one impossible

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let Q := weightedClearingPolynomial (threeOrders witness.D witness.a witness.b 0)
  have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
    SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
  have pairs : ∀ q ∈ labelledPairs 3, pairPolynomial q.1 q.2 ≠ 0 := by
    simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
      Finset.prod_ne_zero_iff.mp uniformNonzero
  have nonzero : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _ (pairs q hq))
  have denominator : algebraMap _ (CommonRational ℂ 3) Q ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (LabelledPolynomial ℂ 3) (CommonRational ℂ 3)).ne nonzero
  let input (P : LabelledPolynomial ℂ 3) : Input witness :=
    ⟨0, 0, 0, -1, -1, -1, 0, 0, P, 0, 0, 0, 0⟩
  have bound : vectorFrequencyBound witness.D witness.a = 0 := by
    change vectorFrequencyBound witness.D 0 = 0
    simp [vectorFrequencyBound]
  have extraction (P : LabelledPolynomial ℂ 3) :
      (actual.readout () witness (input P)).1 =
        rationalTripleReadout witness.D witness.a witness.b 0 P 0 ![-1, -1, -1] -
          (1 / 2 : ℂ) *
            rationalTripleReadout witness.D witness.a witness.b 0 P 0 ![0, -2, -1] := by
    change nestedLeftReadout 1 1 (-1) (-1) (-1)
      (vectorFrequencyBound witness.D witness.a + 1) 0 _ _ _ 0 _ = _
    rw [bound]
    norm_num [nestedLeftReadout, finiteQReadout, input, BinomialKernelDelta.chooseSign,
      StateFieldResidueReconstruction.epsilon, Finset.sum_range_succ] <;> ring
  refine ⟨witness, input 0, input Q, ?_⟩
  intro equality
  have h := congrArg Prod.fst equality
  rw [extraction, extraction] at h
  have zeroReadout (order : Fin 6) (modes : Exponent 3) :
      rationalTripleReadout witness.D witness.a witness.b 0 0 order modes = 0 := by
    simp [rationalTripleReadout]
  have first : rationalTripleReadout witness.D witness.a witness.b 0 Q 0 ![-1, -1, -1] = 1 := by
    unfold rationalTripleReadout
    change (orderedRationalFor ℂ 3 (triplePermutation 0)
      (algebraMap _ (CommonRational ℂ 3) Q / algebraMap _ (CommonRational ℂ 3) Q)).coeff _ = _
    rw [div_self denominator, map_one]
    norm_num [triplePermutation, orderExponents, labelPermutation,
      exponentAddEquiv, exponents] <;> rfl
  have second : rationalTripleReadout witness.D witness.a witness.b 0 Q 0 ![0, -2, -1] = 0 := by
    unfold rationalTripleReadout
    change (orderedRationalFor ℂ 3 (triplePermutation 0)
      (algebraMap _ (CommonRational ℂ 3) Q / algebraMap _ (CommonRational ℂ 3) Q)).coeff _ = _
    rw [div_self denominator, map_one]
    norm_num [triplePermutation, orderExponents, labelPermutation,
      exponentAddEquiv, exponents] <;>
      (intro bad; have hzero := congrArg (fun g : Indices 3 => inverseExponents 3 g 0) bad;
        change (-1 : ℤ) = 0 at hzero; norm_num at hzero)
  rw [zeroReadout, zeroReadout, first, second] at h
  norm_num at h

def familyRegistration : Registration arena (type_of% (@actual_nested_ordered_readouts)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_nested_ordered_readouts) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout.actual_nested_ordered_readouts
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

namespace CollisionTaylor
set_option maxHeartbeats 2000000
open CollisionLaurentKernels.LaurentCollision

structure Input (p : Parameters) where
  K : ℕ
  gamma : ℤ
  delta : ℤ
  d : ℤ
  r : ℤ
  n : ℤ
  x : ActualTensor p.D p.hu
  phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ
  P : LabelledPolynomial ℂ 3
  u : ℕ
  v : ℕ
  m : ℤ
  degree : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ × ℂ × ℂ)

def chart (p : Parameters) (z : Input p) : Rational ℂ :=
  collisionChart z.P z.gamma z.d z.r
    (vectorFrequencyBound p.D p.a + 1) (vectorFrequencyBound p.D p.b + 1) z.K

def fused (p : Parameters) (z : Input p) : ℂ :=
  ∑ u ∈ Finset.range (z.degree + 1), collisionTaylor z.P z.gamma u (z.degree - u) *
    fusedResidueWeight ((u : ℤ) - (vectorFrequencyBound p.D p.b + 1 : ℕ))
      (z.d - (vectorFrequencyBound p.D p.a + 1 : ℕ))

def chambers (p : Parameters) (z : Input p) : ℂ :=
  (∑ u ∈ Finset.range (z.degree + 1), collisionTaylor z.P z.gamma u (z.degree - u) *
    orderedResidueWeight (z.d - (vectorFrequencyBound p.D p.a + 1 : ℕ))
      ((z.degree - u : ℕ) + z.r - z.K)) -
  StateFieldResidueReconstruction.epsilon (z.d - (vectorFrequencyBound p.D p.a + 1 : ℕ)) *
    ∑ u ∈ Finset.range (z.degree + 1), collisionTaylor z.P z.gamma u (z.degree - u) *
      orderedResidueWeight (z.d - (vectorFrequencyBound p.D p.a + 1 : ℕ))
        ((u : ℤ) - (vectorFrequencyBound p.D p.b + 1 : ℕ))

def observed (p : Parameters) (z : Input p) : ℂ × ℂ × ℂ :=
  (associatedTaylor z.P z.gamma z.u z.v,
   (resZ_XZ ℂ (iotaFused ℂ (chart p z))).coeff z.m, fused p z)

def actual : Realization signature := realize signature (fun _ p z =>
  (∑ j ∈ Finset.range (z.v + 1),
      ((z.u + j).choose z.u : ℂ) * collisionTaylor z.P z.gamma (z.u + j) (z.v - j),
   (resZ_ZX ℂ (iotaZX ℂ (chart p z)) - resZ_XZ ℂ (iotaXZ ℂ (chart p z))).coeff z.m,
   chambers p z)) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => (1, 1, 1))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor p.D p.hu)
      (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ q ∈ labelledPairs 3, (threeOrders p.D p.a p.b K q : ℤ)) - d - r - n - 3
          then phi (actualNumerator p.D p.hu p.i p.a p.b gamma delta K x e) else 0) ∧
        (∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          phi (((qField (gamma + 1) r H₁
            (targetSlice p.D p.hu (neutralMode p.D p.i d p.a) (gamma + 1))
            (targetSlice p.D p.hu p.b delta))[[n]]) x) =
            nestedLeftReadout (gamma + 1) 1 d r n (vectorFrequencyBound p.D p.a + 1) H₁
              (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)
              x (rationalTripleReadout p.D p.a p.b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent p.D p.hu p.i)
            (qField gamma (r + j) K (targetSlice p.D p.hu p.a gamma)
              (targetSlice p.D p.hu p.b delta)))[[n]]) x) =
            nestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.a gamma) (targetSlice p.D p.hu p.b delta)
              x (rationalTripleReadout p.D p.a p.b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice p.D p.hu p.a gamma)
            (targetSlice p.D p.hu (neutralMode p.D p.i j p.b) (delta + 1)))[[n]]) x) =
            nestedRightReadout gamma 1 j (d + r - j) n (vectorFrequencyBound p.D p.b + 1) H₃
              (targetSlice p.D p.hu p.a gamma) (targetCurrent p.D p.hu p.i) (targetSlice p.D p.hu p.b delta)
              x (swapCurrentSourceReadout (rationalTripleReadout p.D p.a p.b K P))) ∧
        (∀ u v : ℕ,
          (observed p ⟨K, gamma, delta, d, r, n, x, phi, P, u, v, 0, 0⟩).1 =
            (R.readout () p ⟨K, gamma, delta, d, r, n, x, phi, P, u, v, 0, 0⟩).1) ∧
        (∀ m : ℤ,
          (observed p ⟨K, gamma, delta, d, r, n, x, phi, P, 0, 0, m, 0⟩).2.1 =
            (R.readout () p ⟨K, gamma, delta, d, r, n, x, phi, P, 0, 0, m, 0⟩).2.1) ∧
        ∀ degree : ℕ,
          (degree : ℤ) = (vectorFrequencyBound p.D p.a + 1 : ℕ) +
            (vectorFrequencyBound p.D p.b + 1 : ℕ) + K - d - r - 2 →
          (observed p ⟨K, gamma, delta, d, r, n, x, phi, P, 0, 0, 0, degree⟩).2.2 =
            (R.readout () p ⟨K, gamma, delta, d, r, n, x, phi, P, 0, 0, 0, degree⟩).2.2

theorem source_bridge : (type_of% (@actual_collision_taylor_balance)) ↔ arena.Law actual := by
  constructor
  · intro h p
    obtain ⟨K, hp⟩ := h p.D p.hu p.i p.a p.b
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, readouts, cocycle, balance, numeric⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, readouts, cocycle, ?_, numeric⟩
    intro m
    exact congrArg (fun F : LaurentSeries ℂ => F.coeff m) balance
  · intro h D hu i a b
    obtain ⟨K, hp⟩ := h ⟨D, hu, i, a, b⟩
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, readouts, cocycle, balance, numeric⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, readouts, cocycle, ?_, numeric⟩
    apply HahnSeries.ext
    funext m
    exact balance m

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_collision_taylor_balance)

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let p : Parameters :=
    ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
      ⟨0, by decide⟩, 0, 0⟩
  obtain ⟨K, hp⟩ := law p
  obtain ⟨P, coefficients, _, cocycle, _, _⟩ := hp 0 0 0 0 0 0 0
  have Pzero : P = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    ext e
    simpa using coefficients e
  have bad := cocycle 0 0
  simp [observed, rejected, realize, Pzero, associatedTaylor] at bad

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p : Parameters :=
    ⟨Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic,
      Reg.D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation.hyperbolic_unit,
      ⟨0, by decide⟩, 0, 0⟩
  let input (P : LabelledPolynomial ℂ 3) : Input p :=
    ⟨0, 0, 0, 0, 0, 0, 0, 0, P, 0, 0, 0, 0⟩
  refine ⟨p, input 0, input (AddMonoidAlgebra.single 0 1), ?_⟩
  intro h
  have bad := congrArg Prod.fst h
  norm_num [actual, realize, input, collisionTaylor,
    AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single] at bad

def familyRegistration : Registration arena (type_of% (@actual_collision_taylor_balance)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_collision_taylor_balance) (type_of% (realize signature actual.readout actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout.actual_collision_taylor_balance
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout.CollisionTaylor.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CollisionTaylor

namespace SupportedExtraction

abbrev Input := Reg.D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout.Input
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameters Input (fun _ => ℂ × ℂ × ℂ)

def actual : Realization signature := realize signature (fun _ p u =>
  (supportedNestedLeftReadout (u.gamma + 1) 1 u.d u.r u.n
      (vectorFrequencyBound p.D p.a + 1) u.H₁ (rationalTripleReadout p.D p.a p.b u.K u.P),
   supportedNestedRightReadout 1 u.gamma (u.r + u.j) (u.d - u.j) u.n u.K u.H₂
      (rationalTripleReadout p.D p.a p.b u.K u.P),
   supportedNestedRightReadout u.gamma 1 u.j (u.d + u.r - u.j) u.n
      (vectorFrequencyBound p.D p.b + 1) u.H₃
      (swapCurrentSourceReadout (rationalTripleReadout p.D p.a p.b u.K u.P))))
  (fun empty => nomatch empty)

def supported (p : Parameters) (u : Input p) : Prop :=
  NestedLeftSupported 1 u.d u.r u.n (vectorFrequencyBound p.D p.a + 1) u.H₁
    (rationalTripleReadout p.D p.a p.b u.K u.P) ∧
  NestedRightSupported u.gamma (u.r + u.j) (u.d - u.j) u.n u.K u.H₂
    (rationalTripleReadout p.D p.a p.b u.K u.P) ∧
  NestedRightSupported 1 u.j (u.d + u.r - u.j) u.n
    (vectorFrequencyBound p.D p.b + 1) u.H₃
    (swapCurrentSourceReadout (rationalTripleReadout p.D p.a p.b u.K u.P))

def fibers (p : Parameters) (u : Input p) : ℂ × ℂ × ℂ :=
  (nestedLeftFiberReadout (u.gamma + 1) 1 u.d u.r u.n
      (vectorFrequencyBound p.D p.a + 1) u.H₁ (rationalTripleCarriers p.D p.a p.b u.K u.P),
   nestedRightFiberReadout 1 u.gamma (u.r + u.j) (u.d - u.j) u.n u.K u.H₂
      (rationalTripleCarriers p.D p.a p.b u.K u.P),
   nestedRightFiberReadout u.gamma 1 u.j (u.d + u.r - u.j) u.n
      (vectorFrequencyBound p.D p.b + 1) u.H₃
      (swapCurrentSourceCarriers (rationalTripleCarriers p.D p.a p.b u.K u.P)))

def arena : Arena where
  signature := signature
  Law R := ∀ p, ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor p.D p.hu)
      (phi : ActualTensor p.D p.hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ q ∈ labelledPairs 3, (threeOrders p.D p.a p.b K q : ℤ)) - d - r - n - 3
          then phi (actualNumerator p.D p.hu p.i p.a p.b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          let u : Input p := ⟨K, gamma, delta, d, r, n, x, phi, P, H₁, H₂, H₃, j⟩
          supported p u ∧ observed p u = R.readout () p u ∧ observed p u = fibers p u ∧
          (observed p u).1 = nestedLeftLocalReadout (gamma + 1) 1 d r n
            (vectorFrequencyBound p.D p.a + 1) H₁
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders p.D p.a p.b K))) ∧
          (observed p u).2.1 = nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n K H₂
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders p.D p.a p.b K))) ∧
          (observed p u).2.2 = nestedRightLocalReadout 0 gamma 1 j (d + r - j) n
            (vectorFrequencyBound p.D p.b + 1) H₃
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders p.D p.a p.b K)))

theorem source_bridge :
    (type_of% (@actual_supported_nested_extraction)) ↔ arena.Law actual := by
  constructor
  · intro h p
    obtain ⟨K, hp⟩ := h p.D p.hu p.i p.a p.b
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, ?_⟩
    intro H₁ H₂ H₃ j
    obtain ⟨s₁, s₂, s₃, e₁, e₂, e₃, f₁, f₂, f₃, localValue, localForward, localReverse⟩ := observations H₁ H₂ H₃ j
    exact ⟨⟨s₁, s₂, s₃⟩, Prod.ext e₁ (Prod.ext e₂ e₃), Prod.ext f₁ (Prod.ext f₂ f₃), localValue, localForward, localReverse⟩
  · intro h D hu i a b
    obtain ⟨K, hp⟩ := h ⟨D, hu, i, a, b⟩
    refine ⟨K, ?_⟩
    intro gamma delta d r n x phi
    obtain ⟨P, coefficients, observations⟩ := hp gamma delta d r n x phi
    refine ⟨P, coefficients, ?_⟩
    intro H₁ H₂ H₃ j
    obtain ⟨⟨s₁, s₂, s₃⟩, e, f, localValue, localForward, localReverse⟩ := observations H₁ H₂ H₃ j
    exact ⟨s₁, s₂, s₃, congrArg Prod.fst e, congrArg (fun z => z.2.1) e,
      congrArg (fun z => z.2.2) e, congrArg Prod.fst f,
      congrArg (fun z => z.2.1) f, congrArg (fun z => z.2.2) f, localValue, localForward, localReverse⟩

theorem actual_law : arena.Law actual := source_bridge.mp (@actual_supported_nested_extraction)

def rejected : Realization signature := realize signature (fun _ _ _ => (1, 1, 1))
  (fun empty => nomatch empty)

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨K, hp⟩ := law witness
  obtain ⟨P, coefficients, observations⟩ := hp 0 0 0 0 0 0 0
  have bad := congrArg Prod.fst (observations 0 0 0 0).2.1
  have impossible : (0 : ℂ) = 1 := by simpa [observed, rejected, realize] using bad
  exact zero_ne_one impossible

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

end SupportedExtraction

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

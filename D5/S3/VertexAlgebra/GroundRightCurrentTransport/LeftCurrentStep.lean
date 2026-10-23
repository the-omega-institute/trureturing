/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/LeftCurrentStep
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/LeftCurrentStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native compatibility propagated through an actual first-source current insertion. -/
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceCurrentIterate
import D5.S3.VertexAlgebra.NestedResidues.ActualNestedQIterate

/-! The source iterate and the actual nested residue iterate have identical
finite right sides after the smaller source products are identified. Algebraic
dual separation recovers every mode on the actual tensor carrier; cutoff
independence then gives the native defect zero. No sector matching, eigenstate,
positivity or numerator-compatibility hypothesis is added.
Classical local-field calculus: Matsuo--Nagatomo; Bakalov--Kac math/0402315.
Actual fields: Scott Carnahan, vertexAlg
4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
This conditional current-insertion step does not assert arbitrary-state
compatibility at independently chosen physical lifts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution
open SupportedWordRationalCollision.ActualPolynomialBridge
open NestedResidues.LatticeHalfFockSliceQuotient
open CollisionRationalExpansions.OrderedRationalExpansion Calculus
open scoped BigOperators TensorProduct VertexOperator
noncomputable section
local notation "μ" => LatticeAllStateReconstruction.mu
local notation "σ" => BinomialKernelDelta.chooseSign
local notation "ε" => StateFieldResidueReconstruction.epsilon

local macro "upper" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.Calculus.upper))
local macro "nativeSlice" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeSlice))
local macro "nativeCutoff" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.nativeCutoff))
local macro "native_valid" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.native_valid))
local macro "source_slice_locality" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.ActualLaurentCarriers 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.source_slice_locality))
local macro "current_slice_locality" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.ActualLaurentCarriers 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_slice_locality))
local macro "pair_pow_slice_mul" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient 0) ++
    `D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.pair_pow_slice_mul))
local macro "clearing_pad" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient 0) ++
    `D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.clearing_pad))
local macro "orders_three" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient 0) ++
    `D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.orders_three))

private theorem native_qField_transport
    (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta s r : ℤ) (K : ℕ)
    (hlocal :
      (FieldNormalProductLocality.deltaEnd ^ K)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0) :
    qField s r K (targetSlice D hu a gamma) (targetSlice D hu b delta) =
      Calculus.Q (nativeSlice D hu a gamma)
        (nativeSlice D hu b delta) s r
        (nativeCutoff D hu a b gamma delta) := by
  have supplied_valid :
      Valid (targetSlice D hu a gamma) (targetSlice D hu b delta) K :=
    valid_of_locality _ _ K hlocal
  have chosen_native_valid :
      Valid (targetSlice D hu a gamma) (targetSlice D hu b delta)
        (nativeCutoff D hu a b gamma delta) :=
    native_valid D hu a b gamma delta
  exact Q_cutoff (targetSlice D hu a gamma) (targetSlice D hu b delta)
    s r K (nativeCutoff D hu a b gamma delta) supplied_valid chosen_native_valid

private theorem source_product_native_Q_at
    (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) (gamma delta r : ℤ) (K : ℕ)
    (law : OriginalCompatible D hu a b gamma delta)
    (hlocal :
      (FieldNormalProductLocality.deltaEnd ^ K)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0) :
    targetSlice D hu (μ D a r b) (gamma + delta) =
      Calculus.Q (targetSlice D hu a gamma) (targetSlice D hu b delta)
        gamma r K := by
  have hz := compatible_defect D hu a b gamma delta law r
  have hnative :
      nativeSlice D hu (μ D a r b) (gamma + delta) =
        Calculus.Q (nativeSlice D hu a gamma)
          (nativeSlice D hu b delta) gamma r
          (nativeCutoff D hu a b gamma delta) := by
    simpa only [defect, nativeProduct, sub_eq_zero] using hz
  have hcut := native_qField_transport D hu a b gamma delta gamma r K hlocal
  calc
    _ = nativeSlice D hu (μ D a r b) (gamma + delta) := rfl
    _ = Calculus.Q (nativeSlice D hu a gamma)
        (nativeSlice D hu b delta) gamma r
        (nativeCutoff D hu a b gamma delta) := hnative
    _ = Calculus.Q (targetSlice D hu a gamma)
        (targetSlice D hu b delta) gamma r K := by
      rw [← hcut]
      rfl

theorem left_current_step
    (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a : Carrier D) (gamma d : ℤ)
    (smaller : ∀ (b : Carrier D) (delta : ℤ),
      OriginalCompatible D hu a b gamma delta) :
    ∀ (b : Carrier D) (delta : ℤ),
      OriginalCompatible D hu (neutralMode D i d a) b (gamma + 1) delta := by
  classical
  intro b delta
  obtain ⟨Kloc, hloc⟩ := source_slice_locality D hu a b
  obtain ⟨Kf, hfinite⟩ :=
    LatticeHalfFockClearedTaylorReadout.actual_finite_laurent_carriers D hu i a b
  let K : ℕ := max Kloc (max Kf (upper (Y D a) b))
  have hKloc : Kloc ≤ K := by dsimp [K]; omega
  have hKf : Kf ≤ K := by dsimp [K]; omega
  have hKupper : upper (Y D a) b ≤ K := by dsimp [K]; omega
  have hlocalK :
      (FieldNormalProductLocality.deltaEnd ^ K)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0 := by
    rw [show K = (K - Kloc) + Kloc by omega, pow_add,
      Module.End.mul_apply, hloc gamma delta, map_zero]
  have current (v : Carrier D) (s t : ℤ) :
      targetSlice D hu (neutralMode D i t v) (s + 1) =
        qField 1 t (vectorFrequencyBound D v + 1)
          (targetCurrent D hu i) (targetSlice D hu v s) := by
    exact native_current_inverse D hu i v s t
  apply defect_compatible D hu
  intro r
  obtain ⟨H₁, local₁⟩ := source_slice_locality D hu (neutralMode D i d a) b
  have h₁ := local₁ (gamma + 1) delta
  have inner (j : ℕ) :
      targetSlice D hu (μ D a (r + (j : ℤ)) b) (gamma + delta) =
        qField gamma (r + (j : ℤ)) K
          (targetSlice D hu a gamma) (targetSlice D hu b delta) := by
    exact source_product_native_Q_at D hu a b gamma delta
      (r + (j : ℤ)) K (smaller b delta) hlocalK
  let H₂ : ℕ → ℕ := fun j =>
    vectorFrequencyBound D (μ D a (r + (j : ℤ)) b) + 1
  have h₂ : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H₂ j)
        (FieldNormalProductLocality.commutator
          (targetCurrent D hu i)
          (qField gamma (r + (j : ℤ)) K
            (targetSlice D hu a gamma) (targetSlice D hu b delta))) = 0 := by
    intro j hj
    rw [← inner j]
    exact current_slice_locality D hu i (μ D a (r + (j : ℤ)) b) (gamma + delta)
  let H₃ : ℕ → ℕ := fun j => Classical.choose
    (source_slice_locality D hu a (neutralMode D i (j : ℤ) b))
  have local₃ (j : ℕ) :
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i (j : ℤ) b) (delta + 1))) = 0 :=
    Classical.choose_spec
      (source_slice_locality D hu a (neutralMode D i (j : ℤ) b)) gamma (delta + 1)
  have h₃ : ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu a gamma)
          (qField 1 (j : ℤ) (vectorFrequencyBound D b + 1)
            (targetCurrent D hu i) (targetSlice D hu b delta))) = 0 := by
    intro j hj
    rw [← current b delta (j : ℤ)]
    exact local₃ j
  have leftField (j : ℕ) :
      targetSlice D hu
          (neutralMode D i (d - (j : ℤ)) (μ D a (r + (j : ℤ)) b))
          (gamma + delta + 1) =
        qField 1 (d - (j : ℤ)) (H₂ j) (targetCurrent D hu i)
          (qField gamma (r + (j : ℤ)) K
            (targetSlice D hu a gamma) (targetSlice D hu b delta)) := by
    calc
      _ = qField 1 (d - (j : ℤ)) (H₂ j) (targetCurrent D hu i)
          (targetSlice D hu (μ D a (r + (j : ℤ)) b) (gamma + delta)) :=
        current (μ D a (r + (j : ℤ)) b) (gamma + delta) (d - (j : ℤ))
      _ = _ := by rw [inner j]
  have rightField (j : ℕ) :
      targetSlice D hu
          (μ D a (d + r - (j : ℤ)) (neutralMode D i (j : ℤ) b))
          (gamma + delta + 1) =
        qField gamma (d + r - (j : ℤ)) (H₃ j) (targetSlice D hu a gamma)
          (qField 1 (j : ℤ) (vectorFrequencyBound D b + 1)
            (targetCurrent D hu i) (targetSlice D hu b delta)) := by
    have smaller_at := source_product_native_Q_at D hu a
      (neutralMode D i (j : ℤ) b) gamma (delta + 1)
      (d + r - (j : ℤ)) (H₃ j)
      (smaller (neutralMode D i (j : ℤ) b) (delta + 1)) (local₃ j)
    simpa only [qField, current b delta (j : ℤ), add_assoc] using smaller_at
  have sourceFields :=
    (source_current_iterate_slice D hu i a b K hKupper gamma delta d r).2.2
  simp_rw [leftField, rightField] at sourceFields
  have fields :
      targetSlice D hu (μ D (neutralMode D i d a) r b) (gamma + delta + 1) =
        nativeProduct D hu (neutralMode D i d a) b (gamma + 1) delta r := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
    apply LinearMap.ext
    intro x
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro phi
    let n : ℤ := -e - 1
    change phi
      (((targetSlice D hu (μ D (neutralMode D i d a) r b)
          (gamma + delta + 1))[[n]]) x -
       ((nativeProduct D hu (neutralMode D i d a) b (gamma + 1) delta r)[[n]]) x) = 0
    let Ef : ℤ :=
      (∑ p ∈ labelledPairs 3, (threeOrders D a b Kf p : ℤ)) - d - r - n - 3
    obtain ⟨P₀, hP₀, _carriers⟩ := hfinite gamma delta x phi Ef
    let P := pairPolynomial (1 : Fin 3) 2 ^ (K - Kf) * P₀
    have pad_action :
        polynomialAction (pairPolynomial (1 : Fin 3) 2 ^ (K - Kf))
          (actualNumerator D hu i a b gamma delta Kf x) =
        actualNumerator D hu i a b gamma delta K x := by
      unfold actualNumerator
      rw [← Module.End.mul_apply, ← map_mul, clearing_pad D a b Kf K hKf]
    have hP : ∀ q : Exponent 3, P.coeff q =
        if totalExponent q =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
        then phi (actualNumerator D hu i a b gamma delta K x q) else 0 := by
      intro q
      have h := pair_pow_slice_mul (1 : Fin 3) 2
        (actualNumerator D hu i a b gamma delta Kf x) phi P₀ Ef hP₀ (K - Kf) q
      rw [pad_action] at h
      have aligned : Ef + ((K - Kf : ℕ) : ℤ) =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3 := by
        dsimp only [Ef]
        rw [orders_three, orders_three]
        omega
      simpa only [P, aligned] using h
    have actual := actual_nested_q_iterate D hu i a b K gamma delta d r n x phi P
      hP H₁ H₂ H₃ h₁ h₂ h₃
    have source := congrArg
      (fun T : VertexOperator ℂ (ActualTensor D hu) => phi ((T[[n]]) x)) sourceFields
    simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, LinearMap.sub_apply,
      LinearMap.sum_apply,
      map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul] at source
    have scalar := source.trans actual.symm
    have native :
        qField (gamma + 1) r H₁
          (targetSlice D hu (neutralMode D i d a) (gamma + 1))
          (targetSlice D hu b delta) =
        nativeProduct D hu (neutralMode D i d a) b (gamma + 1) delta r :=
      native_qField_transport D hu (neutralMode D i d a) b
        (gamma + 1) delta (gamma + 1) r H₁ h₁
    have scalarNative := congrArg
      (fun T : VertexOperator ℂ (ActualTensor D hu) => phi ((T[[n]]) x)) native
    rw [map_sub, scalar, scalarNative, sub_self]
  change targetSlice D hu (μ D (neutralMode D i d a) r b) ((gamma + 1) + delta) -
    nativeProduct D hu (neutralMode D i d a) b (gamma + 1) delta r = 0
  rw [show (gamma + 1) + delta = gamma + delta + 1 by omega, fields, sub_self]
end
end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

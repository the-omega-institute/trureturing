/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/ActualReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor/ActualReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete nested-field readouts and independent outer completion. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor.LocalResidues

/-! Complete-field residue calculus with the original signed Laurent powers.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. Hahn operations: mathlib, Apache 2.0.
This is a formalized synthesis and application, with no literature novelty claim.
Consumed boundary helpers are not independent mathematical endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open NestedResidues.ContextualKernelExtraction
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open StateFieldResidueReconstruction

/-- Finiteness is asserted for each complete residue fiber, rather than for
the individual words obtained by expanding an intermediate field. -/
private def QReadoutSupported (r : ℤ) (K : ℕ) (n : ℤ)
    (forward backward : ℤ → ℤ → ℂ) : Prop :=
  ∀ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign (r + ell) u *
        forward (r + ell - u) (n - ell + u)) ∧
    Function.HasFiniteSupport (fun u : ℕ =>
      BinomialKernelDelta.chooseSign (r + ell) u * backward (r + n - u) u)

private theorem actual_q_support (r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    QReadoutSupported r K n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  intro ell hell
  constructor
  · apply (Finset.range
      (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat).finite_toSet.subset
    intro u hu
    apply Finset.mem_range.mpr
    by_contra outside
    have hz : (B[[n - ell + u]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hu (by simp [hz])
  · apply (Finset.range (-((HahnModule.of ℂ).symm (A x)).order).toNat).finite_toSet.subset
    intro u hu
    apply Finset.mem_range.mpr
    by_contra outside
    have hz : (A[[(u : ℤ)]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hu (by simp [hz])

private theorem QReadoutSupported_congr (r : ℤ) (K : ℕ) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    QReadoutSupported r K n f g ↔ QReadoutSupported r K n f' g' := by
  unfold QReadoutSupported
  have forward (ell : ℕ) :
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u *
        f (r + ell - u) (n - ell + u)) =
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u *
        f' (r + ell - u) (n - ell + u)) := by
    funext u
    rw [hf _ _ (by omega)]
  have backward (ell : ℕ) :
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u * g (r + n - u) u) =
      (fun u : ℕ => BinomialKernelDelta.chooseSign (r + ell) u * g' (r + n - u) u) := by
    funext u
    rw [hg _ _ (by omega)]
  simp only [forward, backward]

/-- Support of the complete outer fibers in the right nesting. -/
private def NestedRightSupported (innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : Prop :=
  QReadoutSupported r H n
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m])) ∧
  ∀ k l : ℤ, k + l = r + n →
    QReadoutSupported d K l (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]) ∧
    QReadoutSupported d K k (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m])

private theorem NestedRightSupported_congr (innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    NestedRightSupported innerLift d r n K H R ↔ NestedRightSupported innerLift d r n K H S := by
  unfold NestedRightSupported
  apply and_congr
  · apply QReadoutSupported_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega
  · apply forall_congr'
    intro k
    apply forall_congr'
    intro l
    apply imp_congr_right
    intro hkl
    apply and_congr <;> apply QReadoutSupported_congr <;>
      intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem actual_nested_right_support (innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    NestedRightSupported innerLift d r n K H (tripleScalar A B C x phi) := by
  have forward (k l : ℤ) :
      phi ((A[[k]]) (((qField innerLift d K B C)[[l]]) x)) =
        supportedQReadout innerLift d K l
          (fun m p => tripleScalar A B C x phi 0 ![k, m, p])
          (fun m p => tripleScalar A B C x phi 1 ![k, p, m]) := by
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  have backward (k l : ℤ) :
      phi (((qField innerLift d K B C)[[k]]) ((A[[l]]) x)) =
        supportedQReadout innerLift d K k
          (fun m p => tripleScalar A B C x phi 3 ![l, m, p])
          (fun m p => tripleScalar A B C x phi 5 ![l, p, m]) := by
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  constructor
  · exact (QReadoutSupported_congr r H n _ _ _ _
      (fun k l _ => forward k l) (fun k l _ => backward k l)).mp
        (actual_q_support r H A (qField innerLift d K B C) x n phi)
  · intro k l hkl
    constructor
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def] using
        actual_q_support d K B C x l (phi.comp (A[[k]]))
    · simpa [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def] using
        actual_q_support d K B C ((A[[l]]) x) k phi

private theorem sourceSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := rationalTripleCarriers D a b K P
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (LatticeHalfFockChargedCollision.WeightedLocalCorrelator.weightedClearingPolynomial (threeOrders D a b K))
    rightPairFiberQ s d I k l (W 0) (W 1) =
      lastSourceLocalQ 1 true s d I k l R ∧
    leftPairFiberQ s d I k l (W 3) (W 5) =
      lastSourceLocalQ 1 false s d I k l R := by
  dsimp only
  have f_left : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (1 : Fin 3) (lastSourceTau 1 true) = triplePermutation 0 := by
    ext j; fin_cases j <;> rfl
  have g_left : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (1 : Fin 3) (lastSourceTau 1 true) = triplePermutation 1 := by
    ext j; fin_cases j <;> rfl
  have f_right : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (1 : Fin 3) (lastSourceTau 1 false) = triplePermutation 3 := by
    ext j; fin_cases j <;> rfl
  have g_right : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (1 : Fin 3) (lastSourceTau 1 false) = triplePermutation 5 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold rightPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (1 : Fin 3) (lastSourceTau 1 true)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_left, g_left] at eq
    exact eq
  · unfold leftPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (1 : Fin 3) (lastSourceTau 1 false)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_right, g_right] at eq
    exact eq

private theorem nestedRightLocalReadout_sourceSource (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedRightFiberReadout outerLift innerLift d r n I H
      (rationalTripleCarriers D a b K P) =
    nestedRightLocalReadout 1 outerLift innerLift d r n I H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (LatticeHalfFockChargedCollision.WeightedLocalCorrelator.weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedRightFiberReadout nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (sourceSourceLocalQ_eq D a b K I P innerLift d l k).1
  · intro k l _
    exact (sourceSourceLocalQ_eq D a b K I P innerLift d k l).2

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockClearedTaylorReadout LatticeHalfFockABLocalResidue
open LatticeHalfFockSliceQuotient UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
noncomputable section

/- proof_shape: actual_ab_nested_readout: bind-only
   consumer: actual_ab_joint_outer_support
   derivation: The supplier six-word coefficients on total mode degree
   d+r+n are transported through the actual homogeneous quotient comparison.
   Nested supported extraction then retains an independent inner cutoff I,
   including I=K, rather than comparing cutoff-dependent actual fields. -/
set_option maxHeartbeats 1600000 in
-- Retain the complete dependent homogeneous telescope during extraction.
/-- The actual finite nested Q field, with arbitrary inner cutoff I, is the
supported readout of the complete A/B rational G at the original numerator P,K.
No locality at K or I is assumed. The support is on complete outer fibers. -/
theorem actual_ab_nested_readout
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K I H : ℕ) (gamma delta d r n j : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0) :
    NestedRightSupported gamma (r + j) (d - j) n I H
      (rationalTripleReadout D a b K P) ∧
    phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n I H
        (originalRational D a b K P) ∧
    phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      supportedQReadout 1 (d - j) H n
        (fun k l =>
          (coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1)
            (completeAB gamma (r + j) I (originalRational D a b K P))).coeff
              (exponents 2 ![-k - 1, -l - 1]))
        (fun k l =>
          (coefficientHahn ℂ 1 1 (1 : Fin 3)
            ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
            (completeAB gamma (r + j) I (originalRational D a b K P))).coeff
              (exponents 2 ![-k - 1, -l - 1])) := by
  obtain ⟨K₀, supplier⟩ := actual_finite_laurent_carriers D hu i a b
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ)) - d - r - n - 3
  obtain ⟨P₀, coefficients₀, words⟩ := supplier gamma delta x phi total
  have quotient := (actual_slice_quotient_compat D hu i a b K K₀ gamma delta d r n
    x phi P P₀ coefficients coefficients₀).2.1
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = (r + j) + (d - j) + n) :
      tripleScalar (targetCurrent D hu i) (targetSlice D hu a gamma)
        (targetSlice D hu b delta) x phi order modes =
      rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [ite_eq_left index, ← quotient] at readout
    exact readout.symm
  have identified : phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n I H
        (originalRational D a b K P) := by
    rw [supportedNestedRightReadout_eq]
    rw [supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ same]
    change supportedNestedRightReadout 1 gamma (r + j) (d - j) n I H
      (hahnTripleScalar (rationalTripleCarriers D a b K P)) = _
    rw [← nestedRightFiberReadout_eq]
    exact nestedRightLocalReadout_sourceSource D a b K I P 1 gamma (r + j) (d - j) n H
  refine ⟨(NestedRightSupported_congr _ _ _ _ _ _ _ _ same).mp
    (actual_nested_right_support _ _ _ _ _ _ _ _ _ x phi), identified, ?_⟩
  rw [identified]
  unfold nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (ab_complete_remaining_orders D a b K I P gamma (r + j) l k).2.2.1
  · intro k l _
    exact (ab_complete_remaining_orders D a b K I P gamma (r + j) k l).2.2.2

set_option maxHeartbeats 1600000 in
-- Preserve the original slice through the shifted complete residue.
private theorem actual_ab_outer_completion
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K I H : ℕ) (gamma delta d r n j : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator (targetCurrent D hu i)
        (qField gamma (r + j) I (targetSlice D hu a gamma)
          (targetSlice D hu b delta))) = 0) :
    OuterQCompletion 1 (d - j) n H
      (fun k l => lastSourceLocalQ 1 true gamma (r + j) I l k
        (originalRational D a b K P))
      (fun k l => lastSourceLocalQ 1 false gamma (r + j) I k l
        (originalRational D a b K P)) := by
  apply completeOuterQReadout_of_locality 1 (d - j) n H
    (targetCurrent D hu i)
    (qField gamma (r + j) I (targetSlice D hu a gamma) (targetSlice D hu b delta))
    x phi _ _ locality
  intro ell high
  have coefficients' : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) -
            (d + ell) - r - (n - ell) - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0 := by
    intro e
    rw [show (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) -
        (d + ell) - r - (n - ell) - 3 =
      (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3 by omega]
    exact coefficients e
  have matched := (actual_ab_nested_readout D hu i a b K I
    ((d - j + ell).toNat + 1) gamma delta (d + ell) r (n - ell) j
    x phi P coefficients').2.1.symm
  simpa only [show d + (ell : ℤ) - j = d - j + ell by omega,
    nestedRightLocalReadout] using matched

private theorem finite_joint_antidiagonal (J T : ℕ) (B : ℕ → ℕ)
    (F : ℕ → ℕ → ℂ) (bound : ∀ j < J, j + B j ≤ T)
    (tail : ∀ j < J, ∀ ell, B j ≤ ell → F j ell = 0) :
    (∑ j ∈ Finset.range J, ∑ ell ∈ Finset.range (B j), F j ell) =
      ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (t + 1),
        if j < J then F j (t - j) else 0 := by
  classical
  let S := (Finset.range J).sigma (fun j => Finset.range (B j))
  let U := (Finset.range T).sigma (fun t =>
    (Finset.range (t + 1)).filter (fun j => j < J ∧ t - j < B j))
  have bijection : (∑ p ∈ S, F p.1 p.2) = ∑ p ∈ U, F p.2 (p.1 - p.2) := by
    apply Finset.sum_bij (fun p _ => ⟨p.1 + p.2, p.1⟩)
    · intro p hp
      obtain ⟨hj, he⟩ := Finset.mem_sigma.mp hp
      have hj' := Finset.mem_range.mp hj
      have he' := Finset.mem_range.mp he
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_range.mpr (by dsimp only; have := bound p.1 hj'; omega), ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by dsimp only; omega), hj', by simpa using he'⟩
    · intro p hp q hq same
      have first := congrArg Sigma.fst same
      have second := congrArg Sigma.snd same
      apply Sigma.ext
      · exact second
      · have : p.2 = q.2 := by dsimp at first second; omega
        simpa only [heq_eq_eq] using this
    · intro p hp
      obtain ⟨ht, hj⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hjt, hjJ, hjB⟩ := Finset.mem_filter.mp hj
      have le := Finset.mem_range.mp hjt
      refine ⟨⟨p.2, p.1 - p.2⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_range.mpr hjJ, Finset.mem_range.mpr hjB⟩, ?_⟩
      apply Sigma.ext
      · dsimp; omega
      · rfl
    · intro p hp
      dsimp
      rw [Nat.add_sub_cancel_left]
  calc
    _ = ∑ p ∈ U, F p.2 (p.1 - p.2) := by
      simpa only [S, Finset.sum_sigma] using bijection
    _ = _ := by
      simp only [U, Finset.sum_sigma, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjJ : j < J
      · rw [ite_eq_left hjJ]
        by_cases hjB : t - j < B j
        · rw [ite_eq_left ⟨hjJ, hjB⟩]
        · rw [ite_eq_right (by tauto), tail j hjJ (t - j) (by omega)]
      · rw [ite_eq_right hjJ, ite_eq_right (by tauto)]

/- proof_shape: actual_ab_joint_outer_support: content
   admission_basis: escape-witness
   escape_witness: Complete-field locality at the independent orders H j
   bounds each complete residue fiber. A finite sigma-set bijection sends
   (j,ell) to (j+ell,j), retaining the original actual inner cutoff K. -/
set_option maxHeartbeats 1600000 in
-- Transport the full locality family before the finite reindexing.
/-- Independent genuine outer locality gives complete joint support and a
finite antidiagonal reindexing of the original actual middle family.
No locality is imposed on a monomial or an ordered half. -/
theorem actual_ab_joint_outer_support
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0) :
    let N := ((K : ℤ) - r).toNat
    let B := fun j : ℕ => ((H j : ℤ) - (d - j)).toNat
    let T := N + ∑ j ∈ Finset.range N, B j
    let f := fun (j : ℕ) k l => lastSourceLocalQ 1 true gamma (r + j) K l k
      (originalRational D a b K P)
    let g := fun (j : ℕ) k l => lastSourceLocalQ 1 false gamma (r + j) K k l
      (originalRational D a b K P)
    (∀ j ∈ Finset.range N, OuterQCompletion 1 (d - j) n (H j) (f j) (g j)) ∧
    (∑ j ∈ Finset.range N, BinomialKernelDelta.chooseSign d j *
      phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
        (qField gamma (r + j) K (targetSlice D hu a gamma)
          (targetSlice D hu b delta)))[[n]]) x)) =
      ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range (t + 1),
        if j < N then BinomialKernelDelta.chooseSign d j *
          (Ring.choose (-(1 : ℂ) / 2) (t - j) *
            completeOuterResidue (d - j) n (f j) (g j) (t - j)) else 0 := by
  classical
  dsimp only
  let N := ((K : ℤ) - r).toNat
  let B := fun j : ℕ => ((H j : ℤ) - (d - j)).toNat
  let f := fun (j : ℕ) k l => lastSourceLocalQ 1 true gamma (r + j) K l k
    (originalRational D a b K P)
  let g := fun (j : ℕ) k l => lastSourceLocalQ 1 false gamma (r + j) K k l
    (originalRational D a b K P)
  have completion (j : ℕ) (hj : j ∈ Finset.range N) :
      OuterQCompletion 1 (d - j) n (H j) (f j) (g j) :=
    actual_ab_outer_completion D hu i a b K K (H j) gamma delta d r n j
      x phi P coefficients (locality j hj)
  refine ⟨completion, ?_⟩
  let F := fun j ell => BinomialKernelDelta.chooseSign d j *
    (Ring.choose (-(1 : ℂ) / 2) ell * completeOuterResidue (d - j) n (f j) (g j) ell)
  have rows :
      (∑ j ∈ Finset.range N, BinomialKernelDelta.chooseSign d j *
        phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta)))[[n]]) x)) =
      ∑ j ∈ Finset.range N, ∑ ell ∈ Finset.range (B j), F j ell := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [(actual_ab_nested_readout D hu i a b K K (H j) gamma delta d r n j
      x phi P coefficients).2.1]
    change BinomialKernelDelta.chooseSign d j *
      supportedQReadout 1 (d - j) (H j) n (f j) (g j) = _
    unfold supportedQReadout
    rw [Finset.mul_sum]
    simp only [F, B, completeOuterResidue, Int.cast_one]
  rw [rows]
  apply finite_joint_antidiagonal N _ B F
  · intro j hj
    have hB : B j ≤ ∑ k ∈ Finset.range N, B k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le (B k)) (Finset.mem_range.mpr hj)
    change j + B j ≤ N + ∑ k ∈ Finset.range N, B k
    omega
  · intro j hj ell hell
    have zero : completeOuterResidue (d - j) n (f j) (g j) ell = 0 := by
      by_contra nonzero
      have inside := (completion j (Finset.mem_range.mpr hj)).1
        (Function.mem_support.mpr nonzero)
      have := Finset.mem_range.mp inside
      change ell < B j at this
      omega
    simp only [F, zero, mul_zero]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout


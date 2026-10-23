/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual source/source nested extraction at independent finite cutoffs. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue

/-! Supported extraction keeps the actual inner cutoff independent of the
finite Laurent supplier and retains the original current/source labels. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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

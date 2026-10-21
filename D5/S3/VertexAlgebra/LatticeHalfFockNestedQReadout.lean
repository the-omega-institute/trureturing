/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three nested ordered residues from one actual ternary Laurent numerator. -/

import D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout

/-! Complete intermediate-field cutoffs precede expansion of the inner
ordered halves. The original source and acted-on tensor carriers stay distinct.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. Hahn operations: mathlib, Apache 2.0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
noncomputable section

local macro "completeQCoefficient" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.qField_mode))

section NestedReadout
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open StateFieldResidueReconstruction

/-- Finite complete residue extraction. The right bound uses the complete
first field on the actual input; it does not bound its ordered halves. -/
def finiteQReadout (s r : ℤ) (K : ℕ) (A B : VertexOperator ℂ V)
    (x : V) (n : ℤ) (forward backward : ℤ → ℤ → ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((∑ u ∈ Finset.range
          (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat,
        BinomialKernelDelta.chooseSign (r + ell) u *
          forward (r + ell - u) (n - ell + u)) -
       epsilon (r + ell) *
        ∑ u ∈ Finset.range (-((HahnModule.of ℂ).symm (A x)).order).toNat,
          BinomialKernelDelta.chooseSign (r + ell) u * backward (r + n - u) u)

private theorem finiteQReadout_eq (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = finiteQReadout s r K A B x n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  classical
  rw [completeQCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul]
  congr 1
  unfold fieldResidueCoefficient fieldResidueLeft fieldResidueRight
  have left := (fieldResidue (r + ell) A B).left_finite (n - ell) x
  have right := (fieldResidue (r + ell) A B).right_finite (n - ell) x
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range
    (-((HahnModule.of ℂ).symm (B x)).order - (n - ell)).toNat) (by
      intro u hu
      apply Finset.mem_range.mpr
      by_contra outside
      have hz : (B[[n - ell + u]]) x = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        omega
      exact hu (by simp [hz]))]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range
    (-((HahnModule.of ℂ).symm (A x)).order).toNat) (by
      intro u hu
      apply Finset.mem_range.mpr
      by_contra outside
      have hz : (A[[(u : ℤ)]]) x = 0 := by
        apply VertexOperator.ncoeff_eq_zero_of_lt_order
        omega
      exact hu (by simp [hz]))]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  simp only [BinomialKernelDelta.chooseSign, integerBinomial,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

private theorem finiteQReadout_congr (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    finiteQReadout s r K A B x n f g = finiteQReadout s r K A B x n f' g' := by
  unfold finiteQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · apply Finset.sum_congr rfl
    intro u hu
    rw [hf _ _ (by omega)]
  · congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [hg _ _ (by omega)]

/-- The six labelled orders, from 012 through 210 in lexicographic order. -/
def triplePermutation (order : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 0 1,
    Equiv.ofBijective ![1, 2, 0] (by decide),
    Equiv.ofBijective ![2, 0, 1] (by decide), Equiv.swap 0 2] order

private def tripleScalar (A B C : VertexOperator ℂ V) (x : V)
    (phi : V →ₗ[ℂ] ℂ) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  phi (coefficientDistribution ![A, B, C] x 1
    (List.ofFn (triplePermutation order)) (fun j => -modes j - 1))

/-- Left nesting, retaining the two inner chambers inside each finite outer
range. Every inner range is recomputed on its actual intermediate vector. -/
def nestedLeftReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  finiteQReadout outerLift r H (qField innerLift d K A B) C x n
    (fun k l => finiteQReadout innerLift d K A B ((C[[l]]) x) k
      (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]))
    (fun k l => finiteQReadout innerLift d K A B x l
      (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k]))

/-- Right nesting with the complete inner field supplying the outer left
cutoff, and the actual first-field input supplying the outer right cutoff. -/
def nestedRightReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  finiteQReadout outerLift r H A (qField innerLift d K B C) x n
    (fun k l => finiteQReadout innerLift d K B C x l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => finiteQReadout innerLift d K B C ((A[[l]]) x) k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m]))

private theorem nestedLeftReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H (qField innerLift d K A B) C)[[n]]) x) =
      nestedLeftReadout outerLift innerLift d r n K H A B C x (tripleScalar A B C x phi) := by
  rw [finiteQReadout_eq]
  unfold nestedLeftReadout
  apply finiteQReadout_congr
  · intro k l hkl
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  · intro k l hkl
    change (phi.comp (C[[k]])) (((qField innerLift d K A B)[[l]]) x) = _
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]

private theorem nestedRightReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H A (qField innerLift d K B C))[[n]]) x) =
      nestedRightReadout outerLift innerLift d r n K H A B C x (tripleScalar A B C x phi) := by
  rw [finiteQReadout_eq]
  unfold nestedRightReadout
  apply finiteQReadout_congr
  · intro k l hkl
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  · intro k l hkl
    rw [finiteQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]

private theorem nestedLeftReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    nestedLeftReadout outerLift innerLift d r n K H A B C x R =
      nestedLeftReadout outerLift innerLift d r n K H A B C x S := by
  unfold nestedLeftReadout
  apply finiteQReadout_congr <;> intro k l hkl <;> apply finiteQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem nestedRightReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    nestedRightReadout outerLift innerLift d r n K H A B C x R =
      nestedRightReadout outerLift innerLift d r n K H A B C x S := by
  unfold nestedRightReadout
  apply finiteQReadout_congr <;> intro k l hkl <;> apply finiteQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

end NestedReadout

/-- The rational readout retains the original global labels, including when
the word is read in a different supported order. -/
def rationalTripleReadout (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  (orderedRationalFor ℂ 3 (triplePermutation order)
    (algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K)))).coeff
    (orderExponents 3 (triplePermutation order) (fun j => -modes j - 1))

/-- Exchange the current and first-source labels without changing the
numerator, its clearing factors, or the six supported orders. -/
def swapCurrentSourceReadout (R : Fin 6 → Exponent 3 → ℂ)
    (order : Fin 6) (modes : Exponent 3) : ℂ :=
  R (![2, 3, 0, 1, 5, 4] order) ![modes 1, modes 0, modes 2]

private theorem tripleScalar_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    tripleScalar B A C x phi = swapCurrentSourceReadout (tripleScalar A B C x phi) := by
  funext order modes
  fin_cases order <;>
    simp [tripleScalar, swapCurrentSourceReadout, triplePermutation,
      coefficientDistribution, word, Module.End.mul_apply, Equiv.swap_apply_def]

local macro "nativeCurrentQ" : term => pure (Lean.mkIdent
  ((Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport 0) ++
    `D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q))

/- proof_shape: actual_nested_ordered_readouts: content
   admission_basis: escape-witness
   escape_witness: finiteQReadout_eq uses the actual complete intermediate
   field order before expanding either inner chamber. The two nested
   extraction lemmas retain all four ordered words. Fixed total mode degree
   then identifies every summand with the same actual Laurent slice in its
   own supported permutation. No local Taylor substitution is assumed. -/
/-- The three genuinely nested Q coefficients are read from one and the same
actual ternary Laurent numerator, for all signed indices and all outer cutoffs.
This is ordered extraction, before the collision-coordinate Taylor identity. -/
theorem actual_nested_ordered_readouts (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftReadout (gamma + 1) 1 d r n (vectorFrequencyBound D a + 1) H₁
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField 1 (d - j) H₂ (targetCurrent D hu i)
            (qField gamma (r + j) K (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x) =
            nestedRightReadout 1 gamma (r + j) (d - j) n K H₂
              (targetCurrent D hu i) (targetSlice D hu a gamma) (targetSlice D hu b delta)
              x (rationalTripleReadout D a b K P) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightReadout gamma 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
              (targetSlice D hu a gamma) (targetCurrent D hu i) (targetSlice D hu b delta)
              x (swapCurrentSourceReadout (rationalTripleReadout D a b K P)) := by
  obtain ⟨K, carriers⟩ := actual_finite_laurent_carriers D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
  obtain ⟨P, coefficients, words⟩ := carriers gamma delta x phi total
  refine ⟨P, coefficients, ?_⟩
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = d + r + n) :
      tripleScalar J A B x phi order modes = rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [if_pos index] at readout
    exact readout.symm
  intro H₁ H₂ H₃ j
  refine ⟨?_, ?_, ?_⟩
  · rw [nativeCurrentQ D hu i a gamma d, nestedLeftReadout_eq]
    exact nestedLeftReadout_congr _ _ _ _ _ _ _ J A B x _ _ same
  · rw [nestedRightReadout_eq]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    omega
  · rw [nativeCurrentQ D hu i b delta j, nestedRightReadout_eq, tripleScalar_swap]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    simp [Fin.sum_univ_three] at degree ⊢
    omega

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

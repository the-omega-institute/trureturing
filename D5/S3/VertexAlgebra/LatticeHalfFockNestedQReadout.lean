/- GID: D5/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockNestedQReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual nested Q readouts and finite signed collision Taylor balance. -/

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
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.qField_mode, map_sum]
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
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i a gamma d, nestedLeftReadout_eq]
    exact nestedLeftReadout_congr _ _ _ _ _ _ _ J A B x _ _ same
  · rw [nestedRightReadout_eq]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    omega
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.current_q D hu i b delta j, nestedRightReadout_eq, tripleScalar_swap]
    apply nestedRightReadout_congr
    intro order modes degree
    apply same
    simp [Fin.sum_univ_three] at degree ⊢
    omega

section CollisionTaylor
open CollisionLaurentKernels.LaurentCollision
open CollisionLaurentKernels.RationalFusedResidue
open CollisionLaurentKernels.SeparatedResidue
open CollisionLaurentKernels.PolynomialCollision
open CollisionRationalExpansions.RationalCoefficientCollision
open CollisionRationalExpansions.SpectatorPole
open CollisionRationalExpansions.PartialFractionCollision

/-- Coefficients of the common fractional collision numerator, before division
by the three pairwise poles. Integer numerator powers are unrestricted. -/
def collisionTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 1 : ℂ) - (gamma : ℂ) / 2) v) P.coeff

/-- The same numerator in the left-associated coordinates h=y-v, t=v-z.
The shift by u is the power of z+t remaining after the first extraction. -/
def associatedTaylor (P : LabelledPolynomial ℂ 3) (gamma : ℤ) (u v : ℕ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 3 =>
    Ring.choose ((e 0 : ℂ) - 1 / 2) u *
      Ring.choose ((e 0 : ℂ) + (e 1 : ℂ) - (u : ℂ) - ((gamma : ℂ) + 1) / 2) v)
    P.coeff

private theorem fractional_coordinate_cocycle (a b : ℂ) (u v : ℕ) :
    Ring.choose a u * Ring.choose (a + b - u) v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * Ring.choose a (u + j) * Ring.choose b (v - j) := by
  have vandermonde := Ring.add_choose_eq (R := ℂ)
    (r := a - u) (s := b) v (Commute.all _ _)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
  rw [show a + b - (u : ℂ) = (a - u) + b by ring, vandermonde, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have product := Ring.choose_smul_choose a (n := u + j) (k := u) (by omega)
  rw [nsmul_eq_mul, Nat.add_sub_cancel_left] at product
  rw [product]
  ring

private theorem associatedTaylor_cocycle (P : LabelledPolynomial ℂ 3)
    (gamma : ℤ) (u v : ℕ) :
    associatedTaylor P gamma u v =
      ∑ j ∈ Finset.range (v + 1),
        ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (v - j) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [associatedTaylor, collisionTaylor]
  | add P Q hP hQ =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_add,
      map_add, mul_add, Finset.sum_add_distrib] at hP hQ ⊢
    rw [hP, hQ]
  | single e c =>
    simp only [associatedTaylor, collisionTaylor, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_eq_mul]
    have cocycle := fractional_coordinate_cocycle
      ((e 0 : ℂ) - 1 / 2) ((e 1 : ℂ) - (gamma : ℂ) / 2) u v
    have exponent : (e 0 : ℂ) - 1 / 2 + ((e 1 : ℂ) - (gamma : ℂ) / 2) - u =
        (e 0 : ℂ) + (e 1 : ℂ) - u - ((gamma : ℂ) + 1) / 2 := by ring
    rw [exponent] at cocycle
    rw [cocycle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def fusedResidueWeight (A k : ℤ) : ℂ :=
  if k < 0 then ((Ring.choose A (-k - 1).toNat : ℤ) : ℂ) else 0

def orderedResidueWeight (k B : ℤ) : ℂ :=
  if B < 0 then BinomialKernelDelta.chooseSign k (-B - 1).toNat else 0

private theorem signed_residue_balance (A B k : ℤ) (total : A + B + k = -2) :
    fusedResidueWeight A k = orderedResidueWeight k B -
      StateFieldResidueReconstruction.epsilon k * orderedResidueWeight k A := by
  by_cases negative : k < 0
  · let m := (-k - 1).toNat
    have kform : k = -(m : ℤ) - 1 := by dsimp [m]; omega
    have h := LatticeHalfFockClearedTaylorReadout.signed_kernel_choose m A
    have bform : B = (m : ℤ) - A - 1 := by omega
    simpa only [fusedResidueWeight, orderedResidueWeight, if_pos negative,
      kform, if_pos (show -(m : ℤ) - 1 < 0 by omega), bform, show -((m : ℤ) - A - 1) - 1 = A - m by omega,
      show (m : ℤ) - A - 1 < 0 ↔ 0 ≤ A - m by omega,
      show A < 0 ↔ 0 ≤ -A - 1 by omega,
      show -(-(m : ℤ) - 1) - 1 = m by omega, Int.toNat_natCast] using h.symm
  · obtain ⟨degree, kform⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    subst k
    have chooseNat (j : ℕ) : BinomialKernelDelta.chooseSign (degree : ℤ) j =
        (-1 : ℂ) ^ j * (degree.choose j : ℂ) := by
      simp [BinomialKernelDelta.chooseSign, Ring.choose_natCast]
    unfold fusedResidueWeight orderedResidueWeight
    rw [if_neg (by omega)]
    by_cases hA : A < 0
    · by_cases hB : B < 0
      · rw [if_pos hA, if_pos hB, chooseNat, chooseNat]
        let a := (-A - 1).toNat
        let b := (-B - 1).toNat
        have split : degree = a + b := by dsimp [a, b]; omega
        have symmetry : degree.choose b = degree.choose a := by
          rw [split, Nat.choose_symm_add]
        have sign : StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
          rw [StateFieldResidueReconstruction.epsilon, zpow_natCast, split,
            pow_add]
          have square : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by
            rw [← mul_pow]; norm_num
          calc
            _ = ((-1 : ℂ) ^ a * (-1 : ℂ) ^ a) * (-1 : ℂ) ^ b := by ring
            _ = _ := by rw [square, one_mul]
        change 0 = (-1 : ℂ) ^ b * (degree.choose b : ℂ) -
          StateFieldResidueReconstruction.epsilon (degree : ℤ) *
            ((-1 : ℂ) ^ a * (degree.choose a : ℂ))
        rw [symmetry, ← mul_assoc, sign, sub_self]
      · rw [if_pos hA, if_neg hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-A - 1).toNat by omega)]
        simp
    · rw [if_neg hA]
      by_cases hB : B < 0
      · rw [if_pos hB, chooseNat,
          Nat.choose_eq_zero_of_lt (show degree < (-B - 1).toNat by omega)]
        simp
      · simp [if_neg hB]

private theorem finite_collision_balance (P : LabelledPolynomial ℂ 3)
    (gamma d r : ℤ) (L M N degree : ℕ)
    (antidiagonal : (degree : ℤ) = L + M + N - d - r - 2) :
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      fusedResidueWeight ((u : ℤ) - M) (d - L)) =
    (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
      orderedResidueWeight (d - L) ((degree - u : ℕ) + r - N)) -
    StateFieldResidueReconstruction.epsilon (d - L) *
      ∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
        orderedResidueWeight (d - L) ((u : ℤ) - M) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have bound : u ≤ degree := by simpa using Finset.mem_range.mp hu
  have total : ((u : ℤ) - M) + ((degree - u : ℕ) + r - N) + (d - L) = -2 := by
    rw [Int.natCast_sub bound]
    omega
  rw [signed_residue_balance _ _ _ total]
  ring

private theorem compatible_coefficient_mul (h : RatFunc ℂ)
    (R : CollisionLaurentKernels.LaurentCollision.Rational ℂ)
    (compatible : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ R) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionRationalExpansions.RationalCoefficientCollision.rationalX ℂ h * R) := by
  simp only [Compatible, map_mul, rationalX_ZX, rationalX_XZ, rationalX_fused,
    residue_outerSeries_mul, resXZ_inner_scalar] at *
  rw [← mul_sub, compatible]

private theorem compatible_sub
    (R S : CollisionLaurentKernels.LaurentCollision.Rational ℂ)
    (hR : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ R)
    (hS : CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ S) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ (R - S) := by
  unfold Compatible at *
  have subZX (F G : ZX ℂ) : resZ_ZX ℂ (F - G) = resZ_ZX ℂ F - resZ_ZX ℂ G := by
    ext n
    simp [resZ_ZX, HahnSeries.map_coeff]
  simp only [map_sub, subZX, resZ_XZ, HahnSeries.coeff_sub] at *
  linear_combination hR - hS

private theorem nonnegative_diagonal_collision (degree : ℕ) (B : ℤ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ B *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ degree) := by
  induction degree generalizing B with
  | zero =>
    have law := separated_rational_collision ℂ (RatFunc.X ^ B) 1
    dsimp only at law
    rw [← fused_residue_commutes] at law
    simpa only [Compatible, pow_zero, mul_one, map_one, one_mul, map_zpow₀,
      LatticeHalfFockLeftCurrentTransport.rational_z] using law.symm
  | succ degree ih =>
    have nz : z ℂ ≠ 0 := by
      unfold z
      simpa only [map_zero] using
        (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne Polynomial.X_ne_zero
    have form : z ℂ ^ B * diagonal ℂ ^ (degree + 1) =
        z ℂ ^ (B + 1) * diagonal ℂ ^ degree -
          rationalX ℂ RatFunc.X * (z ℂ ^ B * diagonal ℂ ^ degree) := by
      rw [zpow_add₀ nz, zpow_one, pow_succ,
        LatticeHalfFockLeftCurrentTransport.rational_x]
      unfold diagonal
      ring
    rw [form]
    exact compatible_sub _ _ (ih (B + 1)) (compatible_coefficient_mul _ _ (ih B))

private theorem signed_laurent_collision (B k : ℤ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ B *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ k) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa only [zpow_natCast] using nonnegative_diagonal_collision degree B
  · by_cases hB : 0 ≤ B
    · obtain ⟨degree, rfl⟩ := Int.eq_ofNat_of_zero_le hB
      simpa only [Compatible, zpow_natCast, zpow_zero, one_mul, Nat.cast_zero, sub_zero] using
        laurent_monomial_collision ℂ 0 degree 0 k
    · let p := (-B).toNat
      let q := (-k).toNat
      have Bform : B = -(p : ℤ) := by dsimp [p]; omega
      have kform : k = -(q : ℤ) := by dsimp [q]; omega
      have law := (negative_laurent_collision p q).2
      rw [← fused_residue_commutes] at law
      simpa only [Compatible, Bform, kform] using law.symm

/-- The rational two-residue chart of the actual Taylor antidiagonal. A
negative antidiagonal gives the empty sum. The remaining z power is -n-1
for the degree slice used by actual_nested_ordered_readouts. -/
def collisionChart (P : LabelledPolynomial ℂ 3) (gamma d r : ℤ) (L M N : ℕ) :
    CollisionLaurentKernels.LaurentCollision.Rational ℂ :=
  let degree : ℤ := L + M + N - d - r - 2
  ∑ u ∈ Finset.range (degree + 1).toNat,
    CollisionRationalExpansions.RationalCoefficientCollision.rationalX ℂ
      ((algebraMap ℂ (RatFunc ℂ) (collisionTaylor P gamma u (degree - u).toNat)) *
        RatFunc.X ^ ((degree - u).toNat + r - N)) *
      (CollisionLaurentKernels.LaurentCollision.z ℂ ^ ((u : ℤ) - M) *
        CollisionLaurentKernels.LaurentCollision.diagonal ℂ ^ (d - L))

private theorem collisionChart_balance (P : LabelledPolynomial ℂ 3)
    (gamma d r : ℤ) (L M N : ℕ) :
    CollisionRationalExpansions.PartialFractionCollision.Compatible ℂ
      (collisionChart P gamma d r L M N) := by
  unfold collisionChart
  apply compatible_sum
  intro u hu
  exact compatible_coefficient_mul _ _ (signed_laurent_collision _ _)

/-- The same actual Laurent numerator obeys the finite fractional coordinate
cocycle and the signed two-residue collision balance. These are chart
identities; identification with the complete nested Q coefficients is separate. -/
theorem actual_collision_taylor_balance (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        (∀ (H₁ H₂ H₃ : ℕ) (j : ℤ),
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
              x (swapCurrentSourceReadout (rationalTripleReadout D a b K P))) ∧
        (∀ u v : ℕ, associatedTaylor P gamma u v =
          ∑ j ∈ Finset.range (v + 1),
            ((u + j).choose u : ℂ) * collisionTaylor P gamma (u + j) (v - j)) ∧
        (let R := collisionChart P gamma d r
          (vectorFrequencyBound D a + 1) (vectorFrequencyBound D b + 1) K
         resZ_XZ ℂ (iotaFused ℂ R) =
           resZ_ZX ℂ (iotaZX ℂ R) - resZ_XZ ℂ (iotaXZ ℂ R)) ∧
        ∀ degree : ℕ,
          (degree : ℤ) = (vectorFrequencyBound D a + 1 : ℕ) +
            (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2 →
          (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
            fusedResidueWeight ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℕ))
              (d - (vectorFrequencyBound D a + 1 : ℕ))) =
          (∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
            orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
              ((degree - u : ℕ) + r - K)) -
          StateFieldResidueReconstruction.epsilon (d - (vectorFrequencyBound D a + 1 : ℕ)) *
            ∑ u ∈ Finset.range (degree + 1), collisionTaylor P gamma u (degree - u) *
              orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
                ((u : ℤ) - (vectorFrequencyBound D b + 1 : ℕ)) := by
  obtain ⟨K, actual⟩ := actual_nested_ordered_readouts D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  obtain ⟨P, coefficients, readouts⟩ := actual gamma delta d r n x phi
  refine ⟨P, coefficients, readouts, associatedTaylor_cocycle P gamma, ?_, ?_⟩
  · exact (collisionChart_balance P gamma d r _ _ _).symm
  · intro degree antidiagonal
    exact finite_collision_balance P gamma d r _ _ _ degree antidiagonal

/-- Exact remaining identification with the complete nested Q products.
This proposition is unproved; it is not a hypothesis of a delivered theorem.
The numerator is fixed by its actual coefficient equation. Outer locality
orders apply to complete fields, independently for each intermediate Q. -/
def sameNumeratorCollisionBridge (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) (K : ℕ) (gamma delta d r : ℤ) : Prop :=
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  let Ad := targetSlice D hu (neutralMode D i d a) (gamma + 1)
  let Bj := fun j : ℕ => targetSlice D hu (neutralMode D i j b) (delta + 1)
  let L := vectorFrequencyBound D a + 1
  let M := vectorFrequencyBound D b + 1
  let degree : ℤ := L + M + K - d - r - 2
  ∀ (n : ℤ) (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3),
    (∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0) →
    ∀ (H₁ : ℕ) (H₂ H₃ : ℕ → ℕ),
      (FieldNormalProductLocality.deltaEnd ^ H₁)
        (FieldNormalProductLocality.commutator Ad B) = 0 →
      (∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
        (FieldNormalProductLocality.deltaEnd ^ H₂ j)
          (FieldNormalProductLocality.commutator J (qField gamma (r + j) K A B)) = 0) →
      (∀ j ∈ Finset.range M,
        (FieldNormalProductLocality.deltaEnd ^ H₃ j)
          (FieldNormalProductLocality.commutator A (Bj j)) = 0) →
      phi (((qField (gamma + 1) r H₁ Ad B)[[n]]) x) =
        (∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            fusedResidueWeight ((u : ℤ) - M) (d - L)) ∧
      (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
        BinomialKernelDelta.chooseSign d j *
          phi (((qField 1 (d - j) (H₂ j) J (qField gamma (r + j) K A B))[[n]]) x)) =
        (∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) (degree - u + r - K)) ∧
      StateFieldResidueReconstruction.epsilon d *
        (∑ j ∈ Finset.range M, BinomialKernelDelta.chooseSign d j *
          phi (((qField gamma (d + r - j) (H₃ j) A (Bj j))[[n]]) x)) =
        StateFieldResidueReconstruction.epsilon (d - L) *
          ∑ u ∈ Finset.range (degree + 1).toNat,
            collisionTaylor P gamma u (degree - u).toNat *
              orderedResidueWeight (d - L) ((u : ℤ) - M)

end CollisionTaylor


end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

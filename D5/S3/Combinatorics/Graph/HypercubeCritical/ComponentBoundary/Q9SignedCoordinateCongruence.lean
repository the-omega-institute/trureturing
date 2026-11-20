/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedCoordinateCongruence
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Triangle congruence for signed coordinate pairings of balanced cubic Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-! The signed coordinate triangle relation in §4 of q9-saturated-tree-square-pro.txt,
summed over the full cube. The integer witness is the signed three-step pairing. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip flip_adj gamma gamma_apply IsSwitching switchingVector)
open private huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private intCoeff intCoeff_cast matrix_zero_of_not_adj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangIntegralNormGap
open private flip_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open BalancedCubeGirth (gamma_anticommute)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private gamma_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

/-- The full-cube signed count for the ordered coordinate pair `i,j`. -/
def signedPairing (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ) (i j : Fin 9) : ℝ :=
  switchingVector C σ ⬝ᵥ gamma i (gamma j (switchingVector D τ))

/-- The full-cube signed count for the ordered coordinate triple `i,j,k`. -/
def signedTriplePairing (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ) (i j k : Fin 9) : ℝ :=
  switchingVector C σ ⬝ᵥ gamma i (gamma j (gamma k (switchingVector D τ)))

private theorem gamma_lsum (z : Q 9 → ℝ) :
    (∑ i : Fin 9, gamma i z) = (huangMatrix 9).mulVec z := by
  classical
  funext x
  simp only [Finset.sum_apply, gamma_apply, Matrix.mulVec, dotProduct]
  calc
    _ = ∑ y ∈ Finset.univ.image (BalancedCriticalSpectrum.flip x), huangMatrix 9 x y * z y := by
      rw [Finset.sum_image (fun i _ j _ h => flip_injective x h)]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      have hna : ¬ (hypercube 9).Adj x y := by
        intro hadj
        obtain ⟨i, rfl⟩ := adjacent_exists_flip hadj
        exact hy (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      rw [matrix_zero_of_not_adj x y hna, zero_mul]

private theorem gamma_dotProduct (a : Fin 9) (f g : Q 9 → ℝ) :
    f ⬝ᵥ gamma a g = gamma a f ⬝ᵥ g := by
  let e : Q 9 ≃ Q 9 :=
    { toFun := fun x => flip x a
      invFun := fun x => flip x a
      left_inv := fun x => BalancedCriticalSpectrum.flip_flip x a
      right_inv := fun x => BalancedCriticalSpectrum.flip_flip x a }
  calc
    _ = ∑ x, f (e x) * gamma a g (e x) :=
      (e.sum_comp (fun x => f x * gamma a g x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      change f (flip x a) * gamma a g (flip x a) = gamma a f x * g x
      rw [gamma_apply, gamma_apply, BalancedCriticalSpectrum.flip_flip,
        huangMatrix_symmetric (flip x a) x]
      ring

private theorem triangle_anticommutator {i j k : Fin 9} (z : Q 9 → ℝ) :
    (huangMatrix 9).mulVec (gamma i (gamma j (gamma k z))) +
      gamma i (gamma j (gamma k ((huangMatrix 9).mulVec z))) =
      (2 : ℝ) • (gamma j (gamma k z) - gamma i (gamma k z) + gamma i (gamma j z)) := by
  have clifford (a b : Fin 9) (w : Q 9 → ℝ) :
      gamma a (gamma b w) + gamma b (gamma a w) =
        (if a = b then (2 : ℝ) else 0) • w := by
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left rfl, gamma_square, two_smul]
    · rw [ite_eq_right hab, zero_smul, gamma_anticommute hab w, neg_add_cancel]
  have hcoord (a : Fin 9) :
      gamma a (gamma i (gamma j (gamma k z))) +
        gamma i (gamma j (gamma k (gamma a z))) =
        (if a = i then (2 : ℝ) else 0) • gamma j (gamma k z) -
          (if a = j then (2 : ℝ) else 0) • gamma i (gamma k z) +
          (if a = k then (2 : ℝ) else 0) • gamma i (gamma j z) := by
    have hi := clifford a i (gamma j (gamma k z))
    have hj := congrArg (fun w => gamma i w) (clifford a j (gamma k z))
    have hk := congrArg (fun w => gamma i (gamma j w)) (clifford a k z)
    simp only [map_add, map_smul] at hj hk
    calc
      _ = (gamma a (gamma i (gamma j (gamma k z))) +
            gamma i (gamma a (gamma j (gamma k z)))) -
          (gamma i (gamma a (gamma j (gamma k z))) +
            gamma i (gamma j (gamma a (gamma k z)))) +
          (gamma i (gamma j (gamma a (gamma k z))) +
            gamma i (gamma j (gamma k (gamma a z)))) := by abel
      _ = _ := by rw [hi, hj, hk]
  calc
    _ = ∑ a : Fin 9, (gamma a (gamma i (gamma j (gamma k z))) +
        gamma i (gamma j (gamma k (gamma a z)))) := by
      rw [Finset.sum_add_distrib, gamma_lsum]
      simp only [← map_sum, gamma_lsum]
    _ = _ := by
      simp only [hcoord, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_add, smul_sub]

open Classical in
/-- For balanced induced cubic supports, the signed triangle sum equals three times
the signed triple pairing. -/
theorem signedPairing_triangle (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (i j k : Fin 9) :
    signedPairing C D σ τ i j + signedPairing C D σ τ j k - signedPairing C D σ τ i k =
      3 * signedTriplePairing C D σ τ i j k := by
  let f := switchingVector C σ
  let g := switchingVector D τ
  have hf : (huangMatrix 9).mulVec f = (3 : ℝ) • f :=
    BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C σ hC hσ
  have hg : (huangMatrix 9).mulVec g = (3 : ℝ) • g :=
    BalancedCriticalSpectrum.ambient_eigenvector (d := 3) D τ hD hτ
  have hleft (w : Q 9 → ℝ) : f ⬝ᵥ (huangMatrix 9).mulVec w =
      (huangMatrix 9).mulVec f ⬝ᵥ w := by
    rw [← gamma_lsum w, ← gamma_lsum f, dotProduct_sum, sum_dotProduct]
    exact Finset.sum_congr rfl fun a _ => gamma_dotProduct a f w
  have h := congrArg (fun w => f ⬝ᵥ w) (triangle_anticommutator (i := i) (j := j) (k := k) g)
  rw [dotProduct_add, hleft, hf, smul_dotProduct, hg, map_smul, map_smul, map_smul,
    dotProduct_smul, dotProduct_smul, dotProduct_add, dotProduct_sub] at h
  change f ⬝ᵥ gamma i (gamma j g) + f ⬝ᵥ gamma j (gamma k g) -
    f ⬝ᵥ gamma i (gamma k g) = 3 * (f ⬝ᵥ gamma i (gamma j (gamma k g)))
  simp only [smul_eq_mul] at h
  linarith

private def intSwitchingVector (C : Finset (Q 9)) (σ : Q 9 → ℝ) (x : Q 9) : ℤ :=
  ⌊switchingVector C σ x⌋

private theorem intSwitchingVector_cast {C : Finset (Q 9)} {σ : Q 9 → ℝ}
    (hs : IsSwitching C σ) :
    (fun x => (intSwitchingVector C σ x : ℝ)) = switchingVector C σ := by
  funext x
  by_cases hx : x ∈ C
  · rcases hs.1 x hx with h | h <;> norm_num [intSwitchingVector, switchingVector, hx, h]
  · norm_num [intSwitchingVector, switchingVector, hx]

private def intGamma (i : Fin 9) (z : Q 9 → ℤ) (x : Q 9) : ℤ :=
  intCoeff x (flip x i) * z (flip x i)

private theorem intGamma_cast (i : Fin 9) (z : Q 9 → ℤ) :
    (fun x => (intGamma i z x : ℝ)) = gamma i (fun x => (z x : ℝ)) := by
  funext x
  simp only [intGamma, Int.cast_mul, intCoeff_cast, gamma_apply]

/-- Integer signed count using the actual Huang coefficients along the ordered pair. -/
def signedPairingInt (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ) (i j : Fin 9) : ℤ :=
  intSwitchingVector C σ ⬝ᵥ intGamma i (intGamma j (intSwitchingVector D τ))

/-- Integer signed count using the actual Huang coefficients along the ordered triple. -/
def signedTriplePairingInt (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ) (i j k : Fin 9) : ℤ :=
  intSwitchingVector C σ ⬝ᵥ intGamma i (intGamma j (intGamma k (intSwitchingVector D τ)))

private theorem int_dotProduct_cast (f g : Q 9 → ℤ) :
    ((f ⬝ᵥ g : ℤ) : ℝ) = (fun x => (f x : ℝ)) ⬝ᵥ (fun x => (g x : ℝ)) := by
  simp only [dotProduct, Int.cast_sum, Int.cast_mul]

/-- The integral two-step count agrees with the real Huang pairing. -/
theorem signedPairingInt_cast {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ) (i j : Fin 9) :
    (signedPairingInt C D σ τ i j : ℝ) = signedPairing C D σ τ i j := by
  simp only [signedPairingInt, int_dotProduct_cast, intGamma_cast,
    intSwitchingVector_cast hσ, intSwitchingVector_cast hτ, signedPairing]

/-- The integral three-step count agrees with the real Huang pairing. -/
theorem signedTriplePairingInt_cast {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ) (i j k : Fin 9) :
    (signedTriplePairingInt C D σ τ i j k : ℝ) = signedTriplePairing C D σ τ i j k := by
  simp only [signedTriplePairingInt, int_dotProduct_cast, intGamma_cast,
    intSwitchingVector_cast hσ, intSwitchingVector_cast hτ, signedTriplePairing]

open Classical in
/-- The integer signed counts satisfy the triangle congruence modulo three. -/
theorem signedPairingInt_triangle_mod3 (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (i j k : Fin 9) :
    3 ∣ signedPairingInt C D σ τ i j + signedPairingInt C D σ τ j k -
      signedPairingInt C D σ τ i k := by
  refine ⟨signedTriplePairingInt C D σ τ i j k, ?_⟩
  apply Int.cast_injective (α := ℝ)
  push_cast
  simpa only [signedPairingInt_cast hσ hτ, signedTriplePairingInt_cast hσ hτ] using
    signedPairing_triangle C D σ τ hC hD hσ hτ i j k

open Classical in
/-- Separation forces every row sum of the full-cube signed counts to vanish. -/
theorem signedPairing_row_sum (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (i : Fin 9) :
    ∑ j : Fin 9, signedPairing C D σ τ i j = 0 := by
  have hg := BalancedCriticalSpectrum.ambient_eigenvector (d := 3) D τ hD hτ
  have hstep : switchingVector C σ ⬝ᵥ gamma i (switchingVector D τ) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ C
    · have hy : flip x i ∉ D := fun h => hsep x hx _ h (flip_adj x i)
      simp [gamma_apply, switchingVector, hy]
    · simp [switchingVector, hx]
  simp only [signedPairing]
  rw [← dotProduct_sum, ← map_sum, gamma_lsum, hg, map_smul, dotProduct_smul, hstep, smul_zero]

#print axioms signedPairing_triangle
#print axioms signedPairingInt_cast
#print axioms signedTriplePairingInt_cast
#print axioms signedPairingInt_triangle_mod3
#print axioms signedPairing_row_sum

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

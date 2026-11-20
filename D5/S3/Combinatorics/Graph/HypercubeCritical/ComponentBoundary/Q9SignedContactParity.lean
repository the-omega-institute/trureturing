/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactParity
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Parity equality for signed two-step contacts of separated balanced cubic Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

/-! The parity split of the signed coordinate pairings from §4 of
q9-saturated-tree-square-pro.txt. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactParity

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q flip flip_adj gamma gamma_apply IsSwitching switchingVector ambient_eigenvector anticommutator)
open Q9SignedCoordinateCongruence (signedPairingInt signedPairingInt_cast
  signedPairingInt_triangle_mod3 signedPairing_row_sum)
open private cubeParity cubeParity_ne_of_adj huangMatrix huangMatrix_symmetric from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private gamma_lsum intSwitchingVector intSwitchingVector_cast intGamma intGamma_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedCoordinateCongruence

/-- The two-step Huang pairing summed over one global parity, with `false` denoting even. -/
def signedPairingOnParity (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (p : Bool) (i j : Fin 9) : ℝ :=
  ∑ x ∈ Finset.univ with cubeParity x = p,
    switchingVector C σ x * gamma i (gamma j (switchingVector D τ)) x

/-- The same parity-restricted pairing using integer coefficients and switching signs. -/
def signedPairingOnParityInt (C D : Finset (Q 9)) (σ τ : Q 9 → ℝ)
    (p : Bool) (i j : Fin 9) : ℤ :=
  ∑ x ∈ Finset.univ with cubeParity x = p,
    intSwitchingVector C σ x * intGamma i (intGamma j (intSwitchingVector D τ)) x

private def paritySign (x : Q 9) : ℝ :=
  if cubeParity x then -1 else 1

private def parityMultiply (f : Q 9 → ℝ) (x : Q 9) : ℝ :=
  paritySign x * f x

private theorem gamma_parityMultiply (i : Fin 9) (f : Q 9 → ℝ) :
    gamma i (parityMultiply f) = -parityMultiply (gamma i f) := by
  funext x
  have hne := cubeParity_ne_of_adj (flip_adj x i)
  have hsign : paritySign (flip x i) = -paritySign x := by
    cases hx : cubeParity x <;> cases hy : cubeParity (flip x i) <;>
      simp_all [paritySign]
  rw [gamma_apply]
  change huangMatrix 9 x (flip x i) * (paritySign (flip x i) * f (flip x i)) =
    -(paritySign x * gamma i f x)
  rw [gamma_apply, hsign]
  ring

private theorem huang_parityMultiply (f : Q 9 → ℝ) :
    (huangMatrix 9).mulVec (parityMultiply f) =
      -parityMultiply ((huangMatrix 9).mulVec f) := by
  rw [← gamma_lsum (parityMultiply f), ← gamma_lsum f]
  simp only [gamma_parityMultiply, Finset.sum_neg_distrib]
  funext x
  simp only [Pi.neg_apply, parityMultiply, Finset.sum_apply, Finset.mul_sum]

private theorem pair_commutator (i j : Fin 9) (g : Q 9 → ℝ) :
    (huangMatrix 9).mulVec (gamma i (gamma j g)) -
      gamma i (gamma j ((huangMatrix 9).mulVec g)) =
      (2 : ℝ) • (gamma j g - gamma i g) := by
  have hi := anticommutator i (gamma j g)
  have hj := congrArg (fun w => gamma i w) (anticommutator j g)
  simp only [map_add, map_smul] at hj
  calc
    _ = ((huangMatrix 9).mulVec (gamma i (gamma j g)) +
          gamma i ((huangMatrix 9).mulVec (gamma j g))) -
        (gamma i ((huangMatrix 9).mulVec (gamma j g)) +
          gamma i (gamma j ((huangMatrix 9).mulVec g))) := by abel
    _ = _ := by rw [hi, hj, smul_sub]

open Classical in
private theorem parity_dotProduct_eq_zero {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (i j : Fin 9) :
    parityMultiply (switchingVector C σ) ⬝ᵥ gamma i (gamma j (switchingVector D τ)) = 0 := by
  let f := switchingVector C σ
  let g := switchingVector D τ
  have hf : (huangMatrix 9).mulVec f = (3 : ℝ) • f := ambient_eigenvector (d := 3) C σ hC hσ
  have hg : (huangMatrix 9).mulVec g = (3 : ℝ) • g := ambient_eigenvector (d := 3) D τ hD hτ
  have hfneg : (huangMatrix 9).mulVec (parityMultiply f) = (-3 : ℝ) • parityMultiply f := by
    rw [huang_parityMultiply, hf]
    funext x
    simp only [Pi.neg_apply, parityMultiply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsym : (huangMatrix 9).IsSymm :=
    Matrix.IsSymm.ext (fun x y => huangMatrix_symmetric y x)
  have hleft (w : Q 9 → ℝ) : parityMultiply f ⬝ᵥ (huangMatrix 9).mulVec w =
      (huangMatrix 9).mulVec (parityMultiply f) ⬝ᵥ w := by
    rw [hsym.dotProduct_mulVec_comm, dotProduct_comm]
  have hstep (a : Fin 9) : parityMultiply f ⬝ᵥ gamma a g = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ C
    · have hy : flip x a ∉ D := fun hy => hsep x hx _ hy (flip_adj x a)
      simp [gamma_apply, g, switchingVector, hy]
    · simp [parityMultiply, f, switchingVector, hx]
  have h := congrArg (fun w => parityMultiply f ⬝ᵥ w) (pair_commutator i j g)
  change parityMultiply f ⬝ᵥ gamma i (gamma j g) = 0
  simp only [dotProduct_sub, hleft, hfneg, smul_dotProduct, hg, map_smul, dotProduct_smul,
    hstep, smul_eq_mul, sub_self, mul_zero] at h
  linarith

open Classical in
/-- Separated balanced cubic supports have equal even and odd signed two-step pairings. -/
theorem signedPairingOnParity_eq {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (i j : Fin 9) :
    signedPairingOnParity C D σ τ false i j = signedPairingOnParity C D σ τ true i j := by
  apply sub_eq_zero.mp
  calc
    _ = parityMultiply (switchingVector C σ) ⬝ᵥ gamma i (gamma j (switchingVector D τ)) := by
      simp only [signedPairingOnParity, Finset.sum_filter, ← Finset.sum_sub_distrib, dotProduct]
      apply Finset.sum_congr rfl
      intro x _
      cases hx : cubeParity x <;> simp [hx, parityMultiply, paritySign]
    _ = 0 := parity_dotProduct_eq_zero hC hD hσ hτ hsep i j

private theorem signedPairingOnParityInt_cast {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ) (p : Bool) (i j : Fin 9) :
    (signedPairingOnParityInt C D σ τ p i j : ℝ) = signedPairingOnParity C D σ τ p i j := by
  simp only [signedPairingOnParityInt, signedPairingOnParity, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro x _
  have hf := congrFun (intSwitchingVector_cast hσ) x
  have hg : (fun y => (intGamma i (intGamma j (intSwitchingVector D τ)) y : ℝ)) =
      gamma i (gamma j (switchingVector D τ)) := by
    rw [intGamma_cast, intGamma_cast, intSwitchingVector_cast hτ]
  rw [hf, congrFun hg x]

private theorem signedPairingOnParityInt_add {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (p : Bool) (i j : Fin 9) :
    signedPairingOnParityInt C D σ τ p i j + signedPairingOnParityInt C D σ τ (!p) i j =
      signedPairingInt C D σ τ i j := by
  simp only [signedPairingOnParityInt, signedPairingInt, dotProduct]
  have hneg (x : Q 9) : cubeParity x = !p ↔ ¬ cubeParity x = p := by
    cases p <;> cases cubeParity x <;> decide
  simp only [hneg]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

open Classical in
/-- The integer pairings on opposite global parities coincide. -/
theorem signedPairingOnParityInt_eq {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) (i j : Fin 9) :
    signedPairingOnParityInt C D σ τ p i j = signedPairingOnParityInt C D σ τ (!p) i j := by
  apply Int.cast_injective (α := ℝ)
  simp only [signedPairingOnParityInt_cast hσ hτ]
  have h := signedPairingOnParity_eq hC hD hσ hτ hsep i j
  cases p
  · exact h
  · exact h.symm

open Classical in
private theorem signedPairingInt_eq_twice {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) (i j : Fin 9) :
    signedPairingInt C D σ τ i j = 2 * signedPairingOnParityInt C D σ τ p i j := by
  rw [← signedPairingOnParityInt_add p, ← signedPairingOnParityInt_eq hC hD hσ hτ hsep p, two_mul]

open Classical in
/-- The signed triangle relation holds modulo three on each global parity. -/
theorem signedPairingOnParityInt_triangle_mod3 {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) (i j k : Fin 9) :
    3 ∣ signedPairingOnParityInt C D σ τ p i j + signedPairingOnParityInt C D σ τ p j k -
      signedPairingOnParityInt C D σ τ p i k := by
  obtain ⟨w, hw⟩ := signedPairingInt_triangle_mod3 C D σ τ hC hD hσ hτ i j k
  simp only [signedPairingInt_eq_twice hC hD hσ hτ hsep p] at hw
  refine ⟨signedPairingOnParityInt C D σ τ p i j + signedPairingOnParityInt C D σ τ p j k -
    signedPairingOnParityInt C D σ τ p i k - w, ?_⟩
  omega

open Classical in
/-- Every integer row sum vanishes on each global parity. -/
theorem signedPairingOnParityInt_row_sum {C D : Finset (Q 9)} {σ τ : Q 9 → ℝ}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hσ : IsSwitching C σ) (hτ : IsSwitching D τ)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y) (p : Bool) (i : Fin 9) :
    ∑ j : Fin 9, signedPairingOnParityInt C D σ τ p i j = 0 := by
  have hfull : ∑ j : Fin 9, signedPairingInt C D σ τ i j = 0 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_sum, Int.cast_zero, signedPairingInt_cast hσ hτ] using
      signedPairing_row_sum C D σ τ hD hτ hsep i
  simp only [signedPairingInt_eq_twice hC hD hσ hτ hsep p, ← Finset.mul_sum] at hfull
  omega

#print axioms signedPairingOnParity_eq
#print axioms signedPairingOnParityInt_eq
#print axioms signedPairingOnParityInt_triangle_mod3
#print axioms signedPairingOnParityInt_row_sum

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactParity

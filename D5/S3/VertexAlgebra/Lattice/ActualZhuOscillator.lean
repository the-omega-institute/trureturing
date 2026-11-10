/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuOscillator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuOscillator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal negative-current reduction and all-charge oscillator normal form. -/
/-
Dong--Li--Mason, DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11.
The higher-circle numerator is shifted; Pascal triangular elimination recovers
fixed-numerator current relations in the original literal O-space.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuGroundCurrent
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Eval

/-! Source-side oscillator reduction on the full original charge carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuOscillator
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualConformalState LatticePositiveEnergy
open ActualZhuProduct ActualZhuFinite ActualZhuAlgebra ActualZhuGroundCurrent
open scoped BigOperators VertexOperator
noncomputable section

private theorem pascal_sum {D : LatticeData} (n : ℕ) (f : ℕ → Carrier D) :
    (∑ j ∈ Finset.range (n+2), ((n+1).choose j : ℂ) • f j) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) • (f j + f (j+1)) := by
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun j => ((n+1).choose j : ℂ) • f j),
    Finset.sum_range_succ' (fun j => (n.choose j : ℂ) • f j),
    Finset.sum_range_succ (fun j => ((n+1).choose (j+1) : ℂ) • f (j+1)),
    Finset.sum_range_succ (fun j => (n.choose j : ℂ) • f (j+1))]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, Nat.choose_self]
  have hp : (∑ j ∈ Finset.range n, ((n+1).choose (j+1) : ℂ) • f (j+1)) =
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) • f (j+1)) +
      (∑ j ∈ Finset.range n, (n.choose j : ℂ) • f (j+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ, Nat.cast_add, add_smul]
    abel
  rw [hp]
  abel

/-- The higher-circle row is a triangular combination of fixed-numerator rows. -/
theorem current_higherCircle (D : LatticeData) (i : Fin D.rank) (v : Carrier D) (n : ℕ) :
    higherCircle D 1 (currentState D i) v n =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
        (neutralMode D i ((j : ℤ)-2-n) v + neutralMode D i ((j : ℤ)-1-n) v) := by
  rw [higherCircle]
  simp only [mu, current_state_field, neutralField_ncoeff]
  rw [show 1+n+1 = n+2 by omega, show 1+n = n+1 by omega, pascal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (((j+1 : ℕ) : ℤ)-2-n) = (j : ℤ)-1-n by omega]

/-- Every fixed-numerator negative-current row belongs to the literal O-space. -/
theorem current_pair_mem_zhuO (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (v : Carrier D) (n : ℕ) :
    neutralMode D i (-(n : ℤ)-2) v + neutralMode D i (-(n : ℤ)-1) v ∈ zhuO D := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := higherCircle_mem_zhuO D hD (current_grade D i) v n
    rw [current_higherCircle, Finset.sum_range_succ'] at hc
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, Nat.cast_zero,
      zero_sub] at hc
    have ht : (∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
        (neutralMode D i (((j+1 : ℕ) : ℤ)-2-n) v +
          neutralMode D i (((j+1 : ℕ) : ℤ)-1-n) v)) ∈ zhuO D := by
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      have hj' := Finset.mem_range.mp hj
      rw [show (((j+1 : ℕ) : ℤ)-2-n) = -((n-(j+1) : ℕ) : ℤ)-2 by omega,
        show (((j+1 : ℕ) : ℤ)-1-n) = -((n-(j+1) : ℕ) : ℤ)-1 by omega]
      exact ih (n-(j+1)) (by omega)
    rw [show (-2 : ℤ)-n = -(n : ℤ)-2 by omega,
      show (-1 : ℤ)-n = -(n : ℤ)-1 by omega] at hc
    simpa only [add_sub_cancel_left] using (zhuO D).sub_mem hc ht

/-- Native physical h_i(-n-1) is (-1)^n times h_i(-1) modulo literal O. -/
theorem negative_current_class (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (v : Carrier D) (n : ℕ) :
    (zhuO D).mkQ (neutralMode D i (-(n : ℤ)-1) v) =
      (-1 : ℂ)^n • (zhuO D).mkQ (neutralMode D i (-1) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : (zhuO D).mkQ
        (neutralMode D i (-(n : ℤ)-2) v + neutralMode D i (-(n : ℤ)-1) v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (current_pair_mem_zhuO D hD i v n)
    rw [map_add, ih] at hz
    rw [show (-((n+1 : ℕ) : ℤ)-1) = -(n : ℤ)-2 by omega]
    rw [pow_succ, mul_smul, neg_one_smul]
    simpa only [smul_neg] using eq_neg_of_add_eq_zero_left hz

/-- Replacement holds with every oscillator tail and every charge. -/
theorem oscillator_variable_class (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (δ : Charge D) (i : Fin D.rank) (n : ℕ) (p : Oscillator D) :
    (zhuO D).mkQ (Finsupp.single δ (MvPolynomial.X (i,n) * p)) =
      (-1 : ℂ)^n • (zhuO D).mkQ (Finsupp.single δ (MvPolynomial.X (i,0) * p)) := by
  have he := negative_current_class D hD i (Finsupp.single δ p) n
  simpa [neutralMode_single, neutralPolynomialMode,
    show -(n : ℤ)-1 < 0 by omega] using he

#print axioms current_pair_mem_zhuO
#print axioms oscillator_variable_class
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuOscillator

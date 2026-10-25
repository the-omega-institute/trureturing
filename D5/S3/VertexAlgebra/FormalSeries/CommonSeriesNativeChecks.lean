import D5.S3.VertexAlgebra.Sectors.LatticeSectorThreeFieldCommonSeries

/-! Transient exact applications at empty, singleton and indefinite boundaries. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open D5.S3.VertexAlgebra
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open LatticeSectorThreeFieldCommonSeries
open scoped VertexOperator

-- The empty word has a nonzero recovered coefficient, with input 1.
example : ∃ P : MvPowerSeries (Fin 0) ℂ, P 0 = 1 := by
  let A : Fin 0 → VertexOperator ℂ ℂ := fun i => Fin.elim0 i
  obtain ⟨k, _, h⟩ := ungraded_local_word_common_series A [] (by simp)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨a, P, _, _, common⟩ := h 1
  refine ⟨P, ?_⟩
  have h := common [] (List.Perm.refl []) (fun _ => 0)
  have hidx : signedIndex (fun _ : Fin 0 => 0) = 0 := by
    ext i
    exact Fin.elim0 i
  simpa [clearingPolynomial, labelledPairs, coefficientDistribution, word,
    signedExtend, hidx] using h.symm

-- A singleton label imposes no locality premise, for an arbitrary module.
example {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) :
    type_of% (ungraded_local_word_common_series (fun _ : Fin 1 => A) [0]
      (by simp) (by intro i; fin_cases i; simp)
      (by intro i j hij; fin_cases i; fin_cases j; omega)) := by
  exact ungraded_local_word_common_series (fun _ : Fin 1 => A) [0]
    (by simp) (by intro i; fin_cases i; simp)
    (by intro i j hij; fin_cases i; fin_cases j; omega)

private abbrev zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric _ _ := rfl
  even_diagonal _ := ⟨0, by simp⟩

-- All three original fields coincide on rank zero; input states are nonzero.
example : type_of% (actual_three_field_common_series zeroLattice 0 0 0 1 1 1) :=
  actual_three_field_common_series zeroLattice 0 0 0 1 1 1

private abbrev indefiniteLattice : LatticeData where
  rank := 2
  G := Matrix.diagonal ![2, -2]
  symmetric i j := by
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  even_diagonal i := by
    fin_cases i <;> norm_num [Matrix.diagonal]

example : bilinear indefiniteLattice ![1, 0] ![1, 0] = 2 := by
  norm_num [bilinear, indefiniteLattice, Fin.sum_univ_succ, Matrix.diagonal]

example : bilinear indefiniteLattice ![0, 1] ![0, 1] = -2 := by
  norm_num [bilinear, indefiniteLattice, Fin.sum_univ_succ, Matrix.diagonal]

-- A nonzero descendant on each sign of the form, with signed nonzero charges.
example : type_of% (actual_three_field_common_series indefiniteLattice
    ![1, -1] ![0, 1] ![1, -1]
    (MvPolynomial.X (0, 0)) (MvPolynomial.X (1, 1) ^ 2) (1 : Oscillator indefiniteLattice)) :=
  actual_three_field_common_series indefiniteLattice
    ![1, -1] ![0, 1] ![1, -1]
    (MvPolynomial.X (0, 0)) (MvPolynomial.X (1, 1) ^ 2) (1 : Oscillator indefiniteLattice)

-- Check the negative signed region of the actual all-six-orders conclusion.
example : ∃ k : ℕ, ∃ a : Fin 3 → ℕ,
    polynomialAction (clearingPolynomial 3 k)
      (nestedCanonical zeroLattice ![0, 0, 0] ![1, 1, 1] 0 1 0 1 2)
      (fun i => (![(-1 : ℤ), 0, 0] : Exponent 3) i - a i) = 0 := by
  obtain ⟨k, _, h⟩ := actual_three_field_common_series zeroLattice 0 0 0 1 1 1
  obtain ⟨a, P, _, common⟩ := h 0 1
  refine ⟨k, a, ?_⟩
  have negative : ¬ ∀ i : Fin 3, 0 ≤ (![(-1 : ℤ), 0, 0] : Exponent 3) i := by
    intro hn
    have h0 := hn 0
    norm_num at h0
  simpa [signedExtend, negative] using (common ![(-1 : ℤ), 0, 0]).1

#print axioms ungraded_local_word_common_series
#print axioms actual_three_field_common_series
#check @actual_three_field_common_series

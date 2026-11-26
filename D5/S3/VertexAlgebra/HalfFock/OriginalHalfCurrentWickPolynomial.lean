/- GID: D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite creator and correction recursion for the actual lowering flow. -/

import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

/-! The Wick creation and contraction branches have finite polynomial
coefficients on the original oscillator vacuum. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalHalfCurrentTransport (creationPart contraction contractionScalar normalOrder
  lowering_normal_order_word)
open TwistedGround.OriginalFourMChargeCoset (oscillatorLower)
open private vacuum vacuumProjection_apply from
  D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

/-- A surviving occurrence of mode `m` lowers to `m-k` at order `k`. -/
def creator (D : LatticeData) (x : Index D) : Polynomial (Oscillator D) :=
  ∑ k ∈ Finset.range (x.2 + 1), Polynomial.monomial k
    (Ring.choose ((x.2 : ℂ) + 1 / 2) k • (MvPolynomial.X (x.1, x.2 - k) : Oscillator D))

/-- Removing two occurrences contributes the Gram contraction at their
combined order. -/
def pair (D : LatticeData) (x y : Index D) : Polynomial (Oscillator D) :=
  Polynomial.monomial (x.2 + y.2 + 1)
    (MvPolynomial.C ((D.G x.1 y.1 : ℂ) * contractionScalar x.2 y.2))

/-- Finite Wick recursion with the physical mode on each occurrence.
A creator preserves its colour and a pair removes exactly two positions. -/
def word (D : LatticeData) : List (Index D) → Polynomial (Oscillator D)
  | [] => 1
  | x :: l => creator D x * word D l +
      ∑ j : Fin l.length, pair D x (l.get j) * word D (l.eraseIdx j)
termination_by l => l.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

private theorem creator_apply (D : LatticeData) (x : Index D) (k : ℕ) (p : Oscillator D) :
    PowerSeries.coeff k (creationPart D x) p = (creator D x).coeff k * p := by
  classical
  simp only [creationPart, PowerSeries.coeff_mk, creator, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  by_cases hk : k ≤ x.2
  · simp only [hk, ite_true]
    have hm : (k : ℤ) - (x.2 : ℤ) - 1 = -((x.2 - k : ℕ) : ℤ) - 1 := by omega
    rw [hm, current_negative]
    simp [hk]
  · simp [hk]

private theorem pair_apply (D : LatticeData) (x y : Index D) (k : ℕ) (p : Oscillator D) :
    PowerSeries.coeff k (contraction D x y) p = (pair D x y).coeff k * p := by
  classical
  simp only [contraction, pair, PowerSeries.coeff_monomial, Polynomial.coeff_monomial]
  split_ifs with h <;> simp_all [MvPolynomial.smul_eq_C_mul]

private theorem coeff_mul_apply (D : LatticeData) (S T : PowerSeries (Module.End ℂ (Oscillator D)))
    (P Q : Polynomial (Oscillator D))
    (hP : ∀ k p, PowerSeries.coeff k S p = P.coeff k * p)
    (hQ : ∀ k, PowerSeries.coeff k T (1 : Oscillator D) = Q.coeff k) (k : ℕ) :
    PowerSeries.coeff k (S * T) (1 : Oscillator D) = (P * Q).coeff k := by
  rw [PowerSeries.coeff_mul, Polynomial.coeff_mul]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, hP, hQ]

/-- Each order of the finite occurrence recursion is the corresponding
normal-order coefficient on the actual vacuum. -/
theorem word_coeff (D : LatticeData) (l : List (Index D)) (k : ℕ) :
    PowerSeries.coeff k (normalOrder D l) (1 : Oscillator D) = (word D l).coeff k := by
  induction l using WellFounded.induction (measure List.length).wf generalizing k with
  | h l ih =>
    cases l with
    | nil =>
      rw [word, normalOrder, vacuum, PowerSeries.coeff_C, Polynomial.coeff_one]
      split_ifs <;> simp [vacuumProjection_apply]
    | cons x l =>
      simp only [normalOrder, word, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
        Polynomial.coeff_add, Polynomial.finsetSum_coeff]
      congr 1
      · exact coeff_mul_apply D _ _ _ _ (creator_apply D x) (ih l (Nat.lt_succ_self _)) k
      · apply Finset.sum_congr rfl
        intro j _
        exact coeff_mul_apply D _ _ _ _ (pair_apply D x (l.get j))
          (ih (l.eraseIdx j) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))) k

/-- Evaluating the finite Wick polynomial at the chart lowering parameter
gives the factorial-normalized lowering flow on the original word. -/
theorem eval_word_eq_lowering (D : LatticeData) (hu : IsUnit D.G.det)
    (l : List (Index D)) (θ : ℂ) (N : ℕ) (hN : (word D l).natDegree < N) :
    (word D l).eval (MvPolynomial.C θ) =
      ∑ k ∈ Finset.range N, (θ ^ k / (k.factorial : ℂ)) • (oscillatorLower D ^ k)
        ((l.map (fun x => (MvPolynomial.X x : Oscillator D))).prod) := by
  rw [Polynomial.eval_eq_sum_range' hN]
  apply Finset.sum_congr rfl
  intro k _
  rw [← word_coeff, ← lowering_normal_order_word D hu]
  simp only [← map_pow, mul_comm _ (MvPolynomial.C _), ← MvPolynomial.smul_eq_C_mul,
    smul_smul, div_eq_mul_inv]

end D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

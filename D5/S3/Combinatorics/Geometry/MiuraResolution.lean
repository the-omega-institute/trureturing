/- GID: D5/S3/Combinatorics/Geometry/MiuraResolution
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraResolution
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact normalized residual count has one rational polynomial of strict total degree. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraPartitionCount
public import D5.S3.Combinatorics.Geometry.MiuraFiberEquiv

/-! Gupta's complete residual polynomial degree assertion for every original split. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraResolution
open MiuraHeightEnvelope MiuraResidualCount MiuraPolynomialCoreSum
  MiuraRunCompositions MiuraPartitionCount MiuraFiberEquiv
open scoped BigOperators

/-- The literal actual fiber has exactly the cardinality of its full positive-run product. -/
theorem fiber_card_eq_positive_vectors (a b m n : ℕ) (K : Core a b)
    (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n) :
    Nat.card (Fiber a b m n K) =
      Nat.card (PositiveLengths (m - rowOccupied K) (rowRuns K) ×
        PositiveLengths (n - colOccupied K) (colRuns K)) := by
  obtain ⟨e⟩ := core_positive_vectors_equiv a b m n K hm hn
  exact (Nat.card_congr e).symm

/-- The same core polynomial counts every individual actual residual array at all large dimensions. -/
theorem core_polynomial_counts_residual (a b m n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : 5 ≤ a + b) (hm : 2 * (a + b) - 1 ≤ m) (hn : 2 * (a + b) - 1 ≤ n) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℚ) else (n : ℚ))
      (corePolynomial a b) = (residualCount a b m n (by omega) (by omega) : ℚ) := by
  classical
  rw [core_polynomial_eval a b m n hm hn,
    residual_count_eq_sum_fibers a b m n ha hb hd hm hn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro K _
  exact congrArg (fun k : ℕ => (k : ℚ))
    (fiber_card_eq_positive_vectors a b m n K hm hn).symm

/-- The full unchanged Conjecture 8.3, with one polynomial chosen before both dimensions. -/
theorem result : MiuraResidualCount.claim := by
  intro d a b hd ha hb hab _habOrder
  refine ⟨corePolynomial a b, ?_, ?_⟩
  · simpa only [hab] using core_polynomial_degree_le a b (by omega)
  · intro m n hm hn
    exact core_polynomial_counts_residual a b m n ha hb (by omega) (by omega) (by omega)

end D5.S3.Combinatorics.Geometry.MiuraResolution

/- GID: D5/S3/Quantum/Matrix/HsfContractionCubic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfContractionCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: numeric-reduction; basis=consumer; consumer=D5/S3/Quantum/Matrix/HsfContractionCubic.coefficient_gap_nonneg
   digest: Full-contraction four-Gram identity for the cubic identity-denominator trace. -/

/-
admission_basis: escape-witness
proof_shape: coefficient_gap_identity: content
escape_witness: coefficient_gap_identity
The identity uses only cyclic trace rotations. No projection relation or word
reversal is imposed. The four physical weights retain both endpoints.
-/

module
public import D5.S3.Quantum.Matrix.HsfContractionGrams

@[expose] public section
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.HsfContractionCubic
open WeightedTraceGram HsfContractionGrams HsfQubitMixedCubic
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordered eight noncommutative words, with no reduction of powers of K. -/
def words (A B K : Matrix n n ℂ) : Fin 8 → Matrix n n ℂ :=
  ![A-(A+B)*K, (A-(A+B)*K)*K, A*K-K*A, (A*K-K*A)*K,
    K*(A*K-K*A), B*K-K*B, (B*K-K*B)*K, K*(B*K-K*B)]

section Rotations
variable (A B K : Matrix n n ℂ)

private theorem w_aaka : Matrix.trace (A*(A*(K*(A)))) =
    Matrix.trace (A*(A*(A*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*A*K) (A))

private theorem w_aakka : Matrix.trace (A*(A*(K*(K*(A))))) =
    Matrix.trace (A*(A*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*A*K*K) (A))

private theorem w_aakkka : Matrix.trace (A*(A*(K*(K*(K*(A)))))) =
    Matrix.trace (A*(A*(A*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*A*K*K*K) (A))

private theorem w_aakkkka : Matrix.trace (A*(A*(K*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(A*(K*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*A*K*K*K*K) (A))

private theorem w_aakkkkka : Matrix.trace (A*(A*(K*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(A*(K*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*A*K*K*K*K*K) (A))

private theorem w_abka : Matrix.trace (A*(B*(K*(A)))) =
    Matrix.trace (A*(A*(B*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*B*K) (A))

private theorem w_abkka : Matrix.trace (A*(B*(K*(K*(A))))) =
    Matrix.trace (A*(A*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*B*K*K) (A))

private theorem w_abkkka : Matrix.trace (A*(B*(K*(K*(K*(A)))))) =
    Matrix.trace (A*(A*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*B*K*K*K) (A))

private theorem w_abkkkka : Matrix.trace (A*(B*(K*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(B*(K*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*B*K*K*K*K) (A))

private theorem w_abkkkkka : Matrix.trace (A*(B*(K*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(B*(K*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*B*K*K*K*K*K) (A))

private theorem w_akaa : Matrix.trace (A*(K*(A*(A)))) =
    Matrix.trace (A*(A*(A*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*A))

private theorem w_akaak : Matrix.trace (A*(K*(A*(A*(K))))) =
    Matrix.trace (A*(A*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*A*K))

private theorem w_akaakk : Matrix.trace (A*(K*(A*(A*(K*(K)))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*A*K*K))

private theorem w_akab : Matrix.trace (A*(K*(A*(B)))) =
    Matrix.trace (A*(B*(A*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*B))

private theorem w_akabk : Matrix.trace (A*(K*(A*(B*(K))))) =
    Matrix.trace (A*(B*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*B*K))

private theorem w_akabkk : Matrix.trace (A*(K*(A*(B*(K*(K)))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K) (A*B*K*K))

private theorem w_akaka : Matrix.trace (A*(K*(A*(K*(A))))) =
    Matrix.trace (A*(A*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K) (A))

private theorem w_akakka : Matrix.trace (A*(K*(A*(K*(K*(A)))))) =
    Matrix.trace (A*(A*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K*K) (A))

private theorem w_akakkak : Matrix.trace (A*(K*(A*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K*K) (A*K))

private theorem w_akakkka : Matrix.trace (A*(K*(A*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(K*(A*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K*K*K) (A))

private theorem w_akakkkak : Matrix.trace (A*(K*(A*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(A*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K*K*K) (A*K))

private theorem w_akakkkka : Matrix.trace (A*(K*(A*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(K*(A*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*A*K*K*K*K) (A))

private theorem w_akba : Matrix.trace (A*(K*(B*(A)))) =
    Matrix.trace (A*(A*(K*(B)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B) (A))

private theorem w_akbak : Matrix.trace (A*(K*(B*(A*(K))))) =
    Matrix.trace (A*(K*(A*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B) (A*K))

private theorem w_akbka : Matrix.trace (A*(K*(B*(K*(A))))) =
    Matrix.trace (A*(A*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K) (A))

private theorem w_akbkak : Matrix.trace (A*(K*(B*(K*(A*(K)))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K) (A*K))

private theorem w_akbkka : Matrix.trace (A*(K*(B*(K*(K*(A)))))) =
    Matrix.trace (A*(A*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K*K) (A))

private theorem w_akbkkak : Matrix.trace (A*(K*(B*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K*K) (A*K))

private theorem w_akbkkka : Matrix.trace (A*(K*(B*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(K*(B*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K*K*K) (A))

private theorem w_akbkkkak : Matrix.trace (A*(K*(B*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K*K*K) (A*K))

private theorem w_akbkkkka : Matrix.trace (A*(K*(B*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(K*(B*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*B*K*K*K*K) (A))

private theorem w_akkaa : Matrix.trace (A*(K*(K*(A*(A))))) =
    Matrix.trace (A*(A*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*A))

private theorem w_akkaak : Matrix.trace (A*(K*(K*(A*(A*(K)))))) =
    Matrix.trace (A*(A*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*A*K))

private theorem w_akkaakk : Matrix.trace (A*(K*(K*(A*(A*(K*(K))))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*A*K*K))

private theorem w_akkab : Matrix.trace (A*(K*(K*(A*(B))))) =
    Matrix.trace (A*(B*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*B))

private theorem w_akkabk : Matrix.trace (A*(K*(K*(A*(B*(K)))))) =
    Matrix.trace (A*(B*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*B*K))

private theorem w_akkabkk : Matrix.trace (A*(K*(K*(A*(B*(K*(K))))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*B*K*K))

private theorem w_akkaka : Matrix.trace (A*(K*(K*(A*(K*(A)))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*A*K) (A))

private theorem w_akkakak : Matrix.trace (A*(K*(K*(A*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*K*A*K))

private theorem w_akkakakk : Matrix.trace (A*(K*(K*(A*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(A*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*K*A*K*K))

private theorem w_akkakb : Matrix.trace (A*(K*(K*(A*(K*(B)))))) =
    Matrix.trace (A*(K*(B*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*K*B))

private theorem w_akkakbk : Matrix.trace (A*(K*(K*(A*(K*(B*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*K*B*K))

private theorem w_akkakbkk : Matrix.trace (A*(K*(K*(A*(K*(B*(K*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K) (A*K*B*K*K))

private theorem w_akkakka : Matrix.trace (A*(K*(K*(A*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*A*K*K) (A))

private theorem w_akkakkak : Matrix.trace (A*(K*(K*(A*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(A*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*A*K*K) (A*K))

private theorem w_akkakkka : Matrix.trace (A*(K*(K*(A*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*A*K*K*K) (A))

private theorem w_akkba : Matrix.trace (A*(K*(K*(B*(A))))) =
    Matrix.trace (A*(A*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B) (A))

private theorem w_akkbak : Matrix.trace (A*(K*(K*(B*(A*(K)))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B) (A*K))

private theorem w_akkbakk : Matrix.trace (A*(K*(K*(B*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(A*(K*(K*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B) (A*K*K))

private theorem w_akkbka : Matrix.trace (A*(K*(K*(B*(K*(A)))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K) (A))

private theorem w_akkbkak : Matrix.trace (A*(K*(K*(B*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K) (A*K))

private theorem w_akkbkakk : Matrix.trace (A*(K*(K*(B*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K) (A*K*K))

private theorem w_akkbkka : Matrix.trace (A*(K*(K*(B*(K*(K*(A))))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K*K) (A))

private theorem w_akkbkkak : Matrix.trace (A*(K*(K*(B*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K*K) (A*K))

private theorem w_akkbkkka : Matrix.trace (A*(K*(K*(B*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (A*K*K*B*K*K*K) (A))

private theorem w_baa : Matrix.trace (B*(A*(A))) =
    Matrix.trace (A*(A*(B))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*A))

private theorem w_baak : Matrix.trace (B*(A*(A*(K)))) =
    Matrix.trace (A*(A*(K*(B)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*A*K))

private theorem w_baakk : Matrix.trace (B*(A*(A*(K*(K))))) =
    Matrix.trace (A*(A*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*A*K*K))

private theorem w_babk : Matrix.trace (B*(A*(B*(K)))) =
    Matrix.trace (A*(B*(K*(B)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*B*K))

private theorem w_babkk : Matrix.trace (B*(A*(B*(K*(K))))) =
    Matrix.trace (A*(B*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*B*K*K))

private theorem w_baka : Matrix.trace (B*(A*(K*(A)))) =
    Matrix.trace (A*(B*(A*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K) (A))

private theorem w_bakak : Matrix.trace (B*(A*(K*(A*(K))))) =
    Matrix.trace (A*(K*(A*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*A*K))

private theorem w_bakakk : Matrix.trace (B*(A*(K*(A*(K*(K)))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*A*K*K))

private theorem w_bakb : Matrix.trace (B*(A*(K*(B)))) =
    Matrix.trace (A*(K*(B*(B)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*B))

private theorem w_bakbk : Matrix.trace (B*(A*(K*(B*(K))))) =
    Matrix.trace (A*(K*(B*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*B*K))

private theorem w_bakbkk : Matrix.trace (B*(A*(K*(B*(K*(K)))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*B*K*K))

private theorem w_bakka : Matrix.trace (B*(A*(K*(K*(A))))) =
    Matrix.trace (A*(B*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K) (A))

private theorem w_bakkak : Matrix.trace (B*(A*(K*(K*(A*(K)))))) =
    Matrix.trace (A*(K*(B*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K) (A*K))

private theorem w_bakkakk : Matrix.trace (B*(A*(K*(K*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(A*(K*(K*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*A*K*K))

private theorem w_bakkb : Matrix.trace (B*(A*(K*(K*(B))))) =
    Matrix.trace (A*(K*(K*(B*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*B))

private theorem w_bakkbk : Matrix.trace (B*(A*(K*(K*(B*(K)))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*B*K))

private theorem w_bakkbkk : Matrix.trace (B*(A*(K*(K*(B*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(K*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*B*K*K))

private theorem w_bakkka : Matrix.trace (B*(A*(K*(K*(K*(A)))))) =
    Matrix.trace (A*(B*(A*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K) (A))

private theorem w_bakkkak : Matrix.trace (B*(A*(K*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(B*(A*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K) (A*K))

private theorem w_bakkkakk : Matrix.trace (B*(A*(K*(K*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(A*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K) (A*K*K))

private theorem w_bakkkb : Matrix.trace (B*(A*(K*(K*(K*(B)))))) =
    Matrix.trace (A*(K*(K*(K*(B*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*B))

private theorem w_bakkkbk : Matrix.trace (B*(A*(K*(K*(K*(B*(K))))))) =
    Matrix.trace (A*(K*(K*(K*(B*(K*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*B*K))

private theorem w_bakkkbkk : Matrix.trace (B*(A*(K*(K*(K*(B*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(K*(B*(K*(K*(B)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*B*K*K))

private theorem w_bakkkka : Matrix.trace (B*(A*(K*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(A*(K*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K*K) (A))

private theorem w_bakkkkak : Matrix.trace (B*(A*(K*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(A*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K*K) (A*K))

private theorem w_bakkkkb : Matrix.trace (B*(A*(K*(K*(K*(K*(B))))))) =
    Matrix.trace (A*(K*(K*(K*(K*(B*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*K*B))

private theorem w_bakkkkbk : Matrix.trace (B*(A*(K*(K*(K*(K*(B*(K)))))))) =
    Matrix.trace (A*(K*(K*(K*(K*(B*(K*(B)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*K*B*K))

private theorem w_bakkkkka : Matrix.trace (B*(A*(K*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(A*(K*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*A*K*K*K*K*K) (A))

private theorem w_bakkkkkb : Matrix.trace (B*(A*(K*(K*(K*(K*(K*(B)))))))) =
    Matrix.trace (A*(K*(K*(K*(K*(K*(B*(B)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B) (A*K*K*K*K*K*B))

private theorem w_bbka : Matrix.trace (B*(B*(K*(A)))) =
    Matrix.trace (A*(B*(B*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K) (A))

private theorem w_bbkak : Matrix.trace (B*(B*(K*(A*(K))))) =
    Matrix.trace (A*(K*(B*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K) (A*K))

private theorem w_bbkakk : Matrix.trace (B*(B*(K*(A*(K*(K)))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K) (A*K*K))

private theorem w_bbkka : Matrix.trace (B*(B*(K*(K*(A))))) =
    Matrix.trace (A*(B*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K) (A))

private theorem w_bbkkak : Matrix.trace (B*(B*(K*(K*(A*(K)))))) =
    Matrix.trace (A*(K*(B*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K) (A*K))

private theorem w_bbkkakk : Matrix.trace (B*(B*(K*(K*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K) (A*K*K))

private theorem w_bbkkb : Matrix.trace (B*(B*(K*(K*(B))))) =
    Matrix.trace (B*(B*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K) (B))

private theorem w_bbkkka : Matrix.trace (B*(B*(K*(K*(K*(A)))))) =
    Matrix.trace (A*(B*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K) (A))

private theorem w_bbkkkak : Matrix.trace (B*(B*(K*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(B*(B*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K) (A*K))

private theorem w_bbkkkakk : Matrix.trace (B*(B*(K*(K*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K) (A*K*K))

private theorem w_bbkkkb : Matrix.trace (B*(B*(K*(K*(K*(B)))))) =
    Matrix.trace (B*(B*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K) (B))

private theorem w_bbkkkka : Matrix.trace (B*(B*(K*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(B*(K*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K*K) (A))

private theorem w_bbkkkkak : Matrix.trace (B*(B*(K*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(B*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K*K) (A*K))

private theorem w_bbkkkkb : Matrix.trace (B*(B*(K*(K*(K*(K*(B))))))) =
    Matrix.trace (B*(B*(B*(K*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K*K) (B))

private theorem w_bbkkkkka : Matrix.trace (B*(B*(K*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(B*(K*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K*K*K) (A))

private theorem w_bbkkkkkb : Matrix.trace (B*(B*(K*(K*(K*(K*(K*(B)))))))) =
    Matrix.trace (B*(B*(B*(K*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*B*K*K*K*K*K) (B))

private theorem w_bkaa : Matrix.trace (B*(K*(A*(A)))) =
    Matrix.trace (A*(A*(B*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*A))

private theorem w_bkaak : Matrix.trace (B*(K*(A*(A*(K))))) =
    Matrix.trace (A*(A*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*A*K))

private theorem w_bkaakk : Matrix.trace (B*(K*(A*(A*(K*(K)))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*A*K*K))

private theorem w_bkabk : Matrix.trace (B*(K*(A*(B*(K))))) =
    Matrix.trace (A*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*B*K))

private theorem w_bkabkk : Matrix.trace (B*(K*(A*(B*(K*(K)))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*B*K*K))

private theorem w_bkaka : Matrix.trace (B*(K*(A*(K*(A))))) =
    Matrix.trace (A*(B*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K) (A))

private theorem w_bkakak : Matrix.trace (B*(K*(A*(K*(A*(K)))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*A*K))

private theorem w_bkakakk : Matrix.trace (B*(K*(A*(K*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*A*K*K))

private theorem w_bkakb : Matrix.trace (B*(K*(A*(K*(B))))) =
    Matrix.trace (A*(K*(B*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*B))

private theorem w_bkakbk : Matrix.trace (B*(K*(A*(K*(B*(K)))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*B*K))

private theorem w_bkakbkk : Matrix.trace (B*(K*(A*(K*(B*(K*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*B*K*K))

private theorem w_bkakka : Matrix.trace (B*(K*(A*(K*(K*(A)))))) =
    Matrix.trace (A*(B*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K*K) (A))

private theorem w_bkakkak : Matrix.trace (B*(K*(A*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K*K) (A*K))

private theorem w_bkakkakk : Matrix.trace (B*(K*(A*(K*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*A*K*K))

private theorem w_bkakkb : Matrix.trace (B*(K*(A*(K*(K*(B)))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*B))

private theorem w_bkakkbk : Matrix.trace (B*(K*(A*(K*(K*(B*(K))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*B*K))

private theorem w_bkakkbkk : Matrix.trace (B*(K*(A*(K*(K*(B*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*B*K*K))

private theorem w_bkakkka : Matrix.trace (B*(K*(A*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(K*(A*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K*K*K) (A))

private theorem w_bkakkkak : Matrix.trace (B*(K*(A*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(A*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K*K*K) (A*K))

private theorem w_bkakkkb : Matrix.trace (B*(K*(A*(K*(K*(K*(B))))))) =
    Matrix.trace (A*(K*(K*(K*(B*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*K*B))

private theorem w_bkakkkbk : Matrix.trace (B*(K*(A*(K*(K*(K*(B*(K)))))))) =
    Matrix.trace (A*(K*(K*(K*(B*(K*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*K*B*K))

private theorem w_bkakkkka : Matrix.trace (B*(K*(A*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(K*(A*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*A*K*K*K*K) (A))

private theorem w_bkakkkkb : Matrix.trace (B*(K*(A*(K*(K*(K*(K*(B)))))))) =
    Matrix.trace (A*(K*(K*(K*(K*(B*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (A*K*K*K*K*B))

private theorem w_bkba : Matrix.trace (B*(K*(B*(A)))) =
    Matrix.trace (A*(B*(K*(B)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B) (A))

private theorem w_bkbak : Matrix.trace (B*(K*(B*(A*(K))))) =
    Matrix.trace (A*(K*(B*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B) (A*K))

private theorem w_bkbakk : Matrix.trace (B*(K*(B*(A*(K*(K)))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B) (A*K*K))

private theorem w_bkbbk : Matrix.trace (B*(K*(B*(B*(K))))) =
    Matrix.trace (B*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (B*B*K))

private theorem w_bkbbkk : Matrix.trace (B*(K*(B*(B*(K*(K)))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K) (B*B*K*K))

private theorem w_bkbka : Matrix.trace (B*(K*(B*(K*(A))))) =
    Matrix.trace (A*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K) (A))

private theorem w_bkbkak : Matrix.trace (B*(K*(B*(K*(A*(K)))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K) (A*K))

private theorem w_bkbkakk : Matrix.trace (B*(K*(B*(K*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K) (A*K*K))

private theorem w_bkbkb : Matrix.trace (B*(K*(B*(K*(B))))) =
    Matrix.trace (B*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K) (B))

private theorem w_bkbkka : Matrix.trace (B*(K*(B*(K*(K*(A)))))) =
    Matrix.trace (A*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K) (A))

private theorem w_bkbkkak : Matrix.trace (B*(K*(B*(K*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K) (A*K))

private theorem w_bkbkkakk : Matrix.trace (B*(K*(B*(K*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K) (A*K*K))

private theorem w_bkbkkb : Matrix.trace (B*(K*(B*(K*(K*(B)))))) =
    Matrix.trace (B*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K) (B))

private theorem w_bkbkkbk : Matrix.trace (B*(K*(B*(K*(K*(B*(K))))))) =
    Matrix.trace (B*(K*(B*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K) (B*K))

private theorem w_bkbkkka : Matrix.trace (B*(K*(B*(K*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(K*(B*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K) (A))

private theorem w_bkbkkkak : Matrix.trace (B*(K*(B*(K*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K) (A*K))

private theorem w_bkbkkkb : Matrix.trace (B*(K*(B*(K*(K*(K*(B))))))) =
    Matrix.trace (B*(B*(K*(B*(K*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K) (B))

private theorem w_bkbkkkbk : Matrix.trace (B*(K*(B*(K*(K*(K*(B*(K)))))))) =
    Matrix.trace (B*(K*(B*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K) (B*K))

private theorem w_bkbkkkka : Matrix.trace (B*(K*(B*(K*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(K*(B*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K*K) (A))

private theorem w_bkbkkkkb : Matrix.trace (B*(K*(B*(K*(K*(K*(K*(B)))))))) =
    Matrix.trace (B*(B*(K*(B*(K*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*B*K*K*K*K) (B))

private theorem w_bkkaa : Matrix.trace (B*(K*(K*(A*(A))))) =
    Matrix.trace (A*(A*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*A))

private theorem w_bkkaak : Matrix.trace (B*(K*(K*(A*(A*(K)))))) =
    Matrix.trace (A*(A*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*A*K))

private theorem w_bkkaakk : Matrix.trace (B*(K*(K*(A*(A*(K*(K))))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*A*K*K))

private theorem w_bkkabk : Matrix.trace (B*(K*(K*(A*(B*(K)))))) =
    Matrix.trace (A*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*B*K))

private theorem w_bkkabkk : Matrix.trace (B*(K*(K*(A*(B*(K*(K))))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*B*K*K))

private theorem w_bkkaka : Matrix.trace (B*(K*(K*(A*(K*(A)))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*A*K) (A))

private theorem w_bkkakak : Matrix.trace (B*(K*(K*(A*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*A*K))

private theorem w_bkkakakk : Matrix.trace (B*(K*(K*(A*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*A*K*K))

private theorem w_bkkakb : Matrix.trace (B*(K*(K*(A*(K*(B)))))) =
    Matrix.trace (A*(K*(B*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*B))

private theorem w_bkkakbk : Matrix.trace (B*(K*(K*(A*(K*(B*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*B*K))

private theorem w_bkkakbkk : Matrix.trace (B*(K*(K*(A*(K*(B*(K*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*B*K*K))

private theorem w_bkkakka : Matrix.trace (B*(K*(K*(A*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*A*K*K) (A))

private theorem w_bkkakkak : Matrix.trace (B*(K*(K*(A*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*A*K*K) (A*K))

private theorem w_bkkakkb : Matrix.trace (B*(K*(K*(A*(K*(K*(B))))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*K*B))

private theorem w_bkkakkbk : Matrix.trace (B*(K*(K*(A*(K*(K*(B*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*K*B*K))

private theorem w_bkkakkka : Matrix.trace (B*(K*(K*(A*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*A*K*K*K) (A))

private theorem w_bkkakkkb : Matrix.trace (B*(K*(K*(A*(K*(K*(K*(B)))))))) =
    Matrix.trace (A*(K*(K*(K*(B*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (A*K*K*K*B))

private theorem w_bkkba : Matrix.trace (B*(K*(K*(B*(A))))) =
    Matrix.trace (A*(B*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B) (A))

private theorem w_bkkbak : Matrix.trace (B*(K*(K*(B*(A*(K)))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B) (A*K))

private theorem w_bkkbakk : Matrix.trace (B*(K*(K*(B*(A*(K*(K))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(K*(B))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B) (A*K*K))

private theorem w_bkkbbk : Matrix.trace (B*(K*(K*(B*(B*(K)))))) =
    Matrix.trace (B*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (B*B*K))

private theorem w_bkkbbkk : Matrix.trace (B*(K*(K*(B*(B*(K*(K))))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (B*B*K*K))

private theorem w_bkkbka : Matrix.trace (B*(K*(K*(B*(K*(A)))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K) (A))

private theorem w_bkkbkak : Matrix.trace (B*(K*(K*(B*(K*(A*(K))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K) (A*K))

private theorem w_bkkbkakk : Matrix.trace (B*(K*(K*(B*(K*(A*(K*(K)))))))) =
    Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K) (A*K*K))

private theorem w_bkkbkb : Matrix.trace (B*(K*(K*(B*(K*(B)))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K) (B))

private theorem w_bkkbkbk : Matrix.trace (B*(K*(K*(B*(K*(B*(K))))))) =
    Matrix.trace (B*(K*(B*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (B*K*B*K))

private theorem w_bkkbkbkk : Matrix.trace (B*(K*(K*(B*(K*(B*(K*(K)))))))) =
    Matrix.trace (B*(K*(B*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K) (B*K*B*K*K))

private theorem w_bkkbkka : Matrix.trace (B*(K*(K*(B*(K*(K*(A))))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K) (A))

private theorem w_bkkbkkak : Matrix.trace (B*(K*(K*(B*(K*(K*(A*(K)))))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K) (A*K))

private theorem w_bkkbkkb : Matrix.trace (B*(K*(K*(B*(K*(K*(B))))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K*(K))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K) (B))

private theorem w_bkkbkkbk : Matrix.trace (B*(K*(K*(B*(K*(K*(B*(K)))))))) =
    Matrix.trace (B*(K*(B*(K*(K*(B*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K) (B*K))

private theorem w_bkkbkkka : Matrix.trace (B*(K*(K*(B*(K*(K*(K*(A)))))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K*K) (A))

private theorem w_bkkbkkkb : Matrix.trace (B*(K*(K*(B*(K*(K*(K*(B)))))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K*(K*(K)))))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (B*K*K*B*K*K*K) (B))

private theorem w_kakaa : Matrix.trace (K*(A*(K*(A*(A))))) =
    Matrix.trace (A*(A*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*A*K) (A*A))

private theorem w_kakab : Matrix.trace (K*(A*(K*(A*(B))))) =
    Matrix.trace (A*(B*(K*(A*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*A*K) (A*B))

private theorem w_kakaka : Matrix.trace (K*(A*(K*(A*(K*(A)))))) =
    Matrix.trace (A*(K*(A*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K) (A*K*A*K*A))

private theorem w_kakakb : Matrix.trace (K*(A*(K*(A*(K*(B)))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K) (A*K*A*K*B))

private theorem w_kakba : Matrix.trace (K*(A*(K*(B*(A))))) =
    Matrix.trace (A*(K*(A*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*A*K*B) (A))

private theorem w_kakbb : Matrix.trace (K*(A*(K*(B*(B))))) =
    Matrix.trace (A*(K*(B*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K) (A*K*B*B))

private theorem w_kakbka : Matrix.trace (K*(A*(K*(B*(K*(A)))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*A*K*B*K) (A))

private theorem w_kakbkb : Matrix.trace (K*(A*(K*(B*(K*(B)))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K) (A*K*B*K*B))

private theorem w_kbkaa : Matrix.trace (K*(B*(K*(A*(A))))) =
    Matrix.trace (A*(A*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K) (A*A))

private theorem w_kbkab : Matrix.trace (K*(B*(K*(A*(B))))) =
    Matrix.trace (A*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K) (A*B))

private theorem w_kbkaka : Matrix.trace (K*(B*(K*(A*(K*(A)))))) =
    Matrix.trace (A*(K*(A*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K) (A*K*A))

private theorem w_kbkakb : Matrix.trace (K*(B*(K*(A*(K*(B)))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K) (A*K*B))

private theorem w_kbkba : Matrix.trace (K*(B*(K*(B*(A))))) =
    Matrix.trace (A*(K*(B*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K*B) (A))

private theorem w_kbkbb : Matrix.trace (K*(B*(K*(B*(B))))) =
    Matrix.trace (B*(B*(K*(B*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K) (B*B))

private theorem w_kbkbka : Matrix.trace (K*(B*(K*(B*(K*(A)))))) =
    Matrix.trace (A*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*B*K*B*K) (A))

private theorem w_kbkbkb : Matrix.trace (K*(B*(K*(B*(K*(B)))))) =
    Matrix.trace (B*(K*(B*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K) (B*K*B*K*B))

private theorem w_kkaaa : Matrix.trace (K*(K*(A*(A*(A))))) =
    Matrix.trace (A*(A*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*A*A))

private theorem w_kkaab : Matrix.trace (K*(K*(A*(A*(B))))) =
    Matrix.trace (A*(A*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*A*B))

private theorem w_kkaaka : Matrix.trace (K*(K*(A*(A*(K*(A)))))) =
    Matrix.trace (A*(A*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*A*K*A))

private theorem w_kkaakb : Matrix.trace (K*(K*(A*(A*(K*(B)))))) =
    Matrix.trace (A*(A*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*A*K*B))

private theorem w_kkaba : Matrix.trace (K*(K*(A*(B*(A))))) =
    Matrix.trace (A*(B*(A*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*B*A))

private theorem w_kkabb : Matrix.trace (K*(K*(A*(B*(B))))) =
    Matrix.trace (A*(B*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*B*B))

private theorem w_kkabka : Matrix.trace (K*(K*(A*(B*(K*(A)))))) =
    Matrix.trace (A*(B*(K*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*B*K*A))

private theorem w_kkabkb : Matrix.trace (K*(K*(A*(B*(K*(B)))))) =
    Matrix.trace (A*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*B*K*B))

private theorem w_kkakaa : Matrix.trace (K*(K*(A*(K*(A*(A)))))) =
    Matrix.trace (A*(A*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*A*K) (A*A))

private theorem w_kkakab : Matrix.trace (K*(K*(A*(K*(A*(B)))))) =
    Matrix.trace (A*(B*(K*(K*(A*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*A*K) (A*B))

private theorem w_kkakba : Matrix.trace (K*(K*(A*(K*(B*(A)))))) =
    Matrix.trace (A*(K*(B*(A*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*K*B*A))

private theorem w_kkakbb : Matrix.trace (K*(K*(A*(K*(B*(B)))))) =
    Matrix.trace (A*(K*(B*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (A*K*B*B))

private theorem w_kkbaa : Matrix.trace (K*(K*(B*(A*(A))))) =
    Matrix.trace (A*(A*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B) (A*A))

private theorem w_kkbab : Matrix.trace (K*(K*(B*(A*(B))))) =
    Matrix.trace (A*(B*(K*(K*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B) (A*B))

private theorem w_kkbaka : Matrix.trace (K*(K*(B*(A*(K*(A)))))) =
    Matrix.trace (A*(K*(A*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B) (A*K*A))

private theorem w_kkbakb : Matrix.trace (K*(K*(B*(A*(K*(B)))))) =
    Matrix.trace (A*(K*(B*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B) (A*K*B))

private theorem w_kkbba : Matrix.trace (K*(K*(B*(B*(A))))) =
    Matrix.trace (A*(K*(K*(B*(B))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*B) (A))

private theorem w_kkbbb : Matrix.trace (K*(K*(B*(B*(B))))) =
    Matrix.trace (B*(B*(B*(K*(K))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (B*B*B))

private theorem w_kkbbka : Matrix.trace (K*(K*(B*(B*(K*(A)))))) =
    Matrix.trace (A*(K*(K*(B*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*B*K) (A))

private theorem w_kkbbkb : Matrix.trace (K*(K*(B*(B*(K*(B)))))) =
    Matrix.trace (B*(B*(K*(B*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K) (B*B*K*B))

private theorem w_kkbkaa : Matrix.trace (K*(K*(B*(K*(A*(A)))))) =
    Matrix.trace (A*(A*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*K) (A*A))

private theorem w_kkbkab : Matrix.trace (K*(K*(B*(K*(A*(B)))))) =
    Matrix.trace (A*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*K) (A*B))

private theorem w_kkbkba : Matrix.trace (K*(K*(B*(K*(B*(A)))))) =
    Matrix.trace (A*(K*(K*(B*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*K*B) (A))

private theorem w_kkbkbb : Matrix.trace (K*(K*(B*(K*(B*(B)))))) =
    Matrix.trace (B*(B*(K*(K*(B*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*B*K) (B*B))

private theorem w_kkkaaa : Matrix.trace (K*(K*(K*(A*(A*(A)))))) =
    Matrix.trace (A*(A*(A*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K) (A*A*A))

private theorem w_kkkaab : Matrix.trace (K*(K*(K*(A*(A*(B)))))) =
    Matrix.trace (A*(A*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K) (A*A*B))

private theorem w_kkkaba : Matrix.trace (K*(K*(K*(A*(B*(A)))))) =
    Matrix.trace (A*(B*(A*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K) (A*B*A))

private theorem w_kkkabb : Matrix.trace (K*(K*(K*(A*(B*(B)))))) =
    Matrix.trace (A*(B*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K) (A*B*B))

private theorem w_kkkbaa : Matrix.trace (K*(K*(K*(B*(A*(A)))))) =
    Matrix.trace (A*(A*(K*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K*B) (A*A))

private theorem w_kkkbab : Matrix.trace (K*(K*(K*(B*(A*(B)))))) =
    Matrix.trace (A*(B*(K*(K*(K*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K*B) (A*B))

private theorem w_kkkbba : Matrix.trace (K*(K*(K*(B*(B*(A)))))) =
    Matrix.trace (A*(K*(K*(K*(B*(B)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K*B*B) (A))

private theorem w_kkkbbb : Matrix.trace (K*(K*(K*(B*(B*(B)))))) =
    Matrix.trace (B*(B*(B*(K*(K*(K)))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*K*K) (B*B*B))

end Rotations

private theorem expand_M00 (A B K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hK : K.IsHermitian) :
    traceGram A (1-K) (words A B K) M00 =
    (276 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K)))))).re +
    (-262 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K))))))).re +
    (168 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K*(K)))))))).re +
    (-182 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K*(K*(K))))))))).re +
    (-93 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K)))))).re +
    (179 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K))))))).re +
    (98 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K*(K)))))))).re +
    (-184 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K*(K*(K))))))))).re +
    (250 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K)))))).re +
    (-15 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K))))))).re +
    (46 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K*(K)))))))).re +
    (114 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K*(K*(K))))))))).re +
    (186 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K)))))).re +
    (86 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K))))))).re +
    (-10 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K*(K)))))))).re +
    (88 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K*(K*(K))))))))).re +
    (-15 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K))))))).re +
    (320 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K*(K)))))))).re +
    (-110 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K*(K*(K))))))))).re +
    (-93 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B)))))).re +
    (86 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K))))))).re +
    (-350 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K*(K)))))))).re +
    (-82 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K*(K*(K))))))))).re +
    (46 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(A*(K)))))))).re +
    (-110 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(A*(K*(K))))))))).re +
    (179 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B))))))).re +
    (-10 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B*(K)))))))).re +
    (-82 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B*(K*(K))))))))).re +
    (114 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(A*(K))))))))).re +
    (98 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(B)))))))).re +
    (88 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(B*(K))))))))).re +
    (-184 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(K*(B))))))))).re +
    (-220 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K)))))).re +
    (14 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K))))))).re +
    (-793 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K))))))).re +
    (457 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K)))))))).re +
    (220 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B)))))).re +
    (-142 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K))))))).re +
    (26 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K)))))))).re +
    (92 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(A*(K)))))))).re +
    (-56 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(A*(K*(K))))))))).re +
    (224 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B))))))).re +
    (206 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B*(K)))))))).re +
    (-40 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B*(K*(K))))))))).re +
    (76 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(A*(K))))))))).re +
    (-164 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(B)))))))).re +
    (156 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(B*(K))))))))).re +
    (-280 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(K*(B))))))))).re +
    (-1286 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K))))))).re +
    (998 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K*(K)))))))).re +
    (-346 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K*(K*(K))))))))).re +
    (4 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K))))))).re +
    (651 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K)))))))).re +
    (-154 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K*(K))))))))).re +
    (-6 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(A*(K*(K))))))))).re +
    (-793 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B))))))).re +
    (651 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K)))))))).re +
    (252 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K))))))))).re +
    (92 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(B)))))))).re +
    (-154 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(B*(K))))))))).re +
    (76 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(K*(B))))))))).re +
    (220 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K)))))).re +
    (-14 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K))))))).re +
    (-122 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K)))))))).re +
    (-220 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B)))))).re +
    (60 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K))))))).re +
    (-103 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K)))))))).re +
    (-340 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K))))))))).re +
    (-142 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B))))))).re +
    (-16 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K)))))))).re +
    (117 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K))))))))).re +
    (206 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(B)))))))).re +
    (-264 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(B*(K))))))))).re +
    (156 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(K*(B))))))))).re +
    (457 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B)))))))).re +
    (-340 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K))))))))).re +
    (-56 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(K*(B))))))))).re +
    (-14 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K))))))).re +
    (448 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K*(K)))))))).re +
    (14 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B))))))).re +
    (-103 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K)))))))).re +
    (-448 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K))))))))).re +
    (26 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B)))))))).re +
    (117 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K))))))))).re +
    (-40 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(K*(B))))))))).re := by
  simp only [traceGram, words, M00, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val_elim, star_sub, star_add, star_mul, hA.star_eq, hB.star_eq, hK.star_eq, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_aakka A B K,
    w_aakkka A B K,
    w_aakkkka A B K,
    w_aakkkkka A B K,
    w_abkka A B K,
    w_abkkka A B K,
    w_abkkkka A B K,
    w_abkkkkka A B K,
    w_akaak A B K,
    w_akaakk A B K,
    w_akabk A B K,
    w_akabkk A B K,
    w_akaka A B K,
    w_akakka A B K,
    w_akakkak A B K,
    w_akakkka A B K,
    w_akakkkak A B K,
    w_akakkkka A B K,
    w_akbak A B K,
    w_akbka A B K,
    w_akbkak A B K,
    w_akbkka A B K,
    w_akbkkak A B K,
    w_akbkkka A B K,
    w_akbkkkak A B K,
    w_akbkkkka A B K,
    w_akkaak A B K,
    w_akkaakk A B K,
    w_akkabk A B K,
    w_akkabkk A B K,
    w_akkaka A B K,
    w_akkakak A B K,
    w_akkakakk A B K,
    w_akkakb A B K,
    w_akkakbk A B K,
    w_akkakbkk A B K,
    w_akkakka A B K,
    w_akkakkak A B K,
    w_akkakkka A B K,
    w_akkbak A B K,
    w_akkbakk A B K,
    w_akkbka A B K,
    w_akkbkak A B K,
    w_akkbkakk A B K,
    w_akkbkka A B K,
    w_akkbkkak A B K,
    w_akkbkkka A B K]
  norm_num
  ring

private theorem expand_M01 (A B K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hK : K.IsHermitian) :
    traceGram A K (words A B K) M01 =
    (3456 : ℝ) * (Matrix.trace (A*(A*(A*(K))))).re +
    (-4116 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K)))))).re +
    (1542 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K))))))).re +
    (-168 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K*(K)))))))).re +
    (182 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K*(K*(K))))))))).re +
    (-1675 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K)))))).re +
    (1101 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K))))))).re +
    (-98 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K*(K)))))))).re +
    (184 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K*(K*(K))))))))).re +
    (-3322 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K)))))).re +
    (975 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K))))))).re +
    (-46 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K*(K)))))))).re +
    (-114 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K*(K*(K))))))))).re +
    (-3562 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K)))))).re +
    (1220 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K))))))).re +
    (10 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K*(K)))))))).re +
    (-88 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K*(K*(K))))))))).re +
    (975 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K))))))).re +
    (-320 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K*(K)))))))).re +
    (110 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K*(K*(K))))))))).re +
    (-1675 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B)))))).re +
    (1220 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K))))))).re +
    (-216 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K*(K)))))))).re +
    (82 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K*(K*(K))))))))).re +
    (-46 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(A*(K)))))))).re +
    (110 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(A*(K*(K))))))))).re +
    (1101 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B))))))).re +
    (10 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B*(K)))))))).re +
    (82 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B*(K*(K))))))))).re +
    (-114 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(A*(K))))))))).re +
    (-98 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(B)))))))).re +
    (-88 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(B*(K))))))))).re +
    (184 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(K*(K*(B))))))))).re +
    (771 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K))))))).re +
    (-171 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K)))))))).re +
    (619 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K))))))).re +
    (-155 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K)))))))).re +
    (-92 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(A*(K)))))))).re +
    (56 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(A*(K*(K))))))))).re +
    (1056 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B))))))).re +
    (-206 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B*(K)))))))).re +
    (40 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B*(K*(K))))))))).re +
    (-76 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(A*(K))))))))).re +
    (164 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(B)))))))).re +
    (-156 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(B*(K))))))))).re +
    (280 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(K*(K*(B))))))))).re +
    (1542 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K))))))).re +
    (-998 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K*(K)))))))).re +
    (346 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K*(K*(K))))))))).re +
    (1780 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K))))))).re +
    (-251 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K)))))))).re +
    (154 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K*(K))))))))).re +
    (6 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(A*(K*(K))))))))).re +
    (771 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B))))))).re +
    (-251 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K)))))))).re +
    (-484 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K))))))))).re +
    (-92 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(B)))))))).re +
    (154 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(B*(K))))))))).re +
    (-76 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(K*(K*(B))))))))).re +
    (-684 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K)))))))).re +
    (1162 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K))))))).re +
    (-243 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K)))))))).re +
    (456 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K))))))))).re +
    (619 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B))))))).re +
    (518 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K)))))))).re +
    (-346 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K))))))))).re +
    (-206 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(B)))))))).re +
    (264 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(B*(K))))))))).re +
    (-156 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(K*(K*(B))))))))).re +
    (-171 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B)))))))).re +
    (456 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K))))))))).re +
    (56 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(K*(B))))))))).re +
    (-243 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K)))))))).re +
    (906 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K))))))))).re +
    (-155 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B)))))))).re +
    (-346 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K))))))))).re +
    (40 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(K*(B))))))))).re := by
  simp only [traceGram, words, M01, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val_elim, star_sub, star_add, star_mul, hA.star_eq, hB.star_eq, hK.star_eq, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_aaka A B K,
    w_aakka A B K,
    w_aakkka A B K,
    w_aakkkka A B K,
    w_aakkkkka A B K,
    w_abkka A B K,
    w_abkkka A B K,
    w_abkkkka A B K,
    w_abkkkkka A B K,
    w_akaka A B K,
    w_akakka A B K,
    w_akakkak A B K,
    w_akakkka A B K,
    w_akakkkak A B K,
    w_akakkkka A B K,
    w_akbka A B K,
    w_akbkak A B K,
    w_akbkka A B K,
    w_akbkkak A B K,
    w_akbkkka A B K,
    w_akbkkkak A B K,
    w_akbkkkka A B K,
    w_akkaka A B K,
    w_akkakak A B K,
    w_akkakakk A B K,
    w_akkakbk A B K,
    w_akkakbkk A B K,
    w_akkakka A B K,
    w_akkakkak A B K,
    w_akkakkka A B K,
    w_akkbka A B K,
    w_akkbkak A B K,
    w_akkbkakk A B K,
    w_akkbkka A B K,
    w_akkbkkak A B K,
    w_akkbkkka A B K]
  norm_num
  ring

private theorem expand_M10 (A B K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hK : K.IsHermitian) :
    traceGram B (1-K) (words A B K) M10 =
    (864 : ℝ) * (Matrix.trace (A*(A*(B)))).re +
    (576 : ℝ) * (Matrix.trace (A*(A*(B*(K))))).re +
    (-632 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K)))))).re +
    (576 : ℝ) * (Matrix.trace (A*(A*(K*(B))))).re +
    (1456 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K)))))).re +
    (-346 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K))))))).re +
    (-632 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B)))))).re +
    (-346 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K))))))).re +
    (566 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K*(K)))))))).re +
    (-1848 : ℝ) * (Matrix.trace (A*(B*(A*(K))))).re +
    (976 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K)))))).re +
    (668 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K))))))).re +
    (-260 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K*(K)))))))).re +
    (-400 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K*(K*(K))))))))).re +
    (-576 : ℝ) * (Matrix.trace (A*(B*(B*(K))))).re +
    (522 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K)))))).re +
    (598 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K))))))).re +
    (-272 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K*(K)))))))).re +
    (-272 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K*(K*(K))))))))).re +
    (-1578 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K)))))).re +
    (716 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K))))))).re +
    (92 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K*(K)))))))).re +
    (194 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K*(K*(K))))))))).re +
    (-576 : ℝ) * (Matrix.trace (A*(B*(K*(B))))).re +
    (394 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K)))))).re +
    (306 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K))))))).re +
    (-332 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K*(K)))))))).re +
    (102 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K*(K*(K))))))))).re +
    (914 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K))))))).re +
    (42 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K)))))))).re +
    (-324 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K*(K))))))))).re +
    (-1180 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B)))))).re +
    (511 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K))))))).re +
    (363 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K)))))))).re +
    (-360 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K*(K))))))))).re +
    (-1578 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B)))))).re +
    (-1736 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K))))))).re +
    (152 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K)))))))).re +
    (914 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B))))))).re +
    (152 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K)))))))).re +
    (-566 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K))))))))).re +
    (716 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K))))))).re +
    (92 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K*(K)))))))).re +
    (194 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K*(K*(K))))))))).re +
    (-576 : ℝ) * (Matrix.trace (A*(K*(B*(B))))).re +
    (-988 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K)))))).re +
    (580 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K))))))).re +
    (188 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K*(K)))))))).re +
    (94 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K*(K*(K))))))))).re +
    (550 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K)))))))).re +
    (-270 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K*(K))))))))).re +
    (394 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B)))))).re +
    (-350 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K))))))).re +
    (40 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K)))))))).re +
    (-82 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K*(K))))))))).re +
    (194 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K))))))))).re +
    (511 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B))))))).re +
    (770 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K)))))))).re +
    (-309 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K))))))))).re +
    (42 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B)))))))).re +
    (194 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K))))))))).re +
    (-324 : ℝ) * (Matrix.trace (A*(K*(K*(B*(A*(K*(K*(K))))))))).re +
    (522 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B)))))).re +
    (580 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K))))))).re +
    (-104 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K*(K)))))))).re +
    (-316 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K*(K*(K))))))))).re +
    (306 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B))))))).re +
    (40 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K)))))))).re +
    (70 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K))))))))).re +
    (363 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B)))))))).re +
    (-309 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K))))))))).re +
    (598 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B))))))).re +
    (188 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B*(K)))))))).re +
    (-316 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B*(K*(K))))))))).re +
    (-332 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(B)))))))).re +
    (-82 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(B*(K))))))))).re +
    (-360 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(K*(B))))))))).re +
    (-272 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(B)))))))).re +
    (94 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(B*(K))))))))).re +
    (102 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(K*(B))))))))).re +
    (-272 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(K*(B*(B))))))))).re +
    (480 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K)))))).re +
    (222 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K))))))).re +
    (-344 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K*(K)))))))).re +
    (-358 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K*(K*(K))))))))).re +
    (384 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K)))))).re +
    (536 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K))))))).re +
    (-216 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K*(K)))))))).re +
    (174 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K*(K*(K))))))))).re +
    (536 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K))))))).re +
    (308 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K*(K)))))))).re +
    (-310 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K*(K*(K))))))))).re +
    (-216 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(B*(K)))))))).re +
    (-310 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(B*(K*(K))))))))).re +
    (174 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(K*(B*(K))))))))).re +
    (-262 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K))))))).re +
    (-320 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K*(K)))))))).re +
    (-208 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K*(K*(K))))))))).re +
    (-270 : ℝ) * (Matrix.trace (B*(K*(B*(K*(K*(B*(K*(K))))))))).re := by
  simp only [traceGram, words, M10, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val_elim, star_sub, star_add, star_mul, hA.star_eq, hB.star_eq, hK.star_eq, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_baa A B K,
    w_baak A B K,
    w_baakk A B K,
    w_babk A B K,
    w_babkk A B K,
    w_baka A B K,
    w_bakak A B K,
    w_bakakk A B K,
    w_bakb A B K,
    w_bakbk A B K,
    w_bakbkk A B K,
    w_bakka A B K,
    w_bakkak A B K,
    w_bakkakk A B K,
    w_bakkb A B K,
    w_bakkbk A B K,
    w_bakkbkk A B K,
    w_bakkka A B K,
    w_bakkkak A B K,
    w_bakkkakk A B K,
    w_bakkkb A B K,
    w_bakkkbk A B K,
    w_bakkkbkk A B K,
    w_bakkkka A B K,
    w_bakkkkak A B K,
    w_bakkkkb A B K,
    w_bakkkkbk A B K,
    w_bakkkkka A B K,
    w_bakkkkkb A B K,
    w_bbka A B K,
    w_bbkak A B K,
    w_bbkakk A B K,
    w_bbkka A B K,
    w_bbkkak A B K,
    w_bbkkakk A B K,
    w_bbkkb A B K,
    w_bbkkka A B K,
    w_bbkkkak A B K,
    w_bbkkkakk A B K,
    w_bbkkkb A B K,
    w_bbkkkka A B K,
    w_bbkkkkak A B K,
    w_bbkkkkb A B K,
    w_bbkkkkka A B K,
    w_bbkkkkkb A B K,
    w_bkaa A B K,
    w_bkaak A B K,
    w_bkaakk A B K,
    w_bkabk A B K,
    w_bkabkk A B K,
    w_bkaka A B K,
    w_bkakak A B K,
    w_bkakakk A B K,
    w_bkakb A B K,
    w_bkakbk A B K,
    w_bkakbkk A B K,
    w_bkakka A B K,
    w_bkakkak A B K,
    w_bkakkakk A B K,
    w_bkakkb A B K,
    w_bkakkbk A B K,
    w_bkakkbkk A B K,
    w_bkakkka A B K,
    w_bkakkkak A B K,
    w_bkakkkb A B K,
    w_bkakkkbk A B K,
    w_bkakkkka A B K,
    w_bkakkkkb A B K,
    w_bkba A B K,
    w_bkbak A B K,
    w_bkbakk A B K,
    w_bkbbk A B K,
    w_bkbbkk A B K,
    w_bkbka A B K,
    w_bkbkak A B K,
    w_bkbkakk A B K,
    w_bkbkb A B K,
    w_bkbkka A B K,
    w_bkbkkak A B K,
    w_bkbkkakk A B K,
    w_bkbkkb A B K,
    w_bkbkkbk A B K,
    w_bkbkkka A B K,
    w_bkbkkkak A B K,
    w_bkbkkkb A B K,
    w_bkbkkkbk A B K,
    w_bkbkkkka A B K,
    w_bkbkkkkb A B K,
    w_bkkaa A B K,
    w_bkkaak A B K,
    w_bkkaakk A B K,
    w_bkkabk A B K,
    w_bkkabkk A B K,
    w_bkkaka A B K,
    w_bkkakak A B K,
    w_bkkakakk A B K,
    w_bkkakb A B K,
    w_bkkakbk A B K,
    w_bkkakbkk A B K,
    w_bkkakka A B K,
    w_bkkakkak A B K,
    w_bkkakkb A B K,
    w_bkkakkbk A B K,
    w_bkkakkka A B K,
    w_bkkakkkb A B K,
    w_bkkba A B K,
    w_bkkbak A B K,
    w_bkkbakk A B K,
    w_bkkbbk A B K,
    w_bkkbbkk A B K,
    w_bkkbka A B K,
    w_bkkbkak A B K,
    w_bkkbkakk A B K,
    w_bkkbkb A B K,
    w_bkkbkbk A B K,
    w_bkkbkbkk A B K,
    w_bkkbkka A B K,
    w_bkkbkkak A B K,
    w_bkkbkkb A B K,
    w_bkkbkkbk A B K,
    w_bkkbkkka A B K,
    w_bkkbkkkb A B K]
  norm_num
  ring

private theorem expand_M11 (A B K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hK : K.IsHermitian) :
    traceGram B K (words A B K) M11 =
    (2424 : ℝ) * (Matrix.trace (A*(B*(A*(K))))).re +
    (-3376 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K)))))).re +
    (612 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K))))))).re +
    (260 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K*(K)))))))).re +
    (400 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K*(K*(K))))))))).re +
    (-1482 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K)))))).re +
    (682 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K))))))).re +
    (272 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K*(K)))))))).re +
    (272 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K*(K*(K))))))))).re +
    (-342 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K)))))).re +
    (244 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K))))))).re +
    (-92 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K*(K)))))))).re +
    (-194 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K*(K*(K))))))))).re +
    (-942 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K)))))).re +
    (640 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K))))))).re +
    (332 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K*(K)))))))).re +
    (-102 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K*(K*(K))))))))).re +
    (68 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K))))))).re +
    (-328 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K)))))))).re +
    (324 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K*(K*(K))))))))).re +
    (-28 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K))))))).re +
    (-234 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K)))))))).re +
    (360 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K*(K*(K))))))))).re +
    (-342 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B)))))).re +
    (720 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K))))))).re +
    (-552 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K*(K)))))))).re +
    (68 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B))))))).re +
    (-552 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K)))))))).re +
    (798 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B*(K*(K))))))))).re +
    (244 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K))))))).re +
    (-92 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K*(K)))))))).re +
    (-194 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K*(K*(K))))))))).re +
    (394 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K))))))).re +
    (-188 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K*(K)))))))).re +
    (-94 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K*(K*(K))))))))).re +
    (256 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K)))))))).re +
    (270 : ℝ) * (Matrix.trace (A*(K*(B*(K*(A*(K*(K*(K))))))))).re +
    (-942 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B)))))).re +
    (-104 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K))))))).re +
    (306 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K)))))))).re +
    (82 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K*(K*(K))))))))).re +
    (-310 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(A*(K*(K))))))))).re +
    (-28 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B))))))).re +
    (-1272 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K)))))))).re +
    (538 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B*(K*(K))))))))).re +
    (-328 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B)))))))).re +
    (-310 : ℝ) * (Matrix.trace (A*(K*(K*(A*(K*(K*(B*(K))))))))).re +
    (324 : ℝ) * (Matrix.trace (A*(K*(K*(B*(A*(K*(K*(K))))))))).re +
    (-1482 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B)))))).re +
    (394 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K))))))).re +
    (-344 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K*(K)))))))).re +
    (316 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K*(K*(K))))))))).re +
    (640 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B))))))).re +
    (306 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K)))))))).re +
    (-528 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B*(K*(K))))))))).re +
    (-234 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B)))))))).re +
    (538 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(K*(B*(K))))))))).re +
    (682 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B))))))).re +
    (-188 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B*(K)))))))).re +
    (316 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B*(K*(K))))))))).re +
    (332 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(B)))))))).re +
    (82 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(B*(K))))))))).re +
    (360 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(K*(K*(B))))))))).re +
    (272 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(B)))))))).re +
    (-94 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(B*(K))))))))).re +
    (-102 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(B*(K*(B))))))))).re +
    (272 : ℝ) * (Matrix.trace (A*(K*(K*(K*(K*(K*(B*(B))))))))).re +
    (1058 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K))))))).re +
    (344 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K*(K)))))))).re +
    (358 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K*(K*(K))))))))).re +
    (424 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K))))))).re +
    (216 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K*(K)))))))).re +
    (-174 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K*(K*(K))))))))).re +
    (424 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K))))))).re +
    (-308 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K*(K)))))))).re +
    (310 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K*(K*(K))))))))).re +
    (216 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(B*(K)))))))).re +
    (310 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(B*(K*(K))))))))).re +
    (-174 : ℝ) * (Matrix.trace (B*(B*(K*(K*(K*(K*(B*(K))))))))).re +
    (518 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K))))))).re +
    (320 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K*(K)))))))).re +
    (208 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K*(K*(K))))))))).re +
    (270 : ℝ) * (Matrix.trace (B*(K*(B*(K*(K*(B*(K*(K))))))))).re := by
  simp only [traceGram, words, M11, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val_elim, star_sub, star_add, star_mul, hA.star_eq, hB.star_eq, hK.star_eq, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_baka A B K,
    w_bakak A B K,
    w_bakakk A B K,
    w_bakbk A B K,
    w_bakbkk A B K,
    w_bakka A B K,
    w_bakkak A B K,
    w_bakkakk A B K,
    w_bakkb A B K,
    w_bakkbk A B K,
    w_bakkbkk A B K,
    w_bakkka A B K,
    w_bakkkak A B K,
    w_bakkkakk A B K,
    w_bakkkb A B K,
    w_bakkkbk A B K,
    w_bakkkbkk A B K,
    w_bakkkka A B K,
    w_bakkkkak A B K,
    w_bakkkkb A B K,
    w_bakkkkbk A B K,
    w_bakkkkka A B K,
    w_bakkkkkb A B K,
    w_bbkka A B K,
    w_bbkkak A B K,
    w_bbkkakk A B K,
    w_bbkkka A B K,
    w_bbkkkak A B K,
    w_bbkkkakk A B K,
    w_bbkkkb A B K,
    w_bbkkkka A B K,
    w_bbkkkkak A B K,
    w_bbkkkkb A B K,
    w_bbkkkkka A B K,
    w_bbkkkkkb A B K,
    w_bkaka A B K,
    w_bkakak A B K,
    w_bkakakk A B K,
    w_bkakbk A B K,
    w_bkakbkk A B K,
    w_bkakka A B K,
    w_bkakkak A B K,
    w_bkakkakk A B K,
    w_bkakkb A B K,
    w_bkakkbk A B K,
    w_bkakkbkk A B K,
    w_bkakkka A B K,
    w_bkakkkak A B K,
    w_bkakkkb A B K,
    w_bkakkkbk A B K,
    w_bkakkkka A B K,
    w_bkakkkkb A B K,
    w_bkbka A B K,
    w_bkbkak A B K,
    w_bkbkakk A B K,
    w_bkbkka A B K,
    w_bkbkkak A B K,
    w_bkbkkakk A B K,
    w_bkbkkb A B K,
    w_bkbkkbk A B K,
    w_bkbkkka A B K,
    w_bkbkkkak A B K,
    w_bkbkkkb A B K,
    w_bkbkkkbk A B K,
    w_bkbkkkka A B K,
    w_bkbkkkkb A B K,
    w_bkkaka A B K,
    w_bkkakak A B K,
    w_bkkakakk A B K,
    w_bkkakbk A B K,
    w_bkkakbkk A B K,
    w_bkkakka A B K,
    w_bkkakkak A B K,
    w_bkkakkb A B K,
    w_bkkakkbk A B K,
    w_bkkakkka A B K,
    w_bkkakkkb A B K,
    w_bkkbka A B K,
    w_bkkbkak A B K,
    w_bkkbkakk A B K,
    w_bkkbkbk A B K,
    w_bkkbkbkk A B K,
    w_bkkbkka A B K,
    w_bkkbkkak A B K,
    w_bkkbkkb A B K,
    w_bkkbkkbk A B K,
    w_bkkbkkka A B K,
    w_bkkbkkkb A B K]
  norm_num
  ring

private theorem expand_p2 (A B K : Matrix n n ℂ) :
    coefficient2 (A+B) A K =
    (3 : ℝ) * (Matrix.trace (A*(A*(A)))).re +
    (-6 : ℝ) * (Matrix.trace (A*(A*(A*(K))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K)))))).re +
    (3 : ℝ) * (Matrix.trace (A*(A*(B)))).re +
    (-4 : ℝ) * (Matrix.trace (A*(A*(B*(K))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K)))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K)))))).re +
    (-4 : ℝ) * (Matrix.trace (A*(A*(K*(B))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K)))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B)))))).re +
    (-4 : ℝ) * (Matrix.trace (A*(B*(A*(K))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K)))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(B*(B*(K))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K)))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K)))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(B*(K*(B))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K)))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B)))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B)))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(K*(B*(B))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K)))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B)))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B)))))).re +
    (5/3 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K)))))).re +
    (4/3 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K)))))).re := by
  simp only [coefficient2, traceCoefficient2, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_aaka A B K,
    w_abka A B K,
    w_akaa A B K,
    w_akab A B K,
    w_akba A B K,
    w_kakaa A B K,
    w_kakab A B K,
    w_kakba A B K,
    w_kakbb A B K,
    w_kbkaa A B K,
    w_kbkab A B K,
    w_kbkba A B K,
    w_kbkbb A B K,
    w_kkaaa A B K,
    w_kkaab A B K,
    w_kkaba A B K,
    w_kkabb A B K,
    w_kkbaa A B K,
    w_kkbab A B K,
    w_kkbba A B K,
    w_kkbbb A B K]
  norm_num
  ring

private theorem expand_p3 (A B K : Matrix n n ℂ) :
    coefficient3 (A+B) A K =
    (1 : ℝ) * (Matrix.trace (A*(A*(A)))).re +
    (-6 : ℝ) * (Matrix.trace (A*(A*(A*(K))))).re +
    (5 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K)))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(A*(A*(K*(K*(K))))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(A*(B*(K))))).re +
    (10/3 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K)))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(A*(B*(K*(K*(K))))))).re +
    (4 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(A*(K*(A*(K*(K))))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(A*(K*(B))))).re +
    (8/3 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(A*(K*(B*(K*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(A*(K*(K*(A*(K))))))).re +
    (10/3 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(A*(K*(K*(B*(K))))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(A*(K*(K*(K*(B))))))).re +
    (-2 : ℝ) * (Matrix.trace (A*(B*(A*(K))))).re +
    (10/3 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K)))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(B*(A*(K*(K*(K))))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K)))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(B*(B*(K*(K*(K))))))).re +
    (8/3 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(B*(K*(A*(K*(K))))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(B*(K*(B*(K*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(B*(K*(K*(A*(K))))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(B*(K*(K*(B*(K))))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(B*(K*(K*(K*(B))))))).re +
    (-8/27 : ℝ) * (Matrix.trace (A*(K*(A*(K*(A*(K))))))).re +
    (8/3 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B)))))).re +
    (-8/9 : ℝ) * (Matrix.trace (A*(K*(A*(K*(B*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(A*(K*(K*(B))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(B*(A*(K*(K))))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(B*(B*(K*(K))))))).re +
    (4/3 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B)))))).re +
    (-8/9 : ℝ) * (Matrix.trace (A*(K*(B*(K*(B*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(B*(K*(K*(B))))))).re +
    (5/3 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B)))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(K*(B*(B*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (A*(K*(K*(B*(K*(B))))))).re +
    (-40/27 : ℝ) * (Matrix.trace (A*(K*(K*(K*(B*(B))))))).re +
    (-40/27 : ℝ) * (Matrix.trace (B*(B*(B*(K*(K*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (B*(B*(K*(B*(K*(K))))))).re +
    (-10/9 : ℝ) * (Matrix.trace (B*(B*(K*(K*(B*(K))))))).re +
    (-8/27 : ℝ) * (Matrix.trace (B*(K*(B*(K*(B*(K))))))).re := by
  simp only [coefficient3, traceCoefficient3, 
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Matrix.mul_assoc]
  simp only [
    w_aaka A B K,
    w_aakka A B K,
    w_abkka A B K,
    w_akaa A B K,
    w_akaak A B K,
    w_akab A B K,
    w_akabk A B K,
    w_akaka A B K,
    w_akbak A B K,
    w_akbka A B K,
    w_akkaa A B K,
    w_akkab A B K,
    w_akkba A B K,
    w_kakaka A B K,
    w_kakakb A B K,
    w_kakbka A B K,
    w_kakbkb A B K,
    w_kbkaka A B K,
    w_kbkakb A B K,
    w_kbkbka A B K,
    w_kbkbkb A B K,
    w_kkaaka A B K,
    w_kkaakb A B K,
    w_kkabka A B K,
    w_kkabkb A B K,
    w_kkakaa A B K,
    w_kkakab A B K,
    w_kkakba A B K,
    w_kkakbb A B K,
    w_kkbaka A B K,
    w_kkbakb A B K,
    w_kkbbka A B K,
    w_kkbbkb A B K,
    w_kkbkaa A B K,
    w_kkbkab A B K,
    w_kkbkba A B K,
    w_kkbkbb A B K,
    w_kkkaaa A B K,
    w_kkkaab A B K,
    w_kkkaba A B K,
    w_kkkabb A B K,
    w_kkkbaa A B K,
    w_kkkbab A B K,
    w_kkkbba A B K,
    w_kkkbbb A B K]
  norm_num
  ring

/-- The full K certificate, with exactly the original ordered Taylor coefficients. -/
theorem coefficient_gap_identity (A B K : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hK : K.IsHermitian) :
    144 * (2*coefficient2 (A+B) A K - 6*coefficient3 (A+B) A K) =
      traceGram A (1-K) (words A B K) M00 +
      traceGram A K (words A B K) M01 +
      traceGram B (1-K) (words A B K) M10 +
      traceGram B K (words A B K) M11 := by
  rw [expand_M00 A B K hA hB hK, expand_M01 A B K hA hB hK,
    expand_M10 A B K hA hB hK, expand_M11 A B K hA hB hK,
    expand_p2, expand_p3]
  ring

/-- Positive endpoint weights imply the positive-direction coefficient bound.
The endpoints may be singular and the physical dimension is arbitrary. -/
theorem coefficient_gap_nonneg (U H K : Matrix n n ℂ)
    (hH : H.PosSemidef) (hUH : (U-H).PosSemidef)
    (hK : K.PosSemidef) (hIK : (1-K).PosSemidef) :
    6*coefficient3 U H K ≤ 2*coefficient2 U H K := by
  have he := coefficient_gap_identity H (U-H) K hH.isHermitian
    hUH.isHermitian hK.isHermitian
  have hu : H+(U-H) = U := by abel
  rw [hu] at he
  obtain ⟨h00, h01, h10, h11⟩ := grams_posSemidef
  have h0 := weighted_traceGram_nonneg H (1-K) (words H (U-H) K) M00 hH hIK h00
  have h1 := weighted_traceGram_nonneg H K (words H (U-H) K) M01 hH hK h01
  have h2 := weighted_traceGram_nonneg (U-H) (1-K) (words H (U-H) K) M10 hUH hIK h10
  have h3 := weighted_traceGram_nonneg (U-H) K (words H (U-H) K) M11 hUH hK h11
  linarith

end D5.S3.Quantum.Matrix.HsfContractionCubic

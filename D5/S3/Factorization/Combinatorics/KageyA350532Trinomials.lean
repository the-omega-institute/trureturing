/- GID: D5/S3/Factorization/Combinatorics/KageyA350532Trinomials
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/KageyA350532Trinomials
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact GF(2) trinomial perfect-power counts. -/
/-
admission_basis: open-problem-resolution (#18614; Proved)
escape_witness: none.
Direct frozen dependencies: D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary.
Its current declaration statement_id requires the Stage-B scoped report.
Declaration classifications inline same-delivery helpers and stop at pinned upstream owners.
claim: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: result.
result: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: settling result.
The same-delivery sparse-power count supplies the trinomial count.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21875
-/

import D5.S3.Factorization.Combinatorics.KageyA350532Binomials

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.KageyA350532Trinomials

/-- The third conjecture of OEIS A350532. Subtraction and division are in Nat. -/
def claim : Prop := ∀ n : ℕ, 1 ≤ n →
  KageyA350532Binomials.T (2 * n) 3 = (n ^ 2 - n) / 2

theorem result : claim := by
  intro n hn
  rw [KageyA350532Binomials.card_sparse_powers n 2 (by decide) (by decide),
    Nat.choose_two_right]
  congr 1
  rw [Nat.mul_sub_left_distrib, mul_one, pow_two]

end D5.S3.Factorization.Combinatorics.KageyA350532Trinomials

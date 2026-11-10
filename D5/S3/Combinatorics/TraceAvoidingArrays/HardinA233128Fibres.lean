/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Fibres
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128Fibres
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Exact scanner fibres and finite row-sum coordinates. -/

/-
admission_basis: open-problem-resolution (#28672; Proved)
escape_witness: none; all-height class reduction is semiconjugacy iteration.
After normalizing finite one-step premises, v_eq_w is an instance of
Function.Semiconj.iterate_right. It and its downstream chain are bind-only.
Declaration namespace: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
DIRECT_FROZEN_DEPENDENCIES
DECLARATION_CONSUMERS
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthLegal colour_bond_iff)
open HardinA233255PairTransfer (Row rowLegal PairRow rowProper)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
private theorem class_fibres (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k = ∑ q : PairRow,
      rowWeight s q * if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
        (∀ j, p j ≠ q j) ∧ boundaryClass (rowFinish s q) q = k then 1 else 0 := by
  rw [← scanner_fibres 7 s (fun t q =>
    if (∀ j : Fin 6, q j.castSucc ≠ q j.succ) ∧
      (∀ j, p j ≠ q j) ∧ boundaryClass t q = k then (1 : ℤ) else 0)]
  unfold classCount
  apply Finset.sum_congr rfl
  intro c _
  simp only [← colour_bond_iff]
  change (if rowLegal c ∧ compatible p c ∧ good s c ∧
      boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) =
    if good s c then (if rowLegal c ∧ compatible p c ∧
      boundaryClass (finish s c) (labels c) = k then 1 else 0) else 0
  by_cases hg : good s c <;> simp [hg]

private theorem label_sum (g : PairRow → ℤ) :
    (∑ q, g q) = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      ∑ e : Fin 3, ∑ f : Fin 3, ∑ h : Fin 3, g ![a, b, c, d, e, f, h] := by
  let e : PairRow ≃ Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 :=
    { toFun := fun q => (q 0, q 1, q 2, q 3, q 4, q 5, q 6)
      invFun := fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2]
      left_inv := by intro q; ext j; fin_cases j <;> rfl
      right_inv := by rintro ⟨a, b, c, d, e, f, g⟩; rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

private theorem class_fibres_normalized (s : Seen) (p : PairRow) (k : Fin 21) :
    classCount s p k =
      ∑ q0 : Fin 3, ∑ q1 : Fin 3, ∑ q2 : Fin 3, ∑ q3 : Fin 3,
      ∑ q4 : Fin 3, ∑ q5 : Fin 3, ∑ q6 : Fin 3,
      rowWeight s ![q0, q1, q2, q3, q4, q5, q6] *
      if rowProper ![q0, q1, q2, q3, q4, q5, q6] ∧
        (∀ j : Fin 7, p j ≠ (![q0, q1, q2, q3, q4, q5, q6] : PairRow) j) ∧
        boundaryClass (rowFinish s ![q0, q1, q2, q3, q4, q5, q6])
          ![q0, q1, q2, q3, q4, q5, q6] = k then 1 else 0 := by
  rw [class_fibres, label_sum]
  rfl


end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

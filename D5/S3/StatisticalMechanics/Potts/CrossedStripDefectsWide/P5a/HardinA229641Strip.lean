/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.vector_polynomial
   digest: The order-thirty recurrence for five-row two-defect canonical HDA colourings. -/

/-
admission_basis: open-problem-resolution (#32224; Proved)
escape_witness: result uses the two-defect vector_polynomial and the computed cut bound through HardinA229538Strip.labelled_scale.
a: proof_shape=bind-only; consumers=HardinA229641Strip.result
transfer_count: proof_shape=bind-only; consumers=HardinA229641Strip.result
result: proof_shape=content; consumers=none (external open-problem-resolution #32224)
-/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538StripData
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229641StripCertificate
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Chromatic
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Recurrence
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Algebra.Order.SuccPred

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229641Strip

open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA233178Chromatic (Column)
open HardinA233178Recurrence (columnEquiv)
open HardinA229538StripData (edges cost bondDefects_empty zero_cost_entry oneDefect transfer_readout)
open HardinA229538Strip (canonicalCount transition_entry labelled_scale)
open HardinA229641StripCertificate (twoDefect transfer terminal coefficients641 vector_polynomial)
open DefectTransfer (bondDefects literalCount lumped_count)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def a (n : ℕ) : ℕ := canonicalCount 2 n

private theorem transfer_count (n : ℕ) :
    (literalCount (q := 3) ∅ edges 2 (n + 1) : ℤ) =
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ n).mulVec terminal) := by
  let cl (p : Column) (d : ℕ) : Column ⊕ (Column ⊕ Column) :=
    if d ≤ 1 then Sum.inr (HardinA229538Strip.residual p d) else Sum.inl p
  let C (p : Column) (r : Fin 5 → Fin 3) : ℕ := bondDefects edges (columnEquiv p) r
  let col : Column ⊕ (Column ⊕ Column) → Column := Sum.elim id (Sum.elim id id)
  have ctr (p q : Column) : C p (columnEquiv q) = cost p q := rfl
  have cut (p q : Column) (d : ℕ) (hd : d ≤ 2) (x : Column ⊕ (Column ⊕ Column)) :
      (if cost p q ≤ d ∧ cl q (d - cost p q) = x then (1 : ℤ) else 0) =
        (if col x = q then transfer (cl p d) x else 0) := by
    have cutoff : cost p q ≤ 2 ↔ cost p q = 0 ∨ cost p q = 1 ∨ cost p q = 2 :=
      Order.le_two_iff
    by_cases hd' : d ≤ 1
    · have bound : d - cost p q ≤ 1 := (Nat.sub_le _ _).trans hd'
      cases x with
      | inl x => simp [col, cl, transfer, Matrix.fromBlocks, hd', bound]
      | inr x =>
        simpa [col, cl, transfer, Matrix.fromBlocks, hd', bound] using transition_entry p q d hd' x
    · have hd₂ : d = 2 := Nat.le_antisymm hd (Nat.lt_of_not_ge hd')
      subst d
      rcases x with x | x
      · by_cases hq : x = q
        · subst x
          by_cases h0 : cost p q = 0 <;> by_cases h1 : cost p q = 1 <;>
            by_cases h2 : cost p q = 2 <;>
              simp [col, cl, transfer, Matrix.fromBlocks, ← zero_cost_entry, cutoff, h0, h1, h2]
        · by_cases h0 : cost p q = 0 <;> by_cases h1 : cost p q = 1 <;>
            by_cases h2 : cost p q = 2 <;>
              simp [col, cl, transfer, Matrix.fromBlocks, ← zero_cost_entry, cutoff, h0, h1, h2, hq, Ne.symm hq]
      · rcases x with x | x <;> by_cases hq : x = q
        all_goals
          by_cases h0 : cost p q = 0 <;> by_cases h1 : cost p q = 1 <;>
            by_cases h2 : cost p q = 2 <;>
              simp [col, cl, HardinA229538Strip.residual, transfer, Matrix.fromBlocks, oneDefect, twoDefect, cutoff,
                h0, h1, h2, hq, eq_comm] <;> exact Ne.symm hq
  apply lumped_count ∅ edges columnEquiv.symm C (fun _ d => d ≤ 2) cl transfer
    (Sum.elim (1 : Column → ℤ) 0) terminal 2
  · intro r t
    simp [C]
  · intro p d hd
    by_cases h : d ≤ 1
    · by_cases z : d = 0 <;> simp [cl, HardinA229538Strip.residual, terminal, HardinA229538StripData.terminal, h, z]
    · have z : d ≠ 0 := Nat.ne_zero_of_lt (Nat.lt_of_not_ge h)
      simp [cl, terminal, h, z]
  · intro p d hd r _
    exact (Nat.sub_le _ _).trans hd
  · intro p d hd x
    rw [← columnEquiv.sum_comp]
    simp_rw [bondDefects_empty, Nat.add_zero, ctr, columnEquiv.symm_apply_apply, cut p _ d hd]
    simp [Finset.sum_ite_eq']
  · intro r _
    exact Nat.sub_le _ _
  · intro x
    rw [← columnEquiv.sum_comp]
    simp_rw [bondDefects_empty, Nat.zero_le, Nat.sub_zero, true_and, columnEquiv.symm_apply_apply]
    cases x <;> simp [cl]

attribute [local irreducible] a

/-- Hardin's order-thirty recurrence, starting at width thirty-four. -/
theorem result (n : ℕ) :
    (a (n + 34) : ℤ) =
      18 * (a (n + 33) : ℤ) - 15 * (a (n + 32) : ℤ) - 1191 * (a (n + 31) : ℤ) +
      3468 * (a (n + 30) : ℤ) + 31983 * (a (n + 29) : ℤ) - 108707 * (a (n + 28) : ℤ) -
      424479 * (a (n + 27) : ℤ) + 1614489 * (a (n + 26) : ℤ) + 2851598 * (a (n + 25) : ℤ) -
      13478352 * (a (n + 24) : ℤ) - 7797810 * (a (n + 23) : ℤ) + 66347438 * (a (n + 22) : ℤ) -
      12632640 * (a (n + 21) : ℤ) - 190067859 * (a (n + 20) : ℤ) + 147888798 * (a (n + 19) : ℤ) +
      287096430 * (a (n + 18) : ℤ) - 412178619 * (a (n + 17) : ℤ) - 138135927 * (a (n + 16) : ℤ) +
      522690894 * (a (n + 15) : ℤ) - 168525432 * (a (n + 14) : ℤ) - 273411640 * (a (n + 13) : ℤ) +
      227616084 * (a (n + 12) : ℤ) + 9610272 * (a (n + 11) : ℤ) - 73617984 * (a (n + 10) : ℤ) +
      21460464 * (a (n + 9) : ℤ) + 7359984 * (a (n + 8) : ℤ) - 4611168 * (a (n + 7) : ℤ) +
      186624 * (a (n + 6) : ℤ) + 279936 * (a (n + 5) : ℤ) - 46656 * (a (n + 4) : ℤ) := by
  have bridge (m : ℕ) (hm : 1 ≤ m) :
      dotProduct (Sum.elim (1 : Column → ℤ) 0) ((transfer ^ m).mulVec terminal) =
        6 * (a (m + 1) : ℤ) := by
    rw [← transfer_count]
    have hscale : literalCount (q := 3) ∅ edges 2 (m + 1) = 6 * a (m + 1) := by
      simpa only [a] using labelled_scale 2 m hm (Nat.lt_succ_self 2)
    rw [hscale]
    push_cast
    rfl
  have h := transfer_readout transfer terminal (Sum.elim (1 : Column → ℤ) 0)
    30 3 _ vector_polynomial n
  have mge (k : Fin 30) : 1 ≤ n + 3 + k.val :=
    Nat.le_add_right_of_le (Nat.le_add_left 1 (n + 2))
  have hn : 1 ≤ n + 3 + 30 := Nat.le_add_right_of_le (Nat.le_add_left 1 (n + 2))
  rw [bridge _ hn] at h
  simp_rw [fun k : Fin 30 => bridge (n + 3 + k.val) (mge k)] at h
  norm_num [coefficients641, Fin.sum_univ_succ, Nat.add_assoc] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229641Strip

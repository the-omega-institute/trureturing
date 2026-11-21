/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripData
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.vector_polynomial
   digest: The one-defect extension of the five-row HDA transfer. -/

/-
admission_basis: open-problem-resolution (#32224; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229538Strip.result)
edges: proof_shape=bind-only; consumers=HardinA229538Strip.canonicalCount
cost: proof_shape=bind-only; consumers=HardinA229538StripData.cost_zero
bondDefects_empty: proof_shape=bind-only; consumers=HardinA229538Strip.transfer_count, HardinA229641Strip.transfer_count
cost_zero: proof_shape=bind-only; consumers=HardinA229538StripData.zero_cost_entry._simp_1_1
zero_cost_entry: proof_shape=bind-only; consumers=HardinA229538Strip.transition_entry, HardinA229641Strip.transfer_count._simp_1_1
oneDefect: proof_shape=bind-only; consumers=HardinA229538StripData.transfer
transfer: proof_shape=bind-only; consumers=HardinA229538Strip.result
transfer_readout: proof_shape=bind-only; consumers=HardinA229538Strip.result
terminal: proof_shape=bind-only; consumers=HardinA229538Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Chromatic
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Data.Matrix.Block

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538StripData

open D5.S3.Combinatorics.TraceAvoidingArrays
open HardinA233178Chromatic (Column Bond T)
open HardinA233178Recurrence (columnEquiv)
open D5.S3.StatisticalMechanics.Potts.StripDefects
open DefectTransfer (bondDefects)
open scoped BigOperators

def edges : Finset (Fin 5 × Fin 5) :=
  letI : DecidablePred (fun e : Fin 5 × Fin 5 =>
      @HardinA233178Literal.Edges 2 (e.1, 0) (e.2, 1)) :=
    fun _ => by unfold HardinA233178Literal.Edges; infer_instance
  Finset.univ.filter fun e => @HardinA233178Literal.Edges 2 (e.1, 0) (e.2, 1)

def cost (p q : Column) : ℕ :=
  bondDefects edges (columnEquiv p) (columnEquiv q)

theorem bondDefects_empty (r : Fin 5 → Fin 3) : bondDefects ∅ r r = 0 := by
  rw [bondDefects, Finset.filter_empty, Finset.card_empty]

theorem cost_zero (p q : Column) : cost p q = 0 ↔ Bond p q := by
  simp only [cost, bondDefects, Finset.card_filter_eq_zero_iff, edges,
    Finset.mem_filter, Finset.mem_univ, true_and, HardinA233178Literal.Edges,
    Fin.val_zero, Fin.val_one, zero_add, Bond]
  exact ⟨fun h i j hij => h (i, j) hij, fun h e he => h e.1 e.2 he⟩

theorem zero_cost_entry (p q : Column) : (if cost p q = 0 then (1 : ℤ) else 0) = T p q := by
  simp only [T, cost_zero]

def oneDefect : Matrix Column Column ℤ :=
  fun p q => if cost p q = 1 then 1 else 0

def transfer : Matrix (Column ⊕ Column) (Column ⊕ Column) ℤ :=
  Matrix.fromBlocks T oneDefect 0 T

def terminal : Column ⊕ Column → ℤ := Sum.elim 0 1

/-- A column-vector relation gives the same shifted recurrence for each readout. -/
theorem transfer_readout {S : Type*} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℤ) (u v : S → ℤ) (d b : ℕ) (c : Fin d → ℤ)
    (h : (M ^ (b + d)).mulVec u = ∑ j : Fin d, c j • (M ^ (b + j.val)).mulVec u)
    (n : ℕ) :
    dotProduct v ((M ^ (n + b + d)).mulVec u) =
      ∑ j : Fin d, c j * dotProduct v ((M ^ (n + b + j.val)).mulVec u) := by
  have relation : DefectTransfer.forward M.transpose u (b + d) =
      ∑ j : Fin d, c j • DefectTransfer.forward M.transpose u (b + j.val) := by
    simpa only [DefectTransfer.forward_eq, ← Matrix.transpose_pow, Matrix.vecMul_transpose] using h
  simpa only [← Matrix.transpose_pow, Matrix.dotProduct_transpose_mulVec] using
    DefectTransfer.forward_shift M.transpose u v d b c relation n

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538StripData

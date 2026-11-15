/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Source/TailEntries
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Fourier/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Primitives/QFT/Source/TailEntries.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source
import all D5.S3.Quantum.FourierCircuit.Primitives.QFT.Primitive
import all D5.S3.Quantum.FourierCircuit.Core.Base.UnitaryCircuit.Placement.Entries
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Selection
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact matrix entries of the recursive native QFT tail

The tail uses the original successor positions. Its complete operator acts
on those coordinates and preserves the leading qubit, including coherences.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

open QFTPrimitive (layout)

private lemma tail_complement (n : Nat) (row column : (layout (n + 1)).Basis) :
    (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row =
      (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column ↔ row 0 = column 0 := by
  have zeroOutside : (0 : Fin (n + 1)) ∈
      (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩)ᶜ := by
    simp
  constructor
  · intro same
    exact congrFun same ⟨0, zeroOutside⟩
  · intro same
    funext index
    have isZero : index.val = 0 := by
      have outside := Finset.mem_compl.mp index.property
      rcases index with ⟨position, member⟩
      cases position using Fin.cases with
      | zero => rfl
      | succ position =>
          exact False.elim (outside (Finset.mem_map.mpr
            ⟨position, Finset.mem_univ _, rfl⟩))
    change row index.val = column index.val
    rw [isZero]
    exact same

/-- Placing the recursive word leaves precisely the leading coordinate untouched. -/
public lemma qftSource_tail_matrix_entry (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (layout n))
    (row column : (layout (n + 1)).Basis)
    (environment : oracles.Interpretation) :
    ((tailLayer oracles n body).matrix environment) row column =
      (body.matrix environment) (fun index => row index.succ) (fun index => column index.succ) *
        (if row 0 = column 0 then 1 else 0) := by
  classical
  have placed := UnitaryCircuit.placeAt_matrix (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) body environment
  refine (congrArg (fun operator : UnitaryOperator (layout (n + 1)).register =>
    operator row column) placed).trans ?_
  refine (UnitaryCircuit.operatorAt_entry (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) (body.matrix environment) row column).trans ?_
  change (body.matrix environment) (fun index => row index.succ) (fun index => column index.succ) *
    (if (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row =
      (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column then 1 else 0) = _
  by_cases same : row 0 = column 0
  · rw [if_pos ((tail_complement n row column).mpr same), if_pos same]
  · rw [if_neg (fun equal => same ((tail_complement n row column).mp equal)), if_neg same]

/-- In leading-bit and tail coordinates, the placed word is identity tensor its original matrix. -/
public lemma qftSource_tail_matrix_cons (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (layout n))
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin n → Fin 2)
    (environment : oracles.Interpretation) :
    ((tailLayer oracles n body).matrix environment) (Fin.cons rowHead rowTail) (Fin.cons
      columnHead columnTail) =
      (body.matrix environment) rowTail columnTail * (if rowHead = columnHead then 1 else 0) := by
  exact qftSource_tail_matrix_entry (environment := environment) oracles n body _ _

end

end QuantumAlg.QuantumFourierTransform.Source

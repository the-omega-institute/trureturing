/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Selection
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
Original file: QuantumAlg/Core/Base/Layout/Quantum/Selection.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Exact basis coordinates for selected quantum wires

A selection names positions in an existing layout. Its basis retains the
dimension at each selected physical wire; the complementary basis retains
every remaining wire. Restriction and reassembly use those positions directly,
without choosing a bijection from Hilbert-space cardinalities. This is the
concrete subsystem decomposition of the tensor basis [dW19, qcnotes.tex:389].
-/

section

namespace QuantumAlg.QuantumLayout

variable {systemCount : Nat}

/-- The original positions of the selected physical wires. -/
public abbrev SelectedPosition (selection : Finset (Fin systemCount)) :=
  {index : Fin systemCount // index ∈ selection}


/-- One local finite value at each selected original position. -/
public abbrev SelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :=
  (index : SelectedPosition selection) → Fin (layout.wire index.val).dimension

/-- One local finite value at every position outside the selection. -/
public abbrev ComplementBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :=
  layout.SelectedBasis selectionᶜ

/-- The selected register uses the exact dependent product of local bases. -/
@[expose, implicit_reducible]
public def selectedRegister (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) : Register where
  Index := layout.SelectedBasis selection
  fintype := inferInstance
  decEq := inferInstance

/-- The complementary register contains all unselected original positions. -/
@[expose, implicit_reducible]
public def complementRegister (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) : Register :=
  layout.selectedRegister selectionᶜ

/-- Read the original basis value at each selected position. -/
@[expose]
public def restrictSelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (basis : layout.Basis) :
    layout.SelectedBasis selection :=
  fun index => basis index.val

/-- Read the original basis value at every complementary position. -/
@[expose]
public def restrictComplementBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (basis : layout.Basis) :
    layout.ComplementBasis selection :=
  layout.restrictSelectedBasis selectionᶜ basis

/-- Reassemble a label by membership of each original physical position. -/
@[expose]
public def joinSelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection) : layout.Basis :=
  fun index => if member : index ∈ selection then selected ⟨index, member⟩
    else complement ⟨index, Finset.mem_compl.mpr member⟩

/-- Reassembly restores the full finite value at every selected physical wire. -/
public lemma joinSelectedBasis_selected_value (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection) (index : SelectedPosition selection) :
    layout.joinSelectedBasis selection selected complement index.val = selected index := by
  simp only [joinSelectedBasis, dif_pos index.property]

/-- Reassembly restores the full finite value at every complementary wire. -/
public lemma joinSelectedBasis_complement_value (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection)
    (index : SelectedPosition selectionᶜ) :
    layout.joinSelectedBasis selection selected complement index.val = complement index := by
  simp only [joinSelectedBasis, dif_neg (Finset.mem_compl.mp index.property)]

/-- Selection and complement give an exact basis equivalence by restriction. -/
@[expose]
public def selectionBasisEquiv (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :
    layout.Basis ≃ layout.SelectedBasis selection × layout.ComplementBasis selection where
  toFun basis :=
    (layout.restrictSelectedBasis selection basis, layout.restrictComplementBasis selection basis)
  invFun basis := layout.joinSelectedBasis selection basis.1 basis.2
  left_inv basis := by
    funext index
    by_cases member : index ∈ selection <;>
      simp [joinSelectedBasis, restrictSelectedBasis, restrictComplementBasis, member]
  right_inv basis := by
    apply Prod.ext
    · funext index
      exact layout.joinSelectedBasis_selected_value selection basis.1 basis.2 index
    · funext index
      exact layout.joinSelectedBasis_complement_value selection basis.1 basis.2 index


end QuantumAlg.QuantumLayout

end

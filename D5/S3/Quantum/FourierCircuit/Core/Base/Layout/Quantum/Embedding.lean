/- GID: D5/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Core/Base/Layout/Quantum/Embedding
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
Original file: QuantumAlg/Core/Base/Layout/Quantum/Embedding.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Selection
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum.Selection
import all D5.S3.Quantum.FourierCircuit.Core.Base.Layout.Quantum
public import Mathlib.Logic.Equiv.Basic

/-!
# Embedding the same physical systems in an ambient layout

An embedding selects distinct positions containing exactly the original wires.
Its basis maps only restrict and reassemble those coordinates. They cannot
change a local basis value or implement a permutation of quantum states.
-/

namespace QuantumAlg.QuantumLayout

/-- An ordered subsystem consists of the same physical wires in a larger layout. -/
public structure Embedding {small large : Nat}
    (source : QuantumLayout small) (target : QuantumLayout large) where
  /-- Distinct source positions select distinct ambient positions. -/
  position : Fin small ↪ Fin large
  /-- Selection preserves both physical identity and local dimension. -/
  wire_eq : ∀ index, target.wire (position index) = source.wire index

namespace Embedding

variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- The ambient positions occupied by the ordered subsystem. -/
@[expose]
public def selection (embedding : Embedding source target) : Finset (Fin large) :=
  Finset.univ.map embedding.position

/-- Source order identifies the selected ambient positions without changing their values. -/
@[expose]
public noncomputable def positionEquiv (embedding : Embedding source target) :
    Fin small ≃ SelectedPosition embedding.selection :=
  Equiv.ofBijective
    (fun index => ⟨embedding.position index, Finset.mem_map_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun _ _ equality => embedding.position.injective (congrArg Subtype.val equality), by
      intro index
      obtain ⟨original, _, same⟩ := Finset.mem_map.mp index.property
      exact ⟨original, Subtype.ext same⟩⟩


/-- Dimension equality casts a local value without permuting the computational basis. -/
@[expose]
public noncomputable def valueEquiv (embedding : Embedding source target) (index : Fin small) :
    Fin (source.wire index).dimension ≃
      Fin (target.wire (embedding.positionEquiv index).val).dimension where
  toFun value := Fin.cast (congrArg (fun wire => wire.dimension.val)
    (embedding.wire_eq index).symm) value
  invFun value := Fin.cast (congrArg (fun wire => wire.dimension.val)
    (embedding.wire_eq index)) value
  left_inv value := by
    apply Fin.ext
    rfl
  right_inv value := by
    apply Fin.ext
    rfl


/-- The selected subsystem basis in source order; every coordinate map is a dimension cast. -/
@[expose]
public noncomputable def selectedBasisEquiv (embedding : Embedding source target) :
    source.Basis ≃ target.SelectedBasis embedding.selection :=
  embedding.positionEquiv.piCongr embedding.valueEquiv


/-- Split an ambient basis into the ordered subsystem and every untouched wire. -/
@[expose]
public noncomputable def splitBasis (embedding : Embedding source target) :
    target.Basis ≃ source.Basis × target.ComplementBasis embedding.selection :=
  (target.selectionBasisEquiv embedding.selection).trans
    (Equiv.prodCongr embedding.selectedBasisEquiv.symm (Equiv.refl _))

/-- Splitting reads precisely the original basis value at each selected physical wire. -/
public lemma embedding_splitBasis_selected_value (embedding : Embedding source target)
    (basis : target.Basis) (index : Fin small) :
    ((embedding.splitBasis basis).1 index).val =
      (basis (embedding.position index)).val := rfl


end Embedding

end QuantumAlg.QuantumLayout

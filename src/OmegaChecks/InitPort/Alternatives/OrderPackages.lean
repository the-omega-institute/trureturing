module
import all Init.Data.Int.Package
import all Init.Data.Fin.Package

/-! Construct the order-package proofs directly from the concrete numeric orders. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem Int.instLinearOrderPackage._proof_2 :
    type_of% @_root_.Int.instLinearOrderPackage._proof_2 := by
  dsimp only
  intro a b
  change decide (a = b) = true ↔ a ≤ b ∧ b ≤ a
  constructor
  · intro h
    cases of_decide_eq_true h
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  · intro ⟨h, h'⟩
    exact decide_eq_true (Int.le_antisymm h h')

public theorem Int.instLinearOrderPackage._proof_7 :
    type_of% @_root_.Int.instLinearOrderPackage._proof_7 :=
  fun _ _ => Int.le_antisymm

public theorem Fin.instLinearOrderPackage._proof_5 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_5 := by
  intro n a b
  rw [← Fin.compare_val]
  exact (Std.isLE_compare (a := a.val) (b := b.val)).trans Fin.le_def.symm

public theorem Fin.instLinearOrderPackage._proof_6 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_6 := by
  intro n a b
  rw [← Fin.compare_val]
  exact (Std.isGE_compare (a := a.val) (b := b.val)).trans Fin.le_def.symm

public theorem Fin.instLinearOrderPackage._proof_7 :
    type_of% @_root_.Fin.instLinearOrderPackage._proof_7 :=
  fun {_} _ _ => Fin.le_antisymm

end OmegaChecks.InitPort.Alternatives

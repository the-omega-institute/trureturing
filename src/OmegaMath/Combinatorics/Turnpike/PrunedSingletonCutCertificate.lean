module

public import OmegaMath.Combinatorics.Turnpike.PrunedSingletonCutPair01
public import OmegaMath.Combinatorics.Turnpike.PrunedSingletonCutPair02
public import OmegaMath.Combinatorics.Turnpike.PrunedSingletonCutPair12

/-! Omega original.
# Complete singleton-cut certificate

The three coordinate-pair coverage theorems combine to cover all singleton cuts
for the shared integer assignment. Indices are zero-based.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedSingletonCutCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

theorem cut_checks (τ : Triangle 9) (u v w : Fin 3)
    (huv : u < v) (hwu : w ≠ u) (hwv : w ≠ v) (a b : Fin 20) :
    CutCheck τ u v w a b := by
  have hp : (u = 0 ∧ v = 1 ∧ w = 2) ∨
      (u = 0 ∧ v = 2 ∧ w = 1) ∨ (u = 1 ∧ v = 2 ∧ w = 0) := by
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
  rcases hp with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact cuts_01 τ (triangleCovered τ) a b
  · exact cuts_02 τ (triangleCovered τ) a b
  · exact cuts_12 τ (triangleCovered τ) a b

end
end Omega.Turnpike.PrunedSingletonCutCertificate

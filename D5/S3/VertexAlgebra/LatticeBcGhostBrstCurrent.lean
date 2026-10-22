import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.BcGhostActualConformalState
import D5.S3.VertexAlgebra.VertexOperatorTensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstCurrent

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents BcGhostFockSupport
open LatticeBcGhostBrstCharge
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

def cState : Fock ℂ := c 1 vacuum

def cField : VertexOperator ℂ (Fock ℂ) := BcGhostSuperStateField.Y cState

def ghostStressField : VertexOperator ℂ (Fock ℂ) :=
  BcGhostSuperStateField.Y BcGhostActualConformalState.omegaState

def ghostCurrent : VertexOperator ℂ (Fock ℂ) :=
  SuperFieldProducts.normal 1 cField ghostStressField

def matterField (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    VertexOperator ℂ (Carrier D) :=
  LatticeAllStateField.Y D (LatticeActualConformalState.omega D H)

def current (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    VertexOperator ℂ (State D) :=
  VertexOperatorTensorProduct.field (matterField D H) cField +
    (2 : ℂ)⁻¹ • VertexOperatorTensorProduct.field
      (VertexOperatorTensorProduct.identityField (Carrier D)) ghostCurrent

def candidateState (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    State D :=
  LatticeActualConformalState.omega D H ⊗ₜ[ℂ] cState +
    (2 : ℂ)⁻¹ • (LatticeAllStateField.vacuum D ⊗ₜ[ℂ]
      (cField[[-1]]) BcGhostActualConformalState.omegaState)

theorem cField_modes (index : ℤ) : cField[[index]] = c (index + 2) := by
  rw [cField, cState, BcGhostSuperStateField.stateField_c_generator,
    BcGhostSuperGenerators.currentField_modes]
  rfl

theorem ghostStressField_modes (index : ℤ) :
    ghostStressField[[index]] = L (K := ℂ) (index - 1) := by
  have modes := BcGhostActualConformalState.conformal_modes (index - 1)
  simpa only [ghostStressField, sub_add_cancel] using modes

theorem matterField_modes (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (index : ℤ) :
    (matterField D H)[[index]] = sugawaraMode D H (index - 1) := by
  have modes := LatticeActualConformalState.omega_modes D H (index - 1)
  simpa only [matterField, sub_add_cancel] using modes

theorem ghost_ascending_term (ghost : Fock ℂ) (offset : ℕ) :
    (cField[[-(offset : ℤ) - 1]]) ((ghostStressField[[offset]]) ghost) =
      BcGhostStressTails.outerNormalPair ((offset : ℤ) - 1) ghost := by
  have branch : -1 ≤ (offset : ℤ) - 1 := by omega
  rw [cField_modes, ghostStressField_modes]
  simp only [BcGhostStressTails.outerNormalPair, branch, if_true,
    LinearMap.comp_apply]
  rw [show -(offset : ℤ) - 1 + 2 = -((offset : ℤ) - 1) by omega]

theorem ghost_descending_term (ghost : Fock ℂ) (offset : ℕ) :
    (ghostStressField[[-(offset : ℤ) - 1]]) ((cField[[offset]]) ghost) =
      BcGhostStressTails.outerNormalPair (-2 - (offset : ℤ)) ghost := by
  have branch : ¬ -1 ≤ -2 - (offset : ℤ) := by omega
  rw [cField_modes, ghostStressField_modes]
  simp only [BcGhostStressTails.outerNormalPair, branch, if_false,
    LinearMap.comp_apply]
  rw [show -(offset : ℤ) - 1 - 1 = -2 - (offset : ℤ) by omega,
    show -(-2 - (offset : ℤ)) = (offset : ℤ) + 2 by omega]

theorem ghostCurrent_zero (ghost : Fock ℂ) :
    (ghostCurrent[[0]]) ghost = ∑ᶠ index : ℤ, BcGhostStressTails.outerNormalPair index ghost := by
  classical
  have support := BcGhostBrstSupport.normalGhost_support_interval ghost
  have nonnegative : 0 ≤ BcGhostBrstSupport.bound ghost := Int.natCast_nonneg _
  have split := BcGhostConformalFiniteComparison.split_common_interval
    (fun index : ℤ => BcGhostStressTails.outerNormalPair index ghost)
    (-BcGhostBrstSupport.bound ghost - 2) (2 * BcGhostBrstSupport.bound ghost + 4) (-2)
    (by omega) (by omega) support
  rw [ghostCurrent, SuperFieldProducts.normal_modes]
  simp only [zero_add, zero_sub, one_smul]
  simp_rw [ghost_ascending_term, ghost_descending_term]
  rw [add_comm]
  have asc : (fun offset : ℕ =>
      BcGhostStressTails.outerNormalPair ((offset : ℤ) - 1) ghost) =
      (fun offset : ℕ => BcGhostStressTails.outerNormalPair (-2 + 1 + (offset : ℤ)) ghost) := by
    funext offset
    congr 1
  rw [asc, split]
  exact (finsum_eq_sum_of_support_subset _
    (s := Finset.Icc (-BcGhostBrstSupport.bound ghost - 2)
      (2 * BcGhostBrstSupport.bound ghost + 4))
    (by simpa only [Finset.coe_Icc] using support)).symm

theorem matter_diagonal_reindex (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (matter : Carrier D) (ghost : Fock ℂ) :
    (∑ᶠ first : ℤ, ((matterField D H)[[first]]) matter ⊗ₜ[ℂ]
      (cField[[0 - 1 - first]]) ghost) =
      ∑ᶠ index : ℤ, sugawaraMode D H index matter ⊗ₜ[ℂ] c (-index) ghost := by
  apply finsum_eq_of_bijective (fun first : ℤ => first - 1)
    ⟨by intro first second equality; dsimp at equality; omega,
      by intro index; exact ⟨index + 1, by dsimp; omega⟩⟩
  intro first
  rw [matterField_modes, cField_modes]
  rw [show 0 - 1 - first + 2 = -(first - 1) by omega]

theorem matter_terms_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (matter : Carrier D) (ghost : Fock ℂ) :
    Function.HasFiniteSupport
      (fun index : ℤ => sugawaraMode D H index matter ⊗ₜ[ℂ] c (-index) ghost) := by
  have finite := (VertexOperatorTensorProduct.diagonal_finite
    (matterField D H) cField 0 matter ghost).comp_of_injective
      (show Function.Injective (fun index : ℤ => index + 1) by
        intro first second equality
        dsimp at equality
        omega)
  convert finite using 1
  funext index
  simp only [Function.comp_def, VertexOperatorTensorProduct.diagonal,
    matterField_modes, cField_modes]
  rw [show index + 1 - 1 = index by omega,
    show 0 - 1 - (index + 1) + 2 = -index by omega]

theorem lifted_ghost_terms_finite (D : LatticeData) (matter : Carrier D) (ghost : Fock ℂ) :
    Function.HasFiniteSupport
      (fun index : ℤ => matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair index ghost) := by
  apply (BcGhostStressTails.outer_has_finite_support ghost).subset
  intro index nonzero vanishes
  exact nonzero (by simp [vanishes])

theorem current_zero_tmul (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (matter : Carrier D) (ghost : Fock ℂ) :
    ((current D H)[[0]]) (matter ⊗ₜ[ℂ] ghost) = Q D H (matter ⊗ₜ[ℂ] ghost) := by
  classical
  have matterFinite := matter_terms_finite D H matter ghost
  have ghostFinite := lifted_ghost_terms_finite D matter ghost
  have scaledFinite : Function.HasFiniteSupport (fun index : ℤ =>
      (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair index ghost)) := by
    apply ghostFinite.subset
    intro index nonzero vanishes
    exact nonzero (by simp [vanishes])
  have mapped := (TensorProduct.mk ℂ (Carrier D) (Fock ℂ) matter).toAddMonoidHom.map_finsum
    (BcGhostStressTails.outer_has_finite_support ghost)
  simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply] at mapped
  simp only [current, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [VertexOperatorTensorProduct.field_mode, VertexOperatorTensorProduct.mode_tmul,
    matter_diagonal_reindex, VertexOperatorTensorProduct.field_identity_left]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  rw [ghostCurrent_zero, mapped, smul_finsum' _ ghostFinite,
    ← finsum_add_distrib matterFinite scaledFinite]
  have terms (index : ℤ) :
      sugawaraMode D H index matter ⊗ₜ[ℂ] c (-index) ghost +
        (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ] BcGhostStressTails.outerNormalPair index ghost) =
      A D H index (matter ⊗ₜ[ℂ] ghost) := by
    by_cases branch : -1 ≤ index <;>
      simp [A, N, C, M, G, BcGhostStressTails.outerNormalPair, branch]
  simp_rw [terms]
  rw [finsum_eq_sum_of_support_subset _
    (s := Finset.Icc (-BcGhostBrstSupport.bound ghost - 2) (chargeUpper D H matter ghost))
    (by simpa only [Finset.coe_Icc] using A_support_tmul D H matter ghost), Q_tmul]
  apply Finset.sum_congr rfl
  intro index member
  exact (terms index).symm

theorem current_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    (current D H)[[0]] = Q D H := by
  apply TensorProduct.ext'
  intro matter ghost
  exact current_zero_tmul D H matter ghost

theorem ghostCurrent_zero_vacuum : (ghostCurrent[[0]]) (vacuum : Fock ℂ) = 0 := by
  rw [ghostCurrent, SuperFieldProducts.normal_modes]
  have first (offset : ℕ) :
      (ghostStressField[[offset]]) (vacuum : Fock ℂ) = 0 :=
    BcGhostSuperStateField.stateField_creativity _ _ (by omega)
  have second (offset : ℕ) : (cField[[offset]]) (vacuum : Fock ℂ) = 0 :=
    BcGhostSuperStateField.stateField_creativity _ _ (by omega)
  simp [first, second]

theorem current_zero_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    ((current D H)[[0]]) (LatticeAllStateField.vacuum D ⊗ₜ[ℂ] (vacuum : Fock ℂ)) = 0 := by
  simp only [current, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply]
  rw [VertexOperatorTensorProduct.field_mode, VertexOperatorTensorProduct.mode_tmul,
    VertexOperatorTensorProduct.field_identity_left]
  have diagonalZero (first : ℤ) :
      ((matterField D H)[[first]]) (LatticeAllStateField.vacuum D) ⊗ₜ[ℂ]
        (cField[[0 - 1 - first]]) (vacuum : Fock ℂ) = 0 := by
    by_cases nonnegative : 0 ≤ first
    · rw [matterField, LatticeAllStateField.stateField_creativity D _ first nonnegative,
        TensorProduct.zero_tmul]
    · rw [cField, BcGhostSuperStateField.stateField_creativity _
        (0 - 1 - first) (by omega),
        TensorProduct.tmul_zero]
  simp only [diagonalZero, finsum_zero, TensorProduct.map_tmul,
    ghostCurrent_zero_vacuum, TensorProduct.tmul_zero, smul_zero, add_zero]

theorem Q_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Q D H (LatticeAllStateField.vacuum D ⊗ₜ[ℂ] (vacuum : Fock ℂ)) = 0 := by
  rw [← current_zero]
  exact current_zero_vacuum D H

#check @current_zero
#check @Q_vacuum
#print axioms current_zero
#print axioms Q_vacuum

end
end D5.S3.VertexAlgebra.LatticeBcGhostBrstCurrent

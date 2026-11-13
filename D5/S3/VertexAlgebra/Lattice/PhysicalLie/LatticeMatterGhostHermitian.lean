/-
The current original carrier and the ordinary Hermitian Hm and Hg are used
literally. No rotated ghost form, parity sign, positivity, or finite global
cutoff is introduced. The canonical suppliers and their attribution remain
unchanged: Bakalov--Kac, Scott Carnahan, Kalle Kytölä, Mathlib, Batteries,
and the original BRST literature. This new tensor extension uses their
existing factor-adjoint theorems; it does not reprove the factor adjoints.
-/

import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.Quantum.Fermionic.BcGhostBRSTHermitian
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

/-! Ordinary tensor Hermitian form on the original matter-ghost state space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeMatterGhostCoupling LatticeBRST
open SourceBPZ.OriginalMatterHermitian
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostHermitian

variable {D : LatticeData}

/- The occupation basis is used only to implement the universal finite
tensor extension. It imposes no charge, degree, shell, frame, or rank
restriction. Each coefficient below is an original matter state. -/
private def ghostBasis : Module.Basis (Finset ℕ) ℂ Fock :=
  Finsupp.basisSingleOne

private def slices (D : LatticeData) :
    State D ≃ₗ[ℂ] (Finset ℕ →₀ Carrier D) := by
  classical
  exact (TensorProduct.comm ℂ (Carrier D) Fock).trans
    (TensorProduct.equivFinsuppOfBasisLeft ghostBasis)

private theorem slices_tmul (v : Carrier D) (u : Fock) (S : Finset ℕ) :
    slices D (v ⊗ₜ[ℂ] u) S = u S • v := by
  change TensorProduct.equivFinsuppOfBasisLeft ghostBasis
    (u ⊗ₜ[ℂ] v) S = u S • v
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply ghostBasis u v S

@[simp] private theorem slices_tmul_ket (v : Carrier D) (S : Finset ℕ) :
    slices D (v ⊗ₜ[ℂ] ket S) = Finsupp.single S v := by
  classical
  ext T
  rw [slices_tmul]
  by_cases h : S = T
  · subst T
    simp [ket]
  · simp [ket, h, Ne.symm h]

/-- The true matter-ghost tensor Hermitian form, with both finite supports
taken from the actual algebraic tensor state. -/
def Hmg (x y : State D) : ℂ :=
  (slices D x).sum fun S v =>
    (slices D y).sum fun T w => Hm v w * Hg (ket S) (ket T)

@[simp] theorem Hmg_zero_left (y : State D) : Hmg (0 : State D) y = 0 := by
  unfold Hmg
  rw [(slices D).map_zero]
  rfl

@[simp] theorem Hmg_zero_right (x : State D) : Hmg x 0 = 0 := by
  unfold Hmg
  rw [(slices D).map_zero]
  exact Finset.sum_eq_zero fun _ _ => rfl

theorem Hmg_add_left (x z y : State D) :
    Hmg (x + z) y = Hmg x y + Hmg z y := by
  classical
  unfold Hmg
  rw [(slices D).map_add]
  refine Finsupp.sum_add_index' (f := slices D x) (g := slices D z) ?_ ?_
  · intro S
    apply Finset.sum_eq_zero
    intro T hT
    change Hm (0 : Carrier D) ((slices D y) T) * Hg (ket S) (ket T) = 0
    rw [Hm_zero_left (D := D) ((slices D y) T), zero_mul]
  · intro S v w
    simp only [Hm_add_left, add_mul, Finsupp.sum_add]

theorem Hmg_smul_left (a : ℂ) (x y : State D) :
    Hmg (a • x) y = star a * Hmg x y := by
  classical
  unfold Hmg
  rw [(slices D).map_smul a x]
  rw [Finsupp.sum_smul_index' (g := slices D x) (b := a) (by
    intro S
    apply Finset.sum_eq_zero
    intro T hT
    change Hm (0 : Carrier D) ((slices D y) T) * Hg (ket S) (ket T) = 0
    rw [Hm_zero_left (D := D) ((slices D y) T), zero_mul])]
  simp only [Hm_smul_left]
  change (∑ S ∈ (slices D x).support,
    ∑ T ∈ (slices D y).support,
      (star a * Hm ((slices D x) S) ((slices D y) T)) *
        Hg (ket S) (ket T)) =
    star a * (∑ S ∈ (slices D x).support,
      ∑ T ∈ (slices D y).support,
        Hm ((slices D x) S) ((slices D y) T) * Hg (ket S) (ket T))
  simp only [Finset.mul_sum, mul_assoc]

/-- Ordinary Hermitian symmetry; there is no degree-dependent sign. -/
theorem Hmg_hermitian (x y : State D) : Hmg x y = star (Hmg y x) := by
  classical
  change (∑ S ∈ (slices D x).support,
    ∑ T ∈ (slices D y).support,
      Hm ((slices D x) S) ((slices D y) T) * Hg (ket S) (ket T)) =
    (starRingEnd ℂ) (∑ T ∈ (slices D y).support,
      ∑ S ∈ (slices D x).support,
        Hm ((slices D y) T) ((slices D x) S) * Hg (ket T) (ket S))
  simp only [map_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  rw [Hm_hermitian ((slices D x) S) ((slices D y) T),
    Hg_hermitian (ket S) (ket T)]
  rfl

theorem Hmg_add_right (x y z : State D) :
    Hmg x (y + z) = Hmg x y + Hmg x z := by
  rw [Hmg_hermitian x (y + z), Hmg_add_left, star_add,
    ← Hmg_hermitian x y, ← Hmg_hermitian x z]

theorem Hmg_smul_right (a : ℂ) (x y : State D) :
    Hmg x (a • y) = a * Hmg x y := by
  rw [Hmg_hermitian x (a • y), Hmg_smul_left, star_mul, star_star,
    ← Hmg_hermitian x y]
  exact mul_comm _ _

theorem Hmg_sub_left (x z y : State D) :
    Hmg (x - z) y = Hmg x y - Hmg z y := by
  have hn : Hmg (-z) y = -Hmg z y := by
    simpa only [neg_one_smul, star_neg, star_one, neg_mul, one_mul] using
      Hmg_smul_left (-1) z y
  rw [sub_eq_add_neg, Hmg_add_left, hn, sub_eq_add_neg]

theorem Hmg_sub_right (x y z : State D) :
    Hmg x (y - z) = Hmg x y - Hmg x z := by
  have hn : Hmg x (-z) = -Hmg x z := by
    simpa only [neg_one_smul, neg_mul, one_mul] using Hmg_smul_right (-1) x z
  rw [sub_eq_add_neg, Hmg_add_right, hn, sub_eq_add_neg]

private theorem Hmg_tmul_ket (v w : Carrier D) (S T : Finset ℕ) :
    Hmg (v ⊗ₜ[ℂ] ket S) (w ⊗ₜ[ℂ] ket T) =
      Hm v w * Hg (ket S) (ket T) := by
  classical
  simp [Hmg, slices_tmul_ket]

private theorem Hmg_tmul_ket_left (v w : Carrier D) (S : Finset ℕ) (u : Fock) :
    Hmg (v ⊗ₜ[ℂ] ket S) (w ⊗ₜ[ℂ] u) = Hm v w * Hg (ket S) u := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' =>
      simp only [TensorProduct.tmul_add, Hmg_add_right, Hg_add_right,
        hu, hu', mul_add]
  | single T a =>
      have ha : Finsupp.single T a = a • ket T := by simp [ket]
      rw [ha, TensorProduct.tmul_smul, Hmg_smul_right, Hg_smul_right,
        Hmg_tmul_ket]
      ring

/-- The exact pure-tensor formula for the existing Hm and ordinary Hg. -/
theorem Hmg_tmul (v w : Carrier D) (u z : Fock) :
    Hmg (v ⊗ₜ[ℂ] u) (w ⊗ₜ[ℂ] z) = Hm v w * Hg u z := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' =>
      simp only [TensorProduct.tmul_add, Hmg_add_left, Hg_add_left,
        hu, hu', mul_add]
  | single S a =>
      have ha : Finsupp.single S a = a • ket S := by simp [ket]
      rw [ha, TensorProduct.tmul_smul, Hmg_smul_left, Hg_smul_left,
        Hmg_tmul_ket_left]
      ring

private def leftAdd (y : State D) : State D →+ ℂ where
  toFun x := Hmg x y
  map_zero' := Hmg_zero_left y
  map_add' x z := Hmg_add_left x z y

private def rightAdd (x : State D) : State D →+ ℂ where
  toFun := Hmg x
  map_zero' := Hmg_zero_right x
  map_add' := Hmg_add_right x

private theorem Hmg_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → State D) (y : State D) :
    Hmg (∑ i ∈ s, f i) y = ∑ i ∈ s, Hmg (f i) y :=
  map_sum (leftAdd y) _ _

private theorem Hmg_sum_right {ι : Type*} (s : Finset ι)
    (f : ι → State D) (x : State D) :
    Hmg x (∑ i ∈ s, f i) = ∑ i ∈ s, Hmg x (f i) :=
  map_sum (rightAdd x) _ _

/- This private tensor extension consumes only the supplied factor laws.
Its callers below instantiate them with the existing actual adjoints. -/
private theorem map_adjoint
    (A A' : Module.End ℂ (Carrier D)) (G G' : Module.End ℂ Fock)
    (hA : ∀ v w, Hm (A v) w = Hm v (A' w))
    (hG : ∀ u z, Hg (G u) z = Hg u (G' z)) (x y : State D) :
    Hmg (TensorProduct.map A G x) y = Hmg x (TensorProduct.map A' G' y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | tmul v u =>
      induction y using TensorProduct.inductionOn with
      | tmul w z =>
          simp only [TensorProduct.map_tmul, Hmg_tmul, hA, hG]
      | add y z hy hz =>
          simp only [map_add, Hmg_add_right, hy, hz]
  | add x z hx hz =>
      simp only [map_add, Hmg_add_left, hx, hz]

theorem Hmg_ghostB (m : ℤ) (x y : State D) :
    Hmg (ghostB D m x) y = Hmg x (ghostB D (-m) y) := by
  exact map_adjoint LinearMap.id LinearMap.id (BcGhostFock.b m)
    (BcGhostFock.b (-m)) (fun _ _ => rfl) (Hg_b m) x y

theorem Hmg_ghostC (m : ℤ) (x y : State D) :
    Hmg (ghostC D m x) y = Hmg x (ghostC D (-m) y) := by
  exact map_adjoint LinearMap.id LinearMap.id (BcGhostFock.c m)
    (BcGhostFock.c (-m)) (fun _ _ => rfl) (Hg_c m) x y

theorem Hmg_ghostCharge (x y : State D) :
    Hmg (ghostCharge D x) y = Hmg x (ghostCharge D y) := by
  exact map_adjoint LinearMap.id LinearMap.id BcGhostBRST.Qg BcGhostBRST.Qg
    (fun _ _ => rfl) BcGhostBRST.Hg_Qg x y

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

include hHG hGH in
theorem Hmg_matterMode (m : ℤ) (x y : State D) :
    Hmg (matterMode D H m x) y = Hmg x (matterMode D H (-m) y) := by
  exact map_adjoint (sugawaraMode D H m) (sugawaraMode D H (-m))
    LinearMap.id LinearMap.id (Hm_sugawaraMode H hHG hGH m)
    (fun _ _ => rfl) x y

include hHG hGH in
private theorem Hmg_summand (m : ℤ) (x y : State D) :
    Hmg (summand D H m x) y = Hmg x (summand D H (-m) y) := by
  simpa only [summand, neg_neg] using
    map_adjoint (sugawaraMode D H m) (sugawaraMode D H (-m))
      (BcGhostFock.c (-m)) (BcGhostFock.c m)
      (Hm_sugawaraMode H hHG hGH m)
      (fun u z => by simpa only [neg_neg] using Hg_c (-m) u z) x y

/- A common capture for BOTH actions, enlarged under m ↦ -m. No
support assertion is made about the family of endomorphisms itself. -/
private theorem symmetric_capture (x y : State D) :
    ∃ s : Finset ℤ,
      (Function.support (fun m => summand D H m x) ⊆ (s : Set ℤ)) ∧
      (Function.support (fun m => summand D H m y) ⊆ (s : Set ℤ)) ∧
      (∀ m ∈ s, -m ∈ s) := by
  classical
  obtain ⟨u, hu⟩ := common_capture D H {x, y}
  let s := u ∪ u.image (fun m : ℤ => -m)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro m hm
    exact Finset.mem_union_left _ (hu x (by simp) hm)
  · intro m hm
    exact Finset.mem_union_left _ (hu y (by simp) hm)
  · intro m hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    · rcases Finset.mem_image.mp hm with ⟨n, hn, hnm⟩
      rw [← hnm, neg_neg]
      exact Finset.mem_union_left _ hn

include hHG hGH in
/-- The exact locally finite total matter-c coupling is self-adjoint.
The two Gram inverse equations are retained, at arbitrary lattice rank. -/
theorem Hmg_T (x y : State D) : Hmg (T D H x) y = Hmg x (T D H y) := by
  classical
  obtain ⟨s, hx, hy, hs⟩ := symmetric_capture H x y
  rw [finite_capture D H x s hx, finite_capture D H y s hy,
    Hmg_sum_left, Hmg_sum_right]
  calc
    (∑ m ∈ s, Hmg (summand D H m x) y) =
        ∑ m ∈ s, Hmg x (summand D H (-m) y) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Hmg_summand H hHG hGH m x y
    _ = ∑ m ∈ s, Hmg x (summand D H m y) := by
      apply Finset.sum_bij (fun m _ => -m)
      · intro m hm
        exact hs m hm
      · intro m hm n hn hmn
        exact neg_injective hmn
      · intro m hm
        exact ⟨-m, hs m hm, neg_neg m⟩
      · intro m hm
        rfl

include hHG hGH in
/-- Exact original-Q adjoint for T + the tensor lift of the actual cubic Qg.
No rank26, relative, ghost-degree, shell, or positivity assumption is used. -/
theorem Hmg_totalCharge (x y : State D) :
    Hmg (totalCharge D H x) y = Hmg x (totalCharge D H y) := by
  simp only [totalCharge, LinearMap.add_apply, Hmg_add_left, Hmg_add_right,
    Hmg_T H hHG hGH, Hmg_ghostCharge]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeMatterGhostHermitian

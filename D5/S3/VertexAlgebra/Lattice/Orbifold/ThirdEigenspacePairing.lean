/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdEigenspacePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perfect pairing and dual current bases for the complementary cubic eigenspaces of P48q. -/

/- Source: Library/VertexAlgebra/nebe2014extremal48.md. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
The complex bilinear lattice form gives the coefficient pairing for the two
complementary fractional current grids. The last section uses Nebe's concrete
row-action and Gram certificates to index both grids by the same `Fin 16`.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing

open Module Module.End
open scoped Matrix

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {A : End ℂ V} {B : LinearMap.BilinForm ℂ V} {ζ : ℂ}

/-- The preserved form pairs only eigenspaces whose eigenvalues multiply to one. -/
theorem eigenspace_pairing_eq_zero
    (hB : ∀ x y, B (A x) (A y) = B x y) {α μ : ℂ} {x y : V}
    (hx : x ∈ A.eigenspace α) (hy : y ∈ A.eigenspace μ) (hαμ : α * μ ≠ 1) :
    B x y = 0 := by
  have h := hB x y
  rw [mem_eigenspace_iff.mp hx, mem_eigenspace_iff.mp hy] at h
  have heq : (α * μ) * B x y = B x y := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm μ α] using h
  have hzero : (α * μ - 1) * B x y = 0 := by rw [sub_mul, one_mul, heq, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hαμ)

private theorem square_square (hζ : IsPrimitiveRoot ζ 3) : (ζ ^ 2) ^ 2 = ζ := by
  calc
    (ζ ^ 2) ^ 2 = ζ ^ 3 * ζ := by ring
    _ = ζ := by rw [hζ.pow_eq_one, one_mul]

/-- Each primitive eigenspace is totally isotropic. -/
private theorem moving_isotropic (hζ : IsPrimitiveRoot ζ 3)
    (hB : ∀ x y, B (A x) (A y) = B x y) :
    (∀ x y : A.eigenspace ζ, B x y = 0) ∧
    (∀ x y : A.eigenspace (ζ ^ 2), B x y = 0) := by
  constructor
  · intro x y
    apply eigenspace_pairing_eq_zero hB x.property y.property
    rw [← pow_two]
    exact hζ.pow_ne_one_of_pos_of_lt (by decide : (2 : ℕ) ≠ 0) (by decide)
  · intro x y
    apply eigenspace_pairing_eq_zero hB x.property y.property
    rw [← pow_two, square_square hζ]
    exact hζ.ne_one (by decide)

private def component (A : End ℂ V) (α : ℂ) (x : V) : V :=
  (3 : ℂ)⁻¹ • (x + α ^ 2 • A x + α • A (A x))

private theorem component_mem (hA : A ^ 3 = 1) {α : ℂ} (hα : α ^ 3 = 1) (x : V) :
    component A α x ∈ A.eigenspace α := by
  have hcube : A (A (A x)) = x := by
    simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Module.End.one_apply]
      using congrArg (fun T : End ℂ V => T x) hA
  have hmul : α * α ^ 2 = 1 := by
    calc
      α * α ^ 2 = α ^ 3 := by ring
      _ = 1 := hα
  rw [mem_eigenspace_iff]
  simp only [component, map_smul, map_add, hcube]
  rw [smul_smul α ((3 : ℂ)⁻¹), mul_comm α ((3 : ℂ)⁻¹), ← smul_smul ((3 : ℂ)⁻¹) α]
  apply congrArg (fun y : V => (3 : ℂ)⁻¹ • y)
  simp only [smul_add, smul_smul, hmul, (pow_two α).symm, one_smul]
  abel

theorem exists_eigenspace_decomposition (hA : A ^ 3 = 1)
    (hζ : IsPrimitiveRoot ζ 3) (x : V) :
    ∃ u ∈ A.eigenspace 1, ∃ v ∈ A.eigenspace ζ, ∃ w ∈ A.eigenspace (ζ ^ 2),
      u + (v + w) = x := by
  have hsum : 1 + ζ + ζ ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      using hζ.geom_sum_eq_zero (by decide)
  have hcube : (ζ ^ 2) ^ 3 = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
  refine ⟨component A 1 x, component_mem hA (one_pow 3) x,
    component A ζ x, component_mem hA hζ.pow_eq_one x,
    component A (ζ ^ 2) x, component_mem hA hcube x, ?_⟩
  simp only [component, one_pow, one_smul, square_square hζ, ← smul_add]
  calc
    _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • x + (1 + ζ + ζ ^ 2) • A x +
        (1 + ζ + ζ ^ 2) • A (A x)) := by
      apply congrArg (fun y : V => (3 : ℂ)⁻¹ • y)
      module
    _ = x := by
      simp only [hsum, zero_smul, add_zero, smul_smul,
        inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

/-- The coefficient pairing is the restriction of the complex bilinear lattice form. -/
def movingPairing (A : End ℂ V) (B : LinearMap.BilinForm ℂ V) (ζ : ℂ) :
    A.eigenspace ζ →ₗ[ℂ] A.eigenspace (ζ ^ 2) →ₗ[ℂ] ℂ :=
  B.compl₁₂ (A.eigenspace ζ).subtype (A.eigenspace (ζ ^ 2)).subtype

/-- Both radicals of the restricted pairing vanish. Mathlib supplies the dual equivalences. -/
theorem movingPairing_isPerfPair [FiniteDimensional ℂ V] (hA : A ^ 3 = 1) (hζ : IsPrimitiveRoot ζ 3)
    (hB : ∀ x y, B (A x) (A y) = B x y) (hND : B.Nondegenerate) :
    (movingPairing A B ζ).IsPerfPair := by
  have h1 := hζ.ne_one (by decide : 1 < 3)
  have h2 := hζ.pow_ne_one_of_pos_of_lt (by decide : (2 : ℕ) ≠ 0) (by decide)
  obtain ⟨hiso₁, hiso₂⟩ := moving_isotropic hζ hB
  have hleft : (movingPairing A B ζ).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : V) = 0
    apply hND.1
    intro y
    obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := exists_eigenspace_decomposition hA hζ y
    have hu' := eigenspace_pairing_eq_zero hB x.property hu (by simpa only [mul_one] using h1)
    have hv' : B (x : V) v = 0 := hiso₁ x ⟨v, hv⟩
    have hw' : B (x : V) w = 0 := hx ⟨w, hw⟩
    simp only [map_add, hu', hv', hw', add_zero]
  have hright : (movingPairing A B ζ).SeparatingRight := by
    intro y hy
    apply Subtype.ext
    change (y : V) = 0
    apply hND.2
    intro x
    obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := exists_eigenspace_decomposition hA hζ x
    have hu' := eigenspace_pairing_eq_zero hB hu y.property (by simpa only [one_mul] using h2)
    have hv' : B v (y : V) = 0 := hy ⟨v, hv⟩
    have hw' : B w (y : V) = 0 := hiso₂ ⟨w, hw⟩ y
    simp only [map_add, LinearMap.add_apply, hu', hv', hw', add_zero]
  exact LinearMap.IsPerfPair.of_injective
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hleft))
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp hright))

/-- Transport the dual basis to the opposite eigenspace by the perfect pairing. -/
private def oppositeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (movingPairing A B ζ).IsPerfPair) (b : Basis ι ℂ (A.eigenspace ζ)) :
    Basis ι ℂ (A.eigenspace (ζ ^ 2)) :=
  letI := h
  b.dualBasis.map (movingPairing A B ζ).flip.toPerfPair.symm

private theorem moving_finrank [FiniteDimensional ℂ V] (hA : A ^ 3 = 1) (hζ : IsPrimitiveRoot ζ 3)
    (h : (movingPairing A B ζ).IsPerfPair) :
    finrank ℂ V = finrank ℂ (A.eigenspace 1) + 2 * finrank ℂ (A.eigenspace ζ) ∧
      finrank ℂ (A.eigenspace ζ) = finrank ℂ (A.eigenspace (ζ ^ 2)) := by
  let _ := h
  have heq := Module.finrank_of_isPerfPair (movingPairing A B ζ)
  have hne : ζ ≠ ζ ^ 2 := by
    intro he
    exact (by decide : (1 : ℕ) ≠ 2)
      (hζ.pow_inj (i := 1) (j := 2) (by decide) (by decide) (by simpa only [pow_one] using he))
  have hmov : Disjoint (A.eigenspace ζ) (A.eigenspace (ζ ^ 2)) :=
    A.eigenspaces_iSupIndep.pairwiseDisjoint hne
  have le_otherEigenspaces (a : ℂ) (ha : a ≠ 1) :
      A.eigenspace a ≤ ⨆ (b : ℂ) (_ : b ≠ 1), A.eigenspace b :=
    le_iSup₂ (f := fun (b : ℂ) (_ : b ≠ 1) => A.eigenspace b) a ha
  have hfix : Disjoint (A.eigenspace 1) (A.eigenspace ζ ⊔ A.eigenspace (ζ ^ 2)) :=
    (A.eigenspaces_iSupIndep 1).mono_right <| sup_le
      (le_otherEigenspaces ζ (hζ.ne_one (by decide)))
      (le_otherEigenspaces (ζ ^ 2) (hζ.pow_ne_one_of_pos_of_lt (by decide) (by decide)))
  have htop : A.eigenspace 1 ⊔ (A.eigenspace ζ ⊔ A.eigenspace (ζ ^ 2)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨u, hu, v, hv, w, hw, rfl⟩ := exists_eigenspace_decomposition hA hζ x
    exact Submodule.mem_sup.mpr ⟨u, hu, v + w, Submodule.mem_sup.mpr ⟨v, hv, w, hw, rfl⟩, rfl⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (A.eigenspace ζ) (A.eigenspace (ζ ^ 2))
  rw [hmov.eq_bot, finrank_bot, add_zero] at hsum
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (A.eigenspace 1)
    (A.eigenspace ζ ⊔ A.eigenspace (ζ ^ 2))
  rw [htop, hfix.eq_bot, finrank_top, finrank_bot, add_zero, hsum] at hdim
  exact ⟨by omega, heq⟩

section P48q

open P48qFixedRankCertificate P48qGramCertificate

def p48qAction : End ℂ (Fin 48 → ℂ) := rowAction ℂ nebeOrderThree

def p48qForm : LinearMap.BilinForm ℂ (Fin 48 → ℂ) :=
  (nebeGram.map (Int.castRingHom ℂ)).toBilin'

theorem p48qAction_cube : p48qAction ^ 3 = 1 := by
  let c := Int.castRingHom ℂ
  change (c.mapMatrix nebeOrderThreeᵀ).toLin' ^ 3 = 1
  have ht : nebeOrderThreeᵀ ^ 3 = 1 := by
    rw [← Matrix.transpose_pow, nebeOrderThree_cube, Matrix.transpose_one]
  rw [← Matrix.toLin'_pow, ← map_pow, ht, map_one, Matrix.toLin'_one, ← Module.End.one_eq_id]

theorem p48qForm_invariant (x y : Fin 48 → ℂ) :
    p48qForm (p48qAction x) (p48qAction y) = p48qForm x y := by
  let c := Int.castRingHom ℂ
  let G := c.mapMatrix nebeGram
  let P := c.mapMatrix nebeOrderThreeᵀ
  have h : Pᵀ * G * P = G := by
    change c.mapMatrix nebeOrderThree * c.mapMatrix nebeGram * c.mapMatrix nebeOrderThreeᵀ = G
    rw [← map_mul, ← map_mul, gram_isometry_certificate]
  change (G.toBilin'.comp P.toLin' P.toLin') x y = G.toBilin' x y
  rw [Matrix.toBilin'_comp, h]

theorem p48qForm_nondegenerate : p48qForm.Nondegenerate := by
  let c := Int.castRingHom ℂ
  let G := c.mapMatrix nebeGram
  change G.toBilin'.Nondegenerate
  apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
  have hInv : c.mapMatrix nebeGramInverse * G = 1 := by
    change c.mapMatrix nebeGramInverse * c.mapMatrix nebeGram = 1
    rw [← map_mul, gram_inverse_certificate, map_one]
  have hdet := congrArg Matrix.det hInv
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  intro h
  rw [h, mul_zero] at hdet
  exact zero_ne_one hdet

theorem p48q_movingPairing_isPerfPair (hζ : IsPrimitiveRoot ζ 3) :
    (movingPairing p48qAction p48qForm ζ).IsPerfPair :=
  movingPairing_isPerfPair p48qAction_cube hζ p48qForm_invariant p48qForm_nondegenerate

theorem p48q_moving_isotropic (hζ : IsPrimitiveRoot ζ 3) :
    (∀ x y : p48qAction.eigenspace ζ, p48qForm x y = 0) ∧
    (∀ x y : p48qAction.eigenspace (ζ ^ 2), p48qForm x y = 0) :=
  moving_isotropic hζ p48qForm_invariant

theorem p48q_moving_finrank (hζ : IsPrimitiveRoot ζ 3) :
    finrank ℂ (p48qAction.eigenspace ζ) = 16 ∧
    finrank ℂ (p48qAction.eigenspace (ζ ^ 2)) = 16 := by
  have h48 : finrank ℂ (Fin 48 → ℂ) = 48 := by simp
  have h16 : finrank ℂ (p48qAction.eigenspace 1) = 16 := by
    rw [eigenspace_def, one_smul]
    exact nebeOrderThree_fixedRank16 ℂ
  obtain ⟨hdim, heq⟩ := moving_finrank p48qAction_cube hζ (p48q_movingPairing_isPerfPair hζ)
  rw [h48, h16] at hdim
  exact ⟨by omega, by omega⟩

/-- Coefficients for the residue-one fractional current grid. -/
def p48qBasis (hζ : IsPrimitiveRoot ζ 3) : Basis (Fin 16) ℂ (p48qAction.eigenspace ζ) :=
  Module.finBasisOfFinrankEq ℂ _ (p48q_moving_finrank hζ).1

/-- Coefficients for the residue-two grid, indexed by the same `Fin 16`. -/
def p48qOppositeBasis (hζ : IsPrimitiveRoot ζ 3) :
    Basis (Fin 16) ℂ (p48qAction.eigenspace (ζ ^ 2)) :=
  oppositeBasis (p48q_movingPairing_isPerfPair hζ) (p48qBasis hζ)

theorem p48q_pair_bases (hζ : IsPrimitiveRoot ζ 3) (i j : Fin 16) :
    p48qForm (p48qBasis hζ i) (p48qOppositeBasis hζ j) = if i = j then 1 else 0 := by
  letI := p48q_movingPairing_isPerfPair hζ
  change movingPairing p48qAction p48qForm ζ (p48qBasis hζ i) (p48qOppositeBasis hζ j) = _
  rw [p48qOppositeBasis, oppositeBasis, Basis.map_apply, LinearMap.apply_toPerfPair_flip,
    Basis.dualBasis_apply_self]

end P48q

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdEigenspacePairing

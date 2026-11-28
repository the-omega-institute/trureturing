/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/TwiningTrace/P48qCubicOscillatorBasis
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic current coordinates for the concrete rank-48 P48q oscillator. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! A cyclic current basis for the concrete rank-48 P48q row action. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorBasis

open Module ThirdEigenspacePairing MvPolynomial
open LatticeGeneratingFieldLocality OriginalCurrentMetric
open P48qTwistedChargeAction (lattice g g_apply)
open P48qFixedRankCertificate (nebeOrderThree)
open scoped Matrix
open IsometryLift (oscillator_X)
open P48qMomentumEnergy (Fixed fixedBasis)
open ThirdTwistedChargeCocycle (zeta zeta_primitive)

noncomputable section

local notation "ω₃" => (zeta : ℂ)
local notation "hω₃" => (IsPrimitiveRoot.coe_units_iff.mpr zeta_primitive)
local notation "A" => p48qAction

private def seed (i : Fin 16) : Fin 48 → ℂ :=
  (fixedBasis i : Fin 48 → ℂ) +
    (p48qBasis hω₃ i : Fin 48 → ℂ) +
    (p48qOppositeBasis hω₃ i : Fin 48 → ℂ)

private def orbit (i : Fin 3 × Fin 16) : Fin 48 → ℂ :=
  ![seed i.2, A (seed i.2), A (A (seed i.2))] i.1

private theorem orbit_step (i : Fin 3 × Fin 16) :
    A (orbit i) = orbit (i.1 + 1, i.2) := by
  have cube (v : Fin 48 → ℂ) : A (A (A v)) = v := by
    simpa only [pow_succ, pow_zero, one_mul, End.mul_apply, End.one_apply]
      using congrArg (fun f : End ℂ (Fin 48 → ℂ) => f v) p48qAction_cube
  obtain ⟨k, j⟩ := i
  fin_cases k
  · rfl
  · rfl
  · exact cube _

private theorem orbit_spans : ⊤ ≤ Submodule.span ℂ (Set.range orbit) := by
  let S := Submodule.span ℂ (Set.range orbit)
  have hsum : 1 + ω₃ + ω₃ ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      using (hω₃).geom_sum_eq_zero (by decide)
  have hcube := (hω₃).pow_eq_one
  have hfour : ω₃ ^ 2 * ω₃ ^ 2 = ω₃ := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by decide, pow_add, hcube, one_mul, pow_one]
  have hthree : ω₃ * ω₃ ^ 2 = 1 := by
    simpa only [pow_succ, mul_comm] using hcube
  let b₀ (i : Fin 16) := (fixedBasis i : Fin 48 → ℂ)
  let b₁ (i : Fin 16) := (p48qBasis hω₃ i : Fin 48 → ℂ)
  let b₂ (i : Fin 16) := (p48qOppositeBasis hω₃ i : Fin 48 → ℂ)
  have each (i : Fin 16) : b₀ i ∈ S ∧ b₁ i ∈ S ∧ b₂ i ∈ S := by
    have h₀ : A (b₀ i) = b₀ i := by
      have h : (b₀ i) ∈ Fixed := (fixedBasis i).property
      simpa only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, End.one_apply, sub_eq_zero] using h
    have h₁ : A (b₁ i) = ω₃ • b₁ i :=
      End.mem_eigenspace_iff.mp (p48qBasis hω₃ i).property
    have h₂ : A (b₂ i) = ω₃ ^ 2 • b₂ i :=
      End.mem_eigenspace_iff.mp (p48qOppositeBasis hω₃ i).property
    have hv₀ : seed i = b₀ i + b₁ i + b₂ i := rfl
    have hv₁ : A (seed i) = b₀ i + ω₃ • b₁ i + ω₃ ^ 2 • b₂ i := by
      rw [hv₀, map_add, map_add, h₀, h₁, h₂]
    have hv₂ : A (A (seed i)) = b₀ i + ω₃ ^ 2 • b₁ i + ω₃ • b₂ i := by
      rw [hv₁, map_add, map_add, map_smul, map_smul, h₀, h₁, h₂,
        smul_smul, smul_smul, ← pow_two ω₃, hfour]
    have hm₀ : seed i ∈ S := Submodule.subset_span ⟨(0, i), rfl⟩
    have hm₁ : A (seed i) ∈ S := Submodule.subset_span ⟨(1, i), rfl⟩
    have hm₂ : A (A (seed i)) ∈ S := Submodule.subset_span ⟨(2, i), rfl⟩
    have recover (a b : ℂ) :
        (3 : ℂ)⁻¹ • (seed i + a • A (seed i) + b • A (A (seed i))) ∈ S :=
      S.smul_mem _ (S.add_mem (S.add_mem hm₀ (S.smul_mem _ hm₁)) (S.smul_mem _ hm₂))
    have cancel_three (v : Fin 48 → ℂ) : (3 : ℂ)⁻¹ • ((3 : ℂ) • v) = v := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]
    refine ⟨?_, ?_, ?_⟩
    · convert recover 1 1 using 1
      rw [hv₂, hv₁, hv₀, one_smul, one_smul]
      symm
      calc
        _ = (3 : ℂ)⁻¹ • ((3 : ℂ) • b₀ i +
            (1 + ω₃ + ω₃ ^ 2) • b₁ i + (1 + ω₃ + ω₃ ^ 2) • b₂ i) := by
          congr 1
          module
        _ = _ := by simp only [hsum, zero_smul, add_zero, cancel_three]
    · convert recover (ω₃ ^ 2) ω₃ using 1
      rw [hv₂, hv₁, hv₀]
      symm
      calc
        _ = (3 : ℂ)⁻¹ • ((1 + ω₃ + ω₃ ^ 2) • b₀ i +
            (3 : ℂ) • b₁ i + (1 + ω₃ + ω₃ ^ 2) • b₂ i) := by
          congr 1
          simp only [smul_add, smul_smul, hfour, ← pow_two ω₃, hthree,
            mul_comm (ω₃ ^ 2) ω₃, one_smul]
          module
        _ = _ := by simp only [hsum, zero_smul, add_zero, zero_add, cancel_three]
    · convert recover ω₃ (ω₃ ^ 2) using 1
      rw [hv₂, hv₁, hv₀]
      symm
      calc
        _ = (3 : ℂ)⁻¹ • ((1 + ω₃ + ω₃ ^ 2) • b₀ i +
            (1 + ω₃ + ω₃ ^ 2) • b₁ i + (3 : ℂ) • b₂ i) := by
          congr 1
          simp only [smul_add, smul_smul, hfour, ← pow_two ω₃, hthree,
            mul_comm (ω₃ ^ 2) ω₃, one_smul]
          module
        _ = _ := by simp only [hsum, zero_smul, zero_add, cancel_three]
  have basis_mem {P : Submodule ℂ (Fin 48 → ℂ)} (b : Basis (Fin 16) ℂ P)
      (hb : ∀ i, (b i : Fin 48 → ℂ) ∈ S) (x : P) : (x : Fin 48 → ℂ) ∈ S := by
    have h := congrArg P.subtype (b.sum_repr x)
    simp only [map_sum, map_smul, Submodule.subtype_apply] at h
    rw [← h]
    exact S.sum_mem fun i _ => S.smul_mem _ (hb i)
  intro x _
  obtain ⟨u, hu, v, hv, w, hw, rfl⟩ :=
    exists_eigenspace_decomposition p48qAction_cube hω₃ x
  have hu' : u ∈ Fixed := by
    rwa [End.eigenspace_def, one_smul] at hu
  exact S.add_mem (basis_mem fixedBasis (fun i => (each i).1) ⟨u, hu'⟩)
    (S.add_mem (basis_mem (p48qBasis hω₃) (fun i => (each i).2.1) ⟨v, hv⟩)
      (basis_mem (p48qOppositeBasis hω₃) (fun i => (each i).2.2) ⟨w, hw⟩))

/-- A current basis consisting of sixteen orbits of length three. -/
def cubicBasis : Basis (Fin 3 × Fin 16) ℂ (Fin 48 → ℂ) :=
  basisOfTopLeSpanOfCardEqFinrank orbit orbit_spans (by simp)

/-- The concrete Nebe row action advances the orbit index in the cubic basis. -/
theorem cubicBasis_step (i : Fin 3 × Fin 16) :
    A (cubicBasis i) = cubicBasis (i.1 + 1, i.2) := by
  simpa only [cubicBasis, coe_basisOfTopLeSpanOfCardEqFinrank] using orbit_step i

/-- The variables in the cyclic basis, with the same frequency as in the native ring. -/
abbrev CubicIndex := (Fin 3 × Fin 16) × ℕ

/-- Advance the cyclic basis index at each colour and frequency. -/
def rotate : Equiv.Perm CubicIndex where
  toFun x := ((x.1.1 + 1, x.1.2), x.2)
  invFun x := ((x.1.1 - 1, x.1.2), x.2)
  left_inv x := by simp
  right_inv x := by simp

def colourEquiv : Fin 3 × Fin 16 ≃ Fin 48 := finProdFinEquiv

private def coordinates : (Fin 48 → ℂ) ≃ₗ[ℂ] (Fin 48 → ℂ) :=
  (cubicBasis.reindex colourEquiv).equivFun.symm

private def changeMatrix : Matrix (Fin 48) (Fin 48) ℂ :=
  LinearMap.toMatrix' coordinates.toLinearMap

def inverseMatrix : Matrix (Fin 48) (Fin 48) ℂ :=
  LinearMap.toMatrix' coordinates.symm.toLinearMap

private theorem changeMatrix_mul_inverse :
    changeMatrix * inverseMatrix = 1 := by
  rw [changeMatrix, inverseMatrix, ← LinearMap.toMatrix'_comp]
  rw [show coordinates.toLinearMap.comp coordinates.symm.toLinearMap = LinearMap.id from
    LinearMap.ext (fun x => coordinates.apply_symm_apply x), LinearMap.toMatrix'_id]

private theorem inverseMatrix_mul_change :
    inverseMatrix * changeMatrix = 1 := by
  rw [changeMatrix, inverseMatrix, ← LinearMap.toMatrix'_comp]
  rw [show coordinates.symm.toLinearMap.comp coordinates.toLinearMap = LinearMap.id from
    LinearMap.ext (fun x => coordinates.symm_apply_apply x), LinearMap.toMatrix'_id]

/-- Change from the cubic basis variables to the actual P48q oscillator variables. -/
def oscillatorCoordinates : MvPolynomial CubicIndex ℂ ≃ₐ[ℂ] Oscillator lattice :=
  (renameEquiv ℂ (colourEquiv.prodCongr (Equiv.refl ℕ))).trans
    (substitutionEquiv (fun _ => changeMatrix) (fun _ => inverseMatrix)
      (fun _ => changeMatrix_mul_inverse) (fun _ => inverseMatrix_mul_change))

theorem oscillatorCoordinates_X (i : Fin 3 × Fin 16) (n : ℕ) :
    oscillatorCoordinates (X (i, n)) =
      ∑ j : Fin 48, (cubicBasis i) j • (X (j, n) : Oscillator lattice) := by
  change substitution (fun _ => changeMatrix)
    (rename (colourEquiv.prodCongr (Equiv.refl ℕ)) (X (i, n))) = _
  rw [rename_X, substitution_X]
  change (∑ j : Fin 48, changeMatrix j (colourEquiv i) • (X (j, n) : Oscillator lattice)) = _
  apply Finset.sum_congr rfl
  intro j _
  have h : coordinates (Pi.single (colourEquiv i) (1 : ℂ)) = cubicBasis i := by
    change (cubicBasis.reindex colourEquiv).equivFun.symm _ = _
    rw [Basis.equivFun_symm_apply]
    simp [Pi.single_apply, Basis.reindex_apply, ite_smul]
  rw [changeMatrix, LinearMap.toMatrix'_apply]
  exact congrArg (fun v : Fin 48 → ℂ => v j • (X (j, n) : Oscillator lattice)) h

private theorem oscillator_current (v : Fin 48 → ℂ) (n : ℕ) :
    IsometryLift.oscillator lattice g
      (∑ i : Fin 48, v i • (X (i, n) : Oscillator lattice)) =
    ∑ j : Fin 48, (A v) j • (X (j, n) : Oscillator lattice) := by
  have hentry (i j : Fin 48) :
      (g (unitCharge lattice i) j : ℂ) = (nebeOrderThree i j : ℂ) := by
    rw [g_apply]
    have h : unitCharge lattice i = Pi.single i (1 : ℤ) := by
      funext k
      simp [unitCharge, Pi.single_apply]
    rw [h, Matrix.single_one_vecMul]
    rfl
  simp only [map_sum, map_smul, oscillator_X, hentry, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_smul]
  apply congrArg (fun c : ℂ => c • (X (j, n) : Oscillator lattice))
  change (∑ i : Fin 48, v i * (nebeOrderThree i j : ℂ)) =
    (((nebeOrderThreeᵀ).map (Int.castRingHom ℂ)) *ᵥ v) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
    Int.coe_castRingHom]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- In cyclic coordinates the actual oscillator isometry acts by variable renaming. -/
theorem oscillator_rename (p : MvPolynomial CubicIndex ℂ) :
    IsometryLift.oscillator lattice g (oscillatorCoordinates p) =
      oscillatorCoordinates (rename rotate p) := by
  have h : (IsometryLift.oscillator lattice g).toAlgHom.comp oscillatorCoordinates.toAlgHom =
      oscillatorCoordinates.toAlgHom.comp (rename rotate) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, n⟩
    change IsometryLift.oscillator lattice g (oscillatorCoordinates (X (i, n))) =
      oscillatorCoordinates (rename rotate (X (i, n)))
    rw [rename_X, oscillatorCoordinates_X, oscillator_current, cubicBasis_step]
    exact (oscillatorCoordinates_X (i.1 + 1, i.2) n).symm
  exact AlgHom.congr_fun h p

/-- In particular, each monomial is sent to the monomial with rotated occupation. -/
theorem oscillator_cubicMonomial (d : CubicIndex →₀ ℕ) (c : ℂ) :
    IsometryLift.oscillator lattice g (oscillatorCoordinates (monomial d c)) =
      oscillatorCoordinates (monomial (d.mapDomain rotate) c) := by
  rw [oscillator_rename, rename_monomial]

run_cmd do
  for name in [``cubicBasis, ``cubicBasis_step, ``oscillatorCoordinates,
      ``oscillator_rename, ``oscillator_cubicMonomial] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorBasis

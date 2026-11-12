/-
SOURCE_ONLY_UNCOMPILED.

Finite opposite-charge/Taylor reconstruction in actual integer eigenspaces.
The intermediate formula uses the supplied Taylor boxes, so no weighted
partition resummation or claimed Q-resolution is hidden in this file.
Every local-nilpotence premise is on the original currents. Every projection
and every charged mode is the actual one constructed in the preceding files.

Paper route: sealed 268eb1... Steps 4--5. Scalar regrouping is carried out
in ActualGroundPartitionScalar / ActualGroundSpectralResolution downstream.
-/
import D5.S3.VertexAlgebra.Modules.ActualChargedGroundCalculus
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators DirectSum

namespace D5.S3.VertexAlgebra.Modules.ActualGroundFiniteReconstruction

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock
open StateFieldResidueReconstruction (integerBinomial)

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M) (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

abbrev W := actualWeyl J hNil H hHG

/-- Weighted finite creator degree in the original oscillator indexing. -/
def occupationWeight (d : Index D →₀ ℕ) : ℕ :=
  Finsupp.weight (fun x : Index D => x.2 + 1) d

def occupationScalar (α : Charge D) (d : Index D →₀ ℕ) : ℂ :=
  d.prod (fun x n => (-(bilinear D (unitCharge D x.1) α : ℂ)) ^ n)

@[simp] theorem occupationWeight_zero : occupationWeight (0 : Index D →₀ ℕ) = 0 := by
  simp [occupationWeight]

theorem occupationWeight_add_single (d : Index D →₀ ℕ) (x : Index D) :
    occupationWeight (d + Finsupp.single x 1) = occupationWeight d + (x.2 + 1) := by
  simp [occupationWeight, Finsupp.weight_single]

@[simp] theorem occupationScalar_zero (α : Charge D) :
    occupationScalar α (0 : Index D →₀ ℕ) = 1 := by
  simp [occupationScalar]

theorem occupationScalar_add_single (α : Charge D) (d : Index D →₀ ℕ) (x : Index D) :
    occupationScalar α (d + Finsupp.single x 1) =
      -(bilinear D (unitCharge D x.1) α : ℂ) * occupationScalar α d := by
  rw [occupationScalar, Finsupp.prod_add_index' (by intro i; simp)
    (by intro i a b; exact pow_add _ _ _)]
  simp [occupationScalar, Finsupp.prod_single_index, mul_comm]

/-- Multiindex version of the finite creator commutation, proved by
induction; the product is exactly the generic Fock creation operator. -/
theorem Pi_E_creation_monomial (α : Charge D) (d : Index D →₀ ℕ) :
    ∀ (s : ℤ) (v : M),
      Pi J hNil H hHG (E J α s ((W J hNil H hHG).creation d v)) =
        occupationScalar α d •
          Pi J hNil H hHG (E J α (s - occupationWeight d) v) := by
  classical
  induction d using Finsupp.induction with
  | zero => intro s v; simp
  | single_add x n d hx hn ih =>
    have hall : ∀ k : ℕ, ∀ (s : ℤ) (v : M),
        Pi J hNil H hHG (E J α s
          ((W J hNil H hHG).creation (d + Finsupp.single x k) v)) =
          occupationScalar α (d + Finsupp.single x k) •
            Pi J hNil H hHG (E J α (s - occupationWeight (d + Finsupp.single x k)) v) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        intro s v
        have he : d + Finsupp.single x (k + 1) =
            (d + Finsupp.single x k) + Finsupp.single x 1 := by
          rw [Finsupp.single_add]
          abel
        rw [he, WeylData.creation_add_single, Module.End.mul_apply]
        change Pi J hNil H hHG (E J α s (creation J x.1 x.2
          ((W J hNil H hHG).creation (d + Finsupp.single x k) v))) = _
        rw [E_creation, map_sub, map_smul, Pi_creation, zero_sub, ihk,
          ← neg_smul, smul_smul, occupationScalar_add_single,
          occupationWeight_add_single]
        congr 2
        push_cast
        ring
    simpa only [add_comm (Finsupp.single x n) d] using hall n

/-- Transport of the supplied normalized vacuum to the actual Omega.
This is the already-proved GH kernel equality, not a new ground-space axiom. -/
def vacuumToOmega : (W J hNil H hHG).vacuum ≃ₗ[ℂ] Omega J :=
  LinearEquiv.ofEq _ _ (actualWeyl_vacuum_eq J hNil H hHG hGH)

@[simp] theorem vacuumToOmega_coe (v : (W J hNil H hHG).vacuum) :
    (vacuumToOmega J hNil H hHG hGH v : M) = v.val := rfl

/-- A concrete Taylor box for each inner exponential coefficient. -/
def innerBox (α : Charge D) (p : ℤ) (j : ℕ) (v : Omega J) :
    Finset (Index D →₀ ℕ) :=
  Finset.Iic ((W J hNil H hHG).jointCutoff (E J α (-p - 1 + j) v.val))

/-- Actual reconstruction terms. No eigenspace or projector appears in
their definition; the subsequent eigenrelation is derived. -/
def groundTerm (α : Charge D) (p : ℤ) (q j : ℕ) (d : Index D →₀ ℕ) :
    Module.End ℂ (Omega J) :=
  occupationScalar (-α) d •
    ((Z J hNil H hHG hGH (-α) (p + q - 1 - j - occupationWeight d)).comp
      ((vacuumToOmega J hNil H hHG hGH).toLinearMap.comp
        (((W J hNil H hHG).coefficient d).comp
          ((E J α (-p - 1 + j)).comp (Omega J).subtype))))

theorem groundTerm_eigen (α : Charge D) (p : ℤ) (q j : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (d : Index D →₀ ℕ) (v : Omega J) :
    Hzero J α (groundTerm J hNil H hHG hGH α p q j d v) =
      ((p - j - occupationWeight d : ℤ) : ℂ) •
        groundTerm J hNil H hHG hGH α p q j d v := by
  simp only [groundTerm, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    Hzero_Z_opposite]
  have hi : p + (q : ℤ) - 1 - j - occupationWeight d + 1 - bilinear D α α =
      p - j - occupationWeight d := by omega
  rw [hi, smul_comm]

/-- The supplied Taylor inverse identity on exactly its finite box. -/
theorem inner_taylor (α : Charge D) (p : ℤ) (j : ℕ) (v : Omega J) :
    (∑ d ∈ innerBox J hNil H hHG α p j v,
      (W J hNil H hHG).creation d
        ((W J hNil H hHG).coefficient d (E J α (-p - 1 + j) v.val))) =
      E J α (-p - 1 + j) v.val := by
  classical
  calc
    _ = ∑ d ∈ Finset.Iic ((W J hNil H hHG).jointCutoff
          (E J α (-p - 1 + j) v.val)),
        (WeylData.factorial d : ℂ)⁻¹ •
          (W J hNil H hHG).creation d
            ((W J hNil H hHG).vacuumProjection
              ((W J hNil H hHG).derivative d (E J α (-p - 1 + j) v.val))) := by
      apply Finset.sum_congr
      · ext d
        simp [innerBox]
      · intro d hd
        simp only [WeylData.coefficient, LinearMap.smul_apply,
          LinearMap.comp_apply, Submodule.coe_smul, WeylData.vacuumProject_coe,
          map_smul]
    _ = _ := (W J hNil H hHG).taylor_reconstruction (E J α (-p - 1 + j) v.val)

/-- Genuine finite integer-eigenvector reconstruction, BEFORE the scalar
partition regrouping. Both ranges are finite and input-dependent. -/
theorem finite_ground_reconstruction (α : Charge D) (q : ℕ)
    (hq : (q : ℤ) = bilinear D α α) (hqpos : 0 < q)
    (p : ℤ) (v : Omega J)
    (hcut : ∀ n : ℤ, p ≤ n → E J (-α) n v.val = 0) :
    epsilon D (-α) α • v =
      ∑ j ∈ Finset.range q,
        (((-1 : ℂ)^j) * integerBinomial ((q : ℤ) - 1) j) •
          ∑ d ∈ innerBox J hNil H hHG α p j v,
            groundTerm J hNil H hHG hGH α p q j d v := by
  apply Subtype.ext
  have h := opposite_charge_finite_witness J α q hq hqpos p v.val hcut
  have hp := congrArg (Pi J hNil H hHG) h
  rw [map_smul, Pi_fixes J hNil H hHG hGH v.val v.property, map_sum] at hp
  simp only [map_smul] at hp
  rw [Submodule.coe_smul, Submodule.coe_sum]
  refine hp.trans ?_
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Submodule.coe_smul, Submodule.coe_sum]
  congr 1
  rw [← inner_taylor J hNil H hHG α p j v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Pi_E_creation_monomial]
  rfl

/-- The actual integer eigenspaces, with no finite-dimensionality premise. -/
def integerEigenspace (α : Charge D) (a : ℤ) : Submodule ℂ (Omega J) :=
  (Hzero J α).eigenspace (a : ℂ)

include hNil H hHG hGH in
/-- One-coordinate integrality and diagonalization follows from the actual
mixed-Jacobi/Taylor calculation, before any spectral data are postulated. -/
theorem integer_eigenspaces_span
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (α : Charge D) (hα : α ≠ 0) :
    (⨆ a : ℤ, integerEigenspace J α a) = ⊤ := by
  classical
  apply top_unique
  intro v hv
  have hpositive := norm_positive D hD α hα
  let q := (bilinear D α α).toNat
  have hq : (q : ℤ) = bilinear D α α := Int.toNat_of_nonneg hpositive.le
  have hqpos : 0 < q := by omega
  obtain ⟨p, hp⟩ := module_truncation J (groundState D (-α)) v.val
  have hrec := finite_ground_reconstruction J hNil H hHG hGH α q hq hqpos p v hp
  let U : Submodule ℂ (Omega J) := ⨆ a : ℤ, integerEigenspace J α a
  have hu : epsilon D (-α) α • v ∈ U := by
    rw [hrec]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro d hd
    apply (le_iSup (integerEigenspace J α) (p - j - occupationWeight d))
    rw [integerEigenspace, Module.End.mem_eigenspace_iff]
    exact groundTerm_eigen J hNil H hHG hGH α p q j hq d v
  have hc := U.smul_mem ((epsilon D (-α) α)⁻¹) hu
  simpa only [smul_smul, inv_mul_cancel₀ (original_epsilon_nonzero (-α) α),
    one_smul] using hc

include hNil H hHG hGH in
/-- Directness uses only pinned mathlib's independence of eigenspaces;
the spanning premise is the substantive actual proof immediately above. -/
theorem integer_eigenspaces_internal
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (α : Charge D) (hα : α ≠ 0) :
    DirectSum.IsInternal (integerEigenspace J α) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (Hzero J α).eigenspaces_iSupIndep.comp Int.cast_injective
  · exact integer_eigenspaces_span J hNil H hHG hGH hD α hα

end D5.S3.VertexAlgebra.Modules.ActualGroundFiniteReconstruction

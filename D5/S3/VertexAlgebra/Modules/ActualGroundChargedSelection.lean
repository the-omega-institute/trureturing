/-
Native kernel evidence is supplied by the accompanying scoped report.

Actual common zero-current weights on Omega, selection of the original Z
mode, and lifting selection to the original E modes by a finite Taylor box.
The box is the actual Weyl jointCutoff of E_alpha(m)v, not a presumed
charge cutoff. Every discarded Taylor term is killed by Z_Hzero.

The finite argument follows Steps 4, 7 of the sealed conditional paper
(268eb1b4...) and its independent review (177d2dd2...). Those are mathematical
advice; the actual suppliers are the sealed Stage1 scripts and the accepted
e536d048... current adapter / 27f1072a... algebraic Fock source.

No positivity of G is needed for selection on an already specified actual
jointWeight. Positivity is used upstream to prove that these spaces span.
Both inverse orientations are retained for the actual Taylor/Omega bridge.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundJointWeights
import D5.S3.VertexAlgebra.Modules.ActualGroundTaylorCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Modules.ActualGroundChargedSelection

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundJointWeights ActualGroundTaylorCoefficients
open D5.S3.Quantum.Algebra.AlgebraicHeisenbergFock

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- b is the vector of actual basis-current eigenvalues, physically G lambda. -/
def weightPairing (α b : Charge D) : ℤ := ∑ i, α i * b i

/-- Translation of the actual current-eigenvalue vector, not of dual coordinates. -/
def shiftWeight (b α : Charge D) : Charge D := b + D.G.mulVec α

theorem gram_mulVec_unit (α : Charge D) (i : Fin D.rank) :
    (D.G.mulVec α) i = bilinear D (unitCharge D i) α := by
  simp [Matrix.mulVec, dotProduct, bilinear, unitCharge]

theorem weightPairing_add (α β b : Charge D) :
    weightPairing (α + β) b = weightPairing α b + weightPairing β b := by
  simp [weightPairing, add_mul, Finset.sum_add_distrib]

theorem weightPairing_shift (α β b : Charge D) :
    weightPairing α (shiftWeight b β) = weightPairing α b + bilinear D α β := by
  simp [weightPairing, shiftWeight, Matrix.mulVec, dotProduct, bilinear,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

variable (J : FullJacobiLatticeModule D M)
variable (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- Unfold the actual eigenspaces, including the coercion Omega -> M. -/
theorem mem_jointWeight_iff (b : Charge D) (v : Omega J) :
    v ∈ jointWeight J b ↔
      ∀ i : Fin D.rank, current J i 0 v.val = (b i : ℂ) • v.val := by
  rw [jointWeight, Submodule.mem_iInf]
  constructor
  · intro hv i
    have hi := hv i
    rw [integerEigenspace, Module.End.mem_eigenspace_iff] at hi
    change C J i v = (b i : ℂ) • v at hi
    simpa only [C_coe, Submodule.coe_smul] using congrArg Subtype.val hi
  · intro hv i
    rw [integerEigenspace, Module.End.mem_eigenspace_iff]
    change C J i v = (b i : ℂ) • v
    apply Subtype.ext
    simpa only [C_coe, Submodule.coe_smul] using hv i

theorem Hzero_on_jointWeight (α b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    Hzero J α v = (weightPairing α b : ℂ) • v := by
  have he := (mem_jointWeight_iff J b v).mp hv
  apply Subtype.ext
  simp only [Hzero_coe, Hcharge, LinearMap.sum_apply, LinearMap.smul_apply,
    he, smul_smul, ← Finset.sum_smul, weightPairing, Int.cast_sum,
    Int.cast_mul, Submodule.coe_smul]

/-- Right eigenrelation Z_Hzero selects exactly one original integral mode. -/
theorem Z_selection (α b : Charge D) (m : ℤ) (v : Omega J)
    (hv : v ∈ jointWeight J b) (hm : m ≠ -weightPairing α b - 1) :
    Z J hNil H hHG hGH α m v = 0 := by
  have h := Z_Hzero J hNil H hHG hGH α m v
  rw [Hzero_on_jointWeight J α b v hv, map_smul] at h
  have hz : ((weightPairing α b : ℂ) - (-(m + 1 : ℤ) : ℂ)) •
      Z J hNil H hHG hGH α m v = 0 := by
    rw [sub_smul, h, sub_self]
  have hn : (weightPairing α b : ℂ) - (-(m + 1 : ℤ) : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hi : weightPairing α b = -(m + 1) := Int.cast_injective (by simpa only [Int.cast_neg] using he)
    exact hm (by omega)
  exact (smul_eq_zero.mp hz).resolve_left hn

/-- The actual zero-current commutator shifts every basis eigenvalue. -/
theorem Z_mem_jointWeight (α b : Charge D) (m : ℤ) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    Z J hNil H hHG hGH α m v ∈ jointWeight J (shiftWeight b α) := by
  rw [mem_jointWeight_iff]
  intro i
  have he := (mem_jointWeight_iff J b v).mp hv i
  calc
    current J i 0 (Z J hNil H hHG hGH α m v : M) =
        (b i : ℂ) • (Z J hNil H hHG hGH α m v : M) +
          (bilinear D (unitCharge D i) α : ℂ) •
            (Z J hNil H hHG hGH α m v : M) := by
      rw [current_zero_Z, he, map_smul, map_smul, ← Z_coe]
    _ = _ := by
      rw [← add_smul]
      congr 1
      simp only [shiftWeight, Pi.add_apply, Int.cast_add, gram_mulVec_unit]

/-- This is the original surviving mode, with its weight label explicit.
On other weights no action law for this fixed b is asserted. -/
def S (α b : Charge D) : Module.End ℂ (Omega J) :=
  Z J hNil H hHG hGH α (-weightPairing α b - 1)

theorem S_mem_jointWeight (α b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    S J hNil H hHG hGH α b v ∈ jointWeight J (shiftWeight b α) :=
  Z_mem_jointWeight J hNil H hHG hGH α b _ v hv

/-- The factorial Taylor coefficient formula, evaluated in the original M. -/
theorem coefficient_E_ground_raw (α : Charge D) (d : Index D →₀ ℕ)
    (m : ℤ) (v : Omega J) :
    ((W J hNil H hHG).coefficient d (E J α m v.val) : M) =
      ((WeylData.factorial d : ℂ)⁻¹ * derivativeScalar α d) •
        (Z J hNil H hHG hGH α (m + occupationWeight d) v : M) := by
  have hc := congrArg (fun z : Omega J => (z : M))
    (coefficient_E_ground J hNil H hHG hGH α d m v)
  simpa only [vacuumToOmega_coe, Submodule.coe_smul] using hc

/-- An explicit finite creator formula. No interchange of infinite sums
and no proposed exponential/S product is used. All indices lie in the
actual input-dependent finite Iic jointCutoff supplied by algebraic Taylor. -/
theorem finite_E_ground_taylor (α : Charge D) (m : ℤ) (v : Omega J) :
    E J α m v.val =
      ∑ d ∈ Finset.Iic ((W J hNil H hHG).jointCutoff (E J α m v.val)),
        ((WeylData.factorial d : ℂ)⁻¹ * derivativeScalar α d) •
          (W J hNil H hHG).creation d
            (Z J hNil H hHG hGH α (m + occupationWeight d) v : M) := by
  classical
  calc
    E J α m v.val =
        ∑ d ∈ Finset.Iic ((W J hNil H hHG).jointCutoff (E J α m v.val)),
          (W J hNil H hHG).creation d
            ((W J hNil H hHG).coefficient d (E J α m v.val)) := by
      symm
      calc
        _ = ∑ d ∈ Finset.Iic ((W J hNil H hHG).jointCutoff (E J α m v.val)),
            (WeylData.factorial d : ℂ)⁻¹ •
              (W J hNil H hHG).creation d
                ((W J hNil H hHG).vacuumProjection
                  ((W J hNil H hHG).derivative d (E J α m v.val))) := by
          apply Finset.sum_congr rfl
          intro d hd
          simp only [WeylData.coefficient, LinearMap.smul_apply,
            LinearMap.comp_apply, Submodule.coe_smul, WeylData.vacuumProject_coe,
            map_smul]
        _ = _ := (W J hNil H hHG).taylor_reconstruction (E J α m v.val)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [coefficient_E_ground_raw J hNil H hHG hGH, map_smul]

theorem occupationWeight_pos (d : Index D →₀ ℕ) (hd : d ≠ 0) :
    0 < occupationWeight d := by
  by_contra hn
  have hz : occupationWeight d = 0 := Nat.eq_zero_of_not_pos hn
  apply hd
  ext x
  have he := Finsupp.le_weight (fun y : Index D => y.2 + 1)
    (s := x) (by omega) d
  change d x ≤ occupationWeight d at he
  simp only [Finsupp.zero_apply]
  omega

include hNil H hHG hGH in
/-- Selection for the original E, stronger than selection after Pi.
Every Taylor term has nonnegative weight and its Z coefficient is zero. -/
theorem E_above_leading (α b : Charge D) (m : ℤ) (v : Omega J)
    (hv : v ∈ jointWeight J b) (hm : -weightPairing α b ≤ m) :
    E J α m v.val = 0 := by
  classical
  rw [finite_E_ground_taylor J hNil H hHG hGH]
  apply Finset.sum_eq_zero
  intro d hd
  have hz := Z_selection J hNil H hHG hGH α b
    (m + occupationWeight d) v hv (by omega)
  simp only [hz, Submodule.coe_zero, map_zero, smul_zero]

/-- The leading original mode is already a ground vector. For nonzero
occupations, positivity of oscillator weight kills the Z coefficient.
The unique zero occupation gives factorial=1, scalar=1, creation=Id. -/
theorem E_leading (α b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    E J α (-weightPairing α b - 1) v.val =
      (S J hNil H hHG hGH α b v : M) := by
  classical
  rw [finite_E_ground_taylor J hNil H hHG hGH]
  rw [Finset.sum_eq_single (0 : Index D →₀ ℕ)]
  · simp [S]
  · intro d hd hd0
    have hw := occupationWeight_pos d hd0
    have hz := Z_selection J hNil H hHG hGH α b
      (-weightPairing α b - 1 + occupationWeight d) v hv (by omega)
    simp only [hz, Submodule.coe_zero, map_zero, smul_zero]
  · intro hn
    exact (hn (Finset.mem_Iic.mpr zero_le)).elim

end D5.S3.VertexAlgebra.Modules.ActualGroundChargedSelection

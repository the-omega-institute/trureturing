/- GID: D5/S3/Observer/Dynamics/ToralReturnModuleStructure
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/ToralReturnModuleStructure
   mirror-E: none(waiver:explicit-integer-quotient-isomorphisms)
   anchors: []
   utility: none
   digest: Exact readout kernels classify the actual one-step return groups and expose a uniform exponent separation. -/

import D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The two quotients are precisely the ReturnModule objects of the predecessor.
The quotient maps, surjectivity and image=kernel identities are constructed.
No Smith invariants, group isomorphisms or nonisomorphism are supplied as
premises.  The classification includes k=0 with ZMod 0 = Z; the exponent
separation and finite-cardinality comparison require k>0.

Pinned mathlib source search reused ZMod.intCast_zmod_eq_zero_iff_dvd,
ZMod.natCast_eq_zero_iff and LinearMap.quotKerEquivOfSurjective.
Classical context: Rodrigues--Ramos arXiv:math/0303185 and
Bakker--Rodrigues arXiv:2207.00922.  This is a calibrated structural
recovery result, not a classification of arbitrary toral automorphisms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped Matrix

namespace D5.S3.Observer.Dynamics.ToralReturnModuleStructure

open D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

/-- The actual cyclic residue readout of the first integer lattice. -/
def companionReadout (k : ℕ) : Lattice →ₗ[ℤ] ZMod (4 * k) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun v => (v 1 : ZMod (4 * k))
      map_zero' := by simp
      map_add' := by intro v w; simp }

/-- The two actual residues retained for the second lattice. -/
def balancedReadout (k : ℕ) : Lattice →ₗ[ℤ] ZMod 2 × ZMod (2 * k) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun v => ((v 0 : ZMod 2), ((v 1 - (k : ℤ) * v 0 : ℤ) : ZMod (2 * k)))
      map_zero' := by simp
      map_add' := by
        intro v w
        apply Prod.ext
        · simp
        · change (((v 1 + w 1) - (k : ℤ) * (v 0 + w 0) : ℤ) : ZMod (2 * k)) =
            ((v 1 - (k : ℤ) * v 0 : ℤ) : ZMod (2 * k)) +
            ((w 1 - (k : ℤ) * w 0 : ℤ) : ZMod (2 * k))
          push_cast
          ring }

private theorem companion_return_action (k : ℕ) (v : Lattice) :
    Matrix.toLin' (companion k - 1) v =
      ![4 * (k : ℤ) * v 0 + v 1, 4 * (k : ℤ) * v 0] := by
  change (companion k - 1).mulVec v = _
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, companion] <;> ring

private theorem balanced_return_action (k : ℕ) (v : Lattice) :
    Matrix.toLin' (balanced k - 1) v =
      ![2 * (k : ℤ) * v 0 + 2 * v 1,
        2 * (k : ℤ) * ((k : ℤ) + 1) * v 0 + 2 * (k : ℤ) * v 1] := by
  change (balanced k - 1).mulVec v = _
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, balanced] <;> ring

private theorem companion_readout_surjective (k : ℕ) :
    Function.Surjective (companionReadout k) := by
  intro z
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective z
  refine ⟨![0, b], ?_⟩
  change (b : ZMod (4 * k)) = z
  exact hb

private theorem balanced_readout_surjective (k : ℕ) :
    Function.Surjective (balancedReadout k) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective a
  obtain ⟨y, hy⟩ := ZMod.intCast_surjective b
  refine ⟨![x, y + (k : ℤ) * x], ?_⟩
  apply Prod.ext
  · change (x : ZMod 2) = a
    exact hx
  · change ((y + (k : ℤ) * x - (k : ℤ) * x : ℤ) : ZMod (2 * k)) = b
    simpa using hy

/-- The cyclic residue kernel is exactly the first matrix's return image. -/
theorem companion_image_eq_kernel (k : ℕ) :
    LinearMap.range (Matrix.toLin' (companion k - 1)) =
      LinearMap.ker (companionReadout k) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    change companionReadout k (Matrix.toLin' (companion k - 1) x) = 0
    rw [companion_return_action]
    change ((4 * (k : ℤ) * x 0 : ℤ) : ZMod (4 * k)) = 0
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    refine ⟨x 0, ?_⟩
    simp
  · intro hv
    change (v 1 : ZMod (4 * k)) = 0 at hv
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hv
    push_cast at ha
    refine ⟨![a, v 0 - 4 * (k : ℤ) * a], ?_⟩
    rw [companion_return_action]
    funext i
    fin_cases i
    · simp <;> ring
    · simpa using ha.symm

/-- The two-residue kernel is exactly the second matrix's return image. -/
theorem balanced_image_eq_kernel (k : ℕ) :
    LinearMap.range (Matrix.toLin' (balanced k - 1)) =
      LinearMap.ker (balancedReadout k) := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    change balancedReadout k (Matrix.toLin' (balanced k - 1) x) = 0
    rw [balanced_return_action]
    apply Prod.ext
    · change ((2 * (k : ℤ) * x 0 + 2 * x 1 : ℤ) : ZMod 2) = 0
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      refine ⟨(k : ℤ) * x 0 + x 1, ?_⟩
      norm_num <;> ring
    · change ((2 * (k : ℤ) * ((k : ℤ) + 1) * x 0 + 2 * (k : ℤ) * x 1 -
          (k : ℤ) * (2 * (k : ℤ) * x 0 + 2 * x 1) : ℤ) : ZMod (2 * k)) = 0
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      refine ⟨x 0, ?_⟩
      push_cast
      ring
  · intro hv
    change ((v 0 : ZMod 2), ((v 1 - (k : ℤ) * v 0 : ℤ) : ZMod (2 * k))) = 0 at hv
    have h0 : (v 0 : ZMod 2) = 0 := congrArg Prod.fst hv
    have h1 : ((v 1 - (k : ℤ) * v 0 : ℤ) : ZMod (2 * k)) = 0 := congrArg Prod.snd hv
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
    push_cast at ha hb
    refine ⟨![b, a - (k : ℤ) * b], ?_⟩
    rw [balanced_return_action]
    funext i
    fin_cases i <;> simp <;> nlinarith [ha, hb]

/-- The first isomorphism theorem on the actual first return quotient. -/
def companionReturnEquiv (k : ℕ) :
    ReturnModule (companion k) 1 ≃ₗ[ℤ] ZMod (4 * k) := by
  change (Lattice ⧸ LinearMap.range (Matrix.toLin' (companion k ^ 1 - 1))) ≃ₗ[ℤ] _
  simp only [pow_one]
  rw [companion_image_eq_kernel]
  exact LinearMap.quotKerEquivOfSurjective _ (companion_readout_surjective k)

/-- The first isomorphism theorem on the actual second return quotient. -/
def balancedReturnEquiv (k : ℕ) :
    ReturnModule (balanced k) 1 ≃ₗ[ℤ] ZMod 2 × ZMod (2 * k) := by
  change (Lattice ⧸ LinearMap.range (Matrix.toLin' (balanced k ^ 1 - 1))) ≃ₗ[ℤ] _
  simp only [pow_one]
  rw [balanced_image_eq_kernel]
  exact LinearMap.quotKerEquivOfSurjective _ (balanced_readout_surjective k)

/-- Explicit group classifications for all parameters, including the infinite k=0 case. -/
theorem one_step_return_module_classification (k : ℕ) :
    Nonempty (ReturnModule (companion k) 1 ≃ₗ[ℤ] ZMod (4 * k)) ∧
    Nonempty (ReturnModule (balanced k) 1 ≃ₗ[ℤ] ZMod 2 × ZMod (2 * k)) :=
  ⟨⟨companionReturnEquiv k⟩, ⟨balancedReturnEquiv k⟩⟩

/-- Every element of the second actual return group is killed by 2k. -/
theorem balanced_return_annihilated (k : ℕ) (z : ReturnModule (balanced k) 1) :
    (2 * k) • z = 0 := by
  apply (balancedReturnEquiv k).injective
  rw [map_nsmul, map_zero]
  apply Prod.ext
  · change (2 * k) • (balancedReturnEquiv k z).1 = 0
    have hcast : ((2 * k : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr ⟨k, rfl⟩
    rw [nsmul_eq_mul, hcast, zero_mul]
  · change (2 * k) • (balancedReturnEquiv k z).2 = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The first actual return group contains an element not killed by 2k. -/
theorem companion_return_not_annihilated (k : ℕ) (hk : 0 < k) :
    ∃ z : ReturnModule (companion k) 1, (2 * k) • z ≠ 0 := by
  refine ⟨(companionReturnEquiv k).symm 1, ?_⟩
  intro hz
  have h := congrArg (companionReturnEquiv k) hz
  have hzero : ((2 * k : ℕ) : ZMod (4 * k)) = 0 := by
    simpa only [map_nsmul, LinearEquiv.apply_symm_apply, map_zero, nsmul_eq_mul, mul_one] using h
  have hdiv : 4 * k ∣ 2 * k := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hle := Nat.le_of_dvd (show 0 < 2 * k by omega) hdiv
  omega

/-- The two actual return groups are not additively isomorphic for any positive parameter. -/
theorem one_step_return_modules_not_isomorphic (k : ℕ) (hk : 0 < k) :
    ¬ Nonempty (ReturnModule (companion k) 1 ≃+ ReturnModule (balanced k) 1) := by
  rintro ⟨e⟩
  obtain ⟨z, hz⟩ := companion_return_not_annihilated k hk
  apply hz
  apply e.injective
  simpa only [map_nsmul, map_zero] using balanced_return_annihilated k (e z)

/-- All positive-time sizes agree, yet the actual one-step group structures differ. -/
theorem scalar_spectrum_and_structural_separation (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 0 < n →
      Nat.card (ReturnModule (companion k) n) =
        Nat.card (ReturnModule (balanced k) n)) ∧
    ¬ Nonempty (ReturnModule (companion k) 1 ≃+ ReturnModule (balanced k) 1) :=
  ⟨fun n hn => (equal_cardinality_return_modules k hk n hn).1,
    one_step_return_modules_not_isomorphic k hk⟩

#print axioms companion_image_eq_kernel
#print axioms balanced_image_eq_kernel
#print axioms one_step_return_module_classification
#print axioms balanced_return_annihilated
#print axioms companion_return_not_annihilated
#print axioms one_step_return_modules_not_isomorphic
#print axioms scalar_spectrum_and_structural_separation

end D5.S3.Observer.Dynamics.ToralReturnModuleStructure

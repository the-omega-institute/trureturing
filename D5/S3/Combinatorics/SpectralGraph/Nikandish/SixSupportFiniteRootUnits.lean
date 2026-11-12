/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportFiniteRootUnits
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteRootGeometry

/-! This uses the actual ring, places and embedding
constructed in FiniteDRootGeometry01; it assumes none of the target geometry.
-/
namespace NikandishE3.FiniteDRoot
open Polynomial WithZero
open scoped QuadraticAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (k : Type*) [Field k] [CharZero k]

def localResidueEquiv (r : DRoot k) :
    (Local k r ⧸ IsLocalRing.maximalIdeal (Local k r)) ≃+* k :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal (rootIdeal k r) (Local k r)).symm.toRingEquiv.trans
    (orderResidueEquiv k r)

/-- Residue degree for the actual quotient extension. -/
theorem residue_degree_one (r : DRoot k) : (rootIdeal k r).inertiaDeg (R k) = 1 := by
  have hp : ((rootIdeal k r).under (R k)).IsMaximal := by
    rw [rootIdeal_under]
    infer_instance
  letI := hp
  letI : Field ((R k) ⧸ (rootIdeal k r).under (R k)) := Ideal.Quotient.field _
  letI : Field ((Order k) ⧸ rootIdeal k r) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg_eq_of_isMaximal ((rootIdeal k r).under (R k)) (rootIdeal k r)]
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨Ideal.algebraMap_quotient_injective, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨Ideal.Quotient.mk _ (C (w.re.eval r.1)), ?_⟩
  change Ideal.Quotient.mk _ (algebraMap (R k) (Order k) (C (w.re.eval r.1))) =
    Ideal.Quotient.mk _ w
  apply Ideal.Quotient.eq.mpr
  change ((algebraMap (R k) (Order k) (C (w.re.eval r.1)) - w).re).eval r.1 = 0
  simp

theorem A_eval_ne_zero (r : DRoot k) : (pk k A).eval r.1 ≠ 0 := by
  intro ha
  have hshape : (3 : k) * r.1 - 1 = 0 := by simpa [pk, A] using ha
  have hr : r.1 = (1/3 : k) := by linear_combination (1/3 : k) * hshape
  have hzero := r.2
  rw [hr] at hzero
  have hvalue : (pk k D).eval (1/3 : k) = (16/729 : k) := by
    change (D.map (algebraMap ℚ k)).eval (1/3 : k) = (16/729 : k)
    rw [Polynomial.eval_map]
    have hscalar : algebraMap ℚ k (1/3 : ℚ) = (1/3 : k) := by norm_num
    rw [← hscalar, Polynomial.eval₂_at_apply, special_D]
    norm_num
  rw [hvalue] at hzero
  norm_num at hzero

theorem N_eval_ne_zero (r : DRoot k) : (pk k N).eval r.1 ≠ 0 := by
  obtain ⟨u, v, huv⟩ := coprime_N_D.map (pk k)
  intro hn
  have he := congrArg (Polynomial.eval r.1) huv
  simp only [eval_add, eval_mul, hn, r.2, mul_zero, add_zero, eval_one] at he
  exact zero_ne_one he

/-- A times the actual f, before localization. -/
def fNumerator : Order k :=
  algebraMap (R k) (Order k) (pk k A * (pk k t)^2 + 2 * pk k B) - 2 * Y k

theorem fNumerator_relation :
    intoH k (fNumerator k) = algebraMap (R k) (H k) (pk k A) * f k := by
  have hA : algebraMap (R k) (K k) (pk k A) ≠ 0 := A_nonzero k
  simp only [fNumerator, map_sub, map_mul, map_ofNat, intoH_algebraMap, intoH_Y,
    map_add, map_pow]
  apply QuadraticAlgebra.ext <;>
    simp [f, y, rf, pow_two, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat] <;> field_simp [hA] <;> ring

theorem fNumerator_norm_identity :
    (pk k A * (pk k t)^2 + 2 * pk k B)^2 - 4 * pk k D = pk k A * pk k N := by
  have hd := congrArg (pk k) discriminant_certificate
  have hn := congrArg (pk k) norm_certificate
  simp only [map_sub, map_pow, map_mul, map_add, map_ofNat] at hd hn
  linear_combination 4 * hd + pk k A * hn

theorem fNumerator_eval_ne_zero (r : DRoot k) : rootEval k r (fNumerator k) ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.eval r.1) (fNumerator_norm_identity k)
  have hz' : (pk k A).eval r.1 * ((pk k t).eval r.1)^2 + 2 * (pk k B).eval r.1 = 0 := by
    simpa [rootEval, fNumerator, Y, pow_two] using hz
  simp only [eval_sub, eval_pow, eval_mul, eval_add, eval_ofNat, r.2,
    hz', zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at he
  exact (mul_ne_zero (A_eval_ne_zero k r) (N_eval_ne_zero k r)) he.symm

def localA (r : DRoot k) : Local k r :=
  algebraMap (Order k) (Local k r) (algebraMap (R k) (Order k) (pk k A))
def localNumerator (r : DRoot k) : Local k r :=
  algebraMap (Order k) (Local k r) (fNumerator k)

theorem localA_unit (r : DRoot k) : IsUnit (localA k r) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (Local k r) (rootIdeal k r) _).mpr
  exact A_eval_ne_zero k r
theorem localNumerator_unit (r : DRoot k) : IsUnit (localNumerator k r) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (Local k r) (rootIdeal k r) _).mpr
  exact fNumerator_eval_ne_zero k r

/-- An element of the actual local ring mapping to the accepted f. -/
def localF (r : DRoot k) : Local k r :=
  localNumerator k r * ↑((localA_unit k r).unit⁻¹)

theorem localF_unit (r : DRoot k) : IsUnit (localF k r) :=
  (localNumerator_unit k r).mul (Units.isUnit _)

theorem localF_intoH (r : DRoot k) : algebraMap (Local k r) (H k) (localF k r) = f k := by
  have hA : algebraMap (Local k r) (H k) (localA k r) =
      algebraMap (R k) (H k) (pk k A) := by
    rw [localA, ← IsScalarTower.algebraMap_apply (Order k) (Local k r) (H k)]
    exact (intoH k).commutes _
  have hnum : algebraMap (Local k r) (H k) (localNumerator k r) =
      algebraMap (R k) (H k) (pk k A) * f k := by
    rw [localNumerator, ← IsScalarTower.algebraMap_apply (Order k) (Local k r) (H k)]
    exact fNumerator_relation k
  have hunit : algebraMap (Local k r) (H k) ↑((localA_unit k r).unit⁻¹) =
      (algebraMap (R k) (H k) (pk k A))⁻¹ := by
    rw [map_units_inv, IsUnit.unit_spec, hA]
  rw [localF, map_mul, hnum, hunit]
  have hA0 : algebraMap (R k) (H k) (pk k A) ≠ 0 := by
    change algebraMap (K k) (H k) (rf k A) ≠ 0
    simpa only [map_zero] using (algebraMap (K k) (H k)).injective.ne (A_nonzero k)
  field_simp

theorem valuation_f (r : DRoot k) : normalizedValuation k r (f k) = 1 := by
  rw [← localF_intoH k r]
  exact valuation_local_unit k r _ (localF_unit k r)

theorem order_f_zero (r : DRoot k) :
    IsDiscreteValuationRing.addVal (Local k r) (localF k r) = 0 :=
  IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (localF_unit k r)

end
end NikandishE3.FiniteDRoot

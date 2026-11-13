/- GID: D5/S1/Dynamics/Symbolic/KhetanLineFactorCancellation
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: A genuine Laurent line divisor supplies cancellation on every actual tile fiber. -/

import D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer
import D5.S1.Dynamics.Symbolic.KhetanLatticeGeometry
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The Laurent action, line embedding and negative-exponent exact-cover mask are
the existing ones from `KhetanOneDirectionPeriodizer`. The geometric consumer
uses positive offsets. Consequently a root of the line factor supplies its
inverse as the root in `KhetanLatticeGeometry.FiberCancellation`.

The coefficient field may be any field equipped with a homomorphism to the
complex numbers, in particular the real or complex field. Nonunit means
nonunit over that field, excluding every nonzero scalar times a monomial.
No root, unit-modulus condition, fiber cancellation or factorization of the
mask is assumed beyond the displayed actual line divisibility.

Root extraction reuses Mathlib's Laurent localization, removal of the full
zero-root multiplicity and fundamental theorem of algebra. The new bridge
specializes the actual lattice monomials and reads their determinant-fiber
coefficients. The two-factor theorem feeds these equations to the existing
six-cell geometry theorem for the given tiling. Existence of the requisite
line factors in the remaining cases is outside this implication.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanLineFactorCancellation

open scoped BigOperators
open D5.S1.Dynamics.Symbolic.KhetanLatticeGeometry
open D5.S1.Dynamics.Symbolic.KhetanOneDirectionPeriodizer

variable {R : Type*} [Field R]

private lemma coordinate_add (u x y : Lattice) :
    fiberCoordinate u (x + y) = fiberCoordinate u x + fiberCoordinate u y := by
  simp only [fiberCoordinate, Prod.fst_add, Prod.snd_add]
  ring

private lemma coordinate_neg (u x : Lattice) :
    fiberCoordinate u (-x) = -fiberCoordinate u x := by
  change Int.gcdA u.1 u.2 * (-x.1) + Int.gcdB u.1 u.2 * (-x.2) =
    -(Int.gcdA u.1 u.2 * x.1 + Int.gcdB u.1 u.2 * x.2)
  ring

private lemma coordinate_sub (u x y : Lattice) :
    fiberCoordinate u (x - y) = fiberCoordinate u x - fiberCoordinate u y := by
  rw [sub_eq_add_neg, coordinate_add, coordinate_neg, sub_eq_add_neg]

private lemma determinant_add (u x y : Lattice) :
    det u (x + y) = det u x + det u y := by
  simp only [det, Prod.fst_add, Prod.snd_add]
  ring

private lemma determinant_neg (u x : Lattice) : det u (-x) = -det u x := by
  change u.1 * (-x.2) - u.2 * (-x.1) = -(u.1 * x.2 - u.2 * x.1)
  ring

/-- Specialize the primitive coordinate and retain the transverse exponent. -/
private noncomputable def weightedMonomial (u : Lattice) (root : ℂˣ) :
    Multiplicative Lattice →* LaurentPolynomial ℂ where
  toFun z := AddMonoidAlgebra.single (det u z.toAdd)
    ((root : ℂ) ^ fiberCoordinate u z.toAdd)
  map_one' := by
    change AddMonoidAlgebra.single (det u 0) ((root : ℂ) ^ fiberCoordinate u 0) = 1
    simpa [det, fiberCoordinate] using
      (rfl : AddMonoidAlgebra.single (0 : ℤ) (1 : ℂ) = (1 : LaurentPolynomial ℂ))
  map_mul' x y := by
    change AddMonoidAlgebra.single (det u (x.toAdd + y.toAdd))
      ((root : ℂ) ^ fiberCoordinate u (x.toAdd + y.toAdd)) = _
    rw [determinant_add, coordinate_add, zpow_add₀ root.ne_zero,
      AddMonoidAlgebra.single_mul_single]

private noncomputable def weightedProjection (ρ : R →+* ℂ) (u : Lattice)
    (root : ℂˣ) : AddMonoidAlgebra R Lattice →+* LaurentPolynomial ℂ :=
  AddMonoidAlgebra.liftNCRingHom (LaurentPolynomial.C.comp ρ)
    (weightedMonomial u root) (fun _ _ => Commute.all _ _)

private lemma weighted_projection_single (ρ : R →+* ℂ) (u z : Lattice)
    (root : ℂˣ) (a : R) :
    weightedProjection ρ u root (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (det u z) (ρ a * (root : ℂ) ^ fiberCoordinate u z) := by
  rw [weightedProjection, AddMonoidAlgebra.liftNCRingHom_single]
  change AddMonoidAlgebra.single 0 (ρ a) *
    AddMonoidAlgebra.single (det u z) ((root : ℂ) ^ fiberCoordinate u z) = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]

private lemma weighted_projection_line (ρ : R →+* ℂ) (u : Lattice)
    (hu : Primitive u) (root : ℂˣ) (A : LaurentPolynomial R) :
    weightedProjection ρ u root (lineLaurent u A) =
      LaurentPolynomial.C (LaurentPolynomial.eval₂ ρ root A) := by
  have hb : u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2 = 1 := by
    simpa [show Int.gcd u.1 u.2 = 1 from hu] using
      (Int.gcd_eq_gcd_ab u.1 u.2).symm
  have hcoord (n : ℤ) : fiberCoordinate u (n • u) = n := by
    change Int.gcdA u.1 u.2 * (n * u.1) + Int.gcdB u.1 u.2 * (n * u.2) = n
    calc
      _ = n * (u.1 * Int.gcdA u.1 u.2 + u.2 * Int.gcdB u.1 u.2) := by ring
      _ = n := by rw [hb, mul_one]
  have hdet (n : ℤ) : det u (n • u) = 0 := by
    change u.1 * (n * u.2) - u.2 * (n * u.1) = 0
    ring
  induction A using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single n a =>
    have heval : LaurentPolynomial.eval₂ ρ root (AddMonoidAlgebra.single n a) =
        ρ a * (root : ℂ) ^ n := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T,
        Units.val_zpow_eq_zpow_val]
    simp only [line_laurent_single, weighted_projection_single, hcoord, hdet, heval,
      LaurentPolynomial.single_eq_C]

/-- A nonzero nonunit Laurent polynomial over a subfield of the complex numbers
has a nonzero complex root. Both zero-root removal and nonconstancy are proved. -/
private theorem exists_nonzero_laurent_root (ρ : R →+* ℂ)
    (A : LaurentPolynomial R) (hA : A ≠ 0) (hunit : ¬ IsUnit A) :
    ∃ root : ℂˣ, LaurentPolynomial.eval₂ ρ root A = 0 := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow A
  have hq0 : q ≠ 0 := by
    intro hz
    have hAz : A * LaurentPolynomial.T (n : ℤ) = 0 := by
      rw [← hq, hz, map_zero]
    exact (mul_ne_zero hA (LaurentPolynomial.isUnit_T (n : ℤ)).ne_zero) hAz
  obtain ⟨s, hs, hnotX⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0
  have hs' : q = Polynomial.X ^ q.rootMultiplicity 0 * s := by simpa using hs
  have hs0 : s.coeff 0 ≠ 0 := by
    simpa only [map_zero, sub_zero, Polynomial.X_dvd_iff] using hnotX
  have hdegree : s.natDegree ≠ 0 := by
    intro hdeg
    have hqunit : IsUnit q.toLaurent := by
      rw [hs', Polynomial.eq_C_of_natDegree_eq_zero hdeg, map_mul, map_pow,
        Polynomial.toLaurent_X, Polynomial.toLaurent_C]
      exact ((LaurentPolynomial.isUnit_T (1 : ℤ)).pow _).mul
        ((isUnit_iff_ne_zero.mpr hs0).map LaurentPolynomial.C)
    rw [hq] at hqunit
    exact hunit ((Commute.all A (LaurentPolynomial.T (n : ℤ))).isUnit_mul_iff.mp hqunit).1
  have hmapdegree : 0 < (s.map ρ).degree := by
    rw [Polynomial.degree_map_eq_of_injective ρ.injective]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
  obtain ⟨z, hz⟩ := Complex.exists_root hmapdegree
  have hsroot' : Polynomial.eval₂ ρ z s = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hz
  have hz0 : z ≠ 0 := by
    intro heq
    apply hs0
    apply ρ.injective
    simpa only [heq, Polynomial.eval₂_at_zero, map_zero] using hsroot'
  let root : ℂˣ := Units.mk0 z hz0
  have hsroot : Polynomial.eval₂ ρ (root : ℂ) s = 0 := by
    simpa only [root, Units.val_mk0] using hsroot'
  have hqroot : LaurentPolynomial.eval₂ ρ root q.toLaurent = 0 := by
    rw [LaurentPolynomial.eval₂_toLaurent, hs', Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, hsroot, mul_zero]
  have hprod : LaurentPolynomial.eval₂ ρ root A *
      LaurentPolynomial.eval₂ ρ root (LaurentPolynomial.T (n : ℤ)) = 0 := by
    rw [← map_mul, ← hq]
    exact hqroot
  refine ⟨root, (mul_eq_zero.mp hprod).resolve_right ?_⟩
  exact ((LaurentPolynomial.isUnit_T (n : ℤ)).map
    (LaurentPolynomial.eval₂ ρ root)).ne_zero

private lemma weighted_mask_coefficient (ρ : R →+* ℂ) (F : Finset Lattice)
    (u p : Lattice) (root : ℂˣ) :
    (weightedProjection ρ u root
      (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom R) (exactCoverMask F))).coeff
        (-det u p) =
      ∑ q ∈ fiber F u p, (root : ℂ) ^ (-fiberCoordinate u q) := by
  classical
  simp only [exactCoverMask, map_sum, AddMonoidAlgebra.mapRingHom_single,
    weighted_projection_single, map_one, one_mul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single_apply, determinant_neg,
    coordinate_neg, fiber, Finset.sum_filter, neg_inj]

/-- An actual nonzero nonunit Laurent line divisor of the negative tile mask
supplies the inverse of one of its nonzero complex roots as the geometric root.
The same root works on every occupied determinant fiber. -/
theorem line_factor_fiber_cancellation (ρ : R →+* ℂ) (F : Finset Lattice)
    (u : Lattice) (hu : Primitive u) (A : LaurentPolynomial R)
    (hA : A ≠ 0) (hunit : ¬ IsUnit A)
    (hdiv : lineLaurent u A ∣
      AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom R) (exactCoverMask F)) :
    ∃ root : ℂˣ, LaurentPolynomial.eval₂ ρ root A = 0 ∧
      FiberCancellation F u (root : ℂ)⁻¹ := by
  classical
  obtain ⟨root, hroot⟩ := exists_nonzero_laurent_root ρ A hA hunit
  have hprojection : weightedProjection ρ u root
      (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom R) (exactCoverMask F)) = 0 := by
    obtain ⟨B, hB⟩ := hdiv
    rw [hB, map_mul, weighted_projection_line ρ u hu root A, hroot, map_zero, zero_mul]
  refine ⟨root, hroot, inv_ne_zero root.ne_zero, ?_⟩
  intro p _hp
  have hsum : (∑ q ∈ fiber F u p, (root : ℂ) ^ (-fiberCoordinate u q)) = 0 := by
    simpa only [weighted_mask_coefficient, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using
      congrArg (fun P : LaurentPolynomial ℂ => P.coeff (-det u p)) hprojection
  calc
    (∑ q ∈ fiber F u p, (root : ℂ)⁻¹ ^ fiberCoordinate u (q - p)) =
        ∑ q ∈ fiber F u p,
          (root : ℂ) ^ fiberCoordinate u p * (root : ℂ) ^ (-fiberCoordinate u q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [inv_zpow', coordinate_sub]
      have hexp : -(fiberCoordinate u q - fiberCoordinate u p) =
          fiberCoordinate u p + -fiberCoordinate u q := by ring
      rw [hexp, zpow_add₀ root.ne_zero]
    _ = (root : ℂ) ^ fiberCoordinate u p *
        (∑ q ∈ fiber F u p, (root : ℂ) ^ (-fiberCoordinate u q)) :=
      (Finset.mul_sum _ _ _).symm
    _ = 0 := by rw [hsum, mul_zero]

/-- Two genuine line divisors in independent primitive directions feed the
six-cell geometric consumer. Its conclusion concerns the orbit closure of
the given exact-cover complement. Cancellation is derived, not a premise. -/
theorem two_line_factors_orbit_closure_periodic (ρ : R →+* ℂ)
    (F : Finset Lattice) (T : Lattice → Prop) (u v : Lattice)
    (hF : F.card = 6) (hu : Primitive u) (hv : Primitive v) (huv : det u v ≠ 0)
    (A B : LaurentPolynomial R) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAu : ¬ IsUnit A) (hBu : ¬ IsUnit B)
    (hdivA : lineLaurent u A ∣
      AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom R) (exactCoverMask F))
    (hdivB : lineLaurent v B ∣
      AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom R) (exactCoverMask F))
    (hspan : FullDifferenceSpan F) (hcover : ExactCover F T) :
    ∃ t : Lattice, t ≠ 0 ∧
      ∀ c ∈ closure (Set.range (fun s : Lattice => fun x => indicator T (x + s))),
        ∀ x, c (x + t) = c x := by
  obtain ⟨rootU, _hrootU, hU⟩ := line_factor_fiber_cancellation ρ F u hu A hA hAu hdivA
  obtain ⟨rootV, _hrootV, hV⟩ := line_factor_fiber_cancellation ρ F v hv B hB hBu hdivB
  exact two_direction_orbit_closure_periodic F T u v (rootU : ℂ)⁻¹ (rootV : ℂ)⁻¹
    hF hu hv huv hU hV hspan hcover

end D5.S1.Dynamics.Symbolic.KhetanLineFactorCancellation

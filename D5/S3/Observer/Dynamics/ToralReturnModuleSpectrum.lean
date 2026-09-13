/- GID: D5/S3/Observer/Dynamics/ToralReturnModuleSpectrum
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/ToralReturnModuleSpectrum
   mirror-E: none(waiver:exact-unbounded-integer-family)
   anchors: []
   utility: none
   digest: An explicit infinite family has equal cardinalities of all actual return cokernels but admits no unimodular intertwiner. -/

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Tactic

/-!
The objects are the actual Bowen--Franks return modules
Z^2 / (A^n-I) Z^2.  No determinant is renamed a group cardinality.
The cardinality is derived from the pinned integer-lattice index theorem.
The parameter and time are unbounded; positive parameter/time ensure that
these cokernels are finite and nontrivial.  The zero-time quotient is not
counted as a finite periodic-point set.

Repository-first searches read MinimalBinaryUnimodularBreak, the Solenoid
exact-sequence/recurrence owners, and PRs #7342, #7443 and #7446.  No exact
return-cokernel owner was found.  Pinned mathlib db584cd6 supplies
Submodule.natAbs_det_equiv and LinearMap.det_toLin'.  The family-specific
intertwiner, positivity and integral obstruction are proved below.

Classical provenance: Rodrigues--Ramos, arXiv:math/0303185;
Bakker--Rodrigues, arXiv:2207.00922.  The distinction between the cardinality,
abelian-group structure and marked module structure is essential.
This file does not construct a mapping torus or compute its singular homology.
No Poincare or profinite-rigidity conjecture is claimed solved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped Matrix

namespace D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

abbrev Lattice := Fin 2 → ℤ
abbrev BinaryMatrix := Matrix (Fin 2) (Fin 2) ℤ

/-- The first member has trace 4k+2 and determinant one. -/
def companion (k : ℕ) : BinaryMatrix :=
  !![4 * (k : ℤ) + 1, 1; 4 * (k : ℤ), 1]

/-- The second member has the same characteristic polynomial. -/
def balanced (k : ℕ) : BinaryMatrix :=
  !![2 * (k : ℤ) + 1, 2; 2 * (k : ℤ) * ((k : ℤ) + 1), 2 * (k : ℤ) + 1]

/-- An integral isogeny, not an integral change of basis: its determinant is 2. -/
def bridge (k : ℕ) : BinaryMatrix := !![1, 0; -2 * (k : ℤ), 2]

/-- The genuine integer quotient for return time n, with column-vector convention. -/
abbrev ReturnModule (A : BinaryMatrix) (n : ℕ) :=
  Lattice ⧸ LinearMap.range (Matrix.toLin' (A ^ n - 1))

private theorem companion_det (k : ℕ) : (companion k).det = 1 := by
  norm_num [companion, Matrix.det_fin_two] <;> ring

private theorem balanced_det (k : ℕ) : (balanced k).det = 1 := by
  norm_num [balanced, Matrix.det_fin_two] <;> ring

private theorem bridge_det (k : ℕ) : (bridge k).det = 2 := by
  norm_num [bridge, Matrix.det_fin_two]

private theorem bridge_intertwines (k : ℕ) :
    companion k * bridge k = bridge k * balanced k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [companion, balanced, bridge, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem power_intertwines (A B P : BinaryMatrix)
    (h : A * P = P * B) (n : ℕ) : A ^ n * P = P * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        A ^ (n + 1) * P = A ^ n * (A * P) := by rw [pow_succ, Matrix.mul_assoc]
        _ = A ^ n * (P * B) := by rw [h]
        _ = (A ^ n * P) * B := by rw [Matrix.mul_assoc]
        _ = (P * B ^ n) * B := by rw [ih]
        _ = P * B ^ (n + 1) := by rw [pow_succ, Matrix.mul_assoc]

/-- Equality of all signed return determinants is derived from the degree-two isogeny. -/
theorem same_return_determinant (k n : ℕ) :
    (companion k ^ n - 1).det = (balanced k ^ n - 1).det := by
  have hp := power_intertwines (companion k) (balanced k) (bridge k)
    (bridge_intertwines k) n
  have hr : (companion k ^ n - 1) * bridge k =
      bridge k * (balanced k ^ n - 1) := by
    simpa only [sub_mul, mul_sub, one_mul, mul_one] using
      congrArg (fun X : BinaryMatrix => X - bridge k) hp
  have hd := congrArg Matrix.det hr
  rw [Matrix.det_mul, Matrix.det_mul, bridge_det] at hd
  nlinarith

private theorem companion_nonneg (k : ℕ) (i j : Fin 2) :
    0 ≤ companion k i j := by
  fin_cases i <;> fin_cases j <;> simp [companion] <;> positivity

private theorem companion_power_nonneg (k n : ℕ) :
    ∀ i j : Fin 2, 0 ≤ (companion k ^ n) i j := by
  induction n with
  | zero =>
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num
  | succ n ih =>
      intro i j
      rw [pow_succ]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_nonneg
        (mul_nonneg (ih i 0) (companion_nonneg k 0 j))
        (mul_nonneg (ih i 1) (companion_nonneg k 1 j))

private theorem companion_power_diagonal (k n : ℕ) :
    1 ≤ (companion k ^ n) 0 0 ∧ 1 ≤ (companion k ^ n) 1 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h01 := companion_power_nonneg k n 0 1
      have h10 := companion_power_nonneg k n 1 0
      have hk : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
      have h00 : (companion k ^ (n + 1)) 0 0 =
          (4 * (k : ℤ) + 1) * (companion k ^ n) 0 0 +
          4 * (k : ℤ) * (companion k ^ n) 0 1 := by
        rw [pow_succ]
        simp [Matrix.mul_apply, Fin.sum_univ_two, companion] <;> ring
      have h11 : (companion k ^ (n + 1)) 1 1 =
          (companion k ^ n) 1 0 + (companion k ^ n) 1 1 := by
        rw [pow_succ]
        simp [Matrix.mul_apply, Fin.sum_univ_two, companion]
      rw [h00, h11]
      constructor
      · nlinarith [ih.1, ih.2, mul_nonneg hk h01, mul_nonneg hk (show 0 ≤ (companion k ^ n) 0 0 from le_trans (by norm_num) ih.1)]
      · linarith [ih.2]

private theorem companion_power_trace (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    2 < Matrix.trace (companion k ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hdiag := companion_power_diagonal k m
  have h01 := companion_power_nonneg k m 0 1
  have h10 := companion_power_nonneg k m 1 0
  have hk' : 0 < (k : ℤ) := by exact_mod_cast hk
  have heq : Matrix.trace (companion k ^ (m + 1)) =
      (4 * (k : ℤ) + 1) * (companion k ^ m) 0 0 +
      4 * (k : ℤ) * (companion k ^ m) 0 1 +
      (companion k ^ m) 1 0 + (companion k ^ m) 1 1 := by
    rw [Matrix.trace_fin_two, pow_succ]
    simp [Matrix.mul_apply, Fin.sum_univ_two, companion] <;> ring
  rw [heq]
  nlinarith [hdiag.1, hdiag.2, mul_nonneg hk'.le h01, mul_le_mul_of_nonneg_left hdiag.1 hk'.le]

private theorem det_sub_one (A : BinaryMatrix) :
    (A - 1).det = A.det - Matrix.trace A + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

private theorem companion_return_det_neg (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    (companion k ^ n - 1).det < 0 := by
  rw [det_sub_one, Matrix.det_pow, companion_det, one_pow]
  linarith [companion_power_trace k n hk hn]

private theorem binary_toLin_injective (M : BinaryMatrix) (hd : M.det ≠ 0) :
    Function.Injective (Matrix.toLin' M) := by
  intro x y h
  change M.mulVec x = M.mulVec y at h
  have h0 : M 0 0 * x 0 + M 0 1 * x 1 = M 0 0 * y 0 + M 0 1 * y 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : M 1 0 * x 0 + M 1 1 * x 1 = M 1 0 * y 0 + M 1 1 * y 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  funext i
  fin_cases i
  · apply sub_eq_zero.mp
    have hz : M.det * (x 0 - y 0) = 0 := by
      rw [Matrix.det_fin_two]
      linear_combination M 1 1 * h0 - M 0 1 * h1
    exact (mul_eq_zero.mp hz).resolve_left hd
  · apply sub_eq_zero.mp
    have hz : M.det * (x 1 - y 1) = 0 := by
      rw [Matrix.det_fin_two]
      linear_combination M 0 0 * h1 - M 1 0 * h0
    exact (mul_eq_zero.mp hz).resolve_left hd

/-- An actual quotient-cardinality calculation; the nonsingularity is used to
construct the equivalence from the lattice onto the image submodule. -/
private theorem binary_cokernel_card (M : BinaryMatrix) (hd : M.det ≠ 0) :
    Nat.card (Lattice ⧸ LinearMap.range (Matrix.toLin' M)) = M.det.natAbs := by
  let f : Lattice →ₗ[ℤ] Lattice := Matrix.toLin' M
  have hinj : Function.Injective f := binary_toLin_injective M hd
  let e : Lattice ≃+ LinearMap.range f :=
    AddEquiv.ofBijective f.rangeRestrict.toAddMonoidHom
      ⟨fun x y h => hinj (congrArg Subtype.val h), by
        rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := hy
        exact ⟨x, rfl⟩⟩
  have he : (LinearMap.range f).subtype.comp
      (AddMonoidHom.toIntLinearMap (e : Lattice →+ LinearMap.range f)) = f := by
    ext x i
    rfl
  have hindex := Submodule.natAbs_det_equiv (LinearMap.range f) e
  rw [he] at hindex
  simpa only [f, LinearMap.det_toLin'] using hindex.symm

/-- Every positive-time return module in the two families has the same strictly
positive finite cardinality.  The statement concerns quotients, not just determinants. -/
theorem equal_cardinality_return_modules (k : ℕ) (hk : 0 < k) (n : ℕ) (hn : 0 < n) :
    Nat.card (ReturnModule (companion k) n) =
      Nat.card (ReturnModule (balanced k) n) ∧
    0 < Nat.card (ReturnModule (companion k) n) := by
  have hc : (companion k ^ n - 1).det ≠ 0 :=
    ne_of_lt (companion_return_det_neg k n hk hn)
  have hb : (balanced k ^ n - 1).det ≠ 0 := by
    rw [← same_return_determinant k n]
    exact hc
  have ccard : Nat.card (ReturnModule (companion k) n) =
      (companion k ^ n - 1).det.natAbs := binary_cokernel_card _ hc
  have dcard : Nat.card (ReturnModule (balanced k) n) =
      (balanced k ^ n - 1).det.natAbs := binary_cokernel_card _ hb
  constructor
  · rw [ccard, dcard, same_return_determinant]
  · rw [ccard]
    exact Int.natAbs_pos.mpr hc

/-- Every integral intertwiner has even determinant.  The two top-row equations
already force both entries of its bottom row to be even. -/
theorem intertwiner_determinant_even (k : ℕ) (P : BinaryMatrix)
    (h : companion k * P = P * balanced k) : 2 ∣ P.det := by
  have h0 := congrArg (fun M : BinaryMatrix => M 0 0) h
  have h1 := congrArg (fun M : BinaryMatrix => M 0 1) h
  simp [companion, balanced, Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
  have hc : P 1 0 = 2 * (k : ℤ) * (((k : ℤ) + 1) * P 0 1 - P 0 0) := by
    nlinarith [h0]
  have hd : P 1 1 = 2 * (P 0 0 - (k : ℤ) * P 0 1) := by
    nlinarith [h1]
  refine ⟨P 0 0 * (P 0 0 - (k : ℤ) * P 0 1) -
    P 0 1 * (k : ℤ) * (((k : ℤ) + 1) * P 0 1 - P 0 0), ?_⟩
  rw [Matrix.det_fin_two, hc, hd]
  ring

/-- Equal full return-cardinality sequences do not determine integral conjugacy.
This is an unbounded family with a uniform prime-two obstruction. -/
theorem spectrum_does_not_determine_integral_conjugacy (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 0 < n →
      Nat.card (ReturnModule (companion k) n) =
        Nat.card (ReturnModule (balanced k) n) ∧
      0 < Nat.card (ReturnModule (companion k) n)) ∧
    ¬ ∃ P : BinaryMatrix,
      (P.det = 1 ∨ P.det = -1) ∧ companion k * P = P * balanced k := by
  refine ⟨equal_cardinality_return_modules k hk, ?_⟩
  rintro ⟨P, hdet, hP⟩
  have heven := intertwiner_determinant_even k P hP
  rcases hdet with hp | hp <;> rw [hp] at heven <;> norm_num at heven

#print axioms same_return_determinant
#print axioms equal_cardinality_return_modules
#print axioms intertwiner_determinant_even
#print axioms spectrum_does_not_determine_integral_conjugacy

end D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

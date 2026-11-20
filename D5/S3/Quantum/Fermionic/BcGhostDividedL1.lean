/- GID: D5/S3/Quantum/Fermionic/BcGhostDividedL1
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostDividedL1
   mirror-E: none(waiver:algebraic-original-ghost-mode-product)
   anchors: []
   utility: none
   digest: Finite divided L(1) transport of the original ghost mode products. -/

import D5.S3.Quantum.Fermionic.BcGhostBorcherds
import D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
import D5.S3.VertexAlgebra.Analysis.IntegerNewton
import D5.S3.VertexAlgebra.StateField.BorcherdsPermutations
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Divided Möbius transport on the original ghost Fock space. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostDividedL1

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)
open CountableOccupationFock (Fock ket parity parity_involution)
open BcGhostStateField (Y stateField_translation)
open BcGhostConformalBRSTState (Omega conformal_modes)
open BcGhostVirasoro (L)
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.VertexAlgebra.StateField.BorcherdsPermutations (dividedTranslation)
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock

private abbrev modeMap (m : ℤ) : Fock →ₗ[ℂ] Module.End ℂ Fock :=
  (LinearMap.proj m).comp (VertexOperator.ncoeff.comp Y)

private abbrev mode (u : Fock) (m : ℤ) (v : Fock) : Fock := modeMap m u v

private theorem stress_commutator (p : ℕ) (u v : Fock) (m : ℤ) :
    mode Omega p (mode u m v) - mode u m (mode Omega p v) =
      ∑ i ∈ Finset.range (p + 1), (p.choose i : ℂ) •
        mode (mode Omega i u) ((p : ℤ) + m - i) v := by
  classical
  have hEven : parity Omega = (-1 : ℂ) ^ (0 : ℕ) • Omega := by
    norm_num [Omega, map_add, map_smul, parity_ket]
  have paritySquare : ∀ a : Fock, parity (parity a) = a :=
    fun a => LinearMap.congr_fun parity_involution a
  let comm : Fock →ₗ[ℂ] Fock := {
    toFun := fun a => mode Omega p (mode a m v) - mode a m (mode Omega p v)
    map_add' := fun a b => by
      simp only [mode, map_add, LinearMap.add_apply]
      abel
    map_smul' := fun c a => by
      simp only [mode, map_smul, LinearMap.smul_apply, smul_sub, RingHom.id_apply] }
  let iterates : Fock →ₗ[ℂ] Fock := ∑ i ∈ Finset.range (p + 1),
    (p.choose i : ℂ) •
      (LinearMap.applyₗ (R := ℂ) v).comp ((modeMap ((p : ℤ) + m - i)).comp (modeMap i Omega))
  have homogeneous (a : Fock) (e : ℕ) (ha : parity a = (-1 : ℂ) ^ e • a) :
      comm a = iterates a := by
    have h := (BcGhostBorcherds.borcherds Omega a v 0 e hEven ha p m 0).2.2.2
    change (∑ᶠ i : ℕ, integerBinomial p i •
      mode (mode Omega (0 + i) a) ((p : ℤ) + m - i) v) =
      ∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial 0 i) •
        (mode Omega ((p : ℤ) + 0 - i) (mode a (m + i) v) -
          (epsilon 0 * (-1 : ℂ) ^ (0 * e)) •
            mode a (m + 0 - i) (mode Omega ((p : ℤ) + i) v)) at h
    simp only [zero_add, add_zero, epsilon, zpow_zero, zero_mul, pow_zero, mul_one,
      one_smul] at h
    have zero_sum (f : ℕ → Fock) :
        (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial 0 i) • f i) = f 0 := by
      rw [finsum_eq_single _ 0]
      · simp [integerBinomial]
      · intro i hi
        simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
    rw [zero_sum] at h
    simp only [Int.natCast_zero, sub_zero, add_zero] at h
    change mode Omega p (mode a m v) - mode a m (mode Omega p v) = iterates a
    rw [← h]
    dsimp only [iterates]
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply Finset.mem_range.mpr
    by_contra hout
    exact hi (by simp [Nat.choose_eq_zero_of_lt (show p < i by omega)])
  have plus := homogeneous (u + parity u) 0 (by
    simp only [map_add, paritySquare, pow_zero, one_smul]
    exact add_comm _ _)
  have minus := homogeneous (u - parity u) 1 (by
    simp only [map_sub, paritySquare, pow_one, neg_one_smul]
    exact (neg_sub _ _).symm)
  have both := congrArg₂ (· + ·) plus minus
  have split : u + parity u + (u - parity u) = (2 : ℂ) • u := by
    rw [two_smul]
    abel
  rw [← map_add, ← map_add, split] at both
  simp only [map_smul] at both
  have heq := (smul_right_injective Fock (by norm_num : (2 : ℂ) ≠ 0)) both
  change mode Omega p (mode u m v) - mode u m (mode Omega p v) = iterates u at heq
  rw [heq]
  simp only [iterates, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.applyₗ_apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem translation_state_mode (u v : Fock) (m : ℤ) :
    mode (L (-1) u) m v = -(m : ℂ) • mode u (m - 1) v := by
  have h := stress_commutator 0 u v m
  simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_smul,
    Int.natCast_zero, zero_add, sub_zero] at h
  have hL : ((Y Omega)[[0]]) = L (-1) := by simpa using conformal_modes (-1)
  change ((Y Omega)[[0]]) (mode u m v) - mode u m (((Y Omega)[[0]]) v) =
    mode (((Y Omega)[[0]]) u) m v at h
  rw [hL] at h
  exact h.symm.trans (LinearMap.congr_fun (stateField_translation.2 u m) v)

/-- The native stress-state commutator on an integral ghost energy eigenstate. -/
theorem L1_mode_commutator (u v : Fock) (h m : ℤ) (hu : L 0 u = (h : ℂ) • u) :
    L 1 (((Y u)[[m]]) v) - ((Y u)[[m]]) (L 1 v) =
      ((Y (L 1 u))[[m]]) v + ((2 * h - m - 2 : ℤ) : ℂ) • ((Y u)[[m + 1]]) v := by
  have hc := stress_commutator 2 u v m
  rw [show (2 : ℕ) + 1 = 3 by decide, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hc
  simp only [show (2 : ℕ).choose 2 = 1 by decide, show (2 : ℕ).choose 1 = 2 by decide,
    Nat.choose_zero_right, Nat.cast_one, Nat.cast_ofNat, one_smul, Int.natCast_zero,
    sub_zero] at hc
  have h0 : ((Y Omega)[[0]]) = L (-1) := by simpa using conformal_modes (-1)
  have h1 : ((Y Omega)[[1]]) = L 0 := by simpa using conformal_modes 0
  have h2 : ((Y Omega)[[2]]) = L 1 := by simpa using conformal_modes 1
  change ((Y Omega)[[2]]) (mode u m v) - mode u m (((Y Omega)[[2]]) v) =
    mode (((Y Omega)[[0]]) u) (2 + m) v + (2 : ℂ) •
      mode (((Y Omega)[[1]]) u) (2 + m - 1) v +
      mode (((Y Omega)[[2]]) u) (2 + m - 2) v at hc
  rw [h0, h1, h2, hu, translation_state_mode,
    show 2 + m - 1 = m + 1 by omega, show 2 + m - 2 = m by omega] at hc
  change L 1 (mode u m v) - mode u m (L 1 v) =
    mode (L 1 u) m v + ((2 * h - m - 2 : ℤ) : ℂ) • mode u (m + 1) v
  rw [hc]
  simp only [mode, map_smul, LinearMap.smul_apply, smul_smul]
  have coefficient : -((2 + m : ℤ) : ℂ) + 2 * (h : ℂ) = ((2 * h - m - 2 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [← add_smul, coefficient, add_comm]

#print axioms L1_mode_commutator

local notation "D" => dividedTranslation (L 1)

private theorem divided_zero (x : Fock) : D 0 x = x := by
  simp [dividedTranslation]

private theorem raise_divided (j : ℕ) (x : Fock) : L 1 (D j x) = (j + 1 : ℂ) • D (j + 1) x := by
  have hfac : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hj : (j : ℂ) + 1 ≠ 0 := by
    rw [← Nat.cast_succ]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  simp only [dividedTranslation,
    LinearMap.smul_apply, map_smul, pow_succ', Module.End.mul_apply, smul_smul]
  congr 1
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [hfac, hj]

private theorem raises_lower_weight (x : Fock) (h : ℤ) (hx : L 0 x = (h : ℂ) • x) :
    L 0 (L 1 x) = ((h - 1 : ℤ) : ℂ) • L 1 x := by
  have hw := LinearMap.congr_fun (BcGhostVirasoro.virasoro 0 1) x
  norm_num [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, hx] at hw
  rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul]
  exact (sub_eq_iff_eq_add.mp hw).trans (by abel)

private theorem divided_weight (u : Fock) (h : ℤ) (hu : L 0 u = (h : ℂ) • u) (r : ℕ) :
    L 0 (D r u) = ((h - r : ℤ) : ℂ) • D r u := by
  have hp : ∀ r : ℕ, L 0 ((L 1 ^ r) u) = ((h - r : ℤ) : ℂ) • (L 1 ^ r) u := by
    intro r
    induction r with
    | zero => simpa using hu
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, show h - (r + 1 : ℕ) = h - r - 1 by omega]
        exact raises_lower_weight _ _ ih
  simp only [dividedTranslation,
    LinearMap.smul_apply, map_smul, hp, smul_comm ((r.factorial : ℂ)⁻¹)]

private def tripleSum (j : ℕ) (f : ℕ → ℕ → ℕ → Fock) : Fock :=
  ∑ a ∈ antidiagonal j, ∑ b ∈ antidiagonal a.1,
    f b.1 b.2 a.2

private theorem tripleSum_raise_first (j : ℕ) (f : ℕ → ℕ → ℕ → Fock)
    (h : ∀ s t, f 0 s t = 0) :
    tripleSum (j + 1) f = tripleSum j (fun r s t => f (r + 1) s t) := by
  unfold tripleSum
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h, zero_add]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.Nat.sum_antidiagonal_succ, h, zero_add]

private theorem tripleSum_raise_second (j : ℕ) (f : ℕ → ℕ → ℕ → Fock)
    (h : ∀ r t, f r 0 t = 0) :
    tripleSum (j + 1) f = tripleSum j (fun r s t => f r (s + 1) t) := by
  unfold tripleSum
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, h, zero_add]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.Nat.sum_antidiagonal_succ', h, zero_add]

private theorem tripleSum_raise_third (j : ℕ) (f : ℕ → ℕ → ℕ → Fock)
    (h : ∀ r s, f r s 0 = 0) :
    tripleSum (j + 1) f = tripleSum j (fun r s t => f r s (t + 1)) := by
  unfold tripleSum
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [h, Finset.sum_const_zero, zero_add]

private theorem tripleSum_add (j : ℕ) (f g : ℕ → ℕ → ℕ → Fock) :
    tripleSum j (fun r s t => f r s t + g r s t) = tripleSum j f + tripleSum j g := by
  simp only [tripleSum, Finset.sum_add_distrib]

private theorem tripleSum_map (j : ℕ) (A : Module.End ℂ Fock) (f : ℕ → ℕ → ℕ → Fock) :
    A (tripleSum j f) = tripleSum j (fun r s t => A (f r s t)) := by
  simp only [tripleSum, map_sum]

private def predecessor (C : ℤ) (r t : ℕ) : ℂ :=
  match t with
  | 0 => 0
  | k + 1 => ((C - r - k : ℤ) : ℂ) * integerBinomial C k

private theorem successor_coefficient (C : ℤ) (r s t : ℕ) :
    (r : ℂ) * integerBinomial (C + 1) t + (s : ℂ) * integerBinomial C t +
      predecessor C r t = ((r : ℂ) + s + t) * integerBinomial C t := by
  have cast_choose (x : ℤ) (k : ℕ) : integerBinomial x k = Ring.choose (x : ℂ) k :=
    Ring.map_choose (Int.castRingHom ℂ) x k
  cases t with
  | zero => simp [predecessor, integerBinomial]
  | succ t =>
      rw [predecessor]
      simp only [cast_choose, Int.cast_add, Int.cast_one, Int.cast_sub, Int.cast_natCast,
        Nat.cast_succ, Ring.choose_succ_succ]
      have h := D5.S3.VertexAlgebra.Analysis.IntegerNewton.choose_succ_mul (C : ℂ) t
      linear_combination -h

/-- Divided powers of the actual ghost L(1) on every integer state-field mode.
The outer antidiagonal splits the order into r+s and t. The inner one splits r+s. -/
theorem dividedL1_mode_product (u v : Fock) (h m : ℤ) (j : ℕ)
    (hu : L 0 u = (h : ℂ) • u) :
    D j (((Y u)[[m]]) v) =
      ∑ a ∈ antidiagonal j, ∑ b ∈ antidiagonal a.1,
        integerBinomial (2 * h - m - (b.1 : ℤ) - 2) a.2 •
          ((Y (D b.1 u))[[m + (a.2 : ℤ)]]) (D b.2 v) := by
  let C := fun r : ℕ => 2 * h - m - (r : ℤ) - 2
  let value := fun r s t : ℕ => mode (D r u) (m + t) (D s v)
  let summand := fun r s t => integerBinomial (C r) t • value r s t
  change D j (mode u m v) = tripleSum j summand
  induction j with
  | zero =>
      simp [tripleSum, summand, value, divided_zero, integerBinomial]
  | succ j ih =>
      have hj : (j + 1 : ℂ) ≠ 0 := by
        rw [← Nat.cast_succ]
        exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
      apply smul_right_injective Fock hj
      change (j + 1 : ℂ) • D (j + 1) (mode u m v) = (j + 1 : ℂ) • tripleSum (j + 1) summand
      rw [← raise_divided, ih, tripleSum_map]
      let first := fun r s t : ℕ => ((r : ℂ) * integerBinomial (C r + 1) t) • value r s t
      let second := fun r s t : ℕ => ((s : ℂ) * integerBinomial (C r) t) • value r s t
      let third := fun r s t => predecessor (C r) r t • value r s t
      have step (r s t : ℕ) :
          L 1 (summand r s t) =
            first (r + 1) s t + second r (s + 1) t + third r s (t + 1) := by
        have hc := L1_mode_commutator (D r u) (D s v) (h - r) (m + t)
          (divided_weight u h hu r)
        change L 1 (value r s t) - mode (D r u) (m + t) (L 1 (D s v)) =
          mode (L 1 (D r u)) (m + t) (D s v) +
            ((2 * (h - r) - (m + t) - 2 : ℤ) : ℂ) •
              mode (D r u) (m + t + 1) (D s v) at hc
        rw [sub_eq_iff_eq_add] at hc
        have hC : C (r + 1) + 1 = C r := by dsimp [C]; omega
        have hshift : 2 * (h - r) - (m + t) - 2 = C r - r - t := by dsimp [C]; omega
        change L 1 (integerBinomial (C r) t • value r s t) = _
        rw [map_smul, hc, raise_divided r, raise_divided s, hshift]
        simp only [first, second, third, predecessor, hC, value, mode, map_smul,
          LinearMap.smul_apply, smul_add, smul_smul, Nat.cast_succ]
        rw [show m + ((t : ℤ) + 1) = m + t + 1 by omega]
        rw [mul_comm (integerBinomial (C r) t) ((r : ℂ) + 1),
          mul_comm (integerBinomial (C r) t) ((s : ℂ) + 1),
          mul_comm (integerBinomial (C r) t) (((C r - r - t : ℤ) : ℂ))]
        abel
      simp_rw [step]
      rw [tripleSum_add, tripleSum_add, ← tripleSum_raise_first j first (by simp [first]),
        ← tripleSum_raise_second j second (by simp [second]),
        ← tripleSum_raise_third j third (by simp [third, predecessor]),
        ← tripleSum_add, ← tripleSum_add]
      unfold tripleSum
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have ha' : a.1 + a.2 = j + 1 := mem_antidiagonal.mp ha
      have hb' : b.1 + b.2 = a.1 := mem_antidiagonal.mp hb
      have indices : (b.1 : ℂ) + b.2 + a.2 = (j : ℂ) + 1 := by
        exact_mod_cast (show b.1 + b.2 + a.2 = j + 1 by omega)
      change ((b.1 : ℂ) * integerBinomial (C b.1 + 1) a.2) • value b.1 b.2 a.2 +
        ((b.2 : ℂ) * integerBinomial (C b.1) a.2) • value b.1 b.2 a.2 +
        predecessor (C b.1) b.1 a.2 • value b.1 b.2 a.2 = _
      rw [← add_smul, ← add_smul, successor_coefficient, indices]
      exact (smul_smul ..).symm

#print axioms dividedL1_mode_product

end D5.S3.Quantum.Fermionic.BcGhostDividedL1

/- GID: D5/S3/Matrix/QubitProductOperators
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local matrix actions on the Hilbert space of finite qubit configurations. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Omega original.

Local matrix actions on the Hilbert space of finite qubit configurations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped InnerProductSpace BigOperators Matrix

namespace Omega.QubitProduct

abbrev Configuration := Finset ℕ
abbrev Carrier := lp (fun _ : Configuration => ℂ) 2
abbrev Operator := Carrier →L[ℂ] Carrier

def bit (k : ℕ) (S : Configuration) : Bool := decide (k ∈ S)

def toggle (k : ℕ) (S : Configuration) : Configuration :=
  if k ∈ S then S.erase k else insert k S

@[simp] theorem bit_toggle (k : ℕ) (S : Configuration) :
    bit k (toggle k S) = !bit k S := by
  by_cases h : k ∈ S <;> simp [toggle, bit, h]

@[simp] theorem toggle_toggle (k : ℕ) (S : Configuration) :
    toggle k (toggle k S) = S := by
  by_cases h : k ∈ S <;> simp [toggle, h]

theorem bit_toggle_of_ne {j k : ℕ} (h : j ≠ k) (S : Configuration) :
    bit j (toggle k S) = bit j S := by
  by_cases hk : k ∈ S <;> simp [bit, toggle, hk, h]

theorem toggle_comm {j k : ℕ} (h : j ≠ k) (S : Configuration) :
    toggle j (toggle k S) = toggle k (toggle j S) := by
  ext i
  have hmem (a : ℕ) (T : Configuration) :
      i ∈ toggle a T ↔ if i = a then i ∉ T else i ∈ T := by
    by_cases ha : i = a <;> by_cases hm : a ∈ T <;> simp [toggle, ha, hm]
  simp only [hmem]
  rcases eq_or_ne i j with rfl | hij <;> rcases eq_or_ne i k with heq | hik
  · exact (h heq).elim
  · simp [hik]
  · simp [hij]
  · simp [hij, hik]

def toggleEquiv (k : ℕ) : Configuration ≃ Configuration where
  toFun := toggle k
  invFun := toggle k
  left_inv := toggle_toggle k
  right_inv := toggle_toggle k

def basisVector (S : Configuration) : Carrier := lp.single 2 S 1

@[simp] theorem basisVector_apply (S T : Configuration) :
    basisVector S T = if S = T then 1 else 0 := by
  by_cases h : S = T
  · subst T; simp [basisVector]
  · simp [basisVector, h]

@[simp] theorem norm_basisVector (S : Configuration) : ‖basisVector S‖ = 1 := by
  simp [basisVector, lp.norm_single]

@[simp] theorem inner_basisVector_left (S : Configuration) (x : Carrier) :
    ⟪basisVector S, x⟫_ℂ = x S := by
  simp [basisVector, lp.inner_single_left, RCLike.inner_apply]

theorem operator_ext {P Q : Operator}
    (h : ∀ S, P (basisVector S) = Q (basisVector S)) : P = Q := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro S
  apply ContinuousLinearMap.ext
  intro z
  have hz : lp.single 2 S z = z • basisVector S := by
    rw [basisVector, ← lp.single_smul, smul_eq_mul, mul_one]
  simpa [ContinuousLinearMap.comp_apply, hz, map_smul] using congrArg (z • ·) (h S)

private theorem lp_two_pos : 0 < (2 : ENNReal).toReal := by norm_num

private theorem weight_mem (e : Configuration ≃ Configuration) (f : Configuration → ℂ)
    (B : ℝ) (hB : ∀ S, ‖f S‖ ≤ B) (x : Carrier) :
    Memℓp (fun S => f S * x (e S)) 2 := by
  apply memℓp_gen
  have hx := (lp.memℓp x).summable lp_two_pos
  have hb : Summable (fun S => B ^ (2 : ENNReal).toReal * ‖x (e S)‖ ^ (2 : ENNReal).toReal) :=
    (e.summable_iff.mpr hx).mul_left _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hb
  intro S
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  gcongr
  exact hB S

set_option maxHeartbeats 800000 in
private def weighted (e : Configuration ≃ Configuration) (f : Configuration → ℂ)
    (B : ℝ) (hB : ∀ S, ‖f S‖ ≤ B) : Operator :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun S => f S * x (e S), weight_mem e f B hB x⟩
      map_add' := fun x y => lp.ext (by funext S; exact mul_add ..)
      map_smul' := fun c x => lp.ext (by funext S; simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring) }
    B (fun x => by
      apply lp.norm_le_of_tsum_le lp_two_pos (mul_nonneg ((norm_nonneg _).trans (hB ∅)) (norm_nonneg _))
      simp only [Real.mul_rpow ((norm_nonneg _).trans (hB ∅)) (norm_nonneg _)]
      rw [lp.norm_rpow_eq_tsum lp_two_pos]
      let p := (2 : ENNReal).toReal
      change (∑' S, ‖f S * x (e S)‖ ^ p) ≤ B ^ p * (∑' S, ‖x S‖ ^ p)
      calc
        _ ≤ ∑' S, B ^ p * ‖x (e S)‖ ^ p := by
          apply Summable.tsum_le_tsum
          · intro S
            rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
            gcongr
            exact hB S
          · exact (weight_mem e f B hB x).summable lp_two_pos
          · have hx : Summable (fun S => ‖x (e S)‖ ^ p) :=
              e.summable_iff.mpr ((lp.memℓp x).summable lp_two_pos)
            exact hx.mul_left _
        _ = _ := by
          rw [tsum_mul_left]
          exact congrArg (B ^ p * ·) (e.tsum_eq (fun S => ‖x S‖ ^ p)))


private def entryBound (A : Matrix Bool Bool ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

private theorem norm_entry_le (A : Matrix Bool Bool ℂ) (i j : Bool) :
    ‖A i j‖ ≤ entryBound A :=
  (Finset.single_le_sum (f := fun b => ‖A i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.mem_univ i))

/-- A local matrix acts on the indicated qubit, leaving all other bits fixed. -/
def localAction (k : ℕ) (A : Matrix Bool Bool ℂ) : Operator :=
  weighted (Equiv.refl _) (fun S => A (bit k S) (bit k S)) (entryBound A)
    (fun _ => norm_entry_le _ _ _) +
  weighted (toggleEquiv k) (fun S => A (bit k S) (!bit k S)) (entryBound A)
    (fun _ => norm_entry_le _ _ _)

@[simp] theorem localAction_apply (k : ℕ) (A : Matrix Bool Bool ℂ) (x : Carrier)
    (S : Configuration) :
    localAction k A x S =
      A (bit k S) (bit k S) * x S + A (bit k S) (!bit k S) * x (toggle k S) := rfl

@[simp] theorem localAction_one (k : ℕ) : localAction k 1 = 1 := by
  ext x : 1
  apply lp.ext
  funext S
  cases h : bit k S <;> simp [h, one_apply_eq_self]

theorem localAction_mul (k : ℕ) (A B : Matrix Bool Bool ℂ) :
    localAction k (A * B) = localAction k A * localAction k B := by
  ext x : 1
  apply lp.ext
  funext S
  rw [mul_apply_eq_comp]
  simp only [localAction_apply, bit_toggle, Bool.not_not, toggle_toggle, Matrix.mul_apply,
    Fintype.sum_bool]
  cases bit k S <;> simp <;> ring

theorem localAction_comm {j k : ℕ} (h : j ≠ k) (A B : Matrix Bool Bool ℂ) :
    Commute (localAction j A) (localAction k B) := by
  show localAction j A * localAction k B = localAction k B * localAction j A
  ext x : 1
  apply lp.ext
  funext S
  simp only [mul_apply_eq_comp, localAction_apply,
    bit_toggle_of_ne h, bit_toggle_of_ne h.symm, toggle_comm h]
  ring

private theorem toggle_ne (k : ℕ) (S : Configuration) : toggle k S ≠ S := by
  intro h
  have he := bit_toggle k S
  rw [h] at he
  cases bit k S <;> simp at he

theorem localAction_star (k : ℕ) (A : Matrix Bool Bool ℂ) :
    localAction k (star A) = star (localAction k A) := by
  apply operator_ext
  intro S
  apply lp.ext
  funext T
  change localAction k (star A) (basisVector S) T = (star (localAction k A)) (basisVector S) T
  rw [← inner_basisVector_left T ((star (localAction k A)) (basisVector S))]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ← inner_conj_symm, inner_basisVector_left]
  simp only [localAction_apply, basisVector_apply, Matrix.star_apply]
  by_cases hST : S = T
  · subst T
    simp [Ne.symm (toggle_ne k S)]
  · by_cases ht : toggle k S = T
    · subst T
      simp [Ne.symm (toggle_ne k S), toggle_ne]
    · have hs : toggle k T ≠ S := by
        intro he
        apply ht
        rw [← he, toggle_toggle]
      simp [hST, Ne.symm hST, Ne.symm ht, Ne.symm hs]

/-- The unital star representation of a single site. -/
def siteRep (k : ℕ) : Matrix Bool Bool ℂ →⋆ₐ[ℂ] Operator where
  toFun := localAction k
  map_zero' := by
    ext x : 1
    apply lp.ext
    funext S
    simp
  map_one' := localAction_one k
  map_mul' := localAction_mul k
  map_add' A B := by
    ext x : 1
    apply lp.ext
    funext S
    simp [add_mul]
    ring
  commutes' z := by
    ext x : 1
    apply lp.ext
    funext S
    cases h : bit k S <;> simp [h, Algebra.algebraMap_eq_smul_one,
      one_apply_eq_self, lp.coeFn_smul]
  map_star' := localAction_star k

section Blocks

/-- Ordered products from a finite interval of sites, applying the lowest site first. -/
def block {R : Type*} [Monoid R] (f : ℕ → R) (s : ℕ) : ℕ → R
  | 0 => 1
  | n + 1 => f (s + n) * block f s n

@[simp] theorem block_zero {R : Type*} [Monoid R] (f : ℕ → R) (s : ℕ) :
    block f s 0 = 1 := rfl

theorem block_succ {R : Type*} [Monoid R] (f : ℕ → R) (s n : ℕ) :
    block f s (n + 1) = f (s + n) * block f s n := rfl

theorem block_add {R : Type*} [Monoid R] (f : ℕ → R) (s n m : ℕ) :
    block f s (n + m) = block f (s + n) m * block f s n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.add_succ, block_succ, block_succ, ← Nat.add_assoc, ih, mul_assoc]

theorem map_block {R T : Type*} [Monoid R] [Monoid T] {F : Type*}
    [FunLike F R T] [MonoidHomClass F R T] (g : F) (f : ℕ → R) (s n : ℕ) :
    g (block f s n) = block (fun k => g (f k)) s n := by
  induction n with
  | zero => simp
  | succ n ih => rw [block_succ, block_succ, map_mul, ih]

theorem localAction_commute_block {k s n : ℕ}
    (h : k < s ∨ s + n ≤ k) (A : Matrix Bool Bool ℂ) (f : ℕ → Matrix Bool Bool ℂ) :
    Commute (localAction k A) (block (fun j => localAction j (f j)) s n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [block_succ]
      apply Commute.mul_right (localAction_comm (by omega) _ _) (ih (by omega))

theorem block_off {k s n : ℕ} (hk : k < s ∨ s + n ≤ k)
    (f : ℕ → Matrix Bool Bool ℂ) (S T : Configuration) (h : bit k S ≠ bit k T) :
    block (fun j => localAction j (f j)) s n (basisVector S) T = 0 := by
  induction n generalizing T with
  | zero =>
    have hne : S ≠ T := fun he => h (congrArg (bit k) he)
    simp [one_apply_eq_self, hne]
  | succ n ih =>
      have hne : k ≠ s + n := by omega
      have h' : bit k S ≠ bit k (toggle (s + n) T) := by
        rw [bit_toggle_of_ne hne]
        exact h
      rw [block_succ, mul_apply_eq_comp, localAction_apply, ih (by omega) T h,
        ih (by omega) _ h']
      simp

theorem block_diag (f : ℕ → Matrix Bool Bool ℂ) (s n : ℕ) (S : Configuration) :
    block (fun j => localAction j (f j)) s n (basisVector S) S =
      ∏ j ∈ Finset.range n, f (s + j) (bit (s + j) S) (bit (s + j) S) := by
  induction n with
  | zero => simp [one_apply_eq_self]
  | succ n ih =>
      have hne : bit (s + n) S ≠ bit (s + n) (toggle (s + n) S) := by
        rw [bit_toggle]
        cases bit (s + n) S <;> decide
      rw [block_succ, mul_apply_eq_comp, localAction_apply, ih, block_off (Or.inr le_rfl) f _ _ hne,
        Finset.prod_range_succ]
      ring

/-- The computational vacuum projector on one qubit. -/
def vacuumMatrix : Matrix Bool Bool ℂ :=
  fun i j => if i = false ∧ j = false then 1 else 0

@[simp] theorem vacuumMatrix_star : star vacuumMatrix = vacuumMatrix := by
  ext i j
  cases i <;> cases j <;> simp [vacuumMatrix, Matrix.star_apply]

@[simp] theorem vacuumMatrix_mul : vacuumMatrix * vacuumMatrix = vacuumMatrix := by
  ext i j
  cases i <;> cases j <;> simp [vacuumMatrix, Matrix.mul_apply]

@[simp] theorem localAction_vacuum (k : ℕ) (x : Carrier) (S : Configuration) :
    localAction k vacuumMatrix x S = if bit k S then 0 else x S := by
  cases h : bit k S <;> simp [vacuumMatrix, h]

@[simp] theorem vacuum_fixed (k : ℕ) :
    localAction k vacuumMatrix (basisVector ∅) = basisVector ∅ := by
  apply lp.ext
  funext S
  rw [localAction_vacuum, basisVector_apply]
  by_cases h : S = ∅
  · simp [h, bit]
  · simp [Ne.symm h]

/-- The bit flip on one qubit. -/
def flipMatrix : Matrix Bool Bool ℂ := fun i j => if i = j then 0 else 1

@[simp] theorem localAction_flip (k : ℕ) (x : Carrier) (S : Configuration) :
    localAction k flipMatrix x S = x (toggle k S) := by
  cases h : bit k S <;> simp [flipMatrix, h]

@[simp] theorem flip_basis (k : ℕ) (S : Configuration) :
    localAction k flipMatrix (basisVector S) = basisVector (toggle k S) := by
  apply lp.ext
  funext T
  rw [localAction_flip, basisVector_apply, basisVector_apply]
  have h : S = toggle k T ↔ toggle k S = T :=
    ⟨fun he => by rw [he, toggle_toggle], fun he => by rw [← he, toggle_toggle]⟩
  simp [h]

/-- A phase-aligned qubit change of basis with overlap `r`. -/
def rotation (r : ℝ) : Matrix Bool Bool ℂ := fun i j =>
  if i = j then (r : ℂ) else
    if i then (-Real.sqrt (1 - r ^ 2) : ℝ) else Real.sqrt (1 - r ^ 2)

@[simp] theorem rotation_diag (r : ℝ) (i : Bool) : rotation r i i = r := by
  simp [rotation]

@[simp] theorem rotation_star_diag (r : ℝ) (i : Bool) : star (rotation r) i i = r := by
  simp [Matrix.star_apply]

@[simp] theorem rotation_one : rotation 1 = 1 := by
  ext i j
  cases i <;> cases j <;> norm_num [rotation]

theorem rotation_unitary (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    rotation r ∈ unitary (Matrix Bool Bool ℂ) := by
  have hnon : 0 ≤ 1 - r ^ 2 := by nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
  have hsq := Real.sq_sqrt hnon
  refine ⟨?_, ?_⟩ <;> ext i j <;> cases i <;> cases j <;>
    simp [rotation, Matrix.mul_apply, Matrix.star_apply, ← Complex.ofReal_mul, ← Complex.ofReal_add] <;>
    first | nlinarith only [hsq] | ring

theorem conjugate_vacuum_diag (r : ℝ) (b : Bool) :
    (rotation r * vacuumMatrix * star (rotation r)) b b =
      if b then ((Real.sqrt (1 - r ^ 2) ^ 2 : ℝ) : ℂ) else ((r ^ 2 : ℝ) : ℂ) := by
  cases b <;> simp [rotation, vacuumMatrix, Matrix.mul_apply, Matrix.star_apply, pow_two]

end Blocks

end Omega.QubitProduct

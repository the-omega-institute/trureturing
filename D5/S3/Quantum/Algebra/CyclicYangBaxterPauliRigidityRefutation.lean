/- GID: D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.claim; result=D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.result; claim=D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.claim
   digest: A mixed-sign Gaussian at d = 15 refutes Galindo--Rowell Conjecture 10.6. -/

/-
proof_shape: result: content
escape_witness: form (2): result itself, produced on its live proof path by the Weyl
  commutation bridge, the coefficient-to-braid bridge and the exponent-translation identity
  (the non-binding facts preregistered in #11573, kept as local steps of result)
admission_basis: open-problem-resolution (#11573; Refuted)
Frozen dependencies (direct unless marked transitive):
  D5/S3/Observer/WindowRegister.shiftMatrix — statement_id sha256:821649848ffe7ed9f84f11b97d3d1eb176216ccb5d3910dcbd867105b9d070dd
  D5/S3/Observer/WindowRegister.shiftMatrix_pow_card (transitive, through shiftMatrix_pow_mod) — statement_id sha256:7a3fbd68d9cbc561393327c7d3ea830003b79cba0759c1d85b75ed0aa3737f9e
  D5/S3/Observer/WindowRegister.shiftPerm — statement_id sha256:d089316b1edad69647319d26c3a88b94634c9feaa15ca92ee0bb373dbbd98f83
  D5/S3/Observer/WindowRegister.shiftMatrix_eq_permMatrix — statement_id sha256:3c36c8ef2f8c32a3bdfc77ed9e5a8357e39b23d6df504cd7c4eadd09ab8aafe8
  D5/S3/Observer/WindowRegister.shiftPerm_pow_apply — statement_id sha256:4225ef06cfc6c92dcfd365ecab7b7738db3951b60684425b597af4598e55e2c3
  D5/S3/Quantum/Algebra/WeylDisplacement.shiftMatrix_pow_mod — statement_id sha256:b4d0f93d7ee8ce9da41babb74f152cddacbebd8bbf4e242eaf6fbb084946e55d
  D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.star_shiftMatrix_pow — statement_id sha256:b765f26ec50c04332e4ab648f44479241fadf3d6c764ee6a3fa8e0060474014a
Registration is paused under CLAUDE.md §3.9 (信息逃逸登记暂缓).
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import D5.S3.Observer.WindowRegister
import D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

open scoped BigOperators Kronecker
open Matrix
open D5.S3.Observer.WindowRegister

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Algebra.CyclicYangBaxterPauliRigidityRefutation

/-- Rows are output indices and columns are input indices. -/
def clockZ (w : ℂ) (d : ℕ) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.diagonal fun j => w ^ j.val

def P {d : ℕ} [NeZero d] (w : ℂ) (α : (ZMod d)ˣ) :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  D5.S3.Observer.WindowRegister.shiftMatrix d ⊗ₖ
    (clockZ w d ^ (α : ZMod d).val)

def R {d : ℕ} [NeZero d] (w : ℂ) (α : (ZMod d)ˣ) (a : ZMod d → ℂ) :=
  ∑ t : ZMod d, a t • P w α ^ t.val

/-- Both operators use `i × (j × k)`. `prodAssoc` sends `((i,j),k)`
to `(i,(j,k))`, so the first operator acts on sites 1,2 and the second
on sites 2,3, as in the paper's braid equation. -/
private def leftTensor {d : ℕ} [NeZero d]
    (r : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :=
  Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
    (r ⊗ₖ (1 : Matrix (ZMod d) (ZMod d) ℂ))

private def rightTensor {d : ℕ} [NeZero d]
    (r : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :=
  (1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ r

def BraidYBE {d : ℕ} [NeZero d]
    (r : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) : Prop :=
  leftTensor r * rightTensor r * leftTensor r =
    rightTensor r * leftTensor r * rightTensor r

def ProjectivelyUnitary {d : ℕ} [NeZero d]
    (r : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ c • r ∈ Matrix.unitaryGroup _ ℂ

def claim : Prop := ∀ d : ℕ, ∀ hd : 2 ≤ d, ¬ 4 ∣ d →
  letI : NeZero d := ⟨by omega⟩
  ∀ w : ℂ, IsPrimitiveRoot w d → ∀ α : (ZMod d)ˣ, ∀ a : ZMod d → ℂ,
    a 0 = 1 → (∀ t, ‖a t‖ = 1) → BraidYBE (R w α a) →
    ProjectivelyUnitary (R w α a) →
    ∃ ε : ZMod d, (ε = 1 ∨ ε = -1) ∧
      ∀ s t, a (s+t) = a s * a t * w ^ (ε * (α : ZMod d) * s * t).val

private abbrev D := ZMod 15
private abbrev M := Matrix D D ℂ
private abbrev M2 := Matrix (D × D) (D × D) ℂ
private abbrev M3 := Matrix (D × (D × D)) (D × (D × D)) ℂ

private def C (w : ℂ) (hw : IsPrimitiveRoot w 15) (u : D) : M :=
  Matrix.diagonal fun j => (AddChar.zmodChar 15 hw.pow_eq_one) (u*j)
private def T (w : ℂ) (hw : IsPrimitiveRoot w 15) (u : D) : M2 :=
  (shiftMatrix 15 ^ u.val) ⊗ₖ C w hw u

private def A (w : ℂ) (hw : IsPrimitiveRoot w 15) (u : D) : M3 :=
  (shiftMatrix 15 ^ u.val) ⊗ₖ (C w hw u ⊗ₖ (1 : M))

private def B (w : ℂ) (hw : IsPrimitiveRoot w 15) (u : D) : M3 :=
  (1 : M) ⊗ₖ ((shiftMatrix 15 ^ u.val) ⊗ₖ C w hw u)

private def gauss (w : ℂ) (hw : IsPrimitiveRoot w 15) (t : D) : ℂ :=
  (AddChar.zmodChar 15 hw.pow_eq_one) (2*t*t)

theorem result : ¬ claim := by
  have S_add (u v : D) :
      shiftMatrix 15 ^ (u+v).val = shiftMatrix 15 ^ u.val * shiftMatrix 15 ^ v.val := by
    rw [ZMod.val_add, D5.S3.Quantum.Algebra.WeylDisplacement.shiftMatrix_pow_mod, pow_add]
  have shift_pow_apply (n : ℕ) (r s : D) :
      (shiftMatrix 15 ^ n) r s = if r - s = (n : D) then 1 else 0 := by
    have hPower : shiftMatrix 15 ^ n = (shiftPerm 15 ^ n).permMatrix ℂ := by
      rw [shiftMatrix_eq_permMatrix]
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, ih, ← Matrix.permMatrix_mul, pow_succ']
    rw [hPower]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, shiftPerm_pow_apply]
    congr 1
    apply propext
    simp only [Option.some.injEq]
    constructor <;> intro h <;> linear_combination h
  have C_S (w : ℂ) (hw : IsPrimitiveRoot w 15) (u v : D) :
      C w hw u * (shiftMatrix 15 ^ v.val) =
        (AddChar.zmodChar 15 hw.pow_eq_one) (u*v) •
          ((shiftMatrix 15 ^ v.val) * C w hw u) := by
    ext i j
    simp only [C, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      smul_eq_mul, shift_pow_apply]
    by_cases h : i = j+v
    · subst i
      simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
      rw [show u * (v + j) = u*v + u*j by ring, AddChar.map_add_eq_mul]
    · have h' : i - j ≠ v := by
        intro hdiff
        apply h
        rw [sub_eq_iff_eq_add] at hdiff
        simpa [add_comm] using hdiff
      simp [h']
  have T_pow (w : ℂ) (hw : IsPrimitiveRoot w 15) (n : ℕ) : T w hw (n : D) = P w (1 : Dˣ) ^ n := by
    induction n with
    | zero =>
      have hSzero : shiftMatrix 15 ^ (0 : D).val = 1 := by simp
      have hCzero : C w hw 0 = 1 := by
        ext i j
        simp [C, Matrix.diagonal, Matrix.one_apply]
      simp [T, hSzero, hCzero]
    | succ n ih =>
      have hT (u v : D) : T w hw (u+v) = T w hw u * T w hw v := by
        have hCadd : C w hw (u+v) = C w hw u * C w hw v := by
          rw [C, C, C, Matrix.diagonal_mul_diagonal]
          congr 1
          funext j
          simp [add_mul, AddChar.map_add_eq_mul]
        simp only [T, S_add, hCadd, Matrix.mul_kronecker_mul]
      rw [Nat.cast_add, Nat.cast_one, hT, ih, pow_succ]
      congr 1
      unfold T P
      rw [Units.val_one, show (1 : D).val = 1 by decide, pow_one]
      congr 1
      ext i j
      simp [C, clockZ, AddChar.zmodChar_apply]
  have A_B (w : ℂ) (hw : IsPrimitiveRoot w 15) (u v : D) :
      A w hw u * B w hw v = (AddChar.zmodChar 15 hw.pow_eq_one) (u*v) • (B w hw v * A w hw u) := by
    simp only [A, B, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    rw [C_S, Matrix.smul_kronecker, Matrix.kronecker_smul]
  have gauss_coefficient (w : ℂ) (hw : IsPrimitiveRoot w 15) (s t : D) :
      gauss w hw t * ∑ c, gauss w hw (s-c) * gauss w hw c * (AddChar.zmodChar 15 hw.pow_eq_one) (-(c*t)) =
      gauss w hw s * ∑ c, gauss w hw c * gauss w hw (t-c) * (AddChar.zmodChar 15 hw.pow_eq_one) (-(s*c)) := by
    simp only [Finset.mul_sum, gauss, ← AddChar.map_add_eq_mul]
    apply Fintype.sum_equiv (Equiv.addRight (6*(t-s)))
    intro c
    congr 1
    have htranslation :
        2*t*t + 2*(s-c)*(s-c) + 2*c*c - c*t =
          2*s*s + 2*(c+6*(t-s))*(c+6*(t-s)) +
            2*(t-(c+6*(t-s)))*(t-(c+6*(t-s))) - s*(c+6*(t-s)) := by
      ring_nf
      simp only [show (270 : D) = 0 by decide, show (44 : D) = 14 by decide,
        show (122 : D) = 2 by decide, show (49 : D) = 4 by decide,
        show (152 : D) = 2 by decide, mul_zero]
      have h14 : (14 : D) = -1 := by decide
      rw [h14]
      ring
    change 2*t*t + (2*(s-c)*(s-c) + 2*c*c + -(c*t)) =
      2*s*s + (2*(c+6*(t-s))*(c+6*(t-s)) +
      2*(t-(c+6*(t-s)))*(t-(c+6*(t-s))) + -(s*(c+6*(t-s))))
    simpa only [sub_eq_add_neg, add_assoc] using htranslation
  have normal_left (w : ℂ) (hw : IsPrimitiveRoot w 15) (x y z : D) :
      A w hw x * B w hw y * A w hw z =
      (AddChar.zmodChar 15 hw.pow_eq_one) (-(z*y)) • (A w hw (x+z) * B w hw y) := by
    have hBA : B w hw y * A w hw z =
        (AddChar.zmodChar 15 hw.pow_eq_one) (-(z*y)) • (A w hw z * B w hw y) := by
      rw [A_B, smul_smul, ← AddChar.map_add_eq_mul]
      simp
    have hAadd : A w hw (x+z) = A w hw x * A w hw z := by
      have hCadd : C w hw (x+z) = C w hw x * C w hw z := by
        rw [C, C, C, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        simp [add_mul, AddChar.map_add_eq_mul]
      simp only [A, ← Matrix.mul_kronecker_mul, one_mul, ← S_add, ← hCadd]
    rw [mul_assoc, hBA, mul_smul_comm, ← mul_assoc, ← hAadd]
  have normal_right (w : ℂ) (hw : IsPrimitiveRoot w 15) (x y z : D) :
      B w hw x * A w hw y * B w hw z =
      (AddChar.zmodChar 15 hw.pow_eq_one) (-(y*x)) • (A w hw y * B w hw (x+z)) := by
    have hBA : B w hw x * A w hw y =
        (AddChar.zmodChar 15 hw.pow_eq_one) (-(y*x)) • (A w hw y * B w hw x) := by
      rw [A_B, smul_smul, ← AddChar.map_add_eq_mul]
      simp
    have hBadd : B w hw (x+z) = B w hw x * B w hw z := by
      have hCadd : C w hw (x+z) = C w hw x * C w hw z := by
        rw [C, C, C, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        simp [add_mul, AddChar.map_add_eq_mul]
      simp only [B, ← Matrix.mul_kronecker_mul, one_mul, ← S_add, ← hCadd]
    rw [hBA, smul_mul_assoc, mul_assoc, ← hBadd]
  have sum_pair {E : Type} [AddCommMonoid E] (f : D → D → E) :
      (∑ x, ∑ z, f x z) = ∑ s, ∑ c, f (s-c) c := by
    rw [Finset.sum_comm]
    calc
      (∑ c, ∑ x, f x c) = ∑ c, ∑ s, f (s-c) c := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (Equiv.subRight c).sum_comp (fun x => f x c) |>.symm
      _ = _ := Finset.sum_comm
  have sum_triple {E : Type} [AddCommMonoid E] (f : D → D → D → E) :
      (∑ x, ∑ y, ∑ z, f x y z) = ∑ s, ∑ t, ∑ c, f (s-c) t c := by
    calc
      _ = ∑ y, ∑ x, ∑ z, f x y z := Finset.sum_comm
      _ = ∑ y, ∑ s, ∑ c, f (s-c) y c := by
        apply Finset.sum_congr rfl
        intro y hy
        exact sum_pair (fun x z => f x y z)
      _ = _ := Finset.sum_comm
  have sum_triple_right {E : Type} [AddCommMonoid E] (f : D → D → D → E) :
      (∑ x, ∑ y, ∑ z, f x y z) = ∑ s, ∑ t, ∑ c, f c s (t-c) := by
    calc
      _ = ∑ y, ∑ z, ∑ x, f x y z := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        exact Finset.sum_comm
      _ = ∑ s, ∑ t, ∑ c, f c s (t-c) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact sum_pair (fun z x => f x s z)
  have coefficient_bridge (w : ℂ) (hw : IsPrimitiveRoot w 15) (a : D → ℂ)
      (h : ∀ s t, a t * ∑ c, a (s-c) * a c * (AddChar.zmodChar 15 hw.pow_eq_one) (-(c*t)) =
        a s * ∑ c, a c * a (t-c) * (AddChar.zmodChar 15 hw.pow_eq_one) (-(s*c))) :
      BraidYBE (R w (1 : Dˣ) a) := by
    have hR : R w (1 : Dˣ) a = ∑ t, a t • T w hw t := by
      unfold R
      apply Finset.sum_congr rfl
      intro t ht
      rw [← T_pow w hw t.val, ZMod.natCast_zmod_val]
    have hleft :
        leftTensor (R w (1 : Dˣ) a) = ∑ t, a t • A w hw t := by
      rw [hR]
      ext i j
      simp [leftTensor, A, T, Matrix.reindex, Matrix.submatrix,
        Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
        Finset.sum_mul, mul_assoc]
    have hright :
        rightTensor (R w (1 : Dˣ) a) = ∑ t, a t • B w hw t := by
      rw [hR]
      ext i j
      simp [rightTensor, B, T, Matrix.kroneckerMap_apply, Matrix.sum_apply,
        Matrix.smul_apply, Finset.mul_sum, mul_left_comm]
    unfold BraidYBE
    rw [hleft, hright]
    conv_lhs => rw [mul_assoc]
    conv_rhs => rw [mul_assoc]
    simp only [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
    simp_rw [normal_left w hw, normal_right w hw, smul_smul]
    conv_lhs => rw [sum_triple]
    conv_rhs => rw [sum_triple_right]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    have hcancel (c t : D) : c+(t-c)=t := by
      rw [add_comm c (t-c), sub_add_cancel]
    simp only [sub_add_cancel, hcancel, ← Finset.sum_smul]
    congr 1
    simp only [Finset.mul_sum] at h
    convert h s t using 1 <;>
      apply Finset.sum_congr rfl <;> intro c hc <;> ring
  have gauss_correlation (w : ℂ) (hw : IsPrimitiveRoot w 15) (u : D) :
      (∑ x, star (gauss w hw x) * gauss w hw (x+u)) =
        if u = 0 then (15 : ℂ) else 0 := by
    have hphase (x : D) : star (gauss w hw x) * gauss w hw (x+u) =
        (AddChar.zmodChar 15 hw.pow_eq_one) (2*u*u) * (AddChar.zmodChar 15 hw.pow_eq_one) (4*u*x) := by
      simp only [gauss, RCLike.star_def, ← AddChar.map_neg_eq_conj,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hphase]
    rw [← Finset.mul_sum]
    by_cases hu : u = 0
    · simp [hu]
    · have hn : (4 : D)*u ≠ 0 := by
        intro hh
        have hh' := congrArg (fun z : D => 4*z) hh
        have h16 : (16 : D) = 1 := by decide
        have : u = 0 := by simpa only [← mul_assoc, show (4:D)*4=16 by ring,
          h16, one_mul, mul_zero] using hh'
        exact hu this
      have hprimitive := AddChar.zmodChar_primitive_of_primitive_root 15 hw
      have hz := (AddChar.sum_eq_zero_iff_ne_zero (ψ := ((AddChar.zmodChar 15 hw.pow_eq_one)).mulShift (4*u))).mpr
        (hprimitive hn)
      simp only [AddChar.mulShift_apply] at hz
      simp [hu, hz]
  have sum_difference {E : Type} [AddCommMonoid E] (f : D → D → E) :
      (∑ x, ∑ y, f x y) = ∑ u, ∑ y, f (u+y) y := by
    rw [Finset.sum_comm]
    calc
      (∑ y, ∑ x, f x y) = ∑ y, ∑ u, f (u+y) y := by
        apply Finset.sum_congr rfl
        intro y hy
        symm
        exact Fintype.sum_equiv (Equiv.addRight y) _ _ (fun u => rfl)
      _ = _ := Finset.sum_comm
  have gauss_rrstar (w : ℂ) (hw : IsPrimitiveRoot w 15) :
      R w (1 : Dˣ) (gauss w hw) * (R w (1 : Dˣ) (gauss w hw))ᴴ =
        (15 : ℂ) • (1 : M2) := by
    have hR : R w (1 : Dˣ) (gauss w hw) =
        ∑ t, gauss w hw t • T w hw t := by
      unfold R
      apply Finset.sum_congr rfl
      intro t ht
      rw [← T_pow w hw t.val, ZMod.natCast_zmod_val]
    have hSstar (u : D) : (shiftMatrix 15 ^ u.val)ᴴ = shiftMatrix 15 ^ (-u).val := by
      simpa only [Matrix.star_eq_conjTranspose] using
        (D5.S3.Quantum.Algebra.WeylDisplacementAdjoint.star_shiftMatrix_pow
          (M := 15) u)
    have hCstar (u : D) : (C w hw u)ᴴ = C w hw (-u) := by
      rw [C, Matrix.diagonal_conjTranspose, C]
      congr 1
      funext j
      simp only [neg_mul]
      exact (AddChar.map_neg_eq_conj _ _).symm
    have hTstar (u : D) : (T w hw u)ᴴ = T w hw (-u) := by
      simp only [T, Matrix.conjTranspose_kronecker, hSstar, hCstar]
    rw [hR]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hTstar]
    simp only [Finset.sum_mul_sum]
    have hTadd (u v : D) : T w hw (u+v) = T w hw u * T w hw v := by
      have hCadd : C w hw (u+v) = C w hw u * C w hw v := by
        rw [C, C, C, Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        simp [add_mul, AddChar.map_add_eq_mul]
      simp only [T, S_add, hCadd, Matrix.mul_kronecker_mul]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← hTadd]
    rw [sum_difference]
    simp only [add_assoc, add_neg_cancel, add_zero, ← Finset.sum_smul]
    have hc (u : D) : (∑ y, star (gauss w hw y) * gauss w hw (u+y)) =
        if u = 0 then (15 : ℂ) else 0 := by
      simpa only [add_comm] using gauss_correlation w hw u
    simp_rw [hc]
    have hSzero : shiftMatrix 15 ^ (0 : D).val = 1 := by simp
    have hCzero : C w hw 0 = 1 := by
      ext i j
      simp [C, Matrix.diagonal, Matrix.one_apply]
    have hTzero : T w hw 0 = 1 := by simp [T, hSzero, hCzero]
    simp [hTzero]
  have gauss_unitary (w : ℂ) (hw : IsPrimitiveRoot w 15) : ProjectivelyUnitary (R w (1 : Dˣ) (gauss w hw)) := by
    let c : ℂ := ((Real.sqrt 15)⁻¹ : ℝ)
    have hs : (Real.sqrt 15)^2 = 15 := Real.sq_sqrt (by positivity)
    have hs0 : Real.sqrt 15 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    refine ⟨c, ?_, ?_⟩
    · dsimp only [c]
      exact_mod_cast inv_ne_zero hs0
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
        gauss_rrstar, smul_smul]
      have hcc : c * star c * 15 = 1 := by
        dsimp [c]
        simp only [Complex.conj_ofReal, ← Complex.ofReal_mul,
          ← Complex.ofReal_ofNat]
        apply congrArg Complex.ofReal
        rw [← pow_two, inv_pow, hs]
        norm_num
      rw [hcc, one_smul]
  have gauss_not_polarized (w : ℂ) (hw : IsPrimitiveRoot w 15) :
      ¬ ∃ ε : D, (ε = 1 ∨ ε = -1) ∧ ∀ s t,
        gauss w hw (s+t) = gauss w hw s * gauss w hw t * w ^ (ε*s*t).val := by
    rintro ⟨ε, hε, h⟩
    have h11 := h 1 1
    rcases hε with rfl | rfl
    · change w^8 = w^2 * w^2 * w^1 at h11
      have hp : w^8 = w^5 := by convert h11 using 1; ring
      have := hw.pow_inj (by norm_num : 8 < 15) (by norm_num : 5 < 15) hp
      omega
    · change w^8 = w^2 * w^2 * w^14 at h11
      have hp : w^8 = w^3 := by
        calc w^8 = w^18 := by convert h11 using 1; ring
             _ = w^3 := by rw [show 18 = 15+3 by omega, pow_add, hw.pow_eq_one, one_mul]
      have := hw.pow_inj (by norm_num : 8 < 15) (by norm_num : 3 < 15) hp
      omega
  intro h
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)
  have hw : IsPrimitiveRoot w 15 := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  have hzero : gauss w hw 0 = 1 := by simp [gauss]
  have hnorm (t : D) : ‖gauss w hw t‖ = 1 := AddChar.norm_apply _ _
  have hybe : BraidYBE (R w (1 : Dˣ) (gauss w hw)) :=
    coefficient_bridge w hw _ (gauss_coefficient w hw)
  have hh := h 15 (by norm_num) (by norm_num) w hw 1 (gauss w hw)
    hzero (hnorm) hybe (gauss_unitary w hw)
  apply gauss_not_polarized w hw
  simpa only [Units.val_one, mul_one] using hh


#print axioms result
end D5.S3.Quantum.Algebra.CyclicYangBaxterPauliRigidityRefutation

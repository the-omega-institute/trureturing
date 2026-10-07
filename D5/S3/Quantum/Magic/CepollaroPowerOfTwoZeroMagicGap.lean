/- GID: D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every qudit dimension divisible by four has a three-dimensional zero-magic-gap subspace. -/

/-
Per-declaration judgement (same-delivery helpers inlined; Mat is local notation):
  tau: proof_shape: definition; consumer: lift_solution, paperDisplacement, score_weyl, tau_unit.
  paperDisplacement: proof_shape: definition; consumer: Q, compressed_trace, lift_solution, score_weyl.
  power4: proof_shape: definition; consumer: compressed_trace, score, score_weyl.
  alt: proof_shape: definition; consumer: Q, alt_phase, compressed_trace, lift_solution, moment, moment_formula, score_weyl.
  T: proof_shape: definition; consumer: A4, moment_formula, pair_cycle_sum, perm_trace.
  Q: proof_shape: definition; consumer: aseGap, compressed_trace, lift_solution, score, score_weyl.
  A4: proof_shape: definition; consumer: aseGap, compressed_trace, lift_solution, moment, moment_formula, score, score_weyl.
  score: proof_shape: definition; consumer: aseGap, lift_solution, score_lift, score_weyl.
  aseGap: proof_shape: definition; consumer: claim, lift_solution, result.
  claim: proof_shape: definition; consumer: result.
  s: proof_shape: definition; consumer: V4, lift_solution.
  V4: proof_shape: definition; consumer: liftV, lift_solution.
  W: proof_shape: definition; consumer: W_isometry, liftV, lift_solution, score_lift, subgroup_compression.
  liftV: proof_shape: definition; consumer: lift_solution, result.
  moment: proof_shape: definition; consumer: compressed_trace, lift_solution, moment_formula, score_lift, score_weyl.
  num4: proof_shape: definition; consumer: lift_solution, moment_formula, pair_cycle_sum, score_lift.
  tau_unit: proof_shape: bind-only; consumer: lift_solution, score_weyl.
  displacement_entry: proof_shape: bind-only; consumer: lift_solution, subgroup_compression.
  product4_mul: proof_shape: bind-only; consumer: compressed_trace.
  product4_adjoint: proof_shape: bind-only; consumer: compressed_trace.
  perm_trace: proof_shape: bind-only; consumer: pair_cycle_sum.
  pair_cycle_sum: proof_shape: bind-only; consumer: moment_formula.
  moment_formula: proof_shape: bind-only; consumer: lift_solution, score_lift.
  alt_phase: proof_shape: bind-only; consumer: lift_solution, score_weyl.
  compressed_trace: proof_shape: bind-only; consumer: score_weyl.
  score_weyl: proof_shape: bind-only; consumer: lift_solution, score_lift.
  W_isometry: proof_shape: bind-only; consumer: lift_solution.
  windowRoot_restrict: proof_shape: bind-only; consumer: subgroup_compression.
  subgroup_compression: proof_shape: bind-only; consumer: score_lift.
  lift_sums: proof_shape: bind-only; consumer: score_lift.
  score_lift: proof_shape: bind-only; consumer: lift_solution.
  lift_solution: proof_shape: bind-only; consumer: result.
  power_two_factor: proof_shape: bind-only; consumer: result.
  result: proof_shape: bind-only; consumer: external open-problem settlement.
The scalar identities, isometry certificate, moment tables and base scores are local steps in lift_solution.
Utility is none per declaration: definitions specify the construction and gap; every theorem has
a general dimension, matrix, function or exponent parameter and proves a symbolic identity or family.
No separate finite-table or fixed-instance theorem is declared.
escape_witness: none.
admission_basis: open-problem-resolution (#13822; Proved).
Direct frozen public dependencies (GID; statement_id):
  D5/S3/Observer/WindowRegister.clockMatrix
    sha256:4202291c52addea22c1fe4f89a69a73039c7fe07c6cbbcc94d7f0afb5fd27a75.
  D5/S3/Observer/WindowRegister.shiftMatrix
    sha256:821649848ffe7ed9f84f11b97d3d1eb176216ccb5d3910dcbd867105b9d070dd.
  D5/S3/Observer/WindowRegister.shiftMatrix_eq_permMatrix
    sha256:3c36c8ef2f8c32a3bdfc77ed9e5a8357e39b23d6df504cd7c4eadd09ab8aafe8.
  D5/S3/Observer/WindowRegister.shiftPerm
    sha256:d089316b1edad69647319d26c3a88b94634c9feaa15ca92ee0bb373dbbd98f83.
  D5/S3/Observer/WindowRegister.shiftPerm_pow_apply
    sha256:4225ef06cfc6c92dcfd365ecab7b7738db3951b60684425b597af4598e55e2c3.
  D5/S3/Observer/WindowRegister.windowRoot
    sha256:20cc0afa06ff1993f023b3dc6be29f5eb2de89c279ee88fef72beb0e3e3d3b93.
  D5/S3/Quantum/Algebra/WeylDisplacement.displacement
    sha256:89b26d88ef2ca00bf031fea2b1b79ef1cf2b29eb212643ef0eac312a762c3dd8.
  D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul
    sha256:37724aead0bac0fd9de95c404f45e67929d36918ece752ea75c9236bb340f2a1.
  D5/S3/Quantum/Algebra/WeylDisplacement.displacement_zero
    sha256:4c7925882a6010e9a317fd30818fe6dea2665240743144b56d53a1203422f615.
  D5/S3/Quantum/Algebra/WeylDisplacementAdjoint.displacement_adjoint
    sha256:36517020edf58315ea8c58fcc869e7d60519d0a7168c0329f6f5d54661b5e568.
  D5/S3/Quantum/Algebra/WeylDisplacementPowers.displacement_pow
    sha256:063916bb8f69ada3e43717b9864db20ea87a3d191d159a39ba10880e4eccf102.
  D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace
    sha256:d0cc121497a1d557c619ba831981b3bb276fecd6887ee73c9446f65f5a372775.
  D5/S3/Quantum/Algebra/WeylDisplacementTrace.displacement_trace_eq_zero
    sha256:d9e158f2d14e8cf5fc2ac7f64ea70adc29722e9516b9f2852b2ba7e3d4ed5c81.
  D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_mod
    sha256:59566dcc01f225f4637eb795a88e49b3c16d8d553e820003fee44aa92ae3a499.
  D5/S3/Quantum/Algebra/WeylPhaseArithmetic.windowRoot_pow_val_add
    sha256:826b864e1ac632e31e428742725dfdfe5e5ac74f1a182005cf533610db24f4f4.
  D5/S3/Quantum/Recovery/PurifiedLocalPath.productMap
    sha256:8db6e5665e7fbd3cabf2ecaff9b9ad87e606f0bf633f99375a5ad2e669dcd639.
The productMap declaration belongs to Lean namespace ProductPrefixRigidity.
Pinned Mathlib supplies the generic permutation-matrix and algebraic operations.
A4 is stipulated in closed form; no Haar-integration theorem is asserted.
-/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylDisplacementPowers

set_option linter.style.longLine false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap

open D5.S3.Quantum.Recovery.ProductPrefixRigidity
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
open D5.S3.Quantum.Algebra.WeylDisplacementTrace
open D5.S3.Quantum.Algebra.WeylDisplacementPowers
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic

local notation "Mat" p:max q:max => Matrix (Fin p) (Fin q) ℂ
def tau (d : ℕ) : ℂ := -Complex.exp ((Real.pi : ℂ) * Complex.I / (d : ℂ))
def paperDisplacement (d : ℕ) [NeZero d] (a : ZMod d × ZMod d) :
    Matrix (ZMod d) (ZMod d) ℂ :=
  tau d ^ (a.1.val * a.2.val) • displacement d a.1 a.2
def power4 {P Q : Type} (V : Matrix P Q ℂ) :=
  productMap (fun _ : Fin 4 => Q) (fun _ => V)
def alt {H : Type} (A : Matrix H H ℂ) :=
  productMap (fun _ : Fin 4 => H)
    (![A, Aᴴ, A, Aᴴ] : Fin 4 → Matrix H H ℂ)
def T (H : Type) (σ : Equiv.Perm (Fin 4)) :
    Matrix (Fin 4 → H) (Fin 4 → H) ℂ := by
  classical
  exact Equiv.Perm.permMatrix ℂ (Equiv.arrowCongr σ.symm (Equiv.refl H))
def Q (d : ℕ) [NeZero d] :=
  ((d : ℂ)^2)⁻¹ • (∑ a : ZMod d × ZMod d, alt (paperDisplacement d a))
def A4 (H : Type) [Fintype H] :=
  (Nat.choose (Fintype.card H + 3) 4 : ℂ)⁻¹ •
    ((24 : ℂ)⁻¹ • (∑ σ : Equiv.Perm (Fin 4), T H σ))
def score {dB : ℕ} [NeZero dB] (V : Matrix (ZMod dB) (Fin 3) ℂ) : ℂ :=
  (dB : ℂ) * Matrix.trace (Q dB * power4 V * A4 (Fin 3) * (power4 V)ᴴ)
def aseGap {dB : ℕ} [NeZero dB] (V : Matrix (ZMod dB) (Fin 3) ℂ) : ℂ :=
  3 * Matrix.trace (Q 3 * A4 (ZMod 3)) - score V
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ V : Matrix (ZMod (2^m)) (Fin 3) ℂ,
    Vᴴ * V = 1 ∧ aseGap V = 0

private def s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
private def V4 : Matrix (ZMod 4) (Fin 3) ℂ := !![0,0,s; 1,0,0; 0,0,-s; 0,1,0]
private def W (r : ℕ) : Matrix (ZMod (4*r)) (ZMod 4) ℂ :=
  fun x k => if x.val = r*k.val then 1 else 0
private def liftV (r : ℕ) [NeZero (4 * r)] : Matrix (ZMod (4*r)) (Fin 3) ℂ := W r * V4
private def moment {H : Type} [Fintype H] (A : Matrix H H ℂ) : ℂ :=
  Matrix.trace (alt A * A4 H)
private def num4 {H : Type} [Fintype H] (A B : Matrix H H ℂ) : ℂ :=
  let t : Matrix H H ℂ → ℂ := Matrix.trace
  (t A)^2*(t B)^2 + t (A*A)*(t B)^2 + t (B*B)*(t A)^2 +
  4*t (A*B)*t A*t B + t (A*A)*t (B*B) + 2*(t (A*B))^2 +
  4*t (A*A*B)*t B + 4*t (A*B*B)*t A +
  4*t (A*A*B*B) + 2*t (A*B*A*B)

private theorem tau_unit (d : ℕ) : tau d * star (tau d) = 1 := by
  unfold tau
  rw [star_neg, neg_mul_neg]
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp [neg_div]

private theorem displacement_entry (d : ℕ) [NeZero d] (a b x y : ZMod d) :
    displacement d a b x y =
      if x.val = (y.val + a.val) % d then windowRoot d ^ (b.val*y.val) else 0 := by
  have hp : shiftMatrix d ^ a.val = (shiftPerm d ^ a.val).permMatrix ℂ := by
    rw [shiftMatrix_eq_permMatrix]
    simpa only [Matrix.permMatrixHom_apply, inv_inv, ← inv_pow] using
      ((Matrix.permMatrixHom (R := ℂ)).map_pow (shiftPerm d)⁻¹ a.val).symm
  have hx : (shiftPerm d ^ a.val) x = y ↔ x.val = (y.val + a.val) % d := by
    rw [shiftPerm_pow_apply, a.natCast_zmod_val, sub_eq_iff_eq_add]
    rw [← (ZMod.val_injective d).eq_iff, ZMod.val_add]
  simp only [displacement, clockMatrix, Matrix.diagonal_pow, Matrix.mul_diagonal,
    hp, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, hx, Pi.pow_apply, ← pow_mul]
  split_ifs <;> simp [mul_comm]

private theorem product4_mul {P Q R : Type} [Fintype Q]
    (M : Fin 4 → Matrix P Q ℂ) (N : Fin 4 → Matrix Q R ℂ) :
    productMap (fun _ : Fin 4 => R) (fun i => M i * N i) =
      productMap (fun _ : Fin 4 => Q) M * productMap (fun _ : Fin 4 => R) N := by
  ext x y
  simp only [productMap, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Finset.prod_mul_distrib

private theorem product4_adjoint {P Q : Type} (M : Fin 4 → Matrix P Q ℂ) :
    productMap (fun _ : Fin 4 => P) (fun i => (M i)ᴴ) =
      (productMap (fun _ : Fin 4 => Q) M)ᴴ := by
  ext x y
  simp [productMap, Matrix.conjTranspose_apply]

private theorem perm_trace {H : Type} [Fintype H] (M : Fin 4 → Matrix H H ℂ) (σ : Equiv.Perm (Fin 4)) :
    Matrix.trace (productMap (fun _ : Fin 4 => H) M * T H σ) =
      ∑ x : Fin 4 → H, ∏ i, M i (x i) (x (σ.symm i)) := by
  classical
  have hT (x y : Fin 4 → H) :
      T H σ x y = if x = y ∘ σ.symm then 1 else 0 := by
    simp only [T, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, ← Equiv.eq_symm_apply]
    rfl
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hT, productMap,
    mul_ite, Function.comp_def]

set_option maxHeartbeats 4000000 in
-- The 24 symbolic permutation contractions require a larger elaboration budget.
private theorem pair_cycle_sum {H : Type} [Fintype H] (A B : Matrix H H ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), Matrix.trace (productMap (fun _ : Fin 4 => H) ![A,B,A,B] * T H σ)) =
      num4 A B := by
  classical
  let t : Matrix H H ℂ → ℂ := Matrix.trace
  let e : Fin 4 × Fin 3 × Fin 2 → Equiv.Perm (Fin 4) := fun z =>
    Equiv.swap 0 z.1 * Equiv.swap 1 ⟨z.2.1.val + 1, by omega⟩ *
      Equiv.swap 2 ⟨z.2.2.val + 2, by omega⟩
  have he : Function.Bijective e := by decide
  have hsum (p : Equiv.Perm (Fin 4)) (f : (Fin 4 → H) → ℂ) :
      (∑ x, f x) = ∑ i, ∑ j, ∑ k, ∑ l, f (![i,j,k,l] ∘ p) := by
    let q : (H × H × H × H) ≃ (Fin 4 → H) :=
      { toFun := fun z => ![z.1,z.2.1,z.2.2.1,z.2.2.2]
        invFun := fun x => (x 0,x 1,x 2,x 3)
        left_inv := by rintro ⟨i,j,k,l⟩; rfl
        right_inv := by intro x; ext i; fin_cases i <;> rfl }
    calc
      (∑ x, f x) = ∑ z : H × H × H × H,
          f (![z.1,z.2.1,z.2.2.1,z.2.2.2] ∘ p) :=
        ((q.trans (Equiv.arrowCongr p.symm (Equiv.refl (H)))).sum_comp f).symm
      _ = _ := by simp only [Fintype.sum_prod_type]
  let g : Fin 4 → Fin 3 → Fin 2 → ℂ :=
    ![![![(t A)^2 * (t B)^2, t (A*B) * t A * t B], ![t (A*B) * t A * t B, t (A*B*B) * t A], ![t (B*B) * (t A)^2, t (A*B*B) * t A]],
      ![![t (A*B) * t A * t B, (t (A*B))^2], ![t (A*A*B) * t B, t (A*B*A*B)], ![t (A*B*B) * t A, t (A*A*B*B)]],
      ![![t (A*A) * (t B)^2, t (A*A*B) * t B], ![t (A*A*B) * t B, t (A*A*B*B)], ![t (A*A) * t (B*B), t (A*A*B*B)]],
      ![![t (A*B) * t A * t B, t (A*A*B) * t B], ![(t (A*B))^2, t (A*A*B*B)], ![t (A*B*B) * t A, t (A*B*A*B)]]]
  have htable (i : Fin 4) (j : Fin 3) (k : Fin 2) :
      Matrix.trace (productMap (fun _ : Fin 4 => H) ![A,B,A,B] * T H (e (i,j,k))) = g i j k := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 1) * A (x 2) (x 2) * B (x 3) (x 3)) = (Matrix.trace A)^2 * (Matrix.trace B)^2
      rw [hsum (Equiv.ofBijective ![3,1,2,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A l l * B j j * A k k * B i i) = (Matrix.trace A)^2 * (Matrix.trace B)^2
      simp only [Matrix.trace, Matrix.diag_apply, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 1) * A (x 2) (x 3) * B (x 3) (x 2)) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![1,0,2,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j j * B i i * A k l * B l k) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 2) * A (x 2) (x 1) * B (x 3) (x 3)) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![1,3,2,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j j * B l k * A k l * B i i) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 3) * A (x 2) (x 1) * B (x 3) (x 2)) = Matrix.trace (A*B*B) * Matrix.trace A
      rw [hsum (Equiv.ofBijective ![0,3,1,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i i * B l k * A j l * B k j) = Matrix.trace (A*B*B) * Matrix.trace A
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 3) * A (x 2) (x 2) * B (x 3) (x 1)) = Matrix.trace (B*B) * (Matrix.trace A)^2
      rw [hsum (Equiv.ofBijective ![1,2,0,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j j * B k l * A i i * B l k) = Matrix.trace (B*B) * (Matrix.trace A)^2
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 0) * B (x 1) (x 2) * A (x 2) (x 3) * B (x 3) (x 1)) = Matrix.trace (A*B*B) * Matrix.trace A
      rw [hsum (Equiv.ofBijective ![0,2,1,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i i * B k j * A j l * B l k) = Matrix.trace (A*B*B) * Matrix.trace A
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 0) * A (x 2) (x 2) * B (x 3) (x 3)) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![2,3,1,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B l k * A j j * B i i) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 0) * A (x 2) (x 3) * B (x 3) (x 2)) = (Matrix.trace (A*B))^2
      rw [hsum (Equiv.ofBijective ![2,3,0,1] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B l k * A i j * B j i) = (Matrix.trace (A*B))^2
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 0) * A (x 2) (x 1) * B (x 3) (x 3)) = Matrix.trace (A*A*B) * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![1,2,3,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j l * B k j * A l k * B i i) = Matrix.trace (A*A*B) * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 0) * A (x 2) (x 1) * B (x 3) (x 2)) = Matrix.trace (A*B*A*B)
      rw [hsum (Equiv.ofBijective ![0,1,2,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i l * B j i * A k j * B l k) = Matrix.trace (A*B*A*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 0) * A (x 2) (x 2) * B (x 3) (x 1)) = Matrix.trace (A*B*B) * Matrix.trace A
      rw [hsum (Equiv.ofBijective ![1,2,0,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j l * B k j * A i i * B l k) = Matrix.trace (A*B*B) * Matrix.trace A
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 0) * A (x 2) (x 3) * B (x 3) (x 1)) = Matrix.trace (A*A*B*B)
      rw [hsum (Equiv.ofBijective ![0,1,3,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i l * B j i * A l k * B k j) = Matrix.trace (A*A*B*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 1) * A (x 2) (x 0) * B (x 3) (x 3)) = Matrix.trace (A*A) * (Matrix.trace B)^2
      rw [hsum (Equiv.ofBijective ![2,1,3,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B j j * A l k * B i i) = Matrix.trace (A*A) * (Matrix.trace B)^2
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 1) * A (x 2) (x 0) * B (x 3) (x 2)) = Matrix.trace (A*A*B) * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![3,0,1,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A l k * B i i * A j l * B k j) = Matrix.trace (A*A*B) * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 2) * A (x 2) (x 0) * B (x 3) (x 3)) = Matrix.trace (A*A*B) * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![3,2,1,0] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A l k * B k j * A j l * B i i) = Matrix.trace (A*A*B) * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 3) * A (x 2) (x 0) * B (x 3) (x 2)) = Matrix.trace (A*A*B*B)
      rw [hsum (Equiv.ofBijective ![3,2,0,1] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A l k * B k j * A i l * B j i) = Matrix.trace (A*A*B*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 3) * A (x 2) (x 0) * B (x 3) (x 1)) = Matrix.trace (A*A) * Matrix.trace (B*B)
      rw [hsum (Equiv.ofBijective ![2,0,3,1] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B i j * A l k * B j i) = Matrix.trace (A*A) * Matrix.trace (B*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 2) * A (x 2) (x 0) * B (x 3) (x 1)) = Matrix.trace (A*A*B*B)
      rw [hsum (Equiv.ofBijective ![3,1,0,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A l k * B j i * A i l * B k j) = Matrix.trace (A*A*B*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 1) * A (x 2) (x 2) * B (x 3) (x 0)) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![2,0,1,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B i i * A j j * B l k) = Matrix.trace (A*B) * Matrix.trace A * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 1) * A (x 2) (x 3) * B (x 3) (x 0)) = Matrix.trace (A*A*B) * Matrix.trace B
      rw [hsum (Equiv.ofBijective ![1,0,3,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j l * B i i * A l k * B k j) = Matrix.trace (A*A*B) * Matrix.trace B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 3) * B (x 1) (x 2) * A (x 2) (x 1) * B (x 3) (x 0)) = (Matrix.trace (A*B))^2
      rw [hsum (Equiv.ofBijective ![2,1,0,3] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A k l * B j i * A i j * B l k) = (Matrix.trace (A*B))^2
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pow_two,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 2) * B (x 1) (x 3) * A (x 2) (x 1) * B (x 3) (x 0)) = Matrix.trace (A*A*B*B)
      rw [hsum (Equiv.ofBijective ![0,2,3,1] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i l * B k j * A l k * B j i) = Matrix.trace (A*A*B*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 3) * A (x 2) (x 2) * B (x 3) (x 0)) = Matrix.trace (A*B*B) * Matrix.trace A
      rw [hsum (Equiv.ofBijective ![1,3,0,2] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A j l * B l k * A i i * B k j) = Matrix.trace (A*B*B) * Matrix.trace A
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul, Finset.mul_sum]
      all_goals repeat' (apply Finset.sum_congr rfl; intro _ _)
      all_goals ring
    · rw [perm_trace]
      simp only [Fin.prod_univ_four]
      change (∑ x : Fin 4 → H, A (x 0) (x 1) * B (x 1) (x 2) * A (x 2) (x 3) * B (x 3) (x 0)) = Matrix.trace (A*B*A*B)
      rw [hsum (Equiv.ofBijective ![0,3,2,1] (by decide))]
      change (∑ i : H, ∑ j : H, ∑ k : H, ∑ l : H,
        A i l * B l k * A k j * B j i) = Matrix.trace (A*B*A*B)
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Finset.sum_mul]
  rw [← he.sum_comp (fun σ => Matrix.trace (productMap (fun _ : Fin 4 => H) ![A,B,A,B] * T H σ))]
  simp only [Fintype.sum_prod_type, htable]
  simp [g, num4, t, Fin.sum_univ_succ]
  ring

private theorem moment_formula {H : Type} [Fintype H] (A : Matrix H H ℂ) :
    moment A = (Nat.choose (Fintype.card H+3) 4 : ℂ)⁻¹ * ((24 : ℂ)⁻¹ * num4 A Aᴴ) := by
  classical
  simp only [moment, A4, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum,
    Matrix.trace_sum, smul_eq_mul, alt, pair_cycle_sum]

private theorem alt_phase {H : Type} (A : Matrix H H ℂ) (c : ℂ) (hc : c * star c = 1) :
    alt (c • A) = alt A := by
  ext x y
  simp only [alt, productMap, Fin.prod_univ_four, Matrix.conjTranspose_smul,
    Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  calc
    _ = (c * star c)^2 * (A (x 0) (y 0) * Aᴴ (x 1) (y 1) *
        A (x 2) (y 2) * Aᴴ (x 3) (y 3)) := by ring
    _ = _ := by rw [hc]; simp

private theorem compressed_trace {d : ℕ} [NeZero d] (V : Matrix (ZMod d) (Fin 3) ℂ) :
    Matrix.trace (Q d * power4 V * A4 (Fin 3) * (power4 V)ᴴ) =
      ((d : ℂ)^2)⁻¹ * ∑ a : ZMod d × ZMod d, moment (Vᴴ * paperDisplacement d a * V) := by
  classical
  have hcomp (D : Matrix (ZMod d) (ZMod d) ℂ) :
      alt (Vᴴ * D * V) = (power4 V)ᴴ * alt D * power4 V := by
    unfold alt power4
    rw [← product4_adjoint, ← product4_mul, ← product4_mul]
    congr 1
    funext i
    fin_cases i <;> simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [Q, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold moment
  rw [hcomp, Matrix.trace_mul_comm]
  congr 1
  simp only [Matrix.mul_assoc]

private theorem score_weyl {d : ℕ} [NeZero d] (hd : 0 < d) (V : Matrix (ZMod d) (Fin 3) ℂ) :
    score V = (d : ℂ)⁻¹ * ∑ a : ZMod d × ZMod d,
      moment (Vᴴ * displacement d a.1 a.2 * V) := by
  classical
  have hphase (a : ZMod d × ZMod d) :
      moment (Vᴴ * paperDisplacement d a * V) =
        moment (Vᴴ * displacement d a.1 a.2 * V) := by
    simp only [paperDisplacement, Matrix.mul_smul, Matrix.smul_mul]
    unfold moment
    rw [alt_phase]
    rw [star_pow, ← mul_pow, tau_unit, one_pow]
  unfold score
  rw [compressed_trace]
  simp_rw [hphase]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

private theorem W_isometry (r : ℕ) [NeZero (4 * r)] (hr : 0 < r) : (W r)ᴴ * W r = 1 := by
  classical
  let row (k : ZMod 4) : ZMod (4*r) := (r*k.val : ℕ)
  have hinj : Function.Injective row := by
    intro i j hij
    apply ZMod.val_injective 4
    apply Nat.mul_left_cancel hr
    have hv (k : ZMod 4) : (row k).val = r*k.val := by
      apply ZMod.val_natCast_of_lt
      have := ZMod.val_lt k
      nlinarith
    simpa only [hv] using congrArg ZMod.val hij
  have hW (x : ZMod (4*r)) (k : ZMod 4) :
      W r x k = if x = row k then 1 else 0 := by
    have hv : (row k).val = r*k.val := by
      apply ZMod.val_natCast_of_lt
      have := ZMod.val_lt k
      nlinarith
    simp only [W, ← hv, (ZMod.val_injective (4*r)).eq_iff]
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hW,
    hinj.eq_iff, Matrix.one_apply, eq_comm]

private theorem windowRoot_restrict (r : ℕ) (hr : 0 < r) : windowRoot (4*r) ^ r = windowRoot 4 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold windowRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem subgroup_compression (r : ℕ) [NeZero (4 * r)] (hr : 0 < r) (a b : ZMod (4 * r)) :
    (W r)ᴴ * displacement (4*r) a b * W r =
      if r ∣ a.val then displacement 4 (a.val / r) ((b.val % 4 : ℕ) : ZMod 4) else 0 := by
  classical
  let row (k : ZMod 4) : ZMod (4*r) := (r*k.val : ℕ)
  have hW (x : ZMod (4*r)) (k : ZMod 4) :
      W r x k = if x = row k then 1 else 0 := by
    have hv : (row k).val = r*k.val := by
      apply ZMod.val_natCast_of_lt
      have := ZMod.val_lt k
      nlinarith
    simp only [W, ← hv, (ZMod.val_injective (4*r)).eq_iff]
  have hcomp (M : Matrix (ZMod (4*r)) (ZMod (4*r)) ℂ) (i j : ZMod 4) :
      ((W r)ᴴ * M * W r) i j = M (row i) (row j) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hW, ite_mul, mul_ite]
  ext i j
  rw [hcomp, displacement_entry]
  have hv (k : ZMod 4) : (row k).val = r*k.val := by
    apply ZMod.val_natCast_of_lt
    have := ZMod.val_lt k
    nlinarith
  simp only [hv]
  by_cases ha : r ∣ a.val
  · simp only [ha, if_true]
    rw [displacement_entry 4]
    have hau : a.val / r < 4 := by
      have := ZMod.val_lt a
      exact (Nat.div_lt_iff_lt_mul hr).mpr (by nlinarith)
    simp only [ZMod.val_natCast_of_lt hau, ZMod.val_natCast,
      Nat.mod_mod]
    have ha' : r * (a.val / r) = a.val := Nat.mul_div_cancel' ha
    have hshift : r*i.val = (r*j.val+a.val)%(4*r) ↔
        i.val = (j.val+a.val/r)%4 := by
      have hmod : (r*j.val+a.val)%(4*r) = r*((j.val+a.val/r)%4) := by
        calc
          _ = (r*(j.val+a.val/r))%(r*4) := by congr 1 <;> nlinarith [ha']
          _ = _ := Nat.mul_mod_mul_left r _ 4
      rw [hmod]
      exact Nat.mul_left_cancel_iff hr
    have hphase : windowRoot (4*r) ^ (b.val * (r*j.val)) =
        windowRoot 4 ^ ((b.val%4)*j.val) := by
      calc
        _ = (windowRoot (4*r)^r)^(b.val*j.val) := by
          rw [← pow_mul]
          congr 1
          ring
        _ = windowRoot 4 ^ (b.val*j.val) := by rw [windowRoot_restrict r hr]
        _ = (windowRoot 4 ^ b.val)^j.val := by rw [pow_mul]
        _ = (windowRoot 4 ^ (b.val%4))^j.val := by
          rw [← windowRoot_pow_mod b.val]
        _ = _ := by rw [pow_mul]
    simp only [hshift, hphase]
  · simp only [ha, if_false, Matrix.zero_apply]
    have hshift : r*i.val ≠ (r*j.val+a.val)%(4*r) := by
      intro h
      apply ha
      apply Nat.dvd_of_mod_eq_zero
      calc
        a.val % r = (r*j.val+a.val)%r := by simp [Nat.add_mod]
        _ = ((r*j.val+a.val)%(4*r))%r :=
          (Nat.mod_mod_of_dvd _ (by exact ⟨4, by ring⟩)).symm
        _ = (r*i.val)%r := by rw [← h]
        _ = 0 := Nat.mul_mod_right _ _
    simp only [hshift, if_false]

private theorem lift_sums (r : ℕ) [NeZero (4 * r)] (hr : 0 < r) (f : ℕ → ℂ) :
    ((∑ a : ZMod (4*r), if r ∣ a.val then f (a.val/r) else 0) = ∑ u : Fin 4, f u.val) ∧
    ((∑ b : ZMod (4*r), f (b.val%4)) = (r : ℂ) * ∑ v : Fin 4, f v.val) := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  have hv (a : Fin (4*r)) : ((ZMod.finEquiv (4*r)).toEquiv a).val = a.val := by
    cases r with
    | zero => omega
    | succ r => rfl
  simp only [← (ZMod.finEquiv (4*r)).toEquiv.sum_comp, hv]
  constructor
  · rw [← (finProdFinEquiv : Fin 4 × Fin r ≃ Fin (4*r)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ u : Fin 4, ∑ t : Fin r,
      if r ∣ t.val+r*u.val then f ((t.val+r*u.val)/r) else 0) = _
    have hdiv (u : Fin 4) (t : Fin r) : r ∣ t.val + r*u.val ↔ t = 0 := by
      rw [← Nat.dvd_add_iff_left (dvd_mul_right r u.val)]
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt t.isLt]
      simpa only [Fin.val_zero] using (@Fin.ext_iff r t 0).symm
    simp only [hdiv]
    simp [Nat.add_mul_div_left, hr]
  · let e : Fin r × Fin 4 ≃ Fin (4*r) :=
      finProdFinEquiv.trans (finCongr (Nat.mul_comm r 4))
    rw [← e.sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ q : Fin r, ∑ v : Fin 4, f ((v.val+4*q.val)%4)) = _
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fin.isLt _)]
    simp [nsmul_eq_mul]

set_option maxHeartbeats 1000000 in
-- The nested finite-sum transport requires a larger elaboration budget.
private theorem score_lift (r : ℕ) [NeZero (4 * r)] (hr : 0 < r) (U : Matrix (ZMod 4) (Fin 3) ℂ) :
    score (W r * U) = score U := by
  classical
  have hd : 0 < 4*r := by positivity
  have hu (u : Fin 4) : (u.val : ZMod 4) = u := Fin.cast_val_eq_self u
  have h0 : moment (0 : Mat 3 3) = 0 := by
    rw [moment_formula]
    simp [num4]
  have hc (a b : ZMod (4*r)) :
      moment ((W r * U)ᴴ * displacement (4*r) a b * (W r * U)) =
        if r ∣ a.val then moment (Uᴴ * displacement 4 (a.val/r) ((b.val%4 : ℕ) : ZMod 4) * U) else 0 := by
    rw [Matrix.conjTranspose_mul]
    have he : Uᴴ * (W r)ᴴ * displacement (4*r) a b * (W r * U) =
        Uᴴ * ((W r)ᴴ * displacement (4*r) a b * W r) * U := by
      simp only [Matrix.mul_assoc]
    rw [he, subgroup_compression r hr]
    split_ifs
    · rfl
    · simp only [Matrix.mul_zero, Matrix.zero_mul, h0]
  have hs :
      (∑ a : ZMod (4*r), ∑ b : ZMod (4*r),
        if r ∣ a.val then moment (Uᴴ * displacement 4 (a.val/r) ((b.val%4 : ℕ) : ZMod 4) * U) else 0) =
        (r : ℂ) * ∑ u : Fin 4, ∑ v : Fin 4, moment (Uᴴ * displacement 4 u v * U) := by
    calc
      _ = ∑ b : ZMod (4*r), ∑ u : Fin 4,
          moment (Uᴴ * displacement 4 u ((b.val%4 : ℕ) : ZMod 4) * U) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        simpa only [hu] using
          (lift_sums r hr (fun u =>
            moment (Uᴴ * displacement 4 u ((b.val%4 : ℕ) : ZMod 4) * U))).1
      _ = ∑ u : Fin 4, (r : ℂ) * ∑ v : Fin 4,
          moment (Uᴴ * displacement 4 u v * U) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        simpa only [hu] using
          (lift_sums r hr (fun v => moment (Uᴴ * displacement 4 u v * U))).2
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [score_weyl hd, score_weyl (by norm_num)]
  simp only [Fintype.sum_prod_type, hc]
  rw [hs]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  rfl

set_option maxHeartbeats 6000000 in
-- The local moment tables and their combination require a larger elaboration budget.
private theorem lift_solution (r : ℕ) [NeZero (4 * r)] (hr : 0 < r) :
    (liftV r)ᴴ * liftV r = 1 ∧ aseGap (liftV r) = 0 := by
  classical
  have scalar_data : star s = s ∧ s^2 = (1/2 : ℂ) ∧ windowRoot 4 = Complex.I := by
    have hs : star s = s := by simp [s]
    have hs2 : s^2 = (1/2 : ℂ) := by
      rw [s, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have h4 : windowRoot 4 = Complex.I := by
      unfold windowRoot
      convert Complex.exp_pi_div_two_mul_I using 1
      congr 1
      ring
    exact ⟨hs, hs2, h4⟩
  have V4_isometry : V4ᴴ * V4 = 1 := by
    have hs : (starRingEnd ℂ) s = s := scalar_data.1
    ext i j
    simp only [Matrix.mul_apply, ZMod]
    fin_cases i <;> fin_cases j <;>
      norm_num [V4, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hs]
    linear_combination 2 * scalar_data.2.1
  have ququart_moments (u v : Fin 4) :
      moment (V4ᴴ * displacement 4 u v * V4) =
        if u = 0 ∧ v = 0 then 1 else
          if u.val % 2 = 0 ∧ v.val % 2 = 0 then 1/5 else 1/15 := by
    classical
    have hs : (starRingEnd ℂ) s = s := scalar_data.1
    have hI6 : Complex.I^6 = -1 := by
      simpa only [Nat.reduceMod, Complex.I_sq] using Complex.I_pow_eq_pow_mod 6
    have hI9 : Complex.I^9 = Complex.I := by
      simpa only [Nat.reduceMod, pow_one] using Complex.I_pow_eq_pow_mod 9
    have hs2 := scalar_data.2.1
    have hs4 : s^4 = (1/4 : ℂ) := by
      calc
        _ = (s^2)^2 := by ring
        _ = _ := by rw [hs2]; norm_num
    have he (a b x y : ZMod 4) :
        displacement 4 a b x y = if x.val = (y.val+a.val)%4 then Complex.I^(b.val*y.val) else 0 := by
      rw [displacement_entry 4, scalar_data.2.2]
    let C : Fin 4 → Fin 4 → Mat 3 3 :=
      ![
        ![!![1, 0, 0; 0, 1, 0; 0, 0, 1],
          !![Complex.I, 0, 0; 0, -Complex.I, 0; 0, 0, 0],
          !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
          !![-Complex.I, 0, 0; 0, Complex.I, 0; 0, 0, 0]],
        ![!![0, 0, s; 0, 0, -s; -s, s, 0],
          !![0, 0, s; 0, 0, s; -Complex.I * s, -Complex.I * s, 0],
          !![0, 0, s; 0, 0, -s; s, -s, 0],
          !![0, 0, s; 0, 0, s; Complex.I * s, Complex.I * s, 0]],
        ![!![0, 1, 0; 1, 0, 0; 0, 0, -1],
          !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0],
          !![0, -1, 0; -1, 0, 0; 0, 0, -1],
          !![0, Complex.I, 0; -Complex.I, 0, 0; 0, 0, 0]],
        ![!![0, 0, -s; 0, 0, s; s, -s, 0],
          !![0, 0, s; 0, 0, s; Complex.I * s, Complex.I * s, 0],
          !![0, 0, -s; 0, 0, s; -s, s, 0],
          !![0, 0, s; 0, 0, s; -Complex.I * s, -Complex.I * s, 0]]
      ]
    have hC (a b : Fin 4) : V4ᴴ * displacement 4 a b * V4 = C a b := by
      ext i j
      simp only [Matrix.mul_apply, ZMod]
      fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
        norm_num [C, V4, Matrix.mul_apply, Matrix.conjTranspose_apply,
          ZMod.val, Fin.sum_univ_succ, he, hs,
          Matrix.cons_val_two, Matrix.cons_val_three, hI6, hI9]
      all_goals ring_nf
      all_goals norm_num [hs2, hI6, hI9]
    rw [moment_formula]
    simp only [hC]
    fin_cases u <;> fin_cases v <;>
      norm_num [C, num4, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, hs,
        Complex.star_def, Complex.conj_I, Matrix.vecMul, dotProduct, Nat.choose,
        hI6, hI9]
    all_goals ring_nf
    all_goals norm_num [hs2, hs4, hI6, hI9]
  have qutrit_moments (u v : ZMod 3) :
      moment (displacement 3 u v) = if u = 0 ∧ v = 0 then 1 else 1/10 := by
    classical
    by_cases h : u = 0 ∧ v = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [displacement_zero, moment_formula]
      norm_num [num4, Nat.choose, ZMod.card]
    · have htwo : ∀ x : ZMod 3, (2 : ZMod 3) * x = 0 → x = 0 := by decide
      have h2 : ¬ ((2 : ZMod 3) * u = 0 ∧ (2 : ZMod 3) * v = 0) :=
        fun hz => h ⟨htwo u hz.1, htwo v hz.2⟩
      have ht : Matrix.trace (displacement 3 u v) = 0 :=
        displacement_trace_eq_zero u v h
      have ht2 : Matrix.trace (displacement 3 u v * displacement 3 u v) = 0 := by
        rw [← pow_two, displacement_pow, Matrix.trace_smul, displacement_trace]
        simp only [Nat.cast_ofNat, if_neg h2, smul_zero]
      have hunit : displacement 3 u v * (displacement 3 u v)ᴴ = 1 := by
        rw [← Matrix.star_eq_conjTranspose, displacement_adjoint, Matrix.mul_smul,
          displacement_mul, smul_smul, ← windowRoot_pow_val_add]
        have hz : u*v + v*(-u) = 0 := by ring
        rw [hz]
        simp
      have ht2star : Matrix.trace ((displacement 3 u v)ᴴ * (displacement 3 u v)ᴴ) = 0 := by
        rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, ht2, star_zero]
      have hword : displacement 3 u v * displacement 3 u v *
          (displacement 3 u v)ᴴ * (displacement 3 u v)ᴴ = 1 := by
        calc
          _ = displacement 3 u v * (displacement 3 u v * (displacement 3 u v)ᴴ) *
              (displacement 3 u v)ᴴ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hunit, Matrix.mul_one, hunit]
      rw [moment_formula, if_neg h]
      norm_num [num4, Nat.choose, ht, Matrix.trace_conjTranspose, ht2, ht2star,
        hunit, hword, ZMod.card]
  have base_scores :
      (3 : ℂ) * Matrix.trace (Q 3 * A4 (ZMod 3)) = 3/5 ∧ score V4 = 3/5 := by
    classical
    have hphase (a : Fin 3 × Fin 3) : moment (paperDisplacement 3 a) =
        moment (displacement 3 a.1 a.2) := by
      unfold paperDisplacement moment
      rw [alt_phase]
      rw [star_pow, ← mul_pow, tau_unit, one_pow]
    constructor
    · simp only [Q, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul,
        Matrix.trace_sum, smul_eq_mul]
      change 3 * (((3 : ℂ)^2)⁻¹ * ∑ a : Fin 3 × Fin 3, moment (paperDisplacement 3 a)) = 3/5
      simp_rw [hphase]
      have h3nz : (2 : ZMod 3) ≠ 0 := by decide
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, qutrit_moments, h3nz]
    · rw [score_weyl (by norm_num)]
      simp only [Fintype.sum_prod_type]
      change (4 : ℂ)⁻¹ * (∑ u : Fin 4, ∑ v : Fin 4,
        moment (V4ᴴ * displacement 4 u v * V4)) = 3/5
      norm_num [Fin.sum_univ_succ, ququart_moments]
  unfold liftV
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      V4ᴴ * (W r)ᴴ * (W r * V4) = V4ᴴ * ((W r)ᴴ * W r) * V4 := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [W_isometry r hr, Matrix.mul_one, V4_isometry]
  · unfold aseGap
    rw [score_lift r hr V4, base_scores.1, base_scores.2, sub_self]

private theorem power_two_factor (m : ℕ) (hm : 2 ≤ m) :
    (2 : ℕ)^m = 4 * 2^(m-2) := by
  calc
    (2 : ℕ)^m = 2^((m-2)+2) := by congr 1; omega
    _ = 4 * 2^(m-2) := by simp [pow_add, Nat.mul_comm]

theorem result : claim := by
  intro m hm
  have h := power_two_factor m hm
  have transport : ∀ d : ℕ, ∀ _ : NeZero d,
      d = 4 * 2^(m-2) →
      ∃ V : Matrix (ZMod d) (Fin 3) ℂ, Vᴴ * V = 1 ∧ aseGap V = 0 := by
    intro d hd he
    subst d
    exact ⟨liftV (2^(m-2)), lift_solution _ (by positivity)⟩
  exact transport (2^m) inferInstance h

end D5.S3.Quantum.Magic.CepollaroPowerOfTwoZeroMagicGap
end

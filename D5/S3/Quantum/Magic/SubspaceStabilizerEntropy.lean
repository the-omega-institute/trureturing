/- GID: D5/S3/Quantum/Magic/SubspaceStabilizerEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Magic/SubspaceStabilizerEntropy
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Subspace linear stabilizer entropy gap, fourth-moment polynomial, and invariance. -/

import D5.S3.Quantum.Recovery.PurifiedLocalPath
import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylDisplacementTwoTorsion
import D5.S3.Quantum.Algebra.WeylPhaseArithmetic

/-!
# Subspace linear stabilizer entropy and fourth-moment operators

Phased Weyl–Heisenberg operators, pure-state linear stabilizer entropy, fourfold symmetric Haar
fourth-moment operators, extrinsic and intrinsic terms, subspace gap, and symmetric Schur twirl.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Magic.SubspaceStabilizerEntropy

open D5.S3.Quantum.Recovery.ProductPrefixRigidity D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
open D5.S3.Quantum.Algebra.WeylDisplacementTrace D5.S3.Quantum.Algebra.WeylDisplacementTwoTorsion
open D5.S3.Quantum.Algebra.WeylPhaseArithmetic

/-- Half-turn Weyl phase `-exp(π i / d)`. -/
def tau (d : ℕ) : ℂ := -Complex.exp ((Real.pi : ℂ) * Complex.I / (d : ℂ))
/-- Phased Weyl–Heisenberg displacement `τ^{a₁ a₂} X^{a₁} Z^{a₂}` indexed by `(ZMod d)²`. -/
def paperDisplacement (d : ℕ) [NeZero d] (a : ZMod d × ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  tau d ^ (a.1.val * a.2.val) • displacement d a.1 a.2
/-- Integer-labeled phased Weyl–Heisenberg displacement word `τ^{x y} X^x Z^y` on `ℂ^d`. -/
def intPaperDisplacement (d : ℕ) [NeZero d] (x y : ℤ) : Matrix (ZMod d) (ZMod d) ℂ :=
  tau d ^ (x * y) • (Matrix.permMatrixHom (n := ZMod d) (R := ℂ) ((shiftPerm d)⁻¹ ^ x) *
    Matrix.diagonal (fun j : ZMod d => (windowRoot d ^ j.val) ^ y))
/-- Pure-state linear stabilizer entropy `1 - d⁻¹ ∑_a |⟨ψ | D_a | ψ⟩|⁴` on `ℂ^d`. -/
def linearStabilizerEntropy {d : ℕ} [NeZero d] (ψ : ZMod d → ℂ) : ℝ :=
  1 - (d : ℝ)⁻¹ * ∑ a : ZMod d × ZMod d, ‖star ψ ⬝ᵥ (paperDisplacement d a *ᵥ ψ)‖ ^ 4
/-- Fourfold Kronecker tensor power `V^{⊗ 4}` of a rectangular matrix `V`. -/
def power4 {P Q : Type} (V : Matrix P Q ℂ) : Matrix (Fin 4 → P) (Fin 4 → Q) ℂ :=
  productMap (fun _ : Fin 4 => Q) (fun _ => V)
/-- Alternating fourfold tensor product `A ⊗ Aᴴ ⊗ A ⊗ Aᴴ`. -/
def alt {H : Type} (A : Matrix H H ℂ) : Matrix (Fin 4 → H) (Fin 4 → H) ℂ :=
  productMap (fun _ : Fin 4 => H) (![A, Aᴴ, A, Aᴴ] : Fin 4 → Matrix H H ℂ)
/-- Tensor-factor permutation matrix `T_σ` on `(ℂ^H)^{⊗ 4}` for `σ ∈ S_4`. -/
def T (H : Type) (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4 → H) (Fin 4 → H) ℂ := by
  classical exact Equiv.Perm.permMatrix ℂ (Equiv.arrowCongr σ.symm (Equiv.refl H))
/-- Projector `(1 / 24) ∑_{σ ∈ S_4} T_σ` onto the symmetric subspace of four tensor factors. -/
def symProjector4 (H : Type) [Fintype H] : Matrix (Fin 4 → H) (Fin 4 → H) ℂ :=
  (24 : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin 4), T H σ
/-- Closed-form Haar fourth-moment operator `binom(|H| + 3, 4)⁻¹ • symProjector4 H`. -/
def A4 (H : Type) [Fintype H] : Matrix (Fin 4 → H) (Fin 4 → H) ℂ :=
  (Nat.choose (Fintype.card H + 3) 4 : ℂ)⁻¹ • symProjector4 H
/-- Fourfold Weyl–Heisenberg stabilizer-entropy operator `d⁻² ∑_a (D_a ⊗ D_aᴴ)^{⊗ 2}`. -/
def Q (d : ℕ) [NeZero d] : Matrix (Fin 4 → ZMod d) (Fin 4 → ZMod d) ℂ :=
  ((d : ℂ) ^ 2)⁻¹ • ∑ a : ZMod d × ZMod d, alt (paperDisplacement d a)
/-- Fourth moment `tr(alt(Eᴴ D_a E) A4)` of one Weyl label compressed to an isometric frame `E`. -/
def labelFourthMoment {d : ℕ} [NeZero d] {S : Type} [Fintype S]
    (E : Matrix (ZMod d) S ℂ) (a : ZMod d × ZMod d) : ℂ :=
  Matrix.trace (alt (Eᴴ * paperDisplacement d a * E) * A4 S)
/-- Extrinsic average stabilizer-entropy score `d tr(Q_d E^{⊗ 4} A4 (E^{⊗ 4})ᴴ)`. -/
def extrinsicScore {d : ℕ} [NeZero d] {S : Type} [Fintype S] (E : Matrix (ZMod d) S ℂ) : ℂ :=
  (d : ℂ) * Matrix.trace (Q d * power4 E * A4 S * (power4 E)ᴴ)
/-- Single-qudit intrinsic average stabilizer-entropy term `k tr(Q_k A4)` on `ℂ^k`. -/
def intrinsicTerm (k : ℕ) [NeZero k] : ℂ := (k : ℂ) * Matrix.trace (Q k * A4 (ZMod k))
/-- Average linear stabilizer-entropy gap `intrinsicTerm |S| - extrinsicScore E`. -/
def aseGap {d : ℕ} [NeZero d] {S : Type} [Fintype S] [NeZero (Fintype.card S)]
    (E : Matrix (ZMod d) S ℂ) : ℂ := intrinsicTerm (Fintype.card S) - extrinsicScore E
/-- Algebraic fourfold symmetric Schur twirl `tr(Π_{sym^4} X) • A4 (ZMod d)`. -/
def symTwirl4 (d : ℕ) [NeZero d]
    (X : Matrix (Fin 4 → ZMod d) (Fin 4 → ZMod d) ℂ) : Matrix (Fin 4 → ZMod d) (Fin 4 → ZMod d) ℂ :=
  Matrix.trace (symProjector4 (ZMod d) * X) • A4 (ZMod d)

private def num4 {H : Type} [Fintype H] (A B : Matrix H H ℂ) : ℂ :=
  let t : Matrix H H ℂ → ℂ := Matrix.trace
  (t A) ^ 2 * (t B) ^ 2 + t (A * A) * (t B) ^ 2 + t (B * B) * (t A) ^ 2 +
    4 * t (A * B) * t A * t B + t (A * A) * t (B * B) + 2 * (t (A * B)) ^ 2 +
    4 * t (A * A * B) * t B + 4 * t (A * B * B) * t A +
    4 * t (A * A * B * B) + 2 * t (A * B * A * B)
private theorem tau_unit (d : ℕ) : tau d * star (tau d) = 1 := by
  unfold tau; rw [star_neg, neg_mul_neg]; change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]; simp [neg_div]
private theorem windowRoot_unit (d : ℕ) : windowRoot d * star (windowRoot d) = 1 := by
  unfold windowRoot; change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add, (by simp [map_ofNat]; ring :
    2 * (Real.pi : ℂ) * Complex.I / (d : ℂ) +
      (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) = 0), Complex.exp_zero]
private theorem tau_eq_windowRoot_pow {d : ℕ} [NeZero d] (hd : Odd d) :
    tau d = windowRoot d ^ ((d + 1) / 2) := by
  rcases hd with ⟨m, rfl⟩; rw [(by omega : (2 * m + 1 + 1) / 2 = m + 1)]
  unfold tau windowRoot; rw [← Complex.exp_nat_mul]
  have hd0 : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
  rw [(by field_simp; push_cast; ring :
    ((m + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((2 * m + 1 : ℕ) : ℂ)) =
      (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I / ((2 * m + 1 : ℕ) : ℂ)),
    Complex.exp_add, Complex.exp_pi_mul_I]; ring
private theorem zpow_eq_pow_zmod_val {G : Type} [Group G] {d : ℕ} [NeZero d]
    (g : G) (hg : g ^ d = 1) (z : ℤ) : g ^ z = g ^ (z : ZMod d).val := by
  conv_lhs => rw [← Int.emod_add_mul_ediv z (d : ℤ)]
  rw [zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, mul_one, ← ZMod.val_intCast (n := d) z,
    zpow_natCast]
private theorem zpow_eq_pow_zmod_val_complex {d : ℕ} [NeZero d]
    (ζ : ℂ) (h0 : ζ ≠ 0) (hd : ζ ^ d = 1) (z : ℤ) : ζ ^ z = ζ ^ (z : ZMod d).val := by
  let u : ℂˣ := Units.mk0 ζ h0
  simpa [u] using congrArg Units.val (zpow_eq_pow_zmod_val u (by ext; simpa [u] using hd) z)
private theorem intPaperDisplacement_nat (d : ℕ) [NeZero d] (x y : ℕ) :
    intPaperDisplacement d (x : ℤ) (y : ℤ) =
      tau d ^ (x * y) • (shiftMatrix d ^ x * clockMatrix d ^ y) := by
  unfold intPaperDisplacement
  have hshift : Matrix.permMatrixHom (n := ZMod d) (R := ℂ) ((shiftPerm d)⁻¹ ^ (x : ℤ)) =
      shiftMatrix d ^ x := by
    rw [zpow_natCast, map_pow, shiftMatrix_eq_permMatrix]; congr 1
  have hclock : Matrix.diagonal (fun j : ZMod d => (windowRoot d ^ j.val) ^ (y : ℤ)) =
      clockMatrix d ^ y := by rw [clockMatrix, Matrix.diagonal_pow]; congr 1
  rw [hshift, hclock, ← Nat.cast_mul, zpow_natCast]
private theorem intPaperDisplacement_eq_paperDisplacement {d : ℕ} [NeZero d]
    (hd : Odd d) (x y : ℤ) :
    intPaperDisplacement d x y = paperDisplacement d ((x : ZMod d), (y : ZMod d)) := by
  unfold intPaperDisplacement paperDisplacement displacement
  have htau_eq := tau_eq_windowRoot_pow hd
  have hw_ne : windowRoot d ≠ 0 := (windowRoot_isPrimitiveRoot d).ne_zero (NeZero.ne d)
  have htau_ne : tau d ≠ 0 := by rw [htau_eq]; exact pow_ne_zero _ hw_ne
  have htau_d : tau d ^ d = 1 := by
    rw [htau_eq, ← pow_mul, mul_comm, pow_mul, (windowRoot_isPrimitiveRoot d).pow_eq_one, one_pow]
  have htau_z : tau d ^ (x * y) = tau d ^ ((x : ZMod d).val * (y : ZMod d).val) := by
    rw [zpow_eq_pow_zmod_val_complex (tau d) htau_ne htau_d (x * y), Int.cast_mul x y, ZMod.val_mul]
    conv_rhs => rw [← Nat.mod_add_div ((x : ZMod d).val * (y : ZMod d).val) d]
    rw [pow_add, pow_mul, htau_d, one_pow, mul_one]
  have hperm_d : ((shiftPerm d)⁻¹) ^ d = 1 := by
    rw [inv_pow, (by ext i; rw [shiftPerm_pow_apply]; simp : shiftPerm d ^ d = 1), inv_one]
  have hshift_z : Matrix.permMatrixHom (n := ZMod d) (R := ℂ) ((shiftPerm d)⁻¹ ^ x) =
      shiftMatrix d ^ (x : ZMod d).val := by
    rw [zpow_eq_pow_zmod_val ((shiftPerm d)⁻¹) hperm_d x, map_pow, shiftMatrix_eq_permMatrix]
    congr 1
  have hclock_z : Matrix.diagonal (fun j : ZMod d => (windowRoot d ^ j.val) ^ y) =
      clockMatrix d ^ (y : ZMod d).val := by
    rw [clockMatrix, Matrix.diagonal_pow]; congr 1; funext j
    have hj_d : (windowRoot d ^ j.val) ^ d = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, (windowRoot_isPrimitiveRoot d).pow_eq_one, one_pow]
    exact zpow_eq_pow_zmod_val_complex _ (pow_ne_zero _ hw_ne) hj_d y
  rw [htau_z, hshift_z, hclock_z]
private theorem product4_mul {P Q R : Type} [Fintype Q]
    (M : Fin 4 → Matrix P Q ℂ) (N : Fin 4 → Matrix Q R ℂ) :
    productMap (fun _ : Fin 4 => R) (fun i => M i * N i) =
      productMap (fun _ : Fin 4 => Q) M * productMap (fun _ : Fin 4 => R) N := by
  ext x y; simp only [productMap, Matrix.mul_apply]; rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.prod_mul_distrib)
private theorem product4_adjoint {P Q : Type} (M : Fin 4 → Matrix P Q ℂ) :
    productMap (fun _ : Fin 4 => P) (fun i => (M i)ᴴ) = (productMap (fun _ : Fin 4 => Q) M)ᴴ := by
  ext x y; simp [productMap, Matrix.conjTranspose_apply]
private theorem product4_one (H : Type) [DecidableEq H] :
    productMap (fun _ : Fin 4 => H) (fun _ => (1 : Matrix H H ℂ)) = 1 := by
  ext x y; simp only [productMap, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have hex : ∃ i : Fin 4, x i ≠ y i := by
      by_contra hall; exact h (funext fun i => Classical.not_not.mp fun hne => hall ⟨i, hne⟩)
    rcases hex with ⟨i, hi⟩; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
private theorem alt_one (H : Type) [DecidableEq H] : alt (1 : Matrix H H ℂ) = 1 := by
  have hv : (![(1 : Matrix H H ℂ), (1 : Matrix H H ℂ)ᴴ, 1, (1 : Matrix H H ℂ)ᴴ] :
      Fin 4 → Matrix H H ℂ) = fun _ => 1 := by ext i : 1; fin_cases i <;> simp
  unfold alt; rw [hv, product4_one]
private theorem alt_phase {H : Type} (A : Matrix H H ℂ) (c : ℂ) (hc : c * star c = 1) :
    alt (c • A) = alt A := by
  ext x y
  simp only [alt, productMap, Fin.prod_univ_four, Matrix.conjTranspose_smul, Matrix.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  calc _ = (c * star c) ^ 2 * (A (x 0) (y 0) * Aᴴ (x 1) (y 1) * A (x 2) (y 2) * Aᴴ (x 3) (y 3)) :=
          by ring
    _ = _ := by rw [hc]; simp
private theorem alt_conj {P Q : Type} [Fintype P] (V : Matrix P Q ℂ) (D : Matrix P P ℂ) :
    alt (Vᴴ * D * V) = (power4 V)ᴴ * alt D * power4 V := by
  have hv : (![Vᴴ * D * V, (Vᴴ * D * V)ᴴ, Vᴴ * D * V, (Vᴴ * D * V)ᴴ] : Fin 4 → Matrix Q Q ℂ) =
      fun i => (Vᴴ * (![D, Dᴴ, D, Dᴴ] : Fin 4 → Matrix P P ℂ) i) * V := by
    ext i : 1; fin_cases i <;> simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold alt power4; rw [hv, product4_mul, product4_mul, product4_adjoint]
private theorem T_apply {H : Type} (σ : Equiv.Perm (Fin 4)) (x y : Fin 4 → H) :
    T H σ x y = by classical exact if x = y ∘ σ.symm then 1 else 0 := by
  classical
  simp only [T, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ← Equiv.eq_symm_apply]; rfl
private theorem perm_trace {H : Type} [Fintype H]
    (M : Fin 4 → Matrix H H ℂ) (σ : Equiv.Perm (Fin 4)) :
    Matrix.trace (productMap (fun _ : Fin 4 => H) M * T H σ) =
      ∑ x : Fin 4 → H, ∏ i, M i (x i) (x (σ.symm i)) := by
  classical simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, T_apply, productMap,
    mul_ite, Function.comp_def]

set_option maxHeartbeats 4000000 in
private theorem pair_cycle_sum {H : Type} [Fintype H] (A B : Matrix H H ℂ) :
    (∑ σ : Equiv.Perm (Fin 4),
      Matrix.trace (productMap (fun _ : Fin 4 => H) ![A, B, A, B] * T H σ)) = num4 A B := by
  classical
  let t : Matrix H H ℂ → ℂ := Matrix.trace
  let e : Fin 4 × Fin 3 × Fin 2 → Equiv.Perm (Fin 4) := fun z =>
    Equiv.swap 0 z.1 * Equiv.swap 1 ⟨z.2.1.val + 1, by omega⟩ *
      Equiv.swap 2 ⟨z.2.2.val + 2, by omega⟩
  have he : Function.Bijective e := by decide
  have hsum (p : Equiv.Perm (Fin 4)) (f : (Fin 4 → H) → ℂ) :
      (∑ x, f x) = ∑ i, ∑ j, ∑ k, ∑ l, f (![i, j, k, l] ∘ p) := by
    let q : (H × H × H × H) ≃ (Fin 4 → H) :=
      { toFun := fun z => ![z.1, z.2.1, z.2.2.1, z.2.2.2], invFun := fun x => (x 0, x 1, x 2, x 3)
        left_inv := by rintro ⟨i, j, k, l⟩; rfl
        right_inv := by intro x; ext i; fin_cases i <;> rfl }
    calc (∑ x, f x) = ∑ z : H × H × H × H, f (![z.1, z.2.1, z.2.2.1, z.2.2.2] ∘ p) :=
          ((q.trans (Equiv.arrowCongr p.symm (Equiv.refl H))).sum_comp f).symm
      _ = _ := by simp only [Fintype.sum_prod_type]
  let g : Fin 4 → Fin 3 → Fin 2 → ℂ :=
    ![![![(t A) ^ 2 * (t B) ^ 2, t (A * B) * t A * t B],
        ![t (A * B) * t A * t B, t (A * B * B) * t A],
        ![t (B * B) * (t A) ^ 2, t (A * B * B) * t A]],
      ![![t (A * B) * t A * t B, (t (A * B)) ^ 2], ![t (A * A * B) * t B, t (A * B * A * B)],
        ![t (A * B * B) * t A, t (A * A * B * B)]],
      ![![t (A * A) * (t B) ^ 2, t (A * A * B) * t B], ![t (A * A * B) * t B, t (A * A * B * B)],
        ![t (A * A) * t (B * B), t (A * A * B * B)]],
      ![![t (A * B) * t A * t B, t (A * A * B) * t B], ![(t (A * B)) ^ 2, t (A * A * B * B)],
        ![t (A * B * B) * t A, t (A * B * A * B)]]]
  let pVec : Fin 4 → Fin 3 → Fin 2 → Fin 4 → Fin 4 :=
    ![![![![3, 1, 2, 0], ![1, 0, 2, 3]], ![![1, 3, 2, 0], ![0, 3, 1, 2]],
        ![![1, 2, 0, 3], ![0, 2, 1, 3]]],
      ![![![2, 3, 1, 0], ![2, 3, 0, 1]], ![![1, 2, 3, 0], ![0, 1, 2, 3]],
        ![![1, 2, 0, 3], ![0, 1, 3, 2]]],
      ![![![2, 1, 3, 0], ![3, 0, 1, 2]], ![![3, 2, 1, 0], ![3, 2, 0, 1]],
        ![![2, 0, 3, 1], ![3, 1, 0, 2]]],
      ![![![2, 0, 1, 3], ![1, 0, 3, 2]], ![![2, 1, 0, 3], ![0, 2, 3, 1]],
        ![![1, 3, 0, 2], ![0, 3, 2, 1]]]]
  have hpBij : ∀ i j k, Function.Bijective (pVec i j k) := by decide
  have hfin (x : Fin 4) :
      x = if x.val = 0 then 0 else if x.val = 1 then 1 else if x.val = 2 then 2 else 3 := by
    revert x; decide
  have f42 : ∀ h, (⟨2, h⟩ : Fin 4) = 2 := fun _ => rfl
  have f43 : ∀ h, (⟨3, h⟩ : Fin 4) = 3 := fun _ => rfl
  have f32 : ∀ h, (⟨2, h⟩ : Fin 3) = 2 := fun _ => rfl
  have htable (i : Fin 4) (j : Fin 3) (k : Fin 2) :
      Matrix.trace (productMap (fun _ : Fin 4 => H) ![A, B, A, B] * T H (e (i, j, k))) =
        g i j k := by
    rw [perm_trace, hsum (Equiv.ofBijective (pVec i j k) (hpBij i j k))]
    simp only [Fin.prod_univ_four, Function.comp_apply, Equiv.ofBijective_apply]
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, f42, f43, f32]
      rw [hfin (pVec _ _ _ 0), hfin (pVec _ _ _ 1), hfin (pVec _ _ _ 2), hfin (pVec _ _ _ 3),
        hfin (pVec _ _ _ ((e _).symm 0)), hfin (pVec _ _ _ ((e _).symm 1)),
        hfin (pVec _ _ _ ((e _).symm 2)), hfin (pVec _ _ _ ((e _).symm 3))]
      dsimp only [pVec, e]; simp +decide only [↓reduceIte]; dsimp only [g, t]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.trace,
        Matrix.diag_apply, Matrix.mul_apply, pow_two, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      try ring
  rw [← he.sum_comp (fun σ => Matrix.trace (productMap (fun _ : Fin 4 => H) ![A, B, A, B] * T H σ))]
  simp only [Fintype.sum_prod_type, htable]; simp [g, num4, t, Fin.sum_univ_succ]; ring

private theorem trace_alt_mul_A4 {H : Type} [Fintype H] (A : Matrix H H ℂ) :
    Matrix.trace (alt A * A4 H) =
      (Nat.choose (Fintype.card H + 3) 4 : ℂ)⁻¹ * ((24 : ℂ)⁻¹ * num4 A Aᴴ) := by
  simp only [A4, symProjector4, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum,
    Matrix.trace_sum, smul_eq_mul, alt, pair_cycle_sum]
private theorem choose_add_three_four (n : ℕ) :
    24 * Nat.choose (n + 3) 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  have h := (Nat.descFactorial_eq_factorial_mul_choose (n + 3) 4).symm
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial,
    Nat.sub_zero, Nat.add_sub_cancel_right] at h
  rw [(by omega : n + 3 - 1 = n + 2), (by omega : n + 3 - 2 = n + 1)] at h
  dsimp at h; linear_combination h
private theorem hermitian_fourth_moment_poly {H : Type} [Fintype H] [DecidableEq H]
    (A : Matrix H H ℂ) (hA : Aᴴ = A) :
    ((Fintype.card H : ℂ) * ((Fintype.card H : ℂ) + 1) *
      ((Fintype.card H : ℂ) + 2) * ((Fintype.card H : ℂ) + 3)) * Matrix.trace (alt A * A4 H) =
      (Matrix.trace A) ^ 4 + 6 * (Matrix.trace A) ^ 2 * Matrix.trace (A ^ 2) +
        3 * (Matrix.trace (A ^ 2)) ^ 2 + 8 * Matrix.trace A * Matrix.trace (A ^ 3) +
        6 * Matrix.trace (A ^ 4) := by
  by_cases hn : Fintype.card H = 0
  · have hEmpty : IsEmpty H := Fintype.card_eq_zero_iff.mp hn; rw [hn]; simp [Matrix.trace]
  · rw [trace_alt_mul_A4, hA]
    have hchoose_nat := choose_add_three_four (Fintype.card H)
    have hprod_pos : 0 < Fintype.card H * (Fintype.card H + 1) *
        (Fintype.card H + 2) * (Fintype.card H + 3) := by
      have hp : 0 < Fintype.card H := Nat.pos_of_ne_zero hn; positivity
    have hchoose_ne : (Nat.choose (Fintype.card H + 3) 4 : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : Nat.choose (Fintype.card H + 3) 4 ≠ 0)
    have hchoose_c : ((Fintype.card H : ℂ) * ((Fintype.card H : ℂ) + 1) *
        ((Fintype.card H : ℂ) + 2) * ((Fintype.card H : ℂ) + 3)) =
        (24 : ℂ) * (Nat.choose (Fintype.card H + 3) 4 : ℂ) := by exact_mod_cast hchoose_nat.symm
    rw [hchoose_c, (by field_simp [hchoose_ne] :
      ((24 : ℂ) * (Nat.choose (Fintype.card H + 3) 4 : ℂ)) *
        ((Nat.choose (Fintype.card H + 3) 4 : ℂ)⁻¹ * ((24 : ℂ)⁻¹ * num4 A A)) = num4 A A)]
    have hp3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
    rw [sq A, hp3, (by rw [pow_succ, hp3] : A ^ 4 = A * A * A * A)]; unfold num4; ring
private theorem labelFourthMoment_eq_trace_frame {d : ℕ} [NeZero d] {S : Type} [Fintype S]
    (E : Matrix (ZMod d) S ℂ) (a : ZMod d × ZMod d) :
    labelFourthMoment E a =
      Matrix.trace (alt (paperDisplacement d a) * (power4 E * A4 S * (power4 E)ᴴ)) := by
  unfold labelFourthMoment
  rw [alt_conj, Matrix.mul_assoc ((power4 E)ᴴ),
    Matrix.trace_mul_comm ((power4 E)ᴴ * (alt (paperDisplacement d a) * power4 E)),
    (by simp [Matrix.mul_assoc] : A4 S * ((power4 E)ᴴ * (alt (paperDisplacement d a) * power4 E)) =
      (A4 S * (power4 E)ᴴ) * (alt (paperDisplacement d a) * power4 E)),
    Matrix.trace_mul_comm (A4 S * (power4 E)ᴴ)]; simp [Matrix.mul_assoc]
private theorem extrinsicScore_eq_sum {d : ℕ} [NeZero d] {S : Type} [Fintype S]
    (E : Matrix (ZMod d) S ℂ) :
    extrinsicScore E = (d : ℂ)⁻¹ * ∑ a : ZMod d × ZMod d, labelFourthMoment E a := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold extrinsicScore Q
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.sum_mul, Matrix.sum_mul, Matrix.sum_mul, Matrix.trace_sum]
  have hterm (a : ZMod d × ZMod d) :
      Matrix.trace (alt (paperDisplacement d a) * power4 E * A4 S * (power4 E)ᴴ) =
        labelFourthMoment E a := by rw [labelFourthMoment_eq_trace_frame]; simp [Matrix.mul_assoc]
  simp_rw [hterm]; field_simp [hd0]

/-- Odd-dimension phase periodicity of integer-labeled Weyl–Heisenberg operators, unimodular phase
cancellation in compressed fourth moments, and the five-term cycle-trace fourth-moment polynomial
for Hermitian matrices. -/
theorem fourth_moment_cycle_and_hermitian_formula (d : ℕ) [NeZero d] {S : Type} [Fintype S] :
    (Odd d → tau d = windowRoot d ^ ((d + 1) / 2)) ∧
    (∀ x y : ℕ, intPaperDisplacement d (x : ℤ) (y : ℤ) =
      tau d ^ (x * y) • (shiftMatrix d ^ x * clockMatrix d ^ y)) ∧
    (Odd d → ∀ x y : ℤ,
      intPaperDisplacement d x y = paperDisplacement d ((x : ZMod d), (y : ZMod d))) ∧
    (Odd d → ∀ x y : ℕ, tau d ^ (x * y) • (shiftMatrix d ^ x * clockMatrix d ^ y) =
      paperDisplacement d ((x : ZMod d), (y : ZMod d))) ∧
    (∀ (E : Matrix (ZMod d) S ℂ) (a : ZMod d × ZMod d),
      labelFourthMoment E a = Matrix.trace (alt (Eᴴ * displacement d a.1 a.2 * E) * A4 S)) ∧
    (∀ (E : Matrix (ZMod d) S ℂ),
      extrinsicScore E = (d : ℂ)⁻¹ * ∑ a : ZMod d × ZMod d, labelFourthMoment E a) ∧
    (∀ {H : Type} [Fintype H] [DecidableEq H] (A : Matrix H H ℂ), Aᴴ = A →
      ((Fintype.card H : ℂ) * ((Fintype.card H : ℂ) + 1) *
        ((Fintype.card H : ℂ) + 2) * ((Fintype.card H : ℂ) + 3)) * Matrix.trace (alt A * A4 H) =
        (Matrix.trace A) ^ 4 + 6 * (Matrix.trace A) ^ 2 * Matrix.trace (A ^ 2) +
          3 * (Matrix.trace (A ^ 2)) ^ 2 + 8 * Matrix.trace A * Matrix.trace (A ^ 3) +
          6 * Matrix.trace (A ^ 4)) := by
  refine ⟨tau_eq_windowRoot_pow, intPaperDisplacement_nat d,
    intPaperDisplacement_eq_paperDisplacement, ?_, ?_, extrinsicScore_eq_sum,
    fun {_} _ _ A hA => hermitian_fourth_moment_poly A hA⟩
  · intro hd x y
    simpa [intPaperDisplacement_nat d x y] using
      intPaperDisplacement_eq_paperDisplacement hd (x : ℤ) (y : ℤ)
  · intro E a; unfold labelFourthMoment paperDisplacement
    have hc : tau d ^ (a.1.val * a.2.val) * star (tau d ^ (a.1.val * a.2.val)) = 1 := by
      rw [star_pow, ← mul_pow, tau_unit, one_pow]
    rw [Matrix.mul_smul, Matrix.smul_mul, alt_phase _ _ hc]

private theorem displacement_unitary_pair {k : ℕ} [NeZero k] (p q : ZMod k) :
    (displacement k p q)ᴴ * displacement k p q = 1 ∧
      displacement k p q * (displacement k p q)ᴴ = 1 := by
  have hleft : star (displacement k p q) * displacement k p q = 1 := by
    rw [displacement_adjoint, Matrix.smul_mul, displacement_mul, smul_smul]
    have hphase : windowRoot k ^ (p * q).val * windowRoot k ^ (-q * p).val = 1 := by
      rw [← windowRoot_pow_val_add, (by ring : p * q + -q * p = 0)]; simp
    rw [hphase, (by ring : (-p + p : ZMod k) = 0), (by ring : (-q + q : ZMod k) = 0),
      one_smul, displacement_zero]
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

private theorem displacement_num4 {k : ℕ} [NeZero k] (p q : ZMod k) :
    num4 (displacement k p q) (displacement k p q)ᴴ =
      (if p = 0 ∧ q = 0 then (k : ℂ) ^ 4 + 6 * (k : ℂ) ^ 3 + 8 * (k : ℂ) ^ 2 else 0) +
      (if p + p = 0 ∧ q + q = 0 then (k : ℂ) ^ 2 else 0) + (2 * (k : ℂ) ^ 2 + 6 * (k : ℂ)) := by
  set A := displacement k p q; set B := Aᴴ
  obtain ⟨hBA, hAB⟩ := displacement_unitary_pair p q
  have hAAB : A * A * B = A := by rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
  have hABB : A * B * B = B := by rw [hAB, Matrix.one_mul]
  have hABAB : A * B * A * B = 1 := by rw [hAB, Matrix.one_mul, hAB]
  have ht1 : Matrix.trace (1 : Matrix (ZMod k) (ZMod k) ℂ) = (k : ℂ) := by simp [ZMod.card]
  have htA : Matrix.trace A = if p = 0 ∧ q = 0 then (k : ℂ) else 0 := displacement_trace p q
  have htB : Matrix.trace B = if p = 0 ∧ q = 0 then (k : ℂ) else 0 := by
    change Matrix.trace Aᴴ = _; rw [Matrix.trace_conjTranspose, htA]; split_ifs <;> simp
  have htorsion : Matrix.trace (A * A) * Matrix.trace (B * B) =
      if p + p = 0 ∧ q + q = 0 then (k : ℂ) ^ 2 else 0 := by
    by_cases ht : p + p = 0 ∧ q + q = 0
    · simp only [ht, and_self, ↓reduceIte]
      have hstarA : Aᴴ = windowRoot k ^ (p * q).val • A :=
        star_displacement_of_two_torsion p q ht.1 ht.2
      have h1 : windowRoot k ^ (p * q).val * Matrix.trace (A * A) = (k : ℂ) := by
        have hm : windowRoot k ^ (p * q).val • (A * A) = 1 := by
          have hb : Aᴴ * A = 1 := hBA; rw [hstarA, Matrix.smul_mul] at hb; exact hb
        simpa [Matrix.trace_smul, smul_eq_mul, ht1] using congrArg Matrix.trace hm
      have hBB : Matrix.trace (B * B) = star (Matrix.trace (A * A)) := by
        rw [(by simp [B, Matrix.conjTranspose_mul] : B * B = (A * A)ᴴ), Matrix.trace_conjTranspose]
      have h2' : star (windowRoot k ^ (p * q).val) * Matrix.trace (B * B) = (k : ℂ) := by
        have h2 := congrArg star h1; rw [star_mul, ← hBB, mul_comm] at h2; simpa using h2
      have hw : windowRoot k ^ (p * q).val * star (windowRoot k ^ (p * q).val) = 1 := by
        rw [star_pow, ← mul_pow, windowRoot_unit, one_pow]
      calc Matrix.trace (A * A) * Matrix.trace (B * B) =
            (windowRoot k ^ (p * q).val * star (windowRoot k ^ (p * q).val)) *
              (Matrix.trace (A * A) * Matrix.trace (B * B)) := by rw [hw, one_mul]
        _ = (windowRoot k ^ (p * q).val * Matrix.trace (A * A)) *
              (star (windowRoot k ^ (p * q).val) * Matrix.trace (B * B)) := by ring
        _ = (k : ℂ) ^ 2 := by rw [h1, h2']; ring
    · simp only [ht, ↓reduceIte]
      have hAA0 : Matrix.trace (A * A) = 0 := by
        change Matrix.trace (displacement k p q * displacement k p q) = 0
        rw [displacement_mul, Matrix.trace_smul, smul_eq_mul,
          displacement_trace_eq_zero (p + p) (q + q) ht, mul_zero]
      rw [hAA0, zero_mul]
  dsimp only [num4]; rw [hAAB, hABB, hABAB, hAB, ht1, htorsion]
  by_cases h0 : p = 0 ∧ q = 0
  · rcases h0 with ⟨hp0, hq0⟩; have hA1 : A = 1 := by simp [A, hp0, hq0]
    simp [hp0, hq0, hA1, (by simp [B, hA1] : B = 1), ht1]; ring
  · rw [htA, htB]; simp only [h0, ↓reduceIte]; ring

private theorem card_two_torsion_zmod {k : ℕ} [NeZero k] :
    (Finset.univ.filter (fun x : ZMod k => x + x = 0)).card = if Odd k then 1 else 2 := by
  have hchar (x : ZMod k) : x + x = 0 ↔ x.val + x.val = 0 ∨ x.val + x.val = k := by
    rw [← ZMod.val_eq_zero, ZMod.val_add]; have hx : x.val < k := ZMod.val_lt x
    by_cases hlt : x.val + x.val < k
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  by_cases hk : Odd k
  · simp only [hk, ↓reduceIte]
    have hset : Finset.univ.filter (fun x : ZMod k => x + x = 0) = {0} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hchar]
      rcases hk with ⟨m, rfl⟩; rw [← ZMod.val_eq_zero]; omega
    rw [hset, Finset.card_singleton]
  · simp only [hk, ↓reduceIte]; rcases Nat.not_odd_iff_even.mp hk with ⟨m, rfl⟩
    have hm_pos : 0 < m := by have := NeZero.ne (m + m); omega
    have hm_val : ((m : ℕ) : ZMod (m + m)).val = m := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
    have hne : (0 : ZMod (m + m)) ≠ (m : ZMod (m + m)) := by
      intro h; have hv := congrArg ZMod.val h; simp [hm_val] at hv; omega
    have hset : Finset.univ.filter (fun x : ZMod (m + m) => x + x = 0) =
        {0, (m : ZMod (m + m))} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, hchar]
      refine ⟨fun hx => hx.elim (fun h => Or.inl ((ZMod.val_eq_zero x).mp (by omega)))
        (fun h => Or.inr (ZMod.val_injective (m + m) (by rw [hm_val]; omega))), ?_⟩
      rintro (rfl | rfl); · exact Or.inl (by simp)
      · exact Or.inr (by rw [hm_val])
    rw [hset, Finset.card_pair hne]

private theorem intrinsicTerm_closed_forms (k : ℕ) [NeZero k] :
    (Odd k → intrinsicTerm k = (3 : ℂ) / ((k : ℂ) + 2)) ∧
      (Even k → intrinsicTerm k = (3 * ((k : ℂ) + 2)) / (((k : ℂ) + 1) * ((k : ℂ) + 3))) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have hk2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
  have hk3 : ((k : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : k + 3 ≠ 0)
  have hinv : (Nat.choose (k + 3) 4 : ℂ)⁻¹ * (24 : ℂ)⁻¹ =
      ((k : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) * ((k : ℂ) + 3))⁻¹ := by
    rw [← mul_inv, mul_comm, (by exact_mod_cast choose_add_three_four k :
      (24 : ℂ) * (Nat.choose (k + 3) 4 : ℂ) =
        (k : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) * ((k : ℂ) + 3))]
  have hsum_origin : (∑ a : ZMod k × ZMod k,
      if a.1 = 0 ∧ a.2 = 0 then (k : ℂ) ^ 4 + 6 * (k : ℂ) ^ 3 + 8 * (k : ℂ) ^ 2 else 0) =
      (k : ℂ) ^ 4 + 6 * (k : ℂ) ^ 3 + 8 * (k : ℂ) ^ 2 := by
    have hcond : ∀ a : ZMod k × ZMod k, (a.1 = 0 ∧ a.2 = 0) ↔ a = (0, 0) := by
      rintro ⟨p, q⟩; simp [Prod.ext_iff]
    simp_rw [hcond]; simp
  let S2 : Finset (ZMod k) := Finset.univ.filter (fun x : ZMod k => x + x = 0)
  have hsum_torsion : (∑ a : ZMod k × ZMod k,
      if a.1 + a.1 = 0 ∧ a.2 + a.2 = 0 then (k : ℂ) ^ 2 else 0) =
      ((S2.card : ℂ) ^ 2) * (k : ℂ) ^ 2 := by
    rw [← Finset.sum_filter, (by ext ⟨p, q⟩; simp [S2] :
      Finset.univ.filter (fun a : ZMod k × ZMod k => a.1 + a.1 = 0 ∧ a.2 + a.2 = 0) = S2 ×ˢ S2),
      Finset.sum_const, Finset.card_product]; simp [nsmul_eq_mul, sq]
  have hsum_const : (∑ _a : ZMod k × ZMod k, (2 * (k : ℂ) ^ 2 + 6 * (k : ℂ))) =
      (k : ℂ) ^ 2 * (2 * (k : ℂ) ^ 2 + 6 * (k : ℂ)) := by simp [ZMod.card, nsmul_eq_mul, sq]; ring
  have hint : intrinsicTerm k =
      ((k : ℂ) ^ 2 * ((k : ℂ) + 1) * ((k : ℂ) + 2) * ((k : ℂ) + 3))⁻¹ *
        ((3 * (k : ℂ) ^ 4 + 12 * (k : ℂ) ^ 3 + 8 * (k : ℂ) ^ 2) +
          ((S2.card : ℂ) ^ 2) * (k : ℂ) ^ 2) := by
    unfold intrinsicTerm Q
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.sum_mul, Matrix.trace_sum]
    have hterm (a : ZMod k × ZMod k) :
        Matrix.trace (alt (paperDisplacement k a) * A4 (ZMod k)) =
          ((k : ℂ) * ((k : ℂ) + 1) * ((k : ℂ) + 2) * ((k : ℂ) + 3))⁻¹ *
            num4 (displacement k a.1 a.2) (displacement k a.1 a.2)ᴴ := by
      unfold paperDisplacement
      have hc : tau k ^ (a.1.val * a.2.val) * star (tau k ^ (a.1.val * a.2.val)) = 1 := by
        rw [star_pow, ← mul_pow, tau_unit, one_pow]
      rw [alt_phase _ _ hc, trace_alt_mul_A4]; simp only [ZMod.card]; rw [← mul_assoc, hinv]
    simp_rw [hterm, ← Finset.mul_sum, displacement_num4]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_origin, hsum_torsion, hsum_const]
    field_simp [hk0, hk1, hk2, hk3]; ring
  have hS2 : S2.card = if Odd k then 1 else 2 := card_two_torsion_zmod
  refine ⟨fun hodd => ?_, fun heven => ?_⟩
  · rw [hint, hS2]; simp only [hodd, ↓reduceIte]; field_simp [hk0, hk1, hk2, hk3]; ring
  · have hno : ¬ Odd k := Nat.not_odd_iff_even.mpr heven
    rw [hint, hS2]; simp only [hno, ↓reduceIte]; field_simp [hk0, hk1, hk2, hk3]; ring

private theorem trace_productMap4 {H : Type} [Fintype H] (M : Fin 4 → Matrix H H ℂ) :
    Matrix.trace (productMap (fun _ : Fin 4 => H) M) = ∏ r : Fin 4, Matrix.trace (M r) := by
  simp only [Matrix.trace, Matrix.diag_apply, productMap]
  exact (Fintype.prod_sum (fun r j => M r j j)).symm
private theorem pure_state_entropy_representations {d : ℕ} [NeZero d] (ψ : ZMod d → ℂ) :
    let ρ := Matrix.vecMulVec ψ (star ψ)
    (linearStabilizerEntropy ψ : ℂ) = 1 - (d : ℂ)⁻¹ *
      ∑ a : ZMod d × ZMod d, (‖Matrix.trace ((paperDisplacement d a)ᴴ * ρ)‖ ^ 4 : ℂ) ∧
    (linearStabilizerEntropy ψ : ℂ) = 1 - (d : ℂ) * Matrix.trace (Q d * power4 ρ) := by
  intro ρ; have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hrho_adj : ρᴴ = ρ := by ext i j; simp [ρ, Matrix.vecMulVec_apply, mul_comm]
  have htr_mul (D : Matrix (ZMod d) (ZMod d) ℂ) : Matrix.trace (D * ρ) = star ψ ⬝ᵥ (D *ᵥ ψ) := by
    simp only [ρ, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply]
    apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have htr_adj (D : Matrix (ZMod d) (ZMod d) ℂ) :
      Matrix.trace (Dᴴ * ρ) = star (star ψ ⬝ᵥ (D *ᵥ ψ)) := by
    rw [(by rw [Matrix.conjTranspose_mul, hrho_adj] : Dᴴ * ρ = (ρ * D)ᴴ),
      Matrix.trace_conjTranspose, Matrix.trace_mul_comm, htr_mul]
  refine ⟨?_, ?_⟩
  · unfold linearStabilizerEntropy; push_cast; congr 2
    apply Finset.sum_congr rfl; intro a _; rw [htr_adj, norm_star]
  · unfold linearStabilizerEntropy Q; push_cast
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.sum_mul, Matrix.trace_sum]
    have halt_rho (D : Matrix (ZMod d) (ZMod d) ℂ) :
        Matrix.trace (alt D * power4 ρ) = (‖star ψ ⬝ᵥ (D *ᵥ ψ)‖ ^ 4 : ℂ) := by
      unfold alt power4; rw [← product4_mul, trace_productMap4, Fin.prod_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [htr_adj, htr_mul]
      set z := star ψ ⬝ᵥ (D *ᵥ ψ)
      have hzz : z * star z = ((‖z‖ : ℂ) ^ 2) := by
        simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj z
      calc z * star z * z * star z = (z * star z) * (z * star z) := by ring
        _ = (‖z‖ ^ 4 : ℂ) := by rw [hzz]; ring
    simp_rw [halt_rho]; field_simp [hd0]

/-- Single-qudit odd-dimension and even-dimension intrinsic closed forms, trace and fourfold-tensor
representations of pure-state linear stabilizer entropy, and equality between the subspace gap and
pure-state linear stabilizer entropy on every one-dimensional subspace. -/
theorem intrinsic_term_and_rank_one_entropy (d : ℕ) [NeZero d] :
    (∀ (k : ℕ) [NeZero k],
      (Odd k → intrinsicTerm k = (3 : ℂ) / ((k : ℂ) + 2)) ∧
      (Even k → intrinsicTerm k = (3 * ((k : ℂ) + 2)) / (((k : ℂ) + 1) * ((k : ℂ) + 3)))) ∧
    intrinsicTerm 1 = 1 ∧
    (∀ (ψ : ZMod d → ℂ), star ψ ⬝ᵥ ψ = 1 →
      let ρ := Matrix.vecMulVec ψ (star ψ)
      (linearStabilizerEntropy ψ : ℂ) = 1 - (d : ℂ)⁻¹ *
        ∑ a : ZMod d × ZMod d, (‖Matrix.trace ((paperDisplacement d a)ᴴ * ρ)‖ ^ 4 : ℂ) ∧
      (linearStabilizerEntropy ψ : ℂ) = 1 - (d : ℂ) * Matrix.trace (Q d * power4 ρ)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [Unique S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ),
      Eᴴ * E = 1 → aseGap E = (linearStabilizerEntropy (fun j => E j default) : ℂ)) := by
  have hint1 : intrinsicTerm 1 = 1 := by
    have h := (intrinsicTerm_closed_forms 1).1 odd_one; norm_num at h ⊢; exact h
  refine ⟨fun k _ => intrinsicTerm_closed_forms k, hint1,
    fun ψ _ => pure_state_entropy_representations ψ, ?_⟩
  intro S _ _ _ _ E _
  let ψ : ZMod d → ℂ := fun j => E j default
  let ρ : Matrix (ZMod d) (ZMod d) ℂ := Matrix.vecMulVec ψ (star ψ)
  have hcard : Fintype.card S = 1 := Fintype.card_unique
  have hintS : intrinsicTerm (Fintype.card S) = 1 := by
    rw [(intrinsicTerm_closed_forms (Fintype.card S)).1 (by rw [hcard]; exact odd_one), hcard]
    norm_num
  have hA4_entry (u v : Fin 4 → S) : A4 S u v = 1 := by
    simp only [A4, symProjector4, hcard, Matrix.smul_apply, Matrix.sum_apply, T_apply,
      eq_iff_true_of_subsingleton, ↓reduceIte, smul_eq_mul]; norm_num [Fintype.card_perm]
  have hframe : power4 E * A4 S * (power4 E)ᴴ = power4 ρ := by
    have huniv : (Finset.univ : Finset (Fin 4 → S)) = {fun _ => default} := by
      ext z; simp [Subsingleton.elim z (fun _ => default)]
    ext x y
    simp only [Matrix.mul_apply, huniv, Finset.sum_singleton, hA4_entry, mul_one,
      Matrix.conjTranspose_apply, power4, productMap, ρ, Matrix.vecMulVec_apply, Pi.star_apply,
      star_prod, ← Finset.prod_mul_distrib]; rfl
  unfold aseGap extrinsicScore
  rw [hintS, (by simp [Matrix.mul_assoc] :
    Q d * power4 E * A4 S * (power4 E)ᴴ = Q d * (power4 E * A4 S * (power4 E)ᴴ)), hframe]
  exact (pure_state_entropy_representations ψ).2.symm

private theorem power4_intertwine_T {P R : Type} [Fintype P] [Fintype R]
    (V : Matrix P R ℂ) (σ : Equiv.Perm (Fin 4)) : power4 V * T R σ = T P σ * power4 V := by
  classical
  ext x y; simp only [Matrix.mul_apply, T_apply, power4, productMap, mul_ite, ite_mul,
    mul_one, mul_zero, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (y ∘ σ.symm)]
  simp only [Finset.mem_univ, ↓reduceIte, Function.comp_apply]
  have hiff : ∀ w : Fin 4 → P, (x = w ∘ σ.symm) ↔ (x ∘ σ = w) := fun w =>
    ⟨fun h => by subst h; ext r; simp, fun h => by subst h; ext r; simp⟩
  simp_rw [hiff]; rw [Finset.sum_ite_eq Finset.univ (x ∘ σ)]
  simp only [Finset.mem_univ, ↓reduceIte, Function.comp_apply]
  simpa only [Equiv.apply_symm_apply] using (Equiv.prod_comp σ.symm (fun i => V (x (σ i)) (y i)))
private theorem power4_symProjector4 {P R : Type} [Fintype P] [Fintype R]
    (V : Matrix P R ℂ) : power4 V * symProjector4 R = symProjector4 P * power4 V := by
  unfold symProjector4; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  exact congrArg ((24 : ℂ)⁻¹ • ·) (Finset.sum_congr rfl fun σ _ => power4_intertwine_T V σ)
private theorem T_mul {H : Type} [Fintype H] (σ τ : Equiv.Perm (Fin 4)) :
    T H σ * T H τ = T H (σ * τ) := by
  classical
  ext x z; simp only [Matrix.mul_apply, T_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (z ∘ τ.symm)]; simp only [Finset.mem_univ, ↓reduceIte]; congr 1
private theorem symProjector4_idem (H : Type) [Fintype H] :
    symProjector4 H * symProjector4 H = symProjector4 H := by
  unfold symProjector4; rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_sum]
  have hcol (τ : Equiv.Perm (Fin 4)) :
      (∑ σ : Equiv.Perm (Fin 4), T H σ) * T H τ = ∑ σ : Equiv.Perm (Fin 4), T H σ := by
    rw [Matrix.sum_mul]; simp_rw [T_mul]; exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => T H σ)
  simp_rw [hcol]; rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num [Fintype.card_perm]
private theorem trace_A4 (H : Type) [Fintype H] [NeZero (Fintype.card H)] :
    Matrix.trace (A4 H) = 1 := by
  classical
  have hpoly := hermitian_fourth_moment_poly (1 : Matrix H H ℂ) Matrix.conjTranspose_one
  rw [alt_one, Matrix.one_mul] at hpoly
  have ht1 : Matrix.trace (1 : Matrix H H ℂ) = (Fintype.card H : ℂ) := by simp
  simp only [one_pow, ht1] at hpoly
  have hn0 : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne (Fintype.card H)
  have h1' : ((Fintype.card H : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : Fintype.card H + 1 ≠ 0)
  have h2' : ((Fintype.card H : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : Fintype.card H + 2 ≠ 0)
  have h3' : ((Fintype.card H : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : Fintype.card H + 3 ≠ 0)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hn0 h1') h2') h3'); rw [hpoly]; ring
private theorem isometry_mul_proj_of_range_le {d : ℕ} [NeZero d]
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (EA : Matrix (ZMod d) A ℂ) (EB : Matrix (ZMod d) B ℂ)
    (hEB : EBᴴ * EB = 1) (hle : LinearMap.range EA.mulVecLin ≤ LinearMap.range EB.mulVecLin) :
    (EB * EBᴴ) * (EA * EAᴴ) = EA * EAᴴ := by
  apply Matrix.ext_of_mulVec_single; intro j
  rcases hle ⟨EAᴴ *ᵥ Pi.single j 1, Matrix.mulVec_mulVec (Pi.single j 1) EA EAᴴ⟩ with ⟨u, hu⟩
  change ((EB * EBᴴ) * (EA * EAᴴ)) *ᵥ Pi.single j 1 = (EA * EAᴴ) *ᵥ Pi.single j 1
  rw [← Matrix.mulVec_mulVec, ← hu]; change (EB * EBᴴ) *ᵥ (EB *ᵥ u) = EB *ᵥ u
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hEB, Matrix.mul_one]
private theorem isometry_range_iff_projector {d : ℕ} [NeZero d]
    {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    (E₁ : Matrix (ZMod d) S₁ ℂ) (E₂ : Matrix (ZMod d) S₂ ℂ)
    (hE₁ : E₁ᴴ * E₁ = 1) (hE₂ : E₂ᴴ * E₂ = 1) :
    LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin ↔ E₁ * E₁ᴴ = E₂ * E₂ᴴ := by
  refine ⟨fun hrange => ?_, fun hproj => le_antisymm ?_ ?_⟩
  · have hproj12 := isometry_mul_proj_of_range_le E₁ E₂ hE₂ (le_of_eq hrange)
    have hproj21 := isometry_mul_proj_of_range_le E₂ E₁ hE₁ (le_of_eq hrange.symm)
    have hadj := congrArg Matrix.conjTranspose hproj12
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hadj
    exact hadj.symm.trans hproj21
  · rintro _ ⟨u, rfl⟩; refine ⟨E₂ᴴ *ᵥ (E₁ *ᵥ u), ?_⟩
    change E₂ *ᵥ (E₂ᴴ *ᵥ (E₁ *ᵥ u)) = E₁ *ᵥ u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hproj, Matrix.mul_assoc, hE₁, Matrix.mul_one]
  · rintro _ ⟨u, rfl⟩; refine ⟨E₁ᴴ *ᵥ (E₂ *ᵥ u), ?_⟩
    change E₁ *ᵥ (E₁ᴴ *ᵥ (E₂ *ᵥ u)) = E₂ *ᵥ u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hproj, Matrix.mul_assoc, hE₂, Matrix.mul_one]
private theorem isometry_projector_invariance {d : ℕ} [NeZero d]
    {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
    (E₁ : Matrix (ZMod d) S₁ ℂ) (E₂ : Matrix (ZMod d) S₂ ℂ)
    (hE₁ : E₁ᴴ * E₁ = 1) (hE₂ : E₂ᴴ * E₂ = 1) (hproj : E₁ * E₁ᴴ = E₂ * E₂ᴴ) :
    Fintype.card S₁ = Fintype.card S₂ ∧
      (∀ a : ZMod d × ZMod d, labelFourthMoment E₁ a = labelFourthMoment E₂ a) ∧
      extrinsicScore E₁ = extrinsicScore E₂ := by
  have hcard : Fintype.card S₁ = Fintype.card S₂ := by
    apply Nat.cast_injective (R := ℂ)
    calc (Fintype.card S₁ : ℂ) = Matrix.trace (1 : Matrix S₁ S₁ ℂ) := by simp
      _ = Matrix.trace (E₁ᴴ * E₁) := by rw [hE₁]
      _ = Matrix.trace (E₁ * E₁ᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E₂ * E₂ᴴ) := by rw [hproj]
      _ = Matrix.trace (E₂ᴴ * E₂) := Matrix.trace_mul_comm _ _
      _ = (Fintype.card S₂ : ℂ) := by rw [hE₂]; simp
  have hframe : power4 E₁ * A4 S₁ * (power4 E₁)ᴴ = power4 E₂ * A4 S₂ * (power4 E₂)ᴴ := by
    have hf {S : Type} [Fintype S] (E : Matrix (ZMod d) S ℂ) :
        power4 E * A4 S * (power4 E)ᴴ = (Nat.choose (Fintype.card S + 3) 4 : ℂ)⁻¹ •
          (symProjector4 (ZMod d) * power4 (E * Eᴴ)) := by
      unfold A4; rw [Matrix.mul_smul, Matrix.smul_mul, power4_symProjector4, Matrix.mul_assoc]
      congr 2; unfold power4; rw [← product4_adjoint, ← product4_mul]
    rw [hf E₁, hf E₂, hcard, hproj]
  have hmom (a : ZMod d × ZMod d) : labelFourthMoment E₁ a = labelFourthMoment E₂ a := by
    rw [labelFourthMoment_eq_trace_frame E₁, labelFourthMoment_eq_trace_frame E₂, hframe]
  exact ⟨hcard, hmom, by rw [extrinsicScore_eq_sum E₁, extrinsicScore_eq_sum E₂]; simp_rw [hmom]⟩

/-- Independence of compressed label moments, extrinsic score, and average stabilizer-entropy gap
from the choice of isometric basis of a subspace, origin normalization and unitary symmetry
invariance of label moments, and the fourfold symmetric Schur-twirl identity recovering the ambient
intrinsic term. -/
theorem subspace_gap_isometry_invariance_and_twirl (d : ℕ) [NeZero d] :
    (∀ {S₁ S₂ : Type} [Fintype S₁] [Fintype S₂] [DecidableEq S₁] [DecidableEq S₂]
        [NeZero (Fintype.card S₁)] [NeZero (Fintype.card S₂)]
        (E₁ : Matrix (ZMod d) S₁ ℂ) (E₂ : Matrix (ZMod d) S₂ ℂ),
      E₁ᴴ * E₁ = 1 → E₂ᴴ * E₂ = 1 →
        (LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin ↔ E₁ * E₁ᴴ = E₂ * E₂ᴴ) ∧
        (LinearMap.range E₁.mulVecLin = LinearMap.range E₂.mulVecLin →
          Fintype.card S₁ = Fintype.card S₂ ∧
          (∀ a : ZMod d × ZMod d, labelFourthMoment E₁ a = labelFourthMoment E₂ a) ∧
          extrinsicScore E₁ = extrinsicScore E₂ ∧ aseGap E₁ = aseGap E₂)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      labelFourthMoment E (0, 0) = 1 ∧
      (∀ (U : Matrix (ZMod d) (ZMod d) ℂ) (a b : ZMod d × ZMod d) (c : ℂ),
        Uᴴ * U = 1 → U * (E * Eᴴ) = (E * Eᴴ) * U →
        U * paperDisplacement d a * Uᴴ = c • paperDisplacement d b → c * star c = 1 →
          labelFourthMoment E a = labelFourthMoment E b)) ∧
    (∀ {S : Type} [Fintype S] [DecidableEq S] [NeZero (Fintype.card S)]
        (E : Matrix (ZMod d) S ℂ), Eᴴ * E = 1 →
      symTwirl4 d (power4 E * A4 S * (power4 E)ᴴ) = A4 (ZMod d) ∧
      (d : ℂ) * Matrix.trace (Q d * symTwirl4 d (power4 E * A4 S * (power4 E)ᴴ)) =
        intrinsicTerm d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S₁ S₂ _ _ _ _ _ _ E₁ E₂ hE₁ hE₂
    have hiff := isometry_range_iff_projector E₁ E₂ hE₁ hE₂
    refine ⟨hiff, fun hrange => ?_⟩
    obtain ⟨hcard, hmom, hext⟩ := isometry_projector_invariance E₁ E₂ hE₁ hE₂ (hiff.mp hrange)
    refine ⟨hcard, hmom, hext, ?_⟩
    unfold aseGap
    rw [(by congr 1 : intrinsicTerm (Fintype.card S₁) = intrinsicTerm (Fintype.card S₂)), hext]
  · intro S _ _ _ E hE
    have horigin : labelFourthMoment E (0, 0) = 1 := by
      unfold labelFourthMoment paperDisplacement
      simp only [ZMod.val_zero, mul_zero, pow_zero, displacement_zero, one_smul, Matrix.mul_one,
        hE, alt_one, Matrix.one_mul]; exact trace_A4 S
    refine ⟨horigin, fun U a b c hU hcomm hconj hc => ?_⟩
    have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
    let E' : Matrix (ZMod d) S ℂ := Uᴴ * E
    have hE' : E'ᴴ * E' = 1 := by
      simp only [E', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU, Matrix.one_mul, hE]
    have hproj' : E * Eᴴ = E' * E'ᴴ := by
      simp only [E', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc E * Eᴴ = (Uᴴ * U) * (E * Eᴴ) := by rw [hU, Matrix.one_mul]
        _ = Uᴴ * (U * (E * Eᴴ)) := by simp [Matrix.mul_assoc]
        _ = Uᴴ * ((E * Eᴴ) * U) := by rw [hcomm]
        _ = Uᴴ * E * (Eᴴ * U) := by simp [Matrix.mul_assoc]
    rw [(isometry_projector_invariance E E' hE hE' hproj').2.1 a]
    unfold labelFourthMoment
    have hcomp : E'ᴴ * paperDisplacement d a * E' = c • (Eᴴ * paperDisplacement d b * E) := by
      calc E'ᴴ * paperDisplacement d a * E' = Eᴴ * (U * paperDisplacement d a * Uᴴ) * E := by
            simp [E', Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = c • (Eᴴ * paperDisplacement d b * E) := by rw [hconj, Matrix.mul_smul, Matrix.smul_mul]
    rw [hcomp, alt_phase _ _ hc]
  · intro S _ _ _ E hE
    have htwirl : symTwirl4 d (power4 E * A4 S * (power4 E)ᴴ) = A4 (ZMod d) := by
      unfold symTwirl4
      have htr : Matrix.trace (symProjector4 (ZMod d) * (power4 E * A4 S * (power4 E)ᴴ)) = 1 := by
        have hcyc : Matrix.trace (symProjector4 (ZMod d) * (power4 E * A4 S * (power4 E)ᴴ)) =
            Matrix.trace ((power4 E)ᴴ * (symProjector4 (ZMod d) * power4 E) * A4 S) := by
          rw [(by simp [Matrix.mul_assoc] :
            symProjector4 (ZMod d) * (power4 E * A4 S * (power4 E)ᴴ) =
              (symProjector4 (ZMod d) * (power4 E * A4 S)) * (power4 E)ᴴ),
            Matrix.trace_mul_comm]; simp [Matrix.mul_assoc]
        rw [hcyc, ← power4_symProjector4, ← Matrix.mul_assoc ((power4 E)ᴴ)]
        have hEE : (power4 E)ᴴ * power4 E = 1 := by
          unfold power4; rw [← product4_adjoint, ← product4_mul]; simp only [hE, product4_one]
        rw [hEE, Matrix.one_mul, (by unfold A4; rw [Matrix.mul_smul, symProjector4_idem] :
          symProjector4 S * A4 S = A4 S)]; exact trace_A4 S
      rw [htr, one_smul]
    exact ⟨htwirl, by rw [htwirl]; rfl⟩

end D5.S3.Quantum.Magic.SubspaceStabilizerEntropy

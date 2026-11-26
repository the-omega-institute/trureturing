/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverIntegerFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scaled polynomial tensor splitting and the integral-grid Sugawara action. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverVirasoro
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Analysis.Real.Sqrt

/-!
The ordinary rank-one factor in the third-cover polynomial oscillators.
The tensor splitting uses Mathlib's polynomial tensor equivalence and the
variable-renaming and derivative-transport approach of `LeechHalfFockTensorSplit`.
The current normalization is that of `ThirdCoverVirasoro.current`.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.ThirdCoverIntegerFactor

open MvPolynomial PolynomialFockSugawaraSupport
open scoped TensorProduct

abbrev Complement := {k : ℕ // ¬ 3 ∣ k + 1}
abbrev ComplementFock := MvPolynomial Complement ℂ
abbrev SplitFock := Fock ⊗[ℂ] ComplementFock

def ordinaryVar (n : ℕ) : ℕ := 3 * n + 2

theorem ordinaryVar_injective : Function.Injective ordinaryVar := by
  intro n m h
  unfold ordinaryVar at h
  omega

@[simp] theorem dvd_ordinaryVar_succ (n : ℕ) : 3 ∣ ordinaryVar n + 1 :=
  ⟨n + 1, by unfold ordinaryVar; omega⟩

/-- Relabel the multiples of three by ordinary creation indices. -/
def variableSplit : ℕ ≃ ℕ ⊕ Complement where
  toFun k := if h : 3 ∣ k + 1 then .inl (k / 3) else .inr ⟨k, h⟩
  invFun := Sum.elim ordinaryVar Subtype.val
  left_inv := by
    intro k
    change Sum.elim ordinaryVar Subtype.val
      (if h : 3 ∣ k + 1 then Sum.inl (k / 3) else Sum.inr (⟨k, h⟩ : Complement)) = k
    by_cases h : 3 ∣ k + 1
    · rw [dite_eq_left h]
      change ordinaryVar (k / 3) = k
      rw [Nat.dvd_iff_mod_eq_zero] at h
      unfold ordinaryVar
      omega
    · rw [dite_eq_right h]
      rfl
  right_inv := by
    rintro (n | k)
    · change (if h : 3 ∣ ordinaryVar n + 1 then Sum.inl (ordinaryVar n / 3)
        else Sum.inr (⟨ordinaryVar n, h⟩ : Complement)) = Sum.inl n
      rw [dite_eq_left (dvd_ordinaryVar_succ n)]
      congr 1
      unfold ordinaryVar
      omega
    · change (if h : 3 ∣ k.val + 1 then Sum.inl (k.val / 3)
        else Sum.inr (⟨k.val, h⟩ : Complement)) = Sum.inr k
      rw [dite_eq_right k.property]

private def unscaledJoin : SplitFock ≃ₐ[ℂ] Fock :=
  (tensorEquivSum ℂ ℕ Complement ℂ).trans (renameEquiv ℂ variableSplit.symm)

private theorem unscaledJoin_tmul_one (P : Fock) :
    unscaledJoin (P ⊗ₜ[ℂ] (1 : ComplementFock)) = rename ordinaryVar P := by
  have h : unscaledJoin.toAlgHom.comp Algebra.TensorProduct.includeLeft =
      rename (R := ℂ) ordinaryVar := by
    apply MvPolynomial.algHom_ext
    intro n
    simp [unscaledJoin, variableSplit]
  exact DFunLike.congr_fun h P

private theorem unscaledJoin_one_tmul (Q : ComplementFock) :
    unscaledJoin ((1 : Fock) ⊗ₜ[ℂ] Q) = rename Subtype.val Q := by
  have h : unscaledJoin.toAlgHom.comp Algebra.TensorProduct.includeRight =
      rename (R := ℂ) (Subtype.val : Complement → ℕ) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [unscaledJoin, variableSplit]
  exact DFunLike.congr_fun h Q

private theorem unscaledJoin_tmul (P : Fock) (Q : ComplementFock) :
    unscaledJoin (P ⊗ₜ[ℂ] Q) = rename ordinaryVar P * rename Subtype.val Q := by
  rw [← unscaledJoin_tmul_one, ← unscaledJoin_one_tmul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Substitute a common scalar multiple for each ordinary variable. -/
def scale (a : ℂ) : Fock →ₐ[ℂ] Fock :=
  aeval (fun n => a • X n)

@[simp] private theorem scale_X (a : ℂ) (n : ℕ) : scale a (X n) = a • X n :=
  aeval_X _ _

private theorem scale_comp (a b : ℂ) (h : b * a = 1) :
    (scale a).comp (scale b) = AlgHom.id ℂ Fock := by
  apply MvPolynomial.algHom_ext
  intro n
  simp [smul_smul, h]

private def rescale (s : ℂ) (hs : s ≠ 0) : Fock ≃ₐ[ℂ] Fock :=
  AlgEquiv.ofAlgHom (scale s⁻¹) (scale s)
    (scale_comp _ _ (mul_inv_cancel₀ hs)) (scale_comp _ _ (inv_mul_cancel₀ hs))

private theorem pderiv_scale (a : ℂ) (n : ℕ) (P : Fock) :
    pderiv n (scale a P) = a • scale a (pderiv n P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scale]
  | add p q hp hq => simp [hp, hq, smul_add]
  | mul_X p j hp =>
    rw [map_mul, scale_X, pderiv_mul, Derivation.map_smul, hp, pderiv_mul, map_add,
      map_mul, map_mul, scale_X]
    by_cases h : j = n
    · subst j
      simp [smul_add]
    · simp [pderiv_X_of_ne h]

/-- The inverse of the splitting, with the ordinary variables scaled by the reciprocal
of the chosen square root of three. -/
def join (s : ℂ) (hs : s ≠ 0) : SplitFock ≃ₐ[ℂ] Fock :=
  (Algebra.TensorProduct.congr (rescale s hs) (.refl : ComplementFock ≃ₐ[ℂ] _)).trans unscaledJoin

def split (s : ℂ) (hs : s ≠ 0) : Fock ≃ₐ[ℂ] SplitFock := (join s hs).symm

theorem join_tmul (s : ℂ) (hs : s ≠ 0) (P : Fock) (Q : ComplementFock) :
    join s hs (P ⊗ₜ[ℂ] Q) = rename ordinaryVar (scale s⁻¹ P) * rename Subtype.val Q := by
  simp only [join, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply, unscaledJoin_tmul]
  rfl

@[simp] theorem join_X_tmul_one (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    join s hs (X n ⊗ₜ[ℂ] (1 : ComplementFock)) = s⁻¹ • X (ordinaryVar n) := by
  simp [join_tmul]

@[simp] theorem join_one_tmul_X (s : ℂ) (hs : s ≠ 0) (k : Complement) :
    join s hs ((1 : Fock) ⊗ₜ[ℂ] X k) = X k.val := by
  simp [join_tmul]

/-- A choice of square root for the split. The intertwining works for either root. -/
def sqrtThree : ℂ := (Real.sqrt 3 : ℝ)

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  unfold sqrtThree
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem ne_zero_of_sq_eq_three {s : ℂ} (hsq : s ^ 2 = 3) : s ≠ 0 := by
  rintro rfl
  norm_num at hsq

private theorem pderiv_join_tmul (s : ℂ) (hs : s ≠ 0) (n : ℕ)
    (P : Fock) (Q : ComplementFock) :
    pderiv (ordinaryVar n) (join s hs (P ⊗ₜ[ℂ] Q)) =
      s⁻¹ • join s hs (pderiv n P ⊗ₜ[ℂ] Q) := by
  have hnot : ordinaryVar n ∉ (rename (R := ℂ) (Subtype.val : Complement → ℕ) Q).vars := by
    intro h
    obtain ⟨k, _, hk⟩ := mem_vars_rename (Subtype.val : Complement → ℕ) Q h
    exact k.property (hk ▸ dvd_ordinaryVar_succ n)
  rw [join_tmul, pderiv_mul, pderiv_eq_zero_of_notMem_vars hnot, mul_zero, add_zero,
    pderiv_rename ordinaryVar_injective, pderiv_scale, map_smul, join_tmul, smul_mul_assoc]

/-- The unnormalized cover mode is the ordinary mode multiplied by the square root.
The complementary polynomial is independent of the ordinary one. -/
theorem mode_join_tmul {s : ℂ} (hsq : s ^ 2 = 3) (r : ℤ)
    (P : Fock) (Q : ComplementFock) :
    mode (3 * r) (join s (ne_zero_of_sq_eq_three hsq) (P ⊗ₜ[ℂ] Q)) =
      s • join s (ne_zero_of_sq_eq_three hsq) (mode r P ⊗ₜ[ℂ] Q) := by
  have hs := ne_zero_of_sq_eq_three hsq
  cases r with
  | ofNat r =>
    cases r with
    | zero => simp [mode]
    | succ n =>
      have hi : 3 * Int.ofNat (n + 1) = Int.ofNat (ordinaryVar n + 1) := by
        simp only [ordinaryVar, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one]
        omega
      rw [hi]
      change (↑(ordinaryVar n) + 1 : ℂ) •
          pderiv (ordinaryVar n) (join s hs (P ⊗ₜ[ℂ] Q)) =
        s • join s hs (((↑n + 1 : ℂ) • pderiv n P) ⊗ₜ[ℂ] Q)
      rw [pderiv_join_tmul, ← TensorProduct.smul_tmul', map_smul, smul_smul, smul_smul]
      have hn : (↑(ordinaryVar n) + 1 : ℂ) = 3 * (↑n + 1) := by
        push_cast [ordinaryVar]
        ring
      have hscale : (3 : ℂ) * s⁻¹ = s := by
        rw [← hsq, pow_two, mul_assoc, mul_inv_cancel₀ hs, mul_one]
      rw [hn, mul_right_comm, hscale]
  | negSucc n =>
    have hi : 3 * Int.negSucc n = Int.negSucc (ordinaryVar n) := by
      unfold ordinaryVar
      omega
    rw [hi]
    simp only [mode, create, LinearMap.mulLeft_apply]
    have ht : (X n ⊗ₜ[ℂ] (1 : ComplementFock)) * (P ⊗ₜ[ℂ] Q) =
        (X n * P) ⊗ₜ[ℂ] Q := by simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [← ht, map_mul, join_X_tmul_one, ← smul_mul_assoc, smul_smul,
      mul_inv_cancel₀ hs, one_smul]

/-- The normalized cover mode acts by the ordinary mode on every pure tensor. -/
theorem normalizedMode_join_tmul {s : ℂ} (hsq : s ^ 2 = 3) (r : ℤ)
    (P : Fock) (Q : ComplementFock) :
    Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)
      (join s (ne_zero_of_sq_eq_three hsq) (P ⊗ₜ[ℂ] Q)) =
      join s (ne_zero_of_sq_eq_three hsq) (mode r P ⊗ₜ[ℂ] Q) := by
  rw [Lattice.Orbifold.ThirdCoverVirasoro.current, LinearMap.smul_apply, mode_join_tmul hsq,
    smul_smul,
    inv_mul_cancel₀ (ne_zero_of_sq_eq_three hsq), one_smul]

/-- The mode intertwiner as an equality of endomorphisms on the full tensor product. -/
theorem split_normalizedMode {s : ℂ} (hsq : s ^ 2 = 3) (r : ℤ) :
    (split s (ne_zero_of_sq_eq_three hsq)).toLinearEquiv.conj
      (Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)) =
      TensorProduct.map (mode r) LinearMap.id := by
  apply TensorProduct.ext'
  intro P Q
  change split s _ (Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)
    (join s _ (P ⊗ₜ[ℂ] Q))) = _
  rw [normalizedMode_join_tmul hsq, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join s _).symm_apply_apply _

/-- Normal ordering is preserved by multiplication of both mode indices by three. -/
theorem normalPair_join_tmul {s : ℂ} (hsq : s ^ 2 = 3) (i j : ℤ)
    (P : Fock) (Q : ComplementFock) :
    normalPair (3 * i) (3 * j) (join s (ne_zero_of_sq_eq_three hsq) (P ⊗ₜ[ℂ] Q)) =
      (3 : ℂ) • join s (ne_zero_of_sq_eq_three hsq) (normalPair i j P ⊗ₜ[ℂ] Q) := by
  have horder : 3 * j ≤ 3 * i ↔ j ≤ i := by omega
  have hmul : s * s = 3 := by simpa only [pow_two] using hsq
  by_cases h : j ≤ i
  · simp only [normalPair, horder, ite_eq_left h, LinearMap.comp_apply, mode_join_tmul hsq,
      map_smul, smul_smul, hmul]
  · simp only [normalPair, horder, ite_eq_right h, LinearMap.comp_apply, mode_join_tmul hsq,
      map_smul, smul_smul, hmul]

private theorem normalPair_finiteSupport (m : ℤ) (P : Fock) :
    Function.HasFiniteSupport (fun j : ℤ => normalPair (m - j) j P) :=
  (Set.finite_Ioo _ _).subset (normalPair_support_interval m P)

private def multiplesOfThree : Set ℤ := {k | 3 ∣ k}

private theorem finiteRestrictedSupport (m : ℤ) (P : Fock) :
    (multiplesOfThree ∩ Function.support (fun k : ℤ => normalPair (3 * m - k) k P)).Finite :=
  (normalPair_finiteSupport (3 * m) P).subset Set.inter_subset_right

/-- The multiple-of-three summands of one third of the cover Sugawara operator. -/
def integerSugawara (m : ℤ) : Module.End ℂ Fock where
  toFun P := (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ multiplesOfThree, normalPair (3 * m - k) k P)
  map_add' P Q := by
    simp only [map_add]
    rw [finsum_mem_add_distrib' (finiteRestrictedSupport m P) (finiteRestrictedSupport m Q)]
    simp only [smul_add]
  map_smul' a P := by
    simp only [map_smul, RingHom.id_apply]
    have hsum : a • (∑ᶠ k ∈ multiplesOfThree, normalPair (3 * m - k) k P) =
        ∑ᶠ k ∈ multiplesOfThree, a • normalPair (3 * m - k) k P := by
      simpa only [DistribSMul.toAddMonoidHom_apply] using
        (DistribSMul.toAddMonoidHom Fock a).map_finsum_mem' (finiteRestrictedSupport m P)
    rw [← hsum, smul_comm (2 : ℂ)⁻¹ a, smul_comm (3 : ℂ)⁻¹ a]

theorem integerSugawara_apply (m : ℤ) (P : Fock) :
    integerSugawara m P =
      (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ k ∈ {k : ℤ | 3 ∣ k}, normalPair (3 * m - k) k P) :=
  rfl

/-- The restricted cover sum equals the ordinary Sugawara action on the first factor. -/
theorem integerSugawara_join_tmul {s : ℂ} (hsq : s ^ 2 = 3) (m : ℤ)
    (P : Fock) (Q : ComplementFock) :
    integerSugawara m (join s (ne_zero_of_sq_eq_three hsq) (P ⊗ₜ[ℂ] Q)) =
      join s (ne_zero_of_sq_eq_three hsq) (L m P ⊗ₜ[ℂ] Q) := by
  let J : Fock →ₗ[ℂ] Fock := (join s (ne_zero_of_sq_eq_three hsq)).toLinearMap.comp
    ((TensorProduct.mk ℂ Fock ComplementFock).flip Q)
  have hRange : Set.range (fun j : ℤ => 3 * j) = {k : ℤ | 3 ∣ k} := by
    ext k
    change (∃ j : ℤ, 3 * j = k) ↔ ∃ j : ℤ, k = 3 * j
    exact exists_congr fun _ => eq_comm
  have hInj : Function.Injective (fun j : ℤ => 3 * j) := by
    intro j k h
    change 3 * j = 3 * k at h
    omega
  rw [integerSugawara_apply, ← hRange, finsum_mem_range hInj]
  have hterm (j : ℤ) :
      normalPair (3 * m - 3 * j) (3 * j) (J P) =
        (3 : ℂ) • J (normalPair (m - j) j P) := by
    rw [show 3 * m - 3 * j = 3 * (m - j) by ring]
    exact normalPair_join_tmul hsq (m - j) j P Q
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ∑ᶠ j : ℤ, normalPair (3 * m - 3 * j) (3 * j) (J P)) =
    J (L m P)
  have hfinite := normalPair_finiteSupport m P
  have hfiniteJ : Function.HasFiniteSupport (fun j : ℤ => J (normalPair (m - j) j P)) :=
    hfinite.subset (by
      intro j hj
      change J (normalPair (m - j) j P) ≠ 0 at hj
      change normalPair (m - j) j P ≠ 0
      intro h
      exact hj (by rw [h, map_zero]))
  simp only [hterm]
  have hsum : J (∑ᶠ j : ℤ, normalPair (m - j) j P) =
      ∑ᶠ j : ℤ, J (normalPair (m - j) j P) := by
    simpa only [LinearMap.toAddMonoidHom_coe] using J.toAddMonoidHom.map_finsum hfinite
  rw [← smul_finsum' (3 : ℂ) hfiniteJ, ← hsum]
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ • ((3 : ℂ) • J (∑ᶠ j : ℤ, normalPair (m - j) j P))) =
    J ((2 : ℂ)⁻¹ • ∑ᶠ j : ℤ, normalPair (m - j) j P)
  rw [map_smul, smul_comm (2 : ℂ)⁻¹ (3 : ℂ), smul_smul,
    inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

/-- The Sugawara intertwining holds on arbitrary split states. -/
theorem split_integerSugawara {s : ℂ} (hsq : s ^ 2 = 3) (m : ℤ) :
    (split s (ne_zero_of_sq_eq_three hsq)).toLinearEquiv.conj (integerSugawara m) =
      TensorProduct.map (L m) LinearMap.id := by
  apply TensorProduct.ext'
  intro P Q
  change split s _ (integerSugawara m (join s _ (P ⊗ₜ[ℂ] Q))) = _
  rw [integerSugawara_join_tmul hsq, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join s _).symm_apply_apply _

end D5.S3.VertexAlgebra.ThirdCoverIntegerFactor

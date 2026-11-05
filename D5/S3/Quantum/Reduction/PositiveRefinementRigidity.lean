/- GID: D5/S3/Quantum/Reduction/PositiveRefinementRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Reduction/PositiveRefinementRigidity
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Positive maps dominated by identity have scalar action on every projection. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation

/-!
# Positive domination and projection rigidity

The map is only complex linear and positive; no Kraus representation or
complete positivity is assumed. The Loewner upper bound is imposed on all
positive semidefinite inputs. The support argument includes zero projections.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Reduction.PositiveRefinementRigidity
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem projection_action
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ X)
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    Φ 1 * P = Φ P ∧ P * Φ 1 = Φ P := by
  have hp : P.PosSemidef := by
    have h := posSemidef_conjTranspose_mul_self P
    simpa only [hP, hPP] using h
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have hq : (1 - P).PosSemidef := hproj.one_sub.nonneg.posSemidef
  obtain ⟨hright, hleft⟩ := hproj.mul_right_and_mul_left_of_nonneg_of_le
    (hpos P hp).nonneg (hdom P hp)
  obtain ⟨hqr, hql⟩ := hproj.one_sub.mul_right_and_mul_left_of_nonneg_of_le
    (hpos (1 - P) hq).nonneg (hdom (1 - P) hq)
  have hzeroR : Φ (1 - P) * P = 0 := by
    have := hqr
    rw [mul_sub, mul_one] at this
    exact sub_eq_self.mp this
  have hzeroL : P * Φ (1 - P) = 0 := by
    have := hql
    rw [sub_mul, one_mul] at this
    exact sub_eq_self.mp this
  have hsum : Φ 1 = Φ P + Φ (1 - P) := by rw [← map_add]; congr 1; abel
  rw [hsum, add_mul, mul_add, hright, hleft, hzeroR, hzeroL]
  simp

/-- Positivity-only domination forces the image of the identity to be scalar,
and gives that same scalar on every Hermitian projection. -/
theorem identity_dominated_projection_scalar
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ X) (i₀ : n) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ Φ 1 = (c : ℂ) • (1 : Matrix n n ℂ) ∧
      ∀ P : Matrix n n ℂ, Pᴴ = P → P * P = P → Φ P = (c : ℂ) • P := by
  have hc (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
      Φ 1 * P = P * Φ 1 := by
    obtain ⟨hr, hl⟩ := projection_action Φ hpos hdom P hP hPP
    exact hr.trans hl.symm
  have hoff (i j : n) (hij : i ≠ j) : Φ 1 i j = 0 := by
    have h := congrArg (fun M : Matrix n n ℂ => M i j)
      (hc (single j j 1) (by simp) (by simp))
    simpa [Matrix.mul_apply, Matrix.single, hij, eq_comm] using h
  have hd : Φ 1 = diagonal (fun i => Φ 1 i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, hoff i j hij]
  have heq (i j : n) : Φ 1 i i = Φ 1 j j := by
    by_cases hij : i = j
    · subst j; rfl
    let v : n → ℂ := Pi.single i 1 + Pi.single j 1
    let Q : Matrix n n ℂ := (1 / 2 : ℂ) • vecMulVec v (star v)
    have hv : star v ⬝ᵥ v = 2 := by
      norm_num [v, dotProduct_add, add_dotProduct, hij, Ne.symm hij]
    have hQ : Qᴴ = Q := by simp [Q]
    have hQQ : Q * Q = Q := by
      simp only [Q, smul_mul_assoc, mul_smul_comm, vecMulVec_mul_vecMulVec, hv,
        smul_smul]
      norm_num [smul_smul]
    have h := congrArg (fun M : Matrix n n ℂ => M i j) (hc Q hQ hQQ)
    rw [hd] at h
    simp [Q, v, hij, Ne.symm hij, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.vecMulVec_apply] at h
    linear_combination 2 * h
  have hOne := hpos 1 PosSemidef.one
  have hnonneg := hOne.diag_nonneg (i := i₀)
  have hupper := (Matrix.le_iff.mp (hdom 1 PosSemidef.one)).diag_nonneg (i := i₀)
  let c : ℝ := (Φ 1 i₀ i₀).re
  have hreal : Φ 1 i₀ i₀ = (c : ℂ) := by
    apply Complex.ext <;> simp [c, hnonneg.2.symm]
  have hscalar : Φ 1 = (c : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using (heq i i₀).trans hreal
    · simp [hij, hoff i j hij]
  refine ⟨c, hnonneg.1, ?_, hscalar, ?_⟩
  · simpa [c] using hupper.1
  · intro P hP hPP
    have h := (projection_action Φ hpos hdom P hP hPP).1.symm
    simpa [hscalar] using h

theorem eq_of_projection_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : Matrix n n ℂ →ₗ[ℂ] V)
    (h : ∀ P : Matrix n n ℂ, Pᴴ = P → P * P = P → f P = g P) : f = g := by
  have hh (H : Matrix n n ℂ) (hH : H.IsHermitian) : f H = g H := by
    let U := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
    have hd : diagonal (Complex.ofReal ∘ hH.eigenvalues) =
        ∑ i : n, (hH.eigenvalues i : ℂ) • single i i 1 := by
      rw [← sum_single_eq_diagonal]
      apply Finset.sum_congr rfl
      intro i hi
      simp
    have hex : H = ∑ i : n, (hH.eigenvalues i : ℂ) • U (single i i 1) := by
      calc
        H = U (diagonal (Complex.ofReal ∘ hH.eigenvalues)) := hH.spectral_theorem
        _ = _ := by rw [hd]; simp only [map_sum, map_smul]
    rw [hex, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_smul]
    congr 1
    apply h
    · change star (U (single i i 1)) = U (single i i 1)
      rw [← map_star]
      apply congrArg U
      change (single i i (1 : ℂ))ᴴ = single i i 1
      simp
    · rw [← map_mul]
      congr 1
      simp
  apply LinearMap.ext
  intro X
  have hX := realPart_add_I_smul_imaginaryPart X
  rw [← hX, map_add, map_add, map_smul, map_smul,
    hh _ (realPart X).property,
    hh _ (imaginaryPart X).property]

/-- A positive complex-linear map below identity is a nonnegative scalar
multiple of identity on every matrix, with no complete-positivity premise. -/
theorem identity_dominated_scalar
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ X) (i₀ : n) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ X, Φ X = (c : ℂ) • X := by
  obtain ⟨c, hc, hc', -, hproj⟩ := identity_dominated_projection_scalar Φ hpos hdom i₀
  refine ⟨c, hc, hc', ?_⟩
  have heq : Φ = (c : ℂ) • LinearMap.id :=
    eq_of_projection_eq Φ ((c : ℂ) • LinearMap.id) hproj
  intro X
  exact LinearMap.congr_fun heq X

private def tracePair {m : Type*} [Fintype m] (Y : Matrix m m ℂ) :
    Matrix m m ℂ →ₗ[ℂ] ℂ where
  toFun X := (X * Y).trace
  map_add' X Z := by simp [add_mul]
  map_smul' c X := by simp [smul_mul_assoc]

private theorem positive_kills_projection_products
    {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (Q : Matrix n n ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (hzero : Φ Q = 0)
    (X : Matrix n n ℂ) : Φ (Q * X) = 0 ∧ Φ (X * Q) = 0 := by
  have ht (Y : Matrix m m ℂ) (hY : Y.PosSemidef) :
      (Φ (Q * X) * Y).trace = 0 ∧ (Φ (X * Q) * Y).trace = 0 := by
    let f : Matrix n n ℂ →ₚ[ℂ] ℂ := {
      toLinearMap := (tracePair Y).comp Φ
      monotone' := by
        intro A B hAB
        apply sub_nonneg.mp
        change 0 ≤ (Φ B * Y).trace - (Φ A * Y).trace
        rw [← Matrix.trace_sub, ← sub_mul, ← map_sub]
        exact (hpos (B - A) (Matrix.le_iff.mp hAB)).trace_mul_nonneg hY }
    have hleft := PositiveLinearMap.norm_map_star_mul_le f Q X
    have hright := PositiveLinearMap.norm_map_mul_star_le f X Q
    change ‖f (Qᴴ * X)‖ ≤ _ at hleft
    change ‖f (X * Qᴴ)‖ ≤ _ at hright
    have hf : f (Q * Q) = 0 := by
      change (Φ (Q * Q) * Y).trace = 0
      rw [hQQ, hzero, zero_mul, trace_zero]
    rw [hQ] at hleft hright
    have hl : f (Q * X) = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [Matrix.star_eq_conjTranspose, hQ, hf, norm_zero, Real.sqrt_zero,
        zero_mul] using hleft) (norm_nonneg _)
    have hr : f (X * Q) = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [Matrix.star_eq_conjTranspose, hQ, hf, norm_zero, Real.sqrt_zero,
        mul_zero] using hright) (norm_nonneg _)
    exact ⟨hl, hr⟩
  have hall (Z : Matrix m m ℂ)
      (hz : ∀ Y, Y.PosSemidef → (Z * Y).trace = 0) : Z = 0 := by
    have he := eq_of_projection_eq
      (show Matrix m m ℂ →ₗ[ℂ] ℂ from {
        toFun Y := (Z * Y).trace
        map_add' Y T := by simp [mul_add]
        map_smul' c Y := by simp [mul_smul_comm] }) 0 (by
          intro P hP hPP
          have hp : P.PosSemidef := by
            simpa only [hP, hPP] using posSemidef_conjTranspose_mul_self P
          exact hz P hp)
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    simpa using LinearMap.congr_fun he Y
  exact ⟨hall _ (fun Y hY => (ht Y hY).1), hall _ (fun Y hY => (ht Y hY).2)⟩

/-- Killing the complement of a projection removes both input cross terms
for a positive map. The map need not be completely positive. -/
theorem positive_map_projection_compression
    {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hzero : Φ (1 - P) = 0) (X : Matrix n n ℂ) : Φ (P * X * P) = Φ X := by
  have hQ : (1 - P)ᴴ = 1 - P := by simp [hP]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by noncomm_ring [hPP]
  have hl := (positive_kills_projection_products Φ hpos (1 - P) hQ hQQ hzero X).1
  have hr := (positive_kills_projection_products Φ hpos (1 - P) hQ hQQ hzero (P * X)).2
  have hPX : Φ (P * X) = Φ X := by
    symm
    simpa only [sub_mul, one_mul, map_sub, sub_eq_zero] using hl
  have hPXP : Φ (P * X * P) = Φ (P * X) := by
    symm
    simpa only [mul_sub, mul_one, map_sub, sub_eq_zero] using hr
  exact hPXP.trans hPX

private theorem zero_of_positive_nonpos
    {m : Type*} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ 0) : Φ = 0 := by
  apply eq_of_projection_eq
  intro P hP hPP
  have hp : P.PosSemidef := by
    simpa only [hP, hPP] using posSemidef_conjTranspose_mul_self P
  exact le_antisymm (hdom P hp) (hpos P hp).nonneg

/-- Every actual positive fine-record branch of a blockwise single-operator
filter preserves the original centers, vanishes on zero effect blocks, and
ignores the complement and cross terms of every input support projection. -/
theorem canonical_refinement_structure
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {d : B → Type*} [∀ b, Fintype (d b)] [∀ b, DecidableEq (d b)]
    (R : ∀ b, Matrix (d b) (d b) ℂ)
    (S : A → ((b : B) → Matrix (d b) (d b) ℂ) →ₗ[ℂ]
      ((b : B) → Matrix (d b) (d b) ℂ))
    (hpos : ∀ a X, (∀ b, (X b).PosSemidef) → ∀ b, (S a X b).PosSemidef)
    (hsum : ∀ X b, ∑ a, S a X b = R b * X b * (R b)ᴴ) :
    (∀ a X b, S a X b = S a (Pi.single b (X b)) b) ∧
    (∀ a b, R b = 0 → ∀ X, S a X b = 0) ∧
    (∀ a b (P : Matrix (d b) (d b) ℂ), Pᴴ = P → P * P = P → R b * P = R b →
      ∀ X, S a (Pi.single b (P * X * P)) b = S a (Pi.single b X) b) := by
  classical
  have hpSingle (b : B) (X : Matrix (d b) (d b) ℂ) (hX : X.PosSemidef) :
      ∀ c, ((Pi.single b X : (c : B) → Matrix (d c) (d c) ℂ) c).PosSemidef := by
    intro c
    by_cases h : b = c
    · subst c
      simpa using hX
    · simpa [Pi.single_eq_of_ne (Ne.symm h)] using
        (PosSemidef.zero : (0 : Matrix (d c) (d c) ℂ).PosSemidef)
  have hdom (a : A) (X : (b : B) → Matrix (d b) (d b) ℂ)
      (hX : ∀ b, (X b).PosSemidef) (b : B) : S a X b ≤ R b * X b * (R b)ᴴ := by
    rw [← hsum X b]
    exact Finset.single_le_sum (fun a' _ => (hpos a' X hX b).nonneg) (Finset.mem_univ a)
  let K (a : A) (b c : B) : Matrix (d b) (d b) ℂ →ₗ[ℂ] Matrix (d c) (d c) ℂ :=
    (LinearMap.proj c).comp ((S a).comp (LinearMap.single ℂ _ b))
  have hK (a : A) (b c : B) (X : Matrix (d b) (d b) ℂ) :
      K a b c X = S a (Pi.single b X) c := rfl
  have hKpos (a : A) (b c : B) (X : Matrix (d b) (d b) ℂ) (hX : X.PosSemidef) :
      (K a b c X).PosSemidef := hpos a _ (hpSingle b X hX) c
  have hcross (a : A) (b c : B) (hbc : b ≠ c) : K a b c = 0 := by
    apply zero_of_positive_nonpos _ (hKpos a b c)
    intro X hX
    have h := hdom a _ (hpSingle b X hX) c
    simpa only [hK, Pi.single_eq_of_ne (Ne.symm hbc), mul_zero, zero_mul] using h
  have hlocal (a : A) (X : (b : B) → Matrix (d b) (d b) ℂ) (b : B) :
      S a X b = S a (Pi.single b (X b)) b := by
    calc
      S a X b = ∑ c : B, S a (Pi.single c (X c)) b := by
        have hx : (∑ c : B, Pi.single c (X c)) = X := by ext c i j; simp
        conv_lhs => rw [← hx]
        simp only [map_sum, Finset.sum_apply]
      _ = _ := by
        apply Finset.sum_eq_single b
        · intro c hc hcb
          have h := LinearMap.congr_fun (hcross a c b hcb) (X c)
          exact h
        · intro hb
          exact (hb (Finset.mem_univ b)).elim
  refine ⟨hlocal, ?_, ?_⟩
  · intro a b hR X
    rw [hlocal]
    have hz : K a b b = 0 := by
      apply zero_of_positive_nonpos _ (hKpos a b b)
      intro Y hY
      have h := hdom a _ (hpSingle b Y hY) b
      change S a (Pi.single b Y) b ≤ 0
      simpa [hR] using h
    exact LinearMap.congr_fun hz (X b)
  · intro a b P hP hPP hRP X
    apply positive_map_projection_compression (K a b b) (hKpos a b b) P hP hPP
    apply le_antisymm
    · have hQ : (1 - P).PosSemidef :=
        (show IsStarProjection P from ⟨hPP, hP⟩).one_sub.nonneg.posSemidef
      have h := hdom a _ (hpSingle b (1 - P) hQ) b
      have hz : R b * (1 - P) = 0 := by rw [mul_sub, mul_one, hRP, sub_self]
      simpa only [hK, Pi.single_eq_same, hz, zero_mul] using h
    · exact (hKpos a b b _
        (show (1 - P).PosSemidef from
          (show IsStarProjection P from ⟨hPP, hP⟩).one_sub.nonneg.posSemidef)).nonneg

#print axioms identity_dominated_projection_scalar
#print axioms identity_dominated_scalar
#print axioms positive_map_projection_compression
#print axioms canonical_refinement_structure
end D5.S3.Quantum.Reduction.PositiveRefinementRigidity

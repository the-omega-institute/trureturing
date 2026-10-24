/- GID: D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Optimal unambiguous discrimination of injectively labelled product sequences. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination

open scoped ComplexOrder Matrix MatrixOrder
open Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Ordered sequences of distinct labels. -/
abbrev Label (N k : ℕ) := {x : Fin k → Fin N // Function.Injective x}

/-- Normalized single-system states with common real overlap. -/
def IsEquiangular {N : ℕ} (ψ : Fin N → Fin N → ℂ) (s : ℝ) : Prop :=
  (∀ i, star (ψ i) ⬝ᵥ ψ i = 1) ∧
  ∀ i j, i ≠ j → star (ψ i) ⬝ᵥ ψ j = (s : ℂ)

/-- The tensor product in the coordinate basis. -/
def productState {N k : ℕ} (ψ : Fin N → Fin N → ℂ)
    (x : Label N k) (a : Fin k → Fin N) : ℂ := ∏ j, ψ (x.val j) (a j)

/-- Positive effects, including the inconclusive effect, with no erroneous output. -/
def IsUnambiguousMeasurement {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Prop :=
  (∀ x, (E x).PosSemidef) ∧ E₀.PosSemidef ∧
  (∑ x, E x) + E₀ = 1 ∧
  ∀ x y, y ≠ x → star (φ y) ⬝ᵥ ((E x) *ᵥ φ y) = 0

/-- Uniform average probability of a conclusive correct output. -/
def averageSuccess {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : ℝ :=
  (1 / (Fintype.card (Label N k) : ℝ)) *
    ∑ x, (star (φ x) ⬝ᵥ ((E x) *ᵥ φ x)).re

/-- The effect of a tuple of independent single-system outcomes. -/
def productEffect {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (o : Fin k → Option (Fin N)) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  fun a b => ∏ j, F (o j) (a j) (b j)

/-- Classical processing sums the product effects assigned to the same output. -/
noncomputable def inducedEffect {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (d : (Fin k → Option (Fin N)) → Option (Label N k))
    (z : Option (Label N k)) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  ∑ o, if d o = z then productEffect F o else 0

/-- The same single-system POVM is applied at each position, then processed classically. -/
def IsProductProtocol {N k : ℕ}
    (F : Option (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (d : (Fin k → Option (Fin N)) → Option (Label N k))
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Prop :=
  (∀ o, (F o).PosSemidef) ∧ (∑ o, F o) = 1 ∧
  (∀ x, E x = inducedEffect F d (some x)) ∧ E₀ = inducedEffect F d none

/-- The proposed optimum, including the forced final label for a full permutation. -/
def value (N k : ℕ) (s : ℝ) : ℝ :=
  if k < N then (1 - s) ^ k else (1 - s) ^ (N - 1) * (1 + (N - 1 : ℕ) * s)

/-- The global upper bound and attainment by an independent product measurement. -/
def claim : Prop :=
  ∀ (N k : ℕ), 3 ≤ N → 2 ≤ k → k ≤ N →
  ∀ s : ℝ, 0 < s → s < 1 →
  ∀ ψ : Fin N → Fin N → ℂ, IsEquiangular ψ s →
    (∀ E E₀, IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ →
      averageSuccess (productState (k := k) ψ) E ≤ value N k s) ∧
    ∃ F d E E₀, IsProductProtocol (k := k) F d E E₀ ∧
      IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ ∧
      averageSuccess (productState (k := k) ψ) E = value N k s

private def gram {N k : ℕ} (φ : Label N k → (Fin k → Fin N) → ℂ) :
    Matrix (Label N k) (Label N k) ℂ := fun x y => star (φ x) ⬝ᵥ φ y

private def probabilities {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ) : Label N k → ℝ :=
  fun x => (star (φ x) ⬝ᵥ ((E x) *ᵥ φ x)).re

private def kernel {N k : ℕ} (s : ℝ) : Matrix (Label N k) (Label N k) ℂ :=
  fun x y => ∏ j, if x.val j = y.val j then 1 else (s : ℂ)

private lemma product_gram {N k : ℕ} (ψ : Fin N → Fin N → ℂ) (s : ℝ)
    (hψ : IsEquiangular ψ s) : gram (productState (k := k) ψ) = kernel s := by
  ext x y
  change (∑ a : Fin k → Fin N,
    star (∏ j, ψ (x.val j) (a j)) * ∏ j, ψ (y.val j) (a j)) =
      ∏ j, if x.val j = y.val j then 1 else (s : ℂ)
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin k) (a : Fin N) =>
    star (ψ (x.val j) a) * ψ (y.val j) a)]
  apply Finset.prod_congr rfl
  intro j _
  change star (ψ (x.val j)) ⬝ᵥ ψ (y.val j) = _
  by_cases h : x.val j = y.val j
  · rw [if_pos h, h, hψ.1]
  · rw [if_neg h, hψ.2 _ _ h]

private lemma measurement_gram_bound {N k : ℕ}
    (φ : Label N k → (Fin k → Fin N) → ℂ)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (hE : IsUnambiguousMeasurement φ E E₀) :
    (gram φ - diagonal (fun x => (probabilities φ E x : ℂ))).PosSemidef := by
  classical
  let A : Matrix (Fin k → Fin N) (Label N k) ℂ := fun a x => φ x a
  have hzero (x y : Label N k) (hy : y ≠ x) : E x *ᵥ φ y = 0 :=
    ((hE.1 x).dotProduct_mulVec_zero_iff).mp (hE.2.2.2 x y hy)
  have hreal (x : Label N k) :
      star (φ x) ⬝ᵥ (E x *ᵥ φ x) = (probabilities φ E x : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp ((hE.1 x).dotProduct_mulVec_nonneg (φ x))).2.symm
  have hentry (x y z : Label N k) :
      (Aᴴ * E x * A) y z = star (φ y) ⬝ᵥ (E x *ᵥ φ z) := by
    rw [Matrix.mul_assoc]
    rfl
  have hcompression : Aᴴ * (∑ x, E x) * A =
      diagonal (fun x => (probabilities φ E x : ℂ)) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    ext y z
    simp only [Matrix.sum_apply, hentry]
    by_cases hyz : y = z
    · subst z
      rw [diagonal_apply_eq]
      rw [Finset.sum_eq_single y]
      · exact hreal y
      · intro x _ hxy
        rw [hzero x y hxy.symm, dotProduct_zero]
      · simp
    · rw [diagonal_apply_ne _ hyz]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hzx : z = x
      · subst z
        rw [← (hE.1 x).isHermitian.star_dotProduct_mulVec_comm (φ x) (φ y),
          hzero x y hyz, dotProduct_zero, star_zero]
      · rw [hzero x z hzx, dotProduct_zero]
  have htotal : E₀ = 1 - ∑ x, E x := by
    exact eq_sub_of_add_eq' hE.2.2.1
  have hgram : Aᴴ * A = gram φ := by
    ext x y
    rfl
  have hidentity : Aᴴ * E₀ * A =
      gram φ - diagonal (fun x => (probabilities φ E x : ℂ)) := by
    rw [htotal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgram, hcompression]
  rw [← hidentity]
  exact hE.2.1.conjTranspose_mul_mul_same A

private def relabel {N k : ℕ} (σ : Equiv.Perm (Fin N)) : Label N k ≃ Label N k where
  toFun x := ⟨σ ∘ x.val, σ.injective.comp x.property⟩
  invFun x := ⟨σ.symm ∘ x.val, σ.symm.injective.comp x.property⟩
  left_inv x := Subtype.ext (funext (fun j => σ.symm_apply_apply (x.val j)))
  right_inv x := Subtype.ext (funext (fun j => σ.apply_symm_apply (x.val j)))

private lemma symmetrized_bound {N k : ℕ} (hk : k ≤ N) (s : ℝ)
    (q : Label N k → ℝ)
    (hq : (kernel s - diagonal (fun x => (q x : ℂ))).PosSemidef) :
    (kernel s - (((1 / (Fintype.card (Label N k) : ℝ)) * ∑ x, q x : ℝ) : ℂ) •
      (1 : Matrix (Label N k) (Label N k) ℂ)).PosSemidef := by
  classical
  let c : ℝ := Fintype.card (Equiv.Perm (Fin N))
  let m : ℝ := Fintype.card (Label N k)
  let b : ℝ := (1 / m) * ∑ x, q x
  let t (x : Label N k) : ℝ := ∑ σ : Equiv.Perm (Fin N), q (relabel σ x)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm (Fin N))
  have hm : m ≠ 0 := by
    dsimp [m]
    have hpos : 0 < Fintype.card (Label N k) :=
      Fintype.card_pos_iff.mpr ⟨⟨Fin.castLE hk, Fin.castLE_injective hk⟩⟩
    exact_mod_cast hpos.ne'
  have hconst (x y : Label N k) : t x = t y := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair x.val y.val x.property y.property
    have hy : relabel τ x = y := Subtype.ext (funext hτ)
    rw [← hy]
    change (∑ σ : Equiv.Perm (Fin N), q (relabel σ x)) =
      ∑ σ : Equiv.Perm (Fin N), q (relabel (σ * τ) x)
    exact (Equiv.sum_comp (Equiv.mulRight τ) (fun σ => q (relabel σ x))).symm
  have hmean (x : Label N k) : t x = c * b := by
    have htotal : m * t x = c * ∑ y, q y := by
      calc
        m * t x = ∑ y : Label N k, t y := by
          simp only [← hconst x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
        _ = ∑ σ : Equiv.Perm (Fin N), ∑ y : Label N k, q (relabel σ y) := by
          exact Finset.sum_comm
        _ = c * ∑ y, q y := by
          simp only [Equiv.sum_comp (relabel _) q, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, c]
    calc
      t x = m⁻¹ * (m * t x) := by rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]
      _ = m⁻¹ * (c * ∑ y, q y) := by rw [htotal]
      _ = c * b := by dsimp [b]; rw [one_div]; ring
  have hkernel (σ : Equiv.Perm (Fin N)) (x y : Label N k) :
      kernel s (relabel σ x) (relabel σ y) = kernel s x y := by
    unfold kernel
    apply Finset.prod_congr rfl
    intro j _
    change (if σ (x.val j) = σ (y.val j) then (1 : ℂ) else (s : ℂ)) = _
    simp only [σ.injective.eq_iff]
  let A : Matrix (Label N k) (Label N k) ℂ :=
    ∑ σ : Equiv.Perm (Fin N),
      (kernel s - diagonal (fun x => (q x : ℂ))).submatrix (relabel σ) (relabel σ)
  have hA : A.PosSemidef :=
    Matrix.posSemidef_sum _ (fun σ _ => hq.submatrix (relabel σ))
  have hidentity : A = (c : ℂ) • (kernel s - (b : ℂ) • 1) := by
    have hentry (σ : Equiv.Perm (Fin N)) (x y : Label N k) :
        (kernel s - diagonal (fun x => (q x : ℂ))).submatrix (relabel σ) (relabel σ) x y =
        kernel s x y - diagonal (fun x => (q (relabel σ x) : ℂ)) x y := by
      change kernel s (relabel σ x) (relabel σ y) - _ = _
      rw [hkernel]
      congr 1
      exact congrArg (fun B : Matrix (Label N k) (Label N k) ℂ => B x y)
        (Matrix.submatrix_diagonal_equiv (fun x => (q x : ℂ)) (relabel σ))
    have htc (x : Label N k) :
        (∑ σ : Equiv.Perm (Fin N), (q (relabel σ x) : ℂ)) = (c : ℂ) * (b : ℂ) := by
      exact_mod_cast hmean x
    ext x y
    simp only [A, Matrix.sum_apply, hentry, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul]
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, htc, mul_one]
      change (c : ℂ) * kernel s x x - (c : ℂ) * (b : ℂ) =
        (c : ℂ) * (kernel s x x - (b : ℂ))
      ring
    · simp only [Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy,
        Finset.sum_const_zero, mul_zero, sub_zero]
      rfl
  have hscale := hA.smul (show (0 : ℂ) ≤ (c⁻¹ : ℝ) from by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin N)))))
  rw [hidentity, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc,
    Complex.ofReal_one, one_smul] at hscale
  exact hscale

private lemma kernel_eigenvector {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) :
    ∃ w : Label N k → ℂ, w ≠ 0 ∧ kernel s *ᵥ w = (value N k s : ℂ) • w := by
  sorry

private lemma eigenvalue_bound {N k : ℕ} (s a v : ℝ)
    (h : (kernel (N := N) (k := k) s - (a : ℂ) • 1).PosSemidef)
    (w : Label N k → ℂ) (hw : w ≠ 0) (he : kernel s *ᵥ w = (v : ℂ) • w) :
    a ≤ v := by
  classical
  have hn : 0 < (star w ⬝ᵥ w).re := by
    simpa only [Matrix.one_mulVec, RCLike.re_eq_complex_re] using
      (Matrix.PosDef.one : (1 : Matrix (Label N k) (Label N k) ℂ).PosDef).re_dotProduct_pos hw
  have hb := h.re_dotProduct_nonneg w
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, RCLike.re_eq_complex_re, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hb
  nlinarith

private lemma upper_bound {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) (ψ : Fin N → Fin N → ℂ) (hψ : IsEquiangular ψ s)
    (E : Label N k → Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (E₀ : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ)
    (hE : IsUnambiguousMeasurement (productState (k := k) ψ) E E₀) :
    averageSuccess (productState (k := k) ψ) E ≤ value N k s := by
  have hg := measurement_gram_bound (productState (k := k) ψ) E E₀ hE
  rw [product_gram ψ s hψ] at hg
  have hb := symmetrized_bound hkN s (probabilities (productState (k := k) ψ) E) hg
  obtain ⟨w, hw, he⟩ := kernel_eigenvector hN hk hkN s
  exact eigenvalue_bound s (averageSuccess (productState (k := k) ψ) E) (value N k s) hb w hw he

private lemma product_attainment {N k : ℕ} (hN : 3 ≤ N) (hk : 2 ≤ k)
    (hkN : k ≤ N) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (ψ : Fin N → Fin N → ℂ) (hψ : IsEquiangular ψ s) :
    ∃ F d E E₀, IsProductProtocol (k := k) F d E E₀ ∧
      IsUnambiguousMeasurement (productState (k := k) ψ) E E₀ ∧
      averageSuccess (productState (k := k) ψ) E = value N k s := by
  sorry

theorem result : claim := by
  intro N k hN hk hkN s hs hs1 ψ hψ
  exact ⟨fun E E₀ hE => upper_bound hN hk hkN s ψ hψ E E₀ hE,
    product_attainment hN hk hkN s hs hs1 ψ hψ⟩

end

end D5.S3.Quantum.PureState.NoRepetitionSequenceUnambiguousDiscrimination

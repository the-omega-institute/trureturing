/- GID: D5/S3/Quantum/Recovery/ProductPrefixRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/ProductPrefixRigidity
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Informationally complete common-label tests force positive local Gram rigidity along finite composed paths. -/

import D5.S3.Quantum.Recovery.PurifiedLocalPath


noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace D5.S3.Quantum.Recovery.ProductPrefixRigidity

variable {A I : Type*} [Fintype A] [DecidableEq A] [Nonempty I]
variable (H : A → Type*) (R : ℕ → A → Type*)
variable [∀ a, Fintype (H a)] [∀ a, DecidableEq (H a)]
variable [∀ t a, Fintype (R t a)] [∀ t a, DecidableEq (R t a)]

/-- A finite path of genuinely composed local maps: positive prefixes have full-source
Gram rigidity; a first zero factor annihilates all subsequent product maps. -/
theorem prefix_rigidity
    (B : ∀ a, Matrix (R 0 a) (H a) ℂ)
    (E : ∀ t a, Matrix (R (t+1) a) (R t a) ℂ)
    (actor : ℕ → A)
    (inactive : ∀ t a, a ≠ actor t → ∃ e : R (t+1) a ≃ R t a,
      E t a = (1 : Matrix (R t a) (R t a) ℂ).submatrix e id)
    (root : ∀ a, gram (B a) = 1)
    (s : ∀ a, I → H a → ℂ)
    (normalized : ∀ a i, star (s a i) ⬝ᵥ s a i = 1)
    (complete : ∀ a (Q : Matrix (H a) (H a) ℂ), Q.IsHermitian →
      Q ∈ Submodule.span ℝ (Set.range (fun i => vecMulVec (s a i) (star (s a i)))))
    (N : ℕ) (p : ℕ → ℝ)
    (probability : ∀ t, t ≤ N → ∀ i,
      (∏ a, ∑ k, Complex.normSq ((accumulated H R B E t a *ᵥ s a i) k)) = p t) :
    ∀ t, t ≤ N →
      (p t = 0 ∧ (∃ a, accumulated H R B E t a = 0) ∧
        productMap H (accumulated H R B E t) = 0) ∨
      (0 < p t ∧ ∃ c : A → ℝ,
        (∀ a, 0 < c a ∧ gram (accumulated H R B E t a) = (c a : ℂ) • 1) ∧
        (∏ a, c a) = p t ∧
        ∃ V : ∀ a, Matrix (R t a) (H a) ℂ,
          (∀ a, gram (V a) = 1 ∧
            accumulated H R B E t a = (Real.sqrt (c a) : ℂ) • V a ∧
            ∀ x y : H a → ℂ, star (V a *ᵥ x) ⬝ᵥ (V a *ᵥ y) = star x ⬝ᵥ y) ∧
          productMap H (accumulated H R B E t) =
            (Real.sqrt (p t) : ℂ) • productMap H V) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  have norm_readout (t : ℕ) (a : A) (i : I) :
      readout (gram (accumulated H R B E t a)) (s a i) =
        ∑ k, Complex.normSq ((accumulated H R B E t a *ᵥ s a i) k) := by
    rw [readout, gram, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    simp [dotProduct, Complex.normSq_apply, Complex.mul_re]
  have probability : ∀ t, t ≤ N → ∀ i,
      (∏ a, readout (gram (accumulated H R B E t a)) (s a i)) = p t := by
    simpa only [norm_readout] using probability
  have scalar_eval (a : A) (c : ℝ) (i : I) :
      readout ((c : ℂ) • (1 : Matrix (H a) (H a) ℂ)) (s a i) = c := by
    simp [readout, smul_mulVec, dotProduct_smul, normalized]
  have positive_eval (t : ℕ) (a : A) (i : I) :
      0 ≤ readout (gram (accumulated H R B E t a)) (s a i) := by
    exact (posSemidef_conjTranspose_mul_self (accumulated H R B E t a)).re_dotProduct_nonneg (s a i)
  have separation (a : A) (Q : Matrix (H a) (H a) ℂ) (hQ : Q.IsHermitian)
      (c : ℝ) (hq : ∀ i, readout Q (s a i) = c) : Q = (c : ℂ) • 1 := by
    let D := Q - (c : ℂ) • 1
    have hD : D.IsHermitian := by
      exact hQ.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
    let f : Matrix (H a) (H a) ℂ →ₗ[ℝ] ℝ :=
      { toFun := fun X => (Matrix.trace (D * X)).re
        map_add' := by intros; simp [mul_add, Matrix.trace_add]
        map_smul' := by intros; simp [Matrix.trace_smul] }
    have hker : Submodule.span ℝ
        (Set.range (fun i => vecMulVec (s a i) (star (s a i)))) ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change (Matrix.trace (D * vecMulVec (s a i) (star (s a i)))).re = 0
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
      change readout D (s a i) = 0
      simp only [D, readout, sub_mulVec, dotProduct_sub, Complex.sub_re]
      exact sub_eq_zero.mpr ((hq i).trans (scalar_eval a c i).symm)
    have hzero := hker (complete a D hD)
    change (Matrix.trace (D * D)).re = 0 at hzero
    have hpsd := posSemidef_conjTranspose_mul_self D
    have hnonneg := hpsd.trace_nonneg
    have him : (Matrix.trace (Dᴴ * D)).im = 0 := (Complex.nonneg_iff.mp hnonneg).2.symm
    have htrace : Matrix.trace (Dᴴ * D) = 0 := by
      apply Complex.ext
      · simpa only [hD.eq, Complex.zero_re] using hzero
      · exact him
    have hz : D = 0 := trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
    exact sub_eq_zero.mp hz
  have inv : ∀ t, t ≤ N →
      (∃ a, accumulated H R B E t a = 0) ∨
      ∃ c : A → ℝ, (∀ a, 0 < c a ∧
        gram (accumulated H R B E t a) = (c a : ℂ) • 1) ∧ (∏ a, c a) = p t := by
    intro t
    induction t with
    | zero =>
      intro ht
      right
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro a
        simp [accumulated, root]
      · have hp := probability 0 ht i₀
        simpa [accumulated, root, readout, normalized] using hp
    | succ t ih =>
      intro ht
      rcases ih (Nat.le_trans (Nat.le_succ t) ht) with ⟨a, ha⟩ | ⟨c, hc, hcp⟩
      · left
        exact ⟨a, by simp [accumulated, ha]⟩
      · let b := actor t
        have unchanged (a : A) (hab : a ≠ b) :
            gram (accumulated H R B E (t+1) a) = (c a : ℂ) • 1 := by
          obtain ⟨e, he⟩ := inactive t a hab
          simp only [accumulated, gram, he, conjTranspose_mul, conjTranspose_submatrix,
            conjTranspose_one]
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc
            ((1 : Matrix (R t a) (R t a) ℂ).submatrix id e)]
          rw [Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id,
            Matrix.one_mul]
          exact (hc a).2
        let d : ℝ := ∏ a ∈ Finset.univ.erase b, c a
        have hd : 0 < d := Finset.prod_pos (fun a _ => (hc a).1)
        let q : ℝ := readout (gram (accumulated H R B E (t+1) b)) (s b i₀)
        have hq : 0 ≤ q := positive_eval (t+1) b i₀
        have observations (i : I) :
            readout (gram (accumulated H R B E (t+1) b)) (s b i) * d = p (t+1) := by
          rw [← probability (t+1) ht i, ← Finset.mul_prod_erase Finset.univ
            (fun a => readout (gram (accumulated H R B E (t+1) a)) (s a i))
            (Finset.mem_univ b)]
          congr 1
          apply Finset.prod_congr rfl
          intro a ha
          rw [unchanged a (Finset.mem_erase.mp ha).1, scalar_eval]
        have hsame (i : I) : readout (gram (accumulated H R B E (t+1) b)) (s b i) = q := by
          apply mul_right_cancel₀ (ne_of_gt hd)
          exact (observations i).trans (observations i₀).symm
        have hg : gram (accumulated H R B E (t+1) b) = (q : ℂ) • 1 :=
          separation b _ (isHermitian_conjTranspose_mul_self _) q hsame
        by_cases hq0 : q = 0
        · left
          refine ⟨b, conjTranspose_mul_self_eq_zero.mp ?_⟩
          simpa [hq0, gram] using hg
        · right
          refine ⟨Function.update c b q, ?_, ?_⟩
          · intro a
            by_cases hab : a = b
            · subst a
              simpa using And.intro (lt_of_le_of_ne hq (Ne.symm hq0)) hg
            · simpa [Function.update_of_ne hab] using And.intro (hc a).1 (unchanged a hab)
          · rw [← Finset.mul_prod_erase Finset.univ (Function.update c b q) (Finset.mem_univ b)]
            simp only [Function.update_self]
            have he : (∏ a ∈ Finset.univ.erase b, Function.update c b q a) = d := by
              apply Finset.prod_congr rfl
              intro a ha
              exact Function.update_of_ne (Finset.mem_erase.mp ha).1 _ _
            rw [he]
            exact observations i₀
  intro t ht
  rcases inv t ht with ⟨a, ha⟩ | ⟨c, hc, hcp⟩
  · left
    refine ⟨?_, ⟨a, ha⟩, ?_⟩
    · rw [← probability t ht i₀]
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      simp [ha, gram, readout]
    · ext y x
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])
  · right
    have hp : 0 < p t := by
      rw [← hcp]
      exact Finset.prod_pos (fun a _ => (hc a).1)
    refine ⟨hp, c, hc, hcp, ?_⟩
    let V : ∀ a, Matrix (R t a) (H a) ℂ :=
      fun a => ((Real.sqrt (c a) : ℂ)⁻¹) • accumulated H R B E t a
    have hs (a : A) : (Real.sqrt (c a) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (hc a).1)
    have hsq (a : A) : (Real.sqrt (c a) : ℂ) * (Real.sqrt (c a) : ℂ) = (c a : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (hc a).1.le
    have hV (a : A) : gram (V a) = 1 := by
      simp only [V, gram, conjTranspose_smul,
        Complex.star_def, map_inv₀, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [← gram, (hc a).2]
      simp only [smul_smul]
      rw [← hsq a]
      simp [hs a, mul_assoc]
    have hrec (a : A) : accumulated H R B E t a = (Real.sqrt (c a) : ℂ) • V a := by
      simp [V, smul_smul, hs a]
    refine ⟨V, ?_, ?_⟩
    · intro a
      refine ⟨hV a, hrec a, ?_⟩
      intro x y
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
      change star x ⬝ᵥ (gram (V a) *ᵥ y) = _
      rw [hV, one_mulVec]
    · ext y x
      change (∏ a, accumulated H R B E t a (y a) (x a)) =
        (Real.sqrt (p t) : ℂ) * (∏ a, V a (y a) (x a))
      simp_rw [hrec, Matrix.smul_apply, smul_eq_mul]
      rw [Finset.prod_mul_distrib]
      congr 1
      rw [← Complex.ofReal_prod, ← Real.sqrt_prod _ (fun a _ => (hc a).1.le), hcp]

end D5.S3.Quantum.Recovery.ProductPrefixRigidity

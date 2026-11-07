/- GID: D5/S3/Quantum/Algebra/JordanOutputBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/JordanOutputBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: Square-controlled Jordan derivations have the actual-output square-root-three bound. -/

module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Estimates on the original normed carrier; completeness is not required. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.JordanOutputBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem inner_leibniz
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hcomm : ∀ x y, S x y = S y x)
    (hjordan : ∀ x y, S (S x y) (S x x) = S x (S y (S x x)))
    (r s x y : E) :
    S s (S r (S x y)) - S r (S s (S x y)) =
      S (S s (S r x) - S r (S s x)) y +
        S x (S s (S r y) - S r (S s y)) := by
  let _ : NonUnitalNonAssocCommRing E :=
    { (inferInstance : AddCommGroup E) with
      mul := fun a b => S a b
      left_distrib := fun a b c => (S a).map_add b c
      right_distrib := fun a b c => congrArg (fun f : E →ₗ[ℝ] E => f c) (S.map_add a b)
      zero_mul := fun a => congrArg (fun f : E →ₗ[ℝ] E => f a) S.map_zero
      mul_zero := fun a => (S a).map_zero
      mul_comm := hcomm }
  let _ : IsCommJordan E := ⟨hjordan⟩
  have lin (a b c d : E) :
      a * ((b * c) * d) - (b * c) * (a * d) +
      (b * ((c * a) * d) - (c * a) * (b * d)) +
      (c * ((a * b) * d) - (a * b) * (c * d)) = 0 := by
    have h := congrArg (fun f : AddMonoid.End E => f d)
      (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c)
    let z := a * ((b * c) * d) - (b * c) * (a * d) +
      (b * ((c * a) * d) - (c * a) * (b * d)) +
      (c * ((a * b) * d) - (a * b) * (c * d))
    simp only [two_smul, Ring.lie_def] at h
    change z + z = 0 at h
    have hz : (2 : ℝ) • z = 0 := by simpa only [two_smul] using h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  have h1 := lin s x y r
  have h2 := lin r x y s
  change s * (r * (x * y)) - r * (s * (x * y)) =
    (s * (r * x) - r * (s * x)) * y +
      x * (s * (r * y) - r * (s * y))
  simp only [mul_sub, sub_mul] 
  simp only [mul_comm] at h1 h2 ⊢
  linear_combination (norm := abel) h1 - h2

/-- A derivation whose square is the associator operator is bounded without
assuming that the underlying normed space is complete. -/
private theorem norm_derivation_le
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hnorm : ∀ x y : E, ‖S x y‖ ≤ ‖x‖ * ‖y‖)
    (hsq : ∀ x : E, ‖S x x‖ = ‖x‖ ^ 2)
    (δ : E →ₗ[ℝ] E) (q : E)
    (hder : ∀ x y, δ (S x y) = S (δ x) y + S x (δ y))
    (hdelta : ∀ x, δ (δ x) = S q (S q x) - S (S q q) x)
    (b : E) : ‖δ b‖ ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ := by
  have hH (x : E) : ‖δ (δ x)‖ ≤ 2 * ‖q‖ ^ 2 * ‖x‖ := by
    rw [hdelta]
    calc
      ‖S q (S q x) - S (S q q) x‖ ≤ ‖S q (S q x)‖ + ‖S (S q q) x‖ := norm_sub_le _ _
      _ ≤ ‖q‖ * (‖q‖ * ‖x‖) + ‖q‖ ^ 2 * ‖x‖ := by
        exact add_le_add ((hnorm _ _).trans
          (mul_le_mul_of_nonneg_left (hnorm _ _) (norm_nonneg _)))
          (by simpa only [hsq] using hnorm (S q q) x)
      _ = 2 * ‖q‖ ^ 2 * ‖x‖ := by ring
  have htwice : δ (δ (S b b)) =
      (S (δ (δ b)) b + S b (δ (δ b))) + (S (δ b) (δ b) + S (δ b) (δ b)) := by
    rw [hder, map_add, hder, hder]
    abel
  have hid : S (δ b) (δ b) + S (δ b) (δ b) =
      δ (δ (S b b)) - (S (δ (δ b)) b + S b (δ (δ b))) := by
    rw [htwice]
    abel
  have htwo : 2 * ‖δ b‖ ^ 2 ≤ 6 * ‖q‖ ^ 2 * ‖b‖ ^ 2 := by
    calc
      2 * ‖δ b‖ ^ 2 = ‖S (δ b) (δ b) + S (δ b) (δ b)‖ := by
        rw [← two_smul ℝ, norm_smul, hsq]
        norm_num
      _ ≤ ‖δ (δ (S b b))‖ + ‖S (δ (δ b)) b + S b (δ (δ b))‖ := by
        rw [hid]
        exact norm_sub_le _ _
      _ ≤ 2 * ‖q‖ ^ 2 * ‖S b b‖ +
          (‖S (δ (δ b)) b‖ + ‖S b (δ (δ b))‖) :=
        add_le_add (hH _) (norm_add_le _ _)
      _ ≤ 2 * ‖q‖ ^ 2 * ‖b‖ ^ 2 +
          ((2 * ‖q‖ ^ 2 * ‖b‖) * ‖b‖ + ‖b‖ * (2 * ‖q‖ ^ 2 * ‖b‖)) := by
        rw [hsq]
        exact add_le_add le_rfl (add_le_add
          ((hnorm _ _).trans (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _)))
          ((hnorm _ _).trans (mul_le_mul_of_nonneg_left (hH _) (norm_nonneg _))))
      _ = 6 * ‖q‖ ^ 2 * ‖b‖ ^ 2 := by ring
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ := by positivity
  apply le_of_sq_le_sq _ hpos
  calc
    ‖δ b‖ ^ 2 ≤ 3 * ‖q‖ ^ 2 * ‖b‖ ^ 2 := by linarith
    _ = (Real.sqrt 3 * ‖q‖ * ‖b‖) ^ 2 := by rw [mul_pow, mul_pow, hsqrt]

/-- The square-root-three estimate applies to the actual range of the same
total relation. Only the stated algebraic recovery identities are used;
linearity, continuity and boundedness of the raw relation are not assumed. -/
theorem actual_output_bound
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hcomm : ∀ x y, S x y = S y x)
    (hjordan : ∀ x y, S (S x y) (S x x) = S x (S y (S x x)))
    (hnorm : ∀ x y : E, ‖S x y‖ ≤ ‖x‖ * ‖y‖)
    (hsq : ∀ x : E, ‖S x x‖ = ‖x‖ ^ 2)
    (D : E → E → E)
    (hskew : ∀ a b, D a b = -D b a)
    (hrow : ∀ a b c, D (D a b) c = S b (S a c) - S a (S b c))
    (hR : ∀ a b c, S (S a b) c - S a (S b c) =
      D (D a b) c - D a (D b c))
    {q : E} (hq : q ∈ Set.range (fun p : E × E => D p.1 p.2)) (b : E) :
    ‖D q b‖ ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ ∧
      ‖D b q‖ ≤ Real.sqrt 3 * ‖q‖ * ‖b‖ := by
  obtain ⟨⟨r, s⟩, rfl⟩ := hq
  let δ : E →ₗ[ℝ] E := (S s).comp (S r) - (S r).comp (S s)
  have hδ (x : E) : δ x = D (D r s) x := (hrow r s x).symm
  have hder (x y : E) : δ (S x y) = S (δ x) y + S x (δ y) :=
    inner_leibniz S hcomm hjordan r s x y
  have hdelta (x : E) : δ (δ x) =
      S (D r s) (S (D r s) x) - S (S (D r s) (D r s)) x := by
    have hsquare (a b : E) : D a (D a b) = S a (S a b) - S (S a a) b := by
      have haa : D a a = 0 := by
        have ht : D a a + D a a = 0 := by
          calc
            D a a + D a a = -D a a + D a a := congrArg (· + D a a) (hskew a a)
            _ = 0 := neg_add_cancel _
        have ht' : (2 : ℝ) • D a a = 0 := by simpa only [two_smul] using ht
        exact (smul_eq_zero.mp ht').resolve_left (by norm_num)
      have hz : D 0 b = 0 := by simpa only [haa, sub_self] using hrow a a b
      have hr := hR a a b
      rw [haa, hz, zero_sub] at hr
      simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hr).symm
    rw [hδ, hδ, hsquare]
  have h := norm_derivation_le S hnorm hsq δ (D r s) hder hdelta b
  rw [hδ] at h
  refine ⟨h, ?_⟩
  simpa only [hskew b (D r s), norm_neg] using h

end D5.S3.Quantum.Algebra.JordanOutputBound

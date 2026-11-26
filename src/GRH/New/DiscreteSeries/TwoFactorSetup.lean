import GRH.New.DiscreteSeries.GaussianShape
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Steep parameters, phase cancellation; integrand is large only near diagonal U(X). -/

noncomputable section

open Finset Matrix Norms.Frobenius Complex ComplexConjugate Set ComplexOrder Int HCParam Sgn


variable {n m X S : Type} [Fintype n] [Fintype m] [Fintype X] [Group S] {ε} (l : @HCParam n ε) {η}
  (k : @HCParam m η) (j : S →* USign ε × USign η) (τ : X → m) (B : ℝ) {M} (e : X ⊕ Fin M ≃ n) (φ :
  S → ℂ) {u : Matrix X X ℂ}

/-- For a pair of matrices x = (x₁, x₂), the number tr(Λx₁) − tr(Λ'x₂), with Λ, Λ' the diagonal
matrices of the weights `HCParam.lowestKType` of l and k. -/
def HCParam.phase (x : Matrix n n ℂ × Matrix m m ℂ) :=
  (intDiagonal l.lowestKType * x.1).trace - (intDiagonal k.lowestKType * x.2).trace

/-- With indices numbered by X and 0 ≤ i < M: sign + and Λ = 0 on X; on the rest, signs (−1)^i
and Λ strictly decreasing within [−3B, −B]. -/
structure IsSteep where
  sign_inl x : ε (e (.inl x)) = 1
  sign_inr i : ε (e (.inr i)) = (-1) ^ i.1
  weight_eq_zero x : l.lowestKType (e (.inl x)) = 0
  weight_strictAnti : StrictAnti fun i ↦ l.lowestKType (e (.inr i))
  weight_mem i : (l.lowestKType (e (.inr i)) : ℝ) ∈ Icc (-3 * B) (-B)

/-- For a homomorphism j : S → U(diag ε) × U(diag η) and s in S, the pair of matrices (g − 1, g'
− 1), where j(s) = (g, g'). -/
abbrev subOnePair s := ((j s).1.1.1 - 1, (j s).2.1.1 - 1)

/-- For parameters l = 2λ, k = 2λ', j(s) = (g, g') and any function φ on S, the function θ(s) =
ψ_λ(g) conj(ψ_λ'(g')) e^{−φ(s)}. -/
def HCParam.laplaceIntegrand s := l.dsCoeff (j s).1 * conj (k.dsCoeff (j s).2) * cexp (-φ s)

/-- Hypotheses for Laplace's method on S, j(s) = (g, g'): `IsSteep`; φ = tr Λ(g−1) − tr
Λ'(g'−1), additive, imaginary; tr(g−1) = tr(g'−1); j(S) contains U(X) diagonally; sign and
size conditions on Λ'. -/
structure IsTwoFactor extends IsSteep l B e where
  phase_eq s : l.phase k (subOnePair j s) = φ s
  trace_eq s : (subOnePair j s).1.trace = (subOnePair j s).2.trace
  phase_mul s t : φ (s * t) = φ s + φ t
  re_phase s : (φ s).re = 0
  sign_weight_right x : η (τ x) = 1 ∧ k.lowestKType (τ x) = 0
  weight_bounds_right i i' : 0 ≤ k.lowestKType i ∧ (η i ≠ η i' → k.lowestKType i ≤ 3 * B)
  exists_diagonal : ∀ u ∈ unitaryGroup X ℂ, ∃ s, subOnePair j s = (inclMatrix ℂ (e ∘ .inl) *
    (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ, inclMatrix ℂ τ * (u - 1) * (inclMatrix ℂ τ)ᴴ)

attribute [local simp] diagonal_apply phase Matrix.mul_apply

lemma exists_unitary_sub_one_eq_inclMatrix {Y} [Fintype Y] (e : X ⊕ Y ≃ n) (h : ∀ x,
  ε (e (.inl x)) = 1) (k : uᴴ * u = 1) : ∃ s : USign ε, s.1.1 - 1 =
  inclMatrix ℂ (e ∘ .inl) * (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ := ⟨U.of IsHermInvolution.isUnit _
  (by simp_all [← ext_iff, inclMatrix, signMatrix, reindex_equiv e]), add_sub_cancel_left ..⟩

lemma norm_sq_add_re_trace_le (g : USign ε) (a C : ℝ) (v w : n → ℤ) (h : ∀ i j, a * v i ^ 2 ≤ w i ∧
    (ε i ≠ ε j → w i ≤ C)) : a * ‖intDiagonal v * (g.1.1 - 1)‖ ^ 2 + 2 *
  (intDiagonal w * (g.1.1 - 1)).trace.re ≤ 2 * C * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 := by
  rw [(?_ : 2 * _ = (intDiagonal w * ((g - 1) * (1 - g.1⁻¹))).trace.re)]
  simp [frobenius_norm_sq_eq_sum, trace, mul_sum, ← sum_add_distrib, blockDiagPart, eq_comm]
  gcongr with i _ j; cases h i j
  split_ifs <;> simp_all [mul_right_comm, ← cast_mul, mul_pow,
    Complex.sq_norm, normSq, signMatrix, U.inv_mat] <;> nlinarith
  simp [↓mul_sub, ↓sub_mul, ↓Units.mul_inv, trace, signMatrix, U.inv_mat, mul_right_comm,
    ← cast_mul]; ring

variable {l k j τ B e φ}

lemma IsTwoFactor.phase_logOneAdd (H :
  IsTwoFactor l k j τ B e φ) s (a : ‖(subOnePair j s).1‖ ≤ 2⁻¹) (b : ‖(subOnePair j s).2‖ ≤ 2⁻¹) :
  l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s := by
  have p i t : l.phase k (subOnePair j s ^ i * subOnePair j s * (1 + subOnePair j t)) = 0 ^ i * φ
    s := by induction' i with i h generalizing t <;> [have := H.phase_mul s t; have := h (s *
    t)] <;> simp_all [← H.phase_eq, pow_succ, sub_mul, mul_sub] <;> grind
  have := intervalIntegral.integral_congr_Ioo_of_le (μ := by volume_tac) zero_le_one fun r o ↦
    have G {n} [Fintype n] {X D : Matrix n n ℂ} (h : ‖X‖ ≤ 2⁻¹) :=
      ((hasSum_geom_series_inverse (-r • X) (by simp; grind [norm_smul_le_of_le_one r h])).mul_right
      X).mapL (traceLinearMap .. ∘ₗ .mulLeft ℂ D).toContinuousLinearMap
    ((G a).sub (G b)).unique (hasSum_single 0 fun i _ ↦ by
      simpa [↓smul_pow, *] using Or.inl (p i 1))
  simp_all [← H.phase_eq, trace_mul_logOneAdd, ← nonsing_inv_eq_ringInverse]

open MatMul

lemma dsCoeff_mul_eq_of_zero_weight_block {σ} (z : ∀ x : X, ε (σ x) = 1 ∧ l.lowestKType (σ x) = 0)
  {k g t : USign ε} (hk : k.1.1 - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) (e : t = k * g) :
  intDiagonal l.lowestKType * (k.1.1 - 1) = 0 ∧ l.dsCoeff t =
  l.dsCoeff g ∧ ‖t.1.1 - 1‖ ^ 2 + 2 * (t.1.1 - 1).trace.re ≤ 2 * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 :=
  have F i j : i ∉ range σ ∨ j ∉ range σ → k.1 i j = ite (i = j) 1 0 := by
    simp_all [or_imp, sub_eq_iff_eq_add, inclMatrix, eq_comm]
  have M x : weightMinors l.lowestKType (k * x) = weightMinors l.lowestKType x :=
    finprod_congr fun t ↦ by rw [principalMinor_mul (by grind), principalMinor_eq_det,
    (?_ : 1 - _ = ite (t ≤ 0) k.1.1 1)] <;> split <;> simp [field, ← ext_iff] <;> grind
  have c : ↑k ∈ blockDiagAlg ε := by grind [mem_blockDiagAlg]
  ⟨ext (by simp; grind), by
    simpa [*, ← frobenius_norm_mul_of_unitary (U_one_mem_unitaryGroup ⟨_, mem_maxCompactU.2 c⟩).1
      (g - _), dsCoeff, flenstedJensen] using norm_sq_add_re_trace_le t 1 1 1 1⟩

lemma norm_dsCoeff_pow_four_le {h} [hg : l.HasLargeGap h] (g : USign ε) : ‖l.dsCoeff g‖ ^ 4 ≤
  (1 + ‖g.1.1 - blockDiagPart ε g‖ ^ 2)⁻¹ ^ h := by
  have b (X : Matrix n n ℂ) (H := X.posSemidef_conjTranspose_mul_self) (e := H.eigenvalues_nonneg) :
      1 + ‖X‖ ^ 2 ≤ ‖(Xᴴ * X).charpoly.eval (-1)‖ := by
    rw [← ofReal_re (_ ^ 2), ← trace_star_mul_self_eq_norm_sq]; simpa [H.1.charpoly_eq,
      Polynomial.eval_prod, ← neg_add',
      -neg_add_rev, *, H.1.trace_eq_sum_eigenvalues, add_nonneg, ← re_eq_norm.2] using
      univ.induction_on (by simp) (by simp_intro a s ..; nlinarith [e a, s.sum_nonneg' e])
  grw [b, eval_charpoly, (?_ : _ - _ = -((blockDiagPart ε g)ᴴ * blockDiagPart ε g)), pow_mul _ 2 2,
    det_neg, (le_div_iff₀ _).2 (norm_dsCoeff_sq_mul_det_pow_le_one hg (by bound) g)] <;> simp [sq,
    mul_pow, ↓map_neg]
  linear_combination (norm := (simp [blockDiagPart_eq, IsHermInvolution.mul_self,
    IsHermInvolution.isHermitian.eq]; module)) congr(blockDiagPart ε ($(g.2) * signMatrix ε))

/-- Assume `IsTwoFactor`, B ≥ 1, 0 < r ≤ 1/100. If j(s) = (g, g') has ‖g−a_g‖²+‖g'−a_{g'}‖² ≤ r²
(Frobenius, a the block diagonal part), some t has θ(t) = θ(s), θ = `HCParam.laplaceIntegrand`, with
both components of j(t)−1 of norm ≤ 10r. -/
lemma IsTwoFactor.exists_near_one (H : IsTwoFactor l k j τ B e φ) r (hB : 1 ≤ B) (e0 : 0 < r) (he :
  r ≤ 100⁻¹) s (h : ‖(j s).1.1.1 - blockDiagPart ε (j s).1‖ ^ 2 + ‖(j s).2.1.1 - blockDiagPart η
  (j s).2‖ ^ 2 ≤ r ^ 2) : ∃ t, l.laplaceIntegrand k j φ s =
  l.laplaceIntegrand k j φ t ∧ ‖(subOnePair j t).1‖ ≤ 10 * r ∧ ‖(subOnePair j t).2‖ ≤ 10 * r := by
  let χ i : ℤ := (e.symm i).elim 0 1
  obtain ⟨K, R⟩ := H.exists_diagonal, norm_sq_add_re_trace_le (j s).1 B (3 * B) χ (-l.lowestKType),
    H.phase_eq s ▸ H.re_phase s, norm_sq_add_re_trace_le (j s).1 (-1) 0 χ (-χ),
    norm_sq_add_re_trace_le (j s).2 0 _ 0 _ (mod_cast H.weight_bounds_right)
  set Q := inclMatrix ℂ _
  have : Qᴴ * Q = 1 ∧ intDiagonal χ = 1 - Q * Qᴴ ∧ signMatrix ε * Q = Q := by
    simp [← ext_iff, reindex_equiv e, Q, inclMatrix, signMatrix, χ, H.sign_inl]
  simp [reindex_equiv e, χ, H.weight_eq_zero, ← diagonal_neg, -Matrix.mul_sub, -Matrix.sub_mul] at *
  set c := _ * (subOnePair j s).1
  have : ‖c‖ ^ 2 ≤ 6 * r ^ 2 := by nlinarith [R (by bound) (by grind [IsTwoFactor, IsSteep])]
  have ⟨⟨_, f, _⟩, v⟩ := inv_one_add_bounds (norm_smul_of_nonneg one_half_pos.le c).le
  set W : Matrix n n ℂ := _⁻¹
  let N := (subOnePair j s).1 * W * Q
  have a := mem_unitaryGroup_iff (A := 1 + Nᴴ * Q).2 (by
    linear_combination (norm := (simp [star, N, c, *, IsHermInvolution.isHermitian.eq,
      ← (signMatrix ε).mul_assoc Q]; module)) congr(Qᴴ * Wᴴ *
      $((j s).1.2) * W * Q - (signMatrix ε * $f * Q)ᴴ * N - Nᴴ * signMatrix ε * $f * Q))
  let ⟨s₀, h₁, h₂⟩ := K _ a
  let T := (subOnePair j (s₀ * s)).1
  obtain ⟨k₁, k₂⟩ := dsCoeff_mul_eq_of_zero_weight_block (⟨H.sign_inl ·, H.weight_eq_zero _⟩)
    h₁ congr($(j.map_mul _ s).1), H.trace_eq _ ▸ dsCoeff_mul_eq_of_zero_weight_block
    H.sign_weight_right h₂ congr($(j.map_mul _ s).2), ((re_le_norm _).trans (norm_trace_mul_le
    (norm_sub_le T c) v)).trans_eq' (by linear_combination (norm := (simp +zetaDelta
    [eq_add_of_sub_eq h₁, Q.trace_mul_comm, star, ← Qᴴ.mul_assoc Q, *]; ring)) congr(($(a.2) +
    Nᴴ * Q * Qᴴ * $f * Q).trace.re) : _ = c.trace.re - T.trace.re), sq_nonneg (‖T‖ - 2 * ‖c‖)
  use s₀ * s, by simp [laplaceIntegrand, H.phase_mul, ← H.phase_eq, ↓k₁, ↓k₂], ?_, ?_ <;> nlinarith

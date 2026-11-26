import GRH.Lib.General.LinearAlgebra.FramedCoefficient
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Second-order expansion of log principal minors near 1 with absolute error constants. -/

open Ring Matrix Norms.Frobenius Complex intervalIntegral


variable {n} [Fintype n] {P Q X Y : Matrix n n ℂ} {ε h} {l : @HCParam n ε} {δ c : ℝ}
attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem principalMinor_eq_det coordProj

/-- For orthogonal projections P, Q and Hilbert–Schmidt norms, let ‖X‖ ≤ δ ≤ ½, tr([P,Q]Y) = 0,
‖[P,X]−Y‖ ≤ δc, ‖Y‖, ‖Q−P‖ ≤ c. Then det(1+PX) = exp(tr(Q·lg X) − ¼tr Y² + r) with |r| ≤
100δc², where lg is `logOneAdd`. -/
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hδ :
  δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h0 : (⁅P, Q⁆ * Y).trace = 0) (h1 : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤
  c) (hD : ‖Q - P‖ ≤ c) : ∃ r, (1 + P * X).det = cexp
  ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧ ‖r‖ ≤ 100 * δ * c ^ 2 := by
  obtain ⟨p, ⟨δ0, _⟩ : 0 ≤ δ ∧ 0 ≤ c⟩ := norm_proj_mul_le hP hX, by grind [norm_nonneg]
  obtain ⟨a, ⟨i, d⟩, j, k⟩ := (norm_le_insert' _ Y).trans (by grw [hY, h1, hδ]),
    trace_mul_logOneAdd (p.trans hδ) 1, trace_mul_logOneAdd (hX.trans hδ) Q
  refine ⟨_, ?_, congr(‖$(integral_add (i.sub j) (.mul_const (continuous_ofReal.intervalIntegrable
    ..) (2⁻¹ * (Y * Y).trace)))‖).ge.trans
    ((norm_integral_le_of_norm_le_const fun s h ↦ ?_).trans (by aesop))⟩
  simp_all [det_one_add_eq_exp_trace_logOneAdd (p.trans hδ), integral_ofReal]; ring
  obtain ⟨⟨⟨_, f, F⟩, w⟩, ⟨_, e, E⟩, v⟩ := inv_one_add_bounds (norm_smul_le_of_le_one s hX),
    inv_one_add_bounds (norm_smul_le_of_le_one s p)
  set W := (1 + s • X)⁻¹; set V := (1 + s • (P * X))⁻¹; set A := ⁅P, X⁆; set D := Q - P
  let Z := W - 1; let N := Z * (A * Z + A) + A * Z
  rw [show _ + _ = trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) - trace (s • (P *
    A) * ((N + A) * (V - 1) + N)) - trace ((D - P * D - P * D) * D * (X + Z * X)) - trace ((s / 2) •
    (A - Y) * (A + Y)) by
      linear_combination (norm := (
      simp +zetaDelta [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul]; ring))
        h0 + congr(($E * P * W * X * P + V * P * (A * ($F * P * (1 - W) + W * P *
      $f) - $f * X * P) + (1 - P) * $e * P * X - ⁅P, D⁆ * ($F * P * W - W * P * $f) * X).trace)]
  apply le_trans; apply_rules (transparency :=
    .reducible) (maxDepth := 99) [@norm_smul_le_of_le_one, norm_proj_mul_le hP, norm_proj_mul_le hQ,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le] <;> grind
  nlinarith [mul_nonneg δ0 (sq_nonneg c), sq_nonneg (δ * c)]

/-- Let λ have gap h, X = g−1, ‖X‖ < 10⁻³ (Frobenius). Some y has ψ_λ(g) =
`HCParam.flenstedJensen`(1,y) and, for k∈K and projectors P to sets p of lowest entries of λ,
Δ_p(k*yk) = exp(tr(P log g)+‖[P,X]‖²/4+r), |r| ≤ 2·10⁵‖X‖(‖[P,X]‖²+‖[P,k]‖²). -/
lemma exists_principalMinor_eq_exp (hg : l.HasGap h) (g : USign ε) : let X :=
    g.1.1 - 1; ‖X‖ < 1000⁻¹ → ∃ y, l.dsCoeff g = l.flenstedJensen 1 y ∧ ∀ p [DecidablePred p],
    (∀ i j, p i → ¬p j → l i < l j) → ∀ k : maxCompactU ε, let k := k.1.1.1; ∃ r, principalMinor
      (kᴴ * y * k) p = cexp ((coordProj p * logOneAdd X).trace + ‖⁅coordProj p, X⁆‖ ^ 2 / 4 + r)
    ∧ ‖r‖ ≤ 200000 * ‖X‖ * (‖⁅coordProj p, X⁆‖ ^ 2 + ‖⁅coordProj p, k⁆‖ ^ 2) := by
  intro X _; let r l := lowerMask ε l X; let u := r (-l)
  obtain ⟨⟨i, j⟩ : ‖X‖ ≤ 2⁻¹ ∧ 4 * ‖X‖ ≤ 2⁻¹, δ0, hX⟩ := by grind, norm_nonneg X, le_refl ‖X‖
  let y c := (1 - u) * g * (1 - r c); let m := X - u - u * X; have T c : ‖y c - 1‖ ≤ 4 * ‖X‖
  rw [(by grind : _ - 1 = m - r c - m * r c)]; swap
  use y l, ?_, ?_
  · have A c := isAccretive_of_norm_sub_one_lt ((T c).trans_lt (by bound))
    obtain ⟨a, b⟩ :=
      isAccretive_of_norm_sub_one_lt (by bound), by simpa [y, show r 0 = 0 from rfl] using A 0
    have := (flenstedJensen_shift_eq_conj hg (u := (r l)ᴴ) (by simp [r]; grind) (by
      simpa [IsAccretive, add_comm] using b) (by simpa [y, IsAccretive, add_comm] using A l)).trans
      (congrArg _ (flenstedJensen_shift_eq_conj hg (by simp_all [u, r]) a b))
    simp_all [dsCoeff_eq_flenstedJensen hg (one_mem _), y]
  have I p [DecidablePred p] (hp : ∀ i j, p i → ¬p j → l j < l i) : principalMinor (y l) p =
    principalMinor g p := by
    clear * - hp hg; rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.1, mul_comm, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.neg.1] <;> simp [u, r, BlockTriangular] <;> grind
  intro p _ hp κ k; let s := signMatrix ε
  obtain ⟨w : kᴴ * k = 1, o : k ∈ _, hP, d : Commute s (coordProj p)⟩ := (U_one_mem_unitaryGroup ⟨_,
    κ.2⟩).1, mem_maxCompactU.1 κ.2, isStarProjection_coordProj p, commute_diagonal ..
  set P := coordProj p; set A := ⁅P, X⁆; set B := ⁅P, u⁆; set C := ⁅P, r l⁆; set G := B * X + u * A
  let Q := k * P * kᴴ; let V := (1 + X)⁻¹ - 1; let H := G + m * C - (G + B - A) * r l
  have ⟨N, E⟩ : (∀ c, ⁅P, r c⁆ = lowerMask ε c A) ∧ B = blockDiagPart ε A - C := by
    simp +zetaDelta [← ext_iff, blockDiagPart]; grind
  have M x : (1 + (1 - P) * (x - 1)).det =
    principalMinor x (¬p ·) := by simp [P, det_apply, sub_mul]; grind
  obtain ⟨R, a, b, W, _ : Pᴴ = P, _, _, _ : gᴴ = s * g.1.1⁻¹ * s⟩ := hP.one_sub, norm_nonneg A,
    norm_nonneg ⁅P, k⁆, mul_eq_one_symm w, hP.2, (inv_one_add_bounds hX i).2,
    (N · ▸ norm_entryMask_le), by grind [U.inv_mat, signMatrix_mul_self]
  have := ((by simp [Q, mul_sub, ← mul_assoc, *] : k * ⁅P, k⁆ᴴ =
    P - Q) ▸ frobenius_norm_mul_of_unitary w _).trans_le (norm_star _).le
  have ⟨x, e, _⟩ := exists_det_compress_eq_exp_logOneAdd R R i hX ?_ (by simp [A, mul_sub, sub_mul,
    mul_nonneg]) (norm_neg A).le (by simp)
  have ⟨z, f, _⟩ := exists_det_compress_eq_exp_logOneAdd (Y :=
    B + C - A) (c := 4 * ‖A‖) R R j (T l) ?_ ?_ ?_ (by simp)
  have ⟨t, q, _⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := A - B - C) (c := 4 * (‖A‖ +
    ‖⁅P, k⁆‖)) (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, w, W⟩)) hP j (T l) ?_ ?_ ?_ (by linarith)
  rw [M, I _ (by tauto), ← M, e] at f
  use t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace, .trans (by
    simp [det_one_add_mul_comm k, Q, P]; noncomm_ring [w]) (q.trans (mul_right_cancel₀ (by simp)
    (congr(_ * ($f * $((det_one_add_eq_exp_trace_logOneAdd ((T l).trans j)).symm.trans
    (.trans (by simpa [principalMinor_of_forall, X] using I ⊤)
    (det_one_add_eq_exp_trace_logOneAdd i))))).trans ?_))), ?_
  on_goal 7 => rw [(by simp +zetaDelta; noncomm_ring : _ - _ = H)]
  on_goal 4 => rw [(by simp +zetaDelta; noncomm_ring :
    _ - _ = (y l - 1) * (P - Q) - (P - Q) * (y l - 1) - H)]
  any_goals (apply le_trans; apply_rules (transparency := .reducible) [norm_entryMask_le.trans,
    @norm_smul_le_of_le_one,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le, le_rfl]; on_goal
    -1 => first | nlinarith only [δ0, j, b, mul_nonneg δ0 a, mul_nonneg δ0 (sq_nonneg ‖A‖),
                mul_nonneg δ0 (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖))] | nlinarith)
  all_goals simp [Q, V, s, *, blockDiagPart_eq, d.eq, trace_mul_comm P,
    (mem_blockDiagAlg_iff_commute.1 o).left_comm, ← ofReal_pow,
    A, X, inv_eq_left_inv w ▸ blockDiagAlg.inv_mem o _ rfl, trace_mul_comm k, trace_mul_comm kᴴ,
    trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add, mul_sub, sub_mul,
    ← trace_star_mul_self_eq_norm_sq, inv_le_one₀] <;> ring_nf

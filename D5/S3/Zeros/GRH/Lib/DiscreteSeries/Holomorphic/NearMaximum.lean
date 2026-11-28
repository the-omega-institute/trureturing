/- GID: D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/NearMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.DiscreteSeries.Holomorphic.NearMaximum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/DiscreteSeries/Holomorphic/NearMaximum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Staircase
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: A cusp form is large only away from the cusps (Siegel's argument). The statement
here is for unitary groups over a CM field, highest components of vector weights and forms of rapid
decay, with half the supremum in place of an attained maximum. The depth is the first minimum of the
lattice, and it is bounded below explicitly in weight and level. Source: C. Poor, D. Yuen, Linear
dependence among Siegel modular forms, Math. Ann. 318 (2000) 205-234, Thm 1.3; M. Eichler, Math.
Ann. 213 (1975) 281-291; for the factorisation, Gill, Golub, Murray, Saunders, Math. Comp. 28 (1974)
505-535.

This file: Rapidly decreasing holomorphic forms are large only away from cusps, explicit depth. -/

open NumberField Matrix Real Finset UpperHalfPlane Function Prod ComplexConjugate Space G
  Norms.L2Operator
attribute [local simp ←] dotProduct_mulVec stdForm_dotProduct_fst sqrt_inv Space.map_J exp_add
  exp_mul Real.exp_neg rpow_intCast sum_div exp_sub exp_sum mul_sum sum_mul coe_star_ringOfIntegers
  map_sum mat_snd mat_fst coe_algebraMap_Ô
attribute [local simp] vecMulVec_mul mul_vecMulVec vecMulVec_mulVec star_vecMul vecMul_diagonal
  vecMulVec_apply mul_sub sub_mul filter_or filter_eq' ne_of_gt exp_log mul_div div_mul_eq_mul_div
  sum_ite sub_mem ite_mem mul_assoc baseLattice star_mem_Ô sum_pos_iff_of_nonneg

/-- Let F ≠ 0 be rapidly decreasing, automorphic of level ς = −ς̄, Im Φ_wς ∈ (0,c], c ≥ 1,
holomorphic of weight in [−B,B], B ≥ 2, gap 1. Some z has F(z) ≠ 0, |F| ≤ 2|F(z)|, and
|F(g)| ≥ |F(z)| implies `Space.firstMinimum`(g) ≥ (Bc)^{−½}.

Known result: A cusp form is large only away from the cusps (Siegel's argument). -/
lemma exists_near_max {E n} [Field E] [CMType E] [Fintype n] {s : n → _} [Nonempty n] {V : Space E n
  s} {o u F} (B c) {ς : 𝓞 E} (ho : IsPosFirstOrder s o) (hu : ∀ w, HasHolGap s (u w) 1) (hu' :
  ∀ w i, |↑(u w i)| ≤ B) (h2 : 2 ≤ B) (c1 : 1 ≤ c) (hς : star ς = -ς) (hc : ∀ w, (Φ w ς.val).im ∈
  Set.Ioc 0 c) (hF : F ∈ rapidOfLevel V ς) (hH : IsAdelicHol o u F) (h0 : F ≠ 0) : ∃ z, F z ≠ 0 ∧
  (∀ x, ‖F x‖ ≤ 2 * ‖F z‖) ∧ ∀ g, ‖F z‖ ≤ ‖F g‖ → (√(B * c))⁻¹ ≤ (V.move g).firstMinimum := by
  have K w {η v t} y M (e : M = 1 - t • vecMulVec v (star v) * signMatrix s) (hv :
    star v ⬝ᵥ signMatrix s *ᵥ v = 0) (_ : 1 - Complex.re t * ∑ i, ‖v i‖ ^ 2 =
    y - η) (y0 : 1 < y) (_ : 0 < η) (_ : η ≤ 2⁻¹) : ∃ h b, IsBorelMatrix o b ∧ M =
    (h : USign s) * b ∧ ‖diagChar (u w) b‖ ≤ (2 * B * η).exp / √y := ?_
  have hB := le_ciSup ⟨_, Set.forall_mem_range.2 hF.1.2.bounded.choose_spec⟩
  have h1 := (norm_pos_iff.2 (ne_iff.1 h0).choose_spec).trans_le (hB _)
  peel exists_lt_of_lt_ciSup (half_lt_self h1)
  use by grind [norm_zero], by grind, fun g z ↦ le_firstMinimum_iff.2 ⟨?l, fun y hy _ ↦ ?_⟩
  simp [field]; bound
  by_contra! H
  have iso := form_eq_zero_of_norm_mul_lt_one hy hy (by simp [← sq, H.trans_le, field, ?l]) ▸
    stdForm_vecAtPoint ..
  simp [lt_sqrt, Space.archCoords, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, field] at H hy hc
  set Y := vecAtPoint _ y
  let t : G E s :=
    ofMat (1 - toAdele ς.val • vecMulVec Y (star Y) * stdForm _ s) (by simp [add_mul, *])
  have hp h := by simpa [↓mul_assoc, t.mul_def] using ((hF.1.1.2 (g * t * g⁻¹) (by
    simp [← V.mem_move_Γ, mem_Γ_iff_range, t, Y, Space.vecAtPoint, star_mulVec, -coe_units_inv,
      -mul_assoc, vecMul_apply_eq_sum, ← map_mul]) _).trans (congrFun (hF.2 ⟨t.2, by
    use ?_, (⟨-Y · * star Y · |>.2, ?_⟩) <;> simp (maxDischargeDepth := 4) [t, *, mem_Kf, stdForm,
      apply_ite snd, mul_mem]; rfl⟩⁻¹) (g * (h, 1))) :)
  let x ζ w := 1 - (Φ w ↑ς * (ζ - .I)) • vecMulVec (Y · |>.1 w) (star (Y · |>.1 w)) * signMatrix s
  let a w := (∑ i, ‖(Y i).1 w‖ ^ 2) * (Φ w ς).im
  have a0 w : 0 < a w := by simpa [ne_iff, a, *, sq_pos_iff] using eq_zero_of_vecAtPoint_fst.mt ‹_›
  grw [sum_mul, ← sum_le_sum fun _ _ ↦ by grw [← (hc _).2]] at H
  choose φ hol hF' using by simpa [IsHolOfWeight] using hH g
  choose h b T eq le using fun (z : ℍ) w ↦ K w (1 + z.im * a w) (x z w) rfl (by simp [*]) (by
    simp [by simpa [coe_star_ringOfIntegers, self_eq_neg] using congr((Φ w $hς).re)]; ring)
    (by simp [im_pos, *]) (a0 w) (by nlinarith [le_hasSum (hasSum_fintype a) w (by grind)])
  have hf (z : ℍ) := show ‖φ (x z)‖ ≤ _ by simp [funext (eq z), *]; grw [mul_comm, hB, le]
  have z0 : IsZeroAtImInfty _ := squeeze_zero_norm hf (((tendsto_finsetProd _ fun w _ ↦
    (tendsto_sqrt_atTop.comp (tendsto_const_nhds.add_atTop (.atTop_mul_const (a0 w)
    Filter.map_comap_le))).const_div_atTop _).const_mul _).trans (by simp))
  apply (Complex.dist_le_div_mul_dist_of_mapsTo_ball (differentiableOn_cuspFunction_ball one_pos
    ?P (fun z ↦ ((funext (eq z) ▸ hol _ _ (T z)).differentiableAt.comp _
    (by fun_prop)).comp_mdifferentiableAt z.mdifferentiable_coe) z0.boundedAtFilter) (fun q _ ↦ by
    by_cases! q ≠ 0 <;> simp [*, z0.cuspFunction_apply_zero]
    grw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero, comp_def, hf, ← a0, mul_zero]
    repeat positivity) (by simpa using norm_qParam_lt_one 1 .I)).not_gt
  erw [eq_cuspFunction .I one_ne_zero ?P]
  simp [↓z0.cuspFunction_apply_zero, x,
    Periodic.norm_qParam, by simpa [diagChar, IsBorelMatrix] using hF' 1 1]
  grw [← z, ← this, ← mul_one_div, ← exp_neg_one_lt_half]
  bound [two_le_pi]
  intro z; by_cases 0 < z.im; simpa [*, ofComplex_apply_eq_ite, ← eq, ← hF', fun w ↦ show t.1 w *
    x z w = x (z + 1) w by simp [show t.1 w = x (1 + .I) w by ext; simp [t, x, stdForm, signMatrix,
    apply_ite, ite_apply, -mul_sub], x, *]; module] using hF' (t.1 * h ⟨z, ‹_›⟩) (b ⟨z, ‹_›⟩)
  simp [*, ofComplex_apply_eq_ite]
  clear! F; obtain ⟨⟨hi, _⟩, s1, _, m, _⟩ := ho, (Int.units_eq_one_or <| s ·), (sq_nonneg ‖v ·‖),
    Finite.exists_max fun k ↦ s k * u w k
  let x k := ite (s k = 1) (‖v k‖ ^ 2) (-‖v k‖ ^ 2)
  have hx k : x k = conj (v k) * (s k * v k) := by cases s1 k <;> simp [*, x, RCLike.conj_mul]
  have X0 := by simpa [← Complex.ofReal_sum, ← hx, signMatrix, dotProduct] using hv
  let τ := 2 * t.re
  let p a := 1 - τ * ∑ l with o l < a, x l
  have p0 a : 0 < p a := sub_pos.2 (by
    grw [sum_filter, le_max_left τ 0, sum_le_sum (g := (‖v ·‖ ^ 2)) (by grind), max_def]
    exacts [by bound, (em _).elim sum_nonneg fun _ ↦ X0 ▸ sum_le_sum (by grind)])
  have pq k : p (o k + 1) = p (o k) - τ * x k := by simp [p, le_iff_eq_or_lt, hi.eq_iff]; ring
  let L k := (p (o k + 1)).log - (p (o k)).log
  let r k := (-L k / 2).exp / p (o k)
  let β l := s l * conj (v l) * r l
  let c := of fun k l ↦ ite (o k < o l) (v k * τ * β l) (ite (k = l) (r l * p (o l)) 0)
  have d : IsBorelMatrix o c := ⟨?D,
    det_eq_prod_diag_of_blockTriangular hi ?D ▸ by simp [prod_ne_zero_iff, c, r, *]⟩
  use U.of IsHermInvolution.isUnit (M * c) (ext fun i l ↦ ?_), c⁻¹, d.inv, by simp [d.2]
  have K := univ.sum_nonneg fun k _ ↦ show 0 ≤ L k * (ite (τ ≤ 0) ↑(u w m + (s m).1.toNat) B -
    ite (s k = 1) (ite (τ ≤ 0) 1 (2 * B)) 0 - u w k) by
    simp [L, ↓mul_nonneg_iff, p0, log_le_log_iff]; split <;> simp [*, mul_nonneg_iff,
      mul_nonpos_iff] <;> norm_cast <;> grind [HasHolGap, Units.val_one, Units.val_neg]
  have tel T : (∀ l ∉ T, ∀ k ∈ T, o k < o l) → Finset.sum T L = (1 - τ * T.sum x).log :=
    T.induction_on_max_value o (by simp) fun a S ↦ by
    intros; grind [show univ.filter (o · < o a) = S by grind]
  simp [diagChar, ↓d.inv_apply_diag hi, c, r, *, sqrt_eq_rpow, rpow_def_of_pos, y0.trans',
    (tel {k | s k = 1} (by grind)).trans (congrArg _ (by
    simp [x, filter_filter] at *; grind [sum_filter_add_sum_filter_not] : _ = y - η))] at K ⊢
  split at K <;> nlinarith [log_pos y0, show y.log ≤ (y - η).log + 2 * η by
    grw [log_le_iff_le_exp, exp_add, exp_log, ← add_one_le_exp] <;> nlinarith]
  wlog! a : o i ≤ o l generalizing i l
  simpa [← conjTranspose_apply] using congr(star $(this l i a.le))
  rw [show _ * _ = cᴴ * (signMatrix s * (c - (τ : ℂ) • vecMulVec v β)) by
    simp [← show star v ᵥ* (signMatrix s * c) = β by
      ext; simp [vecMul_eq_sum, signMatrix, c, p, ← mul_assoc, *]
      ring, *, τ, t.re_eq_add_conj]; module, mul_apply, sum_eq_single l] <;> simp [c, signMatrix,
    diagonal_apply, β, apply_ite conj] <;> grind -zetaDelta [(mod_cast by simp [r, L,
    exp_sub, p0, ← pq] : (r l * p (o l) * r l * (p (o l) - τ * x l) : ℂ) = 1)]
  grind [BlockTriangular, of_apply]

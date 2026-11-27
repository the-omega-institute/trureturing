/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/ZeroTermHeight
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Formula/ZeroTermHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Formula.ZeroTermHeight. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Formula/ZeroTermHeight.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ThetaIntegralLaws
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Siegel–Weil formula in the convergent range (known result; see
Lib.SiegelWeil.Formula.SiegelWeilFormula).

This file: Lagrangians, their zero terms, torus action and integrable bound for the theta integral.
Height bounds for zero terms under the parabolic and along the torus. -/

open ContinuousLinearMap ENNReal Filling Fintype Matrix Real Space Subsingleton Splitting

attribute [-simp] map_zero

variable {E n m n₁ r : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] [Fintype n₁]
  [Fintype r] {s t s₁} {S : Space E n s} {S₁ : Space E n₁ s₁} (T : Space E m t) {p : Type}
  [Fintype p] (D₁ : S.Splitting S₁ r) {A : Matrix n r E} (S' : Space E n s) (T' : Space E m t)

/-- The type of splittings of the space T (its explicit argument) into p hyperbolic planes with
zero-dimensional complement, i.e. decompositions T = lE^p ⊕ kE^p. -/
abbrev CompleteSplitting (p : Type) [Fintype p] := T.Splitting (stdSpace E Empty) p

/-- The Weil representation of the pair (S,T) on Hom(S,T) with characters υ^{⌊n/2⌋} and 1, where
n is the rank of S. -/
noncomputable abbrev splitWeil := pairWeil S' T' (1 * WeilData.upsilonU1 ^ (card n / 2)) 1

/-- The type of E-subspaces L of E^n equal to their own orthogonal complement for the form x*Jy
of S. -/
abbrev Lagrangian := {L : Submodule E _ // ∀ y, y ∈ L ↔ ∀ x ∈ L, star x ⬝ᵥ S'.J *ᵥ y = 0}

lemma sourceTerm_zero : D₁.sourceTerm T 0 = (D₁.homSource T).zeroTerm := by ext; simp [sourceTerm]

variable (P : CompleteSplitting S p) (L : Lagrangian S) (γ : U S.J)

section

attribute [local simp] Splitting.comp splitWeil star_mulVec_dotProduct

attribute [simp] sourceTerm_zero ideleAbs_det_dyadicDiag_natCast sqrt_sq_eq_abs abs_of_nonneg

attribute [local simp ←] ext_iff Matrix.mul_assoc

omit [WeilData E] in
@[local simp↓] lemma forall_colSpan_dot_eq_zero_iff {y} : (∀ x ∈ colSpan A, star x ⬝ᵥ y = 0) ↔
  Aᴴ *ᵥ y = 0 := ⟨fun h ↦ funext (h _ ⟨_, A.mulVec_single_one ·⟩), by aesop⟩

lemma exists_decomp_of_orth : ∀ y, D₁.kᴴ *ᵥ S.J *ᵥ y = 0 → ∃ a w, D₁.k *ᵥ a + D₁.i *ᵥ w = y := by
  simp_all [(mulVec_surjective_iff_exists_right_inverse.2 ⟨_, (mul_eq_one_comm_of_card_eq _ _ _ (by
                      simp +arith [D₁.card_eq])).1
    (HasLeftInv.of_isUnit_gram (D₁.gram_eq_hypSum ▸ isUnit_J _)).choose_spec⟩).forall]

/-- For a complete splitting P of S and an adelic matrix x, the continuous functional φ ↦ φ[x], the
value at x in the Schrödinger model attached to P. -/
noncomputable def mixedValue x := θ _ ∘L P.sourceTerm T x

/-- For a complete splitting P of S, the Lagrangian kE^p spanned by the columns of its matrix k. -/
def CompleteSplitting.lagrangian : Lagrangian S :=
  ⟨colSpan P.k, by simpa [iff_def, forall_and, eq_zero P.i] using exists_decomp_of_orth P⟩

omit [WeilData E] in
lemma Lagrangian.eq_of_le {L L' : Lagrangian S} : L.1 ≤ L' → L =
  L' := by grind +extAll [IsConcreteLE.le_iff]

/-- For a Lagrangian L of S, a chosen rank r and splitting S = lE^r ⊕ kE^r into dual isotropic
frames l, k such that kE^r = L. -/
noncomputable def Lagrangian.completeSplitting :
  {P : Σ r, CompleteSplitting S (Fin r) // P.2.lagrangian = L} := Nonempty.some (by
  have ⟨k, i, h⟩ := exists_basis_matrix L.1
  have o {y} := h ▸ L.2 y; simp at o
  obtain ⟨_ | _, _, V, P, rfl⟩ := S.exists_splitting i (ext_col (o.1 ⟨_, k.mulVec_single_one ·⟩))
  use ⟨_, by use P.k, P.l, 0 <;> simp [P.card_eq]⟩, eq_of_le h.le
  simpa [IsUnit.ne_zero] using congr(P.iᴴ *
    S.J * $((exists_mul_eq_of_col_mem_range (o.2 congr(col $P.gram_ki ·))).choose_spec.symm)))

/-- The zero term ev_L along a Lagrangian L: the value at 0 in the Schrödinger model of a chosen
complete splitting with kE^r = L. -/
noncomputable def Lagrangian.zeroTerm := mixedValue T L.completeSplitting.1.2 0

/-- For every complete splitting S = lE^p ⊕ kE^p and datum f on Hom(S,T), the zero term of f
along the Lagrangian kE^p is f[0] in the Schrödinger model of this splitting: the zero term
does not depend on the chosen splitting. -/
lemma zeroTerm_lagrangian_eq_theta f : P.lagrangian.zeroTerm T f = θ _ ((P.homSource T).zeroTerm
  f) := (exists_mul_eq_of_col_mem_range (P.lagrangian.completeSplitting.2.ge ⟨_, mulVec_single_one
  _ ·⟩)).elim fun _ h ↦ by simp [Lagrangian.zeroTerm, mixedValue, P.zeroTerm_homSource_congr, ← h]

/-- For a rational isometry γ of S, the splitting of S with no hyperbolic planes whose
complement is S itself, mapped in by γ. -/
def isometrySplitting : S.Splitting S Empty := by use 0, 0, γ <;> simp [↓← mem_U]

lemma zeroTerm_isometrySplitting f : ((isometrySplitting γ).homSource T).zeroTerm f = splitWeil S T
  (S.ratEmbed γ⁻¹, 1) f := by ext; erw [Splitting.zeroTerm_apply, pairWeil_of_mem_Gamma,
  homSource_iAdelic, iCoord, eq_zero (kAdelic _), ← (S.ratEmbed γ).mat_inv] <;> simp [Γ]

lemma exists_isometry_orthogonal (l : HasLeftInv A) (h : Aᴴ * S.J * A = 0) : ∃ γ : U S.J,
  Aᴴ * S.J * (γ.1.1 * P.k) = 0 := (Function.Embedding.nonempty_of_card_le (by grind [Splitting,
  S.exists_splitting l h, card_empty])).elim fun ι ↦
  (S.witt ⟨_, congr(submatrix $P.gram_lk ι ι).trans (by simp)⟩ l (h ▸ congr(submatrix $P.gram_kk _
  _))).elim (⟨·, · ▸ (U.gram_invariant ..).trans congr(submatrix $P.gram_kk _ _)⟩)

lemma exists_lagrangian_equiv_containing : ∃ σ : _ ≃ {L : Lagrangian S // colSpan D₁.k ≤ L}, ∀ L f,
  Lagrangian.zeroTerm T (σ L) f = Lagrangian.zeroTerm T L ((D₁.homSource T).zeroTerm f) := by
  use ⟨(⟨CompleteSplitting.lagrangian <| D₁.comp ·.completeSplitting.1.2, ?_⟩), fun L ↦
    ⟨.comap D₁.i.mulVecLin L, fun _ ↦ by
    erw [L.1.2, iff_comm]; constructor <;> intro h x hx
    obtain ⟨a, w, rfl⟩ :=
      exists_decomp_of_orth _ x (forall_colSpan_dot_eq_zero_iff.1 ((L.1.2 x).1 hx · <| L.2 ·))
    erw [add_mem_cancel_left (L.2 ⟨_, rfl⟩)] at hx
    all_goals simp [← h _ hx]⟩, ((Lagrangian.eq_of_le ?_).symm.trans ·.completeSplitting.2), fun L ↦
    Subtype.ext (Lagrangian.eq_of_le ?_)⟩, fun _ _ ↦ (zeroTerm_lagrangian_eq_theta ..).trans
    (by simp [Lagrangian.zeroTerm, mixedValue, ↓zeroTerm_homSource_comp]) <;> rintro _ ⟨x, rfl⟩
  exacts [⟨x ⊕ᵥ 0, by simp⟩, ⟨0 ⊕ᵥ x, by simp⟩,
    by simpa using add_mem (L.2 ⟨_, rfl⟩) ((Lagrangian.completeSplitting _).2.le ⟨x ∘ .inr, rfl⟩ :)]

lemma mixedValue_splitWeil h x f : mixedValue T P x (splitWeil S T (1, h) f) =
  mixedValue T P (h⁻¹.mat * x) f := by
  simpa [P.card_eq, pairWeil, eq_one (G.onHom _)] using! congr($(P.sourceTerm_levi T 1 1 1 1 ..) 0)

/-- For x ∈ ℕ^p, the operator 2^{−f·rk T·∑x_i} ω(levi(diag 2^{x_i})), with 2 the archimedean
idele and f the number of infinite places. -/
noncomputable def normalisedTorus (x : p → ℕ) := (((2 ^ numInfPlaces E) ^ ∑ i,
  x i) ^ card m : ℂ)⁻¹ • splitWeil S T (P.levi (dyadicDiag (x ·), 1), 1)

@[simp] lemma normalisedTorus_zero : normalisedTorus T P 0 = 1 := by simp [normalisedTorus,
  dyadicDiag, ← Pi.one_def]

/-- If rk T > 2p, there is a measurable N ≥ 0 with finite integral over [U(T)] such that |θ(ω(1,h)
A_x f)| ≤ N(h)‖f‖ for all h, f and x ∈ ℕ^p, where A_x = `normalisedTorus` T P x. -/
lemma theta_normalisedTorus_le (hm : 2 * card p < card m) : ∃ N, Measurable N ∧ ∫⁻ h,
  N h ∂T.quotMeasure ≠ ⊤ ∧ ∀ h x f, ‖θ _
  (splitWeil S T (1, h) (normalisedTorus T P x f))‖ₑ ≤ N h * ‖f‖ₑ := by
  choose B k M hM using (P.homSource T).exists_tsum_mixedTerm_le
  have hB := (k.prod (isCompact_closedBall_prod_integral (E := E)).matrix).image_auto (fun (a,
    (c : Matrix p p (𝔸 E))) ↦ vecToMat a * c) (by fun_prop [vecToMat])
  refine ⟨_, .mul_const ?N (‖θ ((stdSpace E Empty).hom T)‖ₑ * M), MeasureTheory.lintegral_mul_const
    _ ?N ▸ mul_ne_top (T.lintegral_encard_ne_top hB (by lia)) coe_ne_top, fun h x f ↦ ?_⟩
  use .comp .of_discrete (measurable_encard.comp (measurable_pi_iff.2 fun _ ↦
    hB.isClosed.preimage_of_continuous (f := fun x ↦ _ * (G.mat x⁻¹ * _) * _).measurableSet.mem))
  grw [← (P.hasSum_theta_sourceTerm ..).tsum_eq, enorm_tsum_le_tsum_enorm, mul_left_comm, mul_assoc,
    ← Set.encard_mono ?_, ← hM (.mk' (fun ξ ↦ matToVec ((T.toRatCoords h).1⁻¹.1 * ξ.map toAdele *
    (dyadicDiag (E := E) (x ·)).1)) (by open MatMul in simp [Matrix.map_add])),
    ← ENNReal.tsum_mul_left, ← (θ _).le_opENorm]; gcongr; erw [mixedValue_splitWeil]
  simpa [← sourceTerm_eq_mixedTerm, normalisedTorus, P.card_eq, ← ofReal_norm, field, toRatCoords,
    G.mat] using! congr(‖$(P.sourceTerm_levi T 1 1 (dyadicDiag (x ·)) 1 1 ..) 0‖).le
  use fun ξ k ↦ ⟨(_, _), ⟨k, dyadicDiag_inv_mem x⟩, by simp⟩

end

seal CStarMatrix

attribute [local simp ←] ext_iff Matrix.mul_assoc map_mul

lemma norm_zeroTerm_parabolic_mul {E n m p} [Field E] [CMType E] [WeilData E] [Fintype n]
  [Fintype m] [Fintype p] {s t} {S : Space E n s} {T : Space E m t} {P : CompleteSplitting S p} {g}
  {a : GL p _} (hk : P.ActsOnFrame g a.1) g' f : ‖P.lagrangian.zeroTerm T (splitWeil S T (g * g', 1)
  f)‖ = √(ideleAbs a.det) ^ card m * ‖P.lagrangian.zeroTerm T (splitWeil S T (g', 1) f)‖ := by
  rw [← Prod.mk_one_mul_mk_one, ← rep_apply_apply]
  simp [zeroTerm_lagrangian_eq_theta, splitWeil, P.card_eq, -one_mul,
    homSource_zeroTerm_pairWeil (g₀ := 1) (hk := hk)]

lemma norm_zeroTerm_vacElem_pos g : 0 < ‖P.lagrangian.zeroTerm T
  (splitWeil S T (g, 1) (vacElem _))‖ := by
  simp [zeroTerm_lagrangian_eq_theta, pairWeil]; generalize P.homSource T = P,
    G.onHom (g, 1) (s' := t) = g
  have ⟨g₀, h, _⟩ := P.exists_isAdapted_and_frame_eq 1
  choose κ H b _ e _ using P.iwasawa
  have ⟨_, _, h⟩ := IsAdapted.mixedTerm_omega_vacElem (.of_eq_submatrix_mul (A :=
    G.mat _) (.imp (by simpa [maxCompactU, U] using! · ·) mem_Kf.1 (div_mem (H g) (H g₀))) id h
    (by simp [Splitting.frameAt, division_def]) : P.IsAdapted (g₀ * κ g₀ * (κ g)⁻¹) 1)
  rw [← mul_inv_cancel_right g (κ g), ← rep_apply_apply] at *
  simpa [prod_empty, *, mixedTerm, chiAdelic, vacElem_apply_eq_prod_lineTheta, funext_iff, vacuumFn,
    P.zeroTerm_omega 1 _ (e _) (b _).det rfl] using congr($(h 0) 0 = 0)

/-- P, P′ split S completely with frames k, k′; Zk′=1; K compact. For some R: if g∈K, x,u∈ℕ^p,
Zgk·diag(2^x) = Zgk·diag(2^u) (2 archimedean), the P′-value at 0 of ω(g,1)(`normalisedTorus` T P x
f) has modulus ≤ R‖f‖·2^{d(∑u−∑x)rk T}, d the number of infinite places. -/
lemma exists_zeroTerm_normalisedTorus_le (P' : CompleteSplitting S r) {K} (Z : Matrix r n (𝔸 E))
  (h : Z * P'.kAdelic = 1) (hK : IsCompact K) : ∃ R : NNReal, ∀ g ∈ K, ∀ x u : p → ℕ,
  Z * g.mat * P.kAdelic * (dyadicDiag (x ·)).1 = Z * g.mat * P.kAdelic * (dyadicDiag (u ·)).1 →
  ∀ f, ‖P'.lagrangian.zeroTerm T (splitWeil S T (g, 1) (normalisedTorus T P x f))‖ ≤ R * ‖f‖ *
  ((2 ^ numInfPlaces E) ^ (∑ i, u i - ∑ i, x i : ℤ)) ^ card m := by
  have c := (isCompact_closedBall_prod_integral (E := E)).matrix (m := p) (n := p)
  constructor; introv hg _; choose κ hκ a _ e _ using P'.iwasawa _
  simp [normalisedTorus, rep_apply_apply, ↓zpow_natCast_sub_natCast₀, div_pow, field]
  grw [← mul_inv_cancel_right (g * _), norm_zeroTerm_parabolic_mul e, ← mul_inv_cancel_left _ a.det,
    map_mul, sqrt_mul', ideleAbs_det_dyadicDiag_natCast u, sqrt_sq,
    (le_max_iff.2 ((le_total ..).imp_left (le_csSup ((isCompact_setOf_le_ideleAbs_det
    ((hK.prod (isCompact_maxCompact.prod (c.prod c))).image_auto fun (g, κ, u, x) ↦ !![(fromBlocks
    (Z * g.mat * (P.lAdelic * xᴴ * P.lCoord :) * κ.mat * P'.kAdelic) (Z * g.mat * P.kAdelic)
    (-P.kCoord * κ.mat * P'.kAdelic) u).det]) one_pos).image_auto (ideleAbs ·.det)).bddAbove
    ⟨.scalar _ _, ⟨⟨(_, _, _, _), ⟨hg, hκ, dyadicDiag_inv_mem u, dyadicDiag_inv_mem x⟩, ?_⟩, ·⟩,
    rfl⟩))).trans_eq' (congrArg _ (Units.ext (det_diagonal.trans (prod_unique _)))), le_opNorm,
    le_opNorm, ((pairThetaKer ..).exists_norm_le_of_isCompact (isCompact_maxCompact.prod
    isCompact_maxCompact)).choose_spec, ← le_coe_toNNReal, mul_pow, mul_rotate, ← mul_assoc,
    ← mul_assoc] <;> simp [*, (det_classical _).symm.trans (det_fromBlocks₂₂ ..), add_comm]
  simpa [*, Splitting.levi, add_comm, Matrix.mul_add, Matrix.add_mul, eq_zero iAdelic] using
    congr(_ * Matrix.det (Z * $e))

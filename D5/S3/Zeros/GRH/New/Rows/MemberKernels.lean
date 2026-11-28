/- GID: D5/S3/Zeros/GRH/New/Rows/MemberKernels
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/MemberKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.MemberKernels. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/MemberKernels.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.MovedVacuumComb
import D5.S3.Zeros.GRH.New.Forms.AuxiliaryPair
import D5.S3.Zeros.GRH.New.Exchange.CrudeModularData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Crude denominators and conjugate bounds for theta jets. For theta kernels between definite
unitary groups given by jets of finite sums of translates of the standard theta function, one
non-zero constant makes the values integral away from the denominators of the data and all
conjugates obey a Cauchy-type bound, and this bounds lifts, crude rows and test forms. Algebraicity
and integrality of jets of CM theta functions are known, and the crude clearing of denominators with
a Cauchy bound on conjugates is a standard computation, up to the explicit constants. Related work:
Bannai–Kobayashi, Algebraic theta functions and Eisenstein–Kronecker numbers, 2010; Kings–Sprang,
Eisenstein–Kronecker classes and integrality of critical values, 2019; Katz, p-adic L-functions for
CM fields, 1978.

Part of: Integral comparison forms seeing the twist through one number (see
New.Rows.ComparisonForms).

This file: Cauchy-type bounds for all conjugates of theta jets and Schur jets. Regular parameters
come from weights; bounds for rows and boxes. Integrality and conjugate bounds for theta kernels of
definite pairs; rational automorphy law. Point forms with prescribed residue datum: pairing, and
theta descent as a kernel. Kernel as a vector, the free level, and one class sum at that level. -/
seal Finset.univ Finset.sum Finset.prod

open NumberField.InfinitePlace RingHom ComplexConjugate Finset Fintype MatMul Matrix MeasureTheory
  MvPolynomial NeZero Parameters Real Space

variable {E L N : Type} [Field E] [CMType E] [Fintype L] [Fintype N] (P : Parameters)

/-- If at every τ in Φ one has |n| ≤ |n'| and κ_τ(h) = 0 for |n| < h < |n'|, then ∑_τ
∑_{0≤i<|n|} ∑_{i<h<|n'|} κ_τ(h) equals the number of boxes ∑_τ ∑_{h<|n'|} h·κ_τ(h). -/
lemma FitsRanks.sum_diagramWeight_eq_boxes {n n' Φ} [Fintype n] [Fintype n'] [Fintype Φ] {κ} (h :
  FitsRanks n n' κ) : ∑ x :
  Φ × Fin (card n), diagramWeight (rankAt n') κ (x.1, x.2) = boxes κ (card n') := by
  simp [sum_prod_type, diagramWeight_apply]; congr!; rw [sum_comm' (s' := ({i | ↑i < ·}))]
  congr!; simp [Fin.card_filter_val_lt]; repeat grind

lemma Parameters.exists_algEquiv_norm_eq (σ : ℂ ≃+* ℂ) : ∃ σ' : Gal(ℂ/P.K), ∀ z, ‖σ z‖ = ‖σ' z‖ :=
  (mk_eq_iff.1 (by
  subsingleton) : .domRestrict σ P.K = _ ∨ _).elim (⟨.ofRingEquiv <| RingHom.congr_fun ·, by tauto⟩)
  (⟨{ σ.trans starRingAut with commutes' := RingHom.congr_fun · }, by simp⟩)

/-- Crude bounds for σ-conjugates of jets of ω(g,h)f, g, h finite, f a combination of translated
vacua of size B: at most B_L·A·e^w along Q if |σQ(z)| ≤ A·e^{w+LR} on balls of squared radius
(2L+2)R·e^u, u = log(|σc|²/Ω); likewise an operator bound for `schurJet`.

Crude denominators and conjugate bounds for theta jets. -/
lemma Parameters.norm_jet_le_of_isAdmissibleComb {s n n'} [Fintype n] [Fintype n'] {ea eb a b ψ ψ'}
  [AutChar.HasWeight a ea ψ] [hb : AutChar.HasWeight b eb ψ'] {B f} (H :
  IsAdmissibleComb (finHeisOp _ · (intVacuum _)) .univ 0 0 True B f) {σ : ℂ ≃+* ℂ} {c}
  g h : let u := log (‖σ c‖ ^ 2 / P.bigOmega s)
  let M L w := B * exp (P.c * (P.N₁ s * card (n' × n) + 1) ^ 2 +
    card (P.Φ s × n' × n) * log (2 * L + 2) + w)
  let F := jetSeries _ (c * P.jetScale s)
    (pairWeil (stdSpace (P.E s) n) (stdSpace _ n') a b ((1, g), 1, h) f)
  (∀ Q (L : ℕ) w {A}, 0 ≤ A → (∀ z R, ∑ i, ‖σ (z i)‖ ^ 2 ≤ exp u * (2 * L + 2) * R → ‖σ (eval z Q)‖
    ≤ A * exp (w + L * R)) → ‖σ (jet ℂ Q F)‖ ≤ M L w * A) ∧ ∀ (L : ℕ+) {κ e}, IsLiftWeight n n' κ eb
    e → ∀ ξ, √(weylNormSq (σ ∘ (schurJet κ F *ᵥ ξ))) ≤ M L ((∑ τ, ∑ i ∈ Finset.range (card n),
    (diagramWeight (rankAt n') κ (τ, i) / L + log (diagramWeight (rankAt n') κ (τ, i)).factorial +
    diagramWeight (rankAt n') κ (τ, i) * u)) / 2) * √(weylNormSq (σ ∘ ξ)) := by
  obtain ⟨⟨r, hr, ⟨⟩⟩, υ, hA⟩ := H, P.exists_algEquiv_norm_eq σ
  intro u; refine .symm ⟨fun L _ _ U ξ ↦ sqrt_weylNormSq_le_of_dual _ fun y k ↦ ?_, ?H⟩
  choose ρ i j using by simpa using weylNormSq_schur_le U.1
  grw [dotProduct_schurJet_mulVec, ?H]; simp; introv m
  grw [eval_schurCoeffPoly U, k, funext (f := σ ∘ _) (σ.toRingHom.map_mulVec _ _), ← schur_map U.1,
    j, sqrt_mul (by positivity), pow_le_exp_log_factorial_add _ _ (u + (↑L)⁻¹)]
  simp [← exp_sum, ← exp_half, sum_prod_type, ← sum_div, ↓← sum_mul] at *
  grw (transparency := default) [mul_comm, exp_add, ← add_one_le_exp _⁻¹, i, m]; congr! 2; field
  simp_intro Q L w A hY H [↓hA, -card_prod, Finsupp.sum, ω_ϱ, mulVec_finVec, finHeisOp, smul_smul,
    ↓pairWeil_apply, AutChar.HasWeight.norm_map_eq_one, funext_iff]
  choose t _ _ Λ _ _ l₁ _ l₃ _ using
    exists_semilinear_isJetConjugate ((stdSpace (P.E s) n).hom (stdSpace _ n')) disjoint_bot_left υ
  grw [← hr.3 ⟨⟩ υ, Finsupp.sum, sum_mul, sum_mul, norm_sum_le, add_right_comm]; gcongr
  erw [G.onHom_fin, norm_mul, (?_ : Q.bind₁ _ = bind₁ _ (Q.aeval (c • X))),
    ← jet_jetSeries_eq_theta, map_jet
    υ.toRingHom, l₁, jet_rename (Equiv.prodCongr _ 1).toEmbedding ((renameEquiv ..).right_inv _),
    jet_jetSeries_eq_theta, theta_integrated, integral_smul_measure, exp_add, exp_nat_mul]
  grw [norm_smul, norm_integral_le_of_norm_le
    (.const_mul (.of_integral_ne_zero ((HasGaussianIntegral.integral_exp_eq (t :=
    (2 * L + 2)⁻¹) (by bound)).trans_ne (by positivity))) (A * exp _)) (.of_forall fun y ↦ ?_)]
  simp (disch := positivity) [↓HasGaussianIntegral.integral_exp_eq, -card_prod, mul_pow,
    field, stdLattice.semichar, ↓integral_const_mul, exp_log]
  grw [polyVector_apply, norm_mul₃_le, l₃, (H (c • υ.symm ∘ (t • star y) ∘ (placePerm ..).prodCongr
    1) ((∑ i, ‖y i‖ ^ 2) / (2 * L + 2)) (by grw [← le_exp_log]; simp [mul_pow, ← mul_sum, field, *,
    -Equiv.prodCongr_apply, Equiv.sum_comp _ (‖y ·‖ ^ 2)])).trans_eq' (congrArg _ ?_)]
  simp [realVac, star_dot_self_eq_sum, mul_assoc, sq, ← exp_add]; congr! 2; field
  any_goals rw [Q.as_sum]; simp [monomial_eq, ← C_mul', mul_assoc, holCoord_eq]
  repeat apply_rules [rho_finVec_mem_finitePart, omega_mem_finitePart, Submodule.smul_mem,
    vacElem_mem_finitePart]

attribute [local grind] HasGap hcParameter diagramWeight_apply

lemma boxes_le_of_isHCParam {e : N → ℤ} {l : N → L → ℤ} {κ} [Nonempty L] (h :
  IsHCParam κ e l) {β : ℕ} (hβ : ∀ w i, |l w i| ≤ β) : boxes κ (card L) ≤ card N * card L * β ∧ ∀ w,
  (e w).natAbs ≤ β := by grw [← FitsRanks.refl.sum_diagramWeight_eq_boxes,
  sum_le_card_nsmul _ _ β] <;> simp <;> intro w <;> grind [h.exists_decrPosition_eq w
  (Nat.sub_one_lt (by simp)), h.exists_decrPosition_eq w, card_pos_iff, Ioo_eq_empty]

lemma exists_isHCParam_of_le {Φ n : Type} [Fintype Φ] [Fintype n] {s : n → ℤˣ} (κ : Φ → ℕ → ℕ) {e :
  Φ → ℤ} {c : ℝ} {l : Φ → n → ℤ} (hc : ∀ w, (toHCParam s (l w)).HasGap c) (hg : ∀ w i, e w ≤
  l w i / 2 + card n /
  2) : ∃ f, IsHCParam f (fun w ↦ e w + f w (card n)) l ∧ ∀ᵉ (w) (k > card n), f w k = κ w k := by
  choose! f _ p _ using fun w ↦ (induction_on_min_value (l w) · (by aesop) fun a S _ _ ih g f
    _ ↦ (ih (l w a / 2 + 1) (Function.update f (#S + 1) (l w a / 2 - g).toNat) (by grind)).imp
    (by simp; grind [Ioc_self, sum_Ioc_succ_top]) : ∀ S g f, (∀ i ∈ S, g ≤ l .. / 2) → ∃ κ,
    (∀ k > #S, κ k = f k) ∧ ∀ i ∈ S, ∃ p < #S, l .. / 2 + p + 1 = g +
    ↑(#S + (Ioc p #S).sum κ)) univ (e w - card n / 2) (κ w) (by grind)
  use f, fun w ↦ ⟨?_, (⟨p w ·, ?_⟩)⟩ <;> grind [Ioo_insert_right]

/-- If every l_w satisfies `HasGap` (in particular has distinct entries ≡ n − 1 mod 2), then l
is twice the Harish-Chandra parameter of some weight (κ,e). -/
lemma exists_isHCParam_of_hasGap {s : L → ℤˣ} {c : ℝ} {l : N → L → ℤ} (hc : ∀ w,
  (toHCParam s (l w)).HasGap c) :
  ∃ κ e, IsHCParam κ e l := by grind [exists_isHCParam_of_le 0 hc fun _ ↦ Finite.ciInf_le _]

/-- For characters a, b of weights e, e′ and rational γ ∈ U(I_L), γ′ ∈ U(I_N), left translating
the finite arguments of the theta kernel by γ, γ′ multiplies it by ∏_τ Φ_τ(det
γ′)^{−e_τ}Φ_τ(det γ)^{e′_τ} and substitutes (γ′⁻¹, γ) into the polynomial Q. -/
lemma modKernel_embFin_mul [WeilData E]
    {a b e e' ψ ψ'} (ha : a.HasWeight e ψ) (hb : b.HasWeight e' ψ') 𝔪 Ψ Q γ
  γ' g h : modKernelI (stdSpace ..) a b 𝔪 Ψ Q (1, (stdSpace E L).embFin γ * g)
  ((stdSpace E N).embFin γ' * h) = (∏ τ, Φ τ γ'.1.1.det ^ (-e τ) * Φ τ γ.1.1.det ^ e' τ) *
  modKernelI (stdSpace ..) a b 𝔪 Ψ (twoSidedSubst (γ'⁻¹.1.1.map <| Φ ·) (γ.1.1.map <| Φ ·) Q) (1, g)
  h := by erw [modKernelI, modKernel, pairTheta, ← (pairThetaKer ..).4 ⟨γ⁻¹, rfl⟩ ⟨γ'⁻¹, rfl⟩,
  pairWeil_integrated_all, realPairWeil_polyVector, mul_one] <;> simp [↓stdSpace_ratEmbed_apply,
  embFin, modKernel, modDatum, pairTheta, ← map_det, ← mapMatrix_apply]

lemma sum_mem_integralAbove γ g {p γ' g'} (h : (stdSpace E L).embFin γ * g ∈ integralAbove L p)
  (h' : stdEmbFin γ' * g' ∈ integralAbove N p) : stdEmbFin (U.blockSumOne (γ, γ')) * U.blockSumOne
  (g, g') ∈ integralAbove _ p := have := stdSpace_embFin (U.blockSumOne (γ, γ'))
  by simp_all [mem_localLevel, Gf.atPlace, mem_intGL, mul_apply, U.sum, ← map_inv]

variable {E : Type} {r n} [Field E] [CMType E] [Fintype r]
  [Fintype n] {O : AuxPair E r n} (h : Gf E n) {Y : ∀ i,
  Matrix n r (ResField (O.placeAt (.inl i)))} (hY : ∀ i, (Y i).mulVec.Injective) (e : r ↪ n)
  (L N : Type) [Fintype L] [Fintype N] {E' r' n'} {m : Type} [Field E'] [CMType E'] [Fintype r']
  [Fintype n'] [Fintype m] [WeilData E'] (O' : AuxPair E' r' n') (b)

/-- For each d some c ≠ 0 serves all kernels θ of definite pairs with Q homogeneous of degree d, qg²
∈ 𝔪, Ψ integral off q: c·θ is p-integral for p ∤ q, Q and points integral at p; for q = 1, ranks ≤
40k, d ≤ g, |σ(c·θ)| ≤ exp(x₁)MB if M bounds all conjugates of Ψ and B bounds σQ on entries ≤ g⁴.

Crude denominators and conjugate bounds for theta jets. -/
lemma exists_modKernel_integral_bound {P} (D : Data P) d : ∃ c ≠ 0, ∀ {a b ea eb ψ ψ'} 𝔪 q Ψ,
  a.HasWeight ea ψ → b.HasWeight eb ψ' → ↑(q * D.gProd ^ 2) ∈ 𝔪.ideal →
  (∀ x, Ψ x ∈ integralAway q) → ∀ Q g h, (∀ c ≠ (0 : ℂ), Q.aeval (c • X ·) = c ^ d • Q) →
  let v := c * modKernelI (stdSpace D.E L) a b 𝔪 Ψ Q (1, g) h; (∀ p [Fact p.Prime] [PadicPlace p],
  p.Coprime q → g ∈ integralAbove L p → h ∈ integralAbove N p → Q ∈ (MvPolynomial.map
  embValRing.subtype).range → ‖ιₚ v‖ ≤ 1) ∧ (card L ≤ 40 * D.k → card N ≤ 40 * D.k → d ≤ D.gProd →
  q = 1 → ∀ (σ : ℂ ≃+* ℂ) (M : ℕ) B, (∀ (σ : ℂ ≃+* ℂ) x, ‖σ (Ψ x)‖ ≤ M) → (∀ z, (∀ i, ‖σ (z i)‖ ≤
  D.gProd ^ 4) → ‖σ (Q.eval z)‖ ≤ B) → ‖σ v‖ ≤ exp D.x₁ * M * B) := by
  repeat constructor
  swap; introv ha hb hk hΨ hQ v; rw [← (?_ : _ = v)]
  use fun p _ _ hp hg hh ⟨_, k⟩ ↦ norm_jet_jetSeries_le_one ?_
    (pairWeil_mem_standardData ha hb (smul_vacuumDatum_mem_standardData hk hΨ hp) hg hh) k
  rintro l n hd rfl σ M B hM hB; have := (norm_nonneg _).trans (hB 0 (by simp))
  grw [map_smul, map_smul, map_smul, smul_eq_mul, map_mul, norm_mul,
    (P.norm_jet_le_of_isAdmissibleComb (isAdmissibleComb_vacuumDatum M
    hM) g h).1 Q d 0 this fun z R e ↦ by simpa [exp_nat_mul, field, mul_comm B, ↓hQ] using (
    comp_aeval_apply (σ.symm (exp R)⁻¹ • X ·) (aeval z) Q ▸ hB _ fun i ↦ le_of_sq_le_sq (by
      simp [field]; grw [(single_le_sum (by simp) (mem_univ i)).trans e, mul_comm]; gcongr
      nlinarith [add_one_le_exp R]; grw [hd]
      simpa [exp_log_eq_abs, bigOmega_pos.ne', ne] using D.le_of_hasLogBound) (by simp) :)]
  simp [mul_right_comm _ (M : ℝ), ← mul_assoc]
  grw [@card_eq_nat_card 𝔪.ResRing, 𝔪.card_resRing_le hk one_le, ← le_exp_of_log_le]
  simp [ne, log_mul]; norm_cast; grw [le_abs_self P.c, hd, l, n]; use D.le_of_hasLogBound
  swap; simp [↓hQ, ne, ← pairWeil_integrated_fin, ← mul_assoc]; rfl
  all_goals simp [ne]

attribute [-simp] Sum.elim_inl Sum.elim_inr

include hY in
lemma exists_reduceAt_mul_incl_eq : ∃ k, ↑k ∈ Gf.supportedOn n O.places ∧
  (∀ i, (Kf.reduceAt _ k).1 * inclMatrix _ O.incl = Y i) ∧ ∀ i,
  (Kf.reduceAt (O.placeAt (.inr i)) k).1ᵀ * inclMatrix _ e = inclMatrix _ O.incl := by
  choose A a using (exists_GL_mul_inclMatrix O.incl <| hY ·)
  choose B b using (exists_GL_mul_inclMatrix e <| inclMatrix_mulVecLin_injective O.incl <|
    ResField <| O.twistPlace ·)
  peel exists_reduceFamily_eq (Sum.rec A (transposeGL <| B ·))
  simp_all [_root_.funext_iff, Kf.reduceFamily]; tauto

/-- The point form: v ↦ `deltaForm` of v at hk, for a chosen k in K₀ with columns `O.incl` equal to
Y at M and rows e equal to the rows `O.incl` of 1 at Q. -/
noncomputable def pointForm : (WeylIndex n O.κ → ℂ) →ₗ[ℂ] O.FormV :=
  deltaForm _ _ _ (h * (exists_reduceAt_mul_incl_eq hY e).choose)

lemma inner_pointForm φ v : inner ℂ (pointForm h hY e v) φ =
  gramForm v (φ (h * (exists_reduceAt_mul_incl_eq hY e).choose)) := by
  simp_rw [inner, LevelPlaces.LevelForm.innerAt_eq_stdClassSum]
  apply classSum_deltaForm (φ · |> gramForm.flip |>.toAddMonoidHom)
  simp [↓levelSpace_smoothFormRep_apply φ.2, gramForm_conjWeylRep, ← mul_assoc, Complex.conj_mul',
    -MonoidHom.coe_comp, weightRep_apply, (LevelPlaces.isOfFinOrder_level_char _).norm_eq_one]

set_option backward.isDefEq.respectTransparency false in
lemma theta_pointForm [WeilData E]
    v g : O.θ (pointForm h hY e v) g = conj (modKernel O.W (stdSpace ..) O.a O.b
  (O.levelModulus 2) (fun T ↦ if ∀ i, T.map (levelResidueAt _) = Y i then ∏ i,
  O.ψ _ ((T.map (levelResidueAt (.inr i))).submatrix e _root_.id).det else 0)
  (O.harmonicPoly (star v)) g h) := (classSum_deltaForm (O.conjKernel g · |>.toAddMonoidHom)
  (O.conjKernel_equivariant · · ..)).trans ((congrArg star (modKernel_mul_Kf_right ..)).trans (by
  have ⟨s, t⟩ := (exists_reduceAt_mul_incl_eq hY e).choose_spec.2
  set A := Exists.choose _; simp [← map_inv]
  simp [AuxPair.resDetDatum, s, ← inclMatrix_transpose_mul, ← t,
    inv_mul_eq_iff_eq_mul_of_invertible]))

/-- The vector whose i-th coordinate is the conjugate theta kernel of (W, I_m) at (g, h), with
datum Ψ modulo 𝔪 and basis polynomial i of weight κ in the negative letters. -/
noncomputable def kernelVector 𝔪 Ψ κ g h (i : WeylIndex m κ) := star
    (modKernelI O'.W O'.a b 𝔪 Ψ (fockLetters O'.signs O'.ord (-1) (nablaBasis ℂ _ κ i)) g h)

/-- The subgroup of K₀ of points whose reduction mod M²Q has the columns of 1 off e and whose
reduction A mod M² satisfies wA = w. -/
noncomputable abbrev rowFixingLevel {E r m} [Field E] [CMType E] [Fintype r] [Fintype m] {c} (S :
  LevelPlaces E) (w : Matrix c m _) (e : r ↪ m) :=
  (S.levelModulus 2).levelOfSubgroup (rowStabilizer reduceToR₀ w e)

/-- The class sum, at level `rowFixingLevel`, over h of the theta kernel of (W, I_m) at (g, h) with
datum `columnDatum` and the polynomial of y(h) in the positive letters. -/
noncomputable def cosetKernelSum {c} (w : Matrix c m O'.chosenModulusSq.ResRing) e (y : _ →
  WeylIndex m O'.colsPlus → ℂ) g := stdClassSum (rowFixingLevel _ w
  e) fun h ↦ modKernelI O'.W O'.a b _ (columnDatum (Modulus.charOfTamePart _ O'.ψ) reduceToR₀ w e)
  (letterPoly O'.signs O'.ord 1 _ (y h)) g h

/- GID: D5/S3/Zeros/GRH/New/Seesaw/DoubleLiftValue
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/DoubleLiftValue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.DoubleLiftValue. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/DoubleLiftValue.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.EdgePair
import D5.S3.Zeros.GRH.New.Seesaw.IntegralAsCosetSum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

Part of: Theta lift for a definite unitary pair as a class sum on algebraic modular forms (known
result; see Lib.Weil.CompactLift.RallisFormula).

This file: Two unfolding steps equal a double theta lift of the evaluated datum. -/

open Grading Matrix MeasureTheory Space Subtype Splitting

attribute [local simp] formAdjoint_formAdjoint boxProd_integrated Std.map_integrated
  Subgroup.mem_prod GradeZeroPart.splitting vecToMat entrywise mul_assoc
  realMap_flipCoords_polyVector realBoxProd_polyVector matToVec pairChar

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι]
  [Fintype ι'] [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype X₀] [Fintype q]
  {ε ε' ε'' N s s' s''} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  {Y : Grading V N X s} {Y' : Grading V' N X' s'} {Y'' : Grading V'' N X₀ s''}

/-! The value of two unfolding steps is the double lift of the finite evaluation. -/

/-- Let k, k' be families of theta lifts X → X' → X₀. For fixed u and t, some t'' works for all o,
y, φ, g: integrating coefficient t of φ against the theta kernel of `integrated _ u (arrowTensor y)`
over [U(X)] × [U(X')] gives coefficient t'' of the double lift. -/
lemma integral_theta_eq_lift₂ {κ e e' e'' O k k'} {a b : O → _} (hk :
  IsThetaLift κ e e' (rankTwist <| a ·) k) (hk' : IsThetaLift κ _ e'' (rankTwist <| b ·) k') u t :
  let L o := TensorProduct.lift (.flip (.compl₁₂ (.llcomp ..) (k' o) (k o))); ∃ t'', ∀ o y φ g, ∫ x,
    algFormCoeff 1 t φ x * ∫ r, θ _ (tripleWeil (V'' := stdSpace E X₀) (a o) (b o) (x, r,
    g) (integrated _ u (arrowTensor y))) ∂(stdSpace E X').quotMeasure ∂(stdSpace E X).quotMeasure =
    algFormCoeff 1 t'' (L o y φ) g := by
  intro L; choose z _ hz using theta_arrowProduct (stdSpace E X) (stdSpace E X') (stdSpace E X₀)
  let F o (φ : AlgForm X κ e) g x := algFormCoeff 1 t φ (.fst x) • θ ((stdSpace E X').hom
    (flipSum (stdSpace ..) (stdSpace E X₀))) ∘L tripleWeil (a o) (b o) (x.1, x.2, g)
  have i {o φ g} f : Integrable (F o φ g · f) (.prod (stdSpace ..).quotMeasure
    (stdSpace ..).quotMeasure) := ((stdSpace ..).isAutomorphic_algFormCoeff φ).rec fun _ _ _ ↦
    integrable_of_cocompact (cocompact_prod (stdSpace ..).exists_isCompact_of_definite (stdSpace
    ..).exists_isCompact_of_definite) (by simp [F, tripleWeil, -circleChar_inv_apply]; fun_prop)
    (by simp_all [F, ↓theta_tripleWeil_rat_mul])
  refine (isClosed_property denseRange_polyVector ((IsLinearMap.mk' (R := ℂ) (algFormCoeff 1 ·
    <| L · · ·) ⟨by tauto, by tauto⟩).range.closed_of_finiteDimensional.preimage_of_continuous (f :=
    fun u o y φ g ↦ strongIntegral (.prod (stdSpace ..).quotMeasure (stdSpace ..).quotMeasure)
    (F o φ g) (integrated _ u (arrowTensor y)))) (fun P ↦ Submodule.mul_induction_on
    (mem_rename_range_mul (.map (·) (.map .inl (·) ∘ .swap)) (.map (·) (.map
    .inr (·))) (by simp) P) (fun _ ⟨P, p⟩ _ ⟨Q, q⟩ ↦ (hk P t).rec fun t' G ↦ (hk' (z • Q) t').imp
    fun _ H ↦ ?_) fun _ _ h ↦ by simpa using! add_mem h) u).imp fun _ h ↦ by
    simpa [funext_iff, ← integral_const_mul, strongIntegral_apply, integral_prod, i] using! h.symm
  ext o y; simp; induction y <;> try simp [*]
  simp [↓strongIntegral_apply, ↓integral_prod_symm, i, L, -θ_apply, ← H, ← G, ← integral_const_mul]
  congr!; rw [mul_rotate', mul_rotate, mul_rotate', mul_assoc, ← hz, arrowProduct_twistedPairWeil]
  simp [← p, ← q, arrowProduct, flipPoly, pairSign, MvPolynomial.rename_eq_aeval,
    MvPolynomial.bind₁_bind₁]; rfl

/-- For a pair D there is one constant z such that, for generic P on U(V), the integral over
[B] × [B'] of P(gt) times the two constant terms at T, T' equals z∫_{[U(X)]} P(gt) ∫_{[U(X')]}
θ(Ω(g, r, D.embX k) ev ϱ(T*, T')(f ⊗ f')), ev the zero term along `ArrowPair.splitting`. -/
lemma ArrowPair.integral_constTermAtT_mul (D : ArrowPair X'' q Y Y' Y'') : ∃ z, ∀ a b f f' k P t,
  Y.IsGeneric P → let F g r := P (g * t) * Y.constTermAtT Y' (rankTwist a) f g r *
    Y'.constTermAtT Y'' (rankTwist b) f' r (Y''.inclX k)
  ∫ r, ∫ g, F g r ∂Y.besselMeasure ∂Y'.besselMeasure = ∫ g, P (Y.inclX g * t) * (z * ∫ r,
    θ _ (tripleWeil a b (g, r, D.embX k) (D.splitting.zeroTerm (homHeisOp (stackedT Y Y' Y'')
    (arrowProduct f f')))) ∂(stdSpace E _).quotMeasure) ∂(stdSpace E X).quotMeasure := by
  obtain ⟨⟨z, h, M⟩, B, ⟨κ, K⟩, O, ⟨⟩, ⟨⟩, c⟩ := theta_arrowProduct V V' V'',
    Y.formAdjoint_apply Y', Y.integral_besselMeasure_eq_of_mean (.refl _), D.string_spec
  have hz f f' w w' : Y.constTerm Y'.gradeOf f w * Y'.constTerm Y''.gradeOf f' w' =
    z⁻¹ * D.homZeroPart.splitting.zeroTerm (arrowProduct (homHeisOp w f) (homHeisOp w' f')) 0 := by
    rw [eq_inv_mul_iff_mul_eq₀ h, Splitting.zeroTerm_apply,
      ← quotMean_quotMean (_root_.ratVectors ..) _ (_root_.ratVectors ..) (.mk' (fun a ↦
      matToVec ((V.formAdjoint V' (vecToMat a.1)).fromRows (vecToMat a.2)) ∘ val) (id _)) _ _
      (val_injective.surjective_comp_right.forall.2 fun b ↦ ⟨(matToVec (V'.formAdjoint V
      (vecToMat b).toRows₁), matToVec (vecToMat b).toRows₂), by simp [-vecToMat]⟩)]
    any_goals rintro _ ⟨a, ⟨⟩⟩ _ ⟨b, ⟨⟩⟩
    any_goals simp [↓isContPeriodic_along_k, continuous_pi_iff, mem_ratVectors, B, ← map_mul,
      ratAdeles, -continuous_prodMk, funext_iff, add_mul, mul_add] <;> constructor <;> fun_prop
    simp_rw [constTerm, quotMean, ← integral_mul_const, ← integral_const_mul, ← θ_ϱ, ← M,
      ← homHeisOp_arrowProduct, homHeisOp, ← x_inv_mulVec_matToVec, mulVec_zero, zero_add]; congr!
    apply (kAdelic_mulVec _ rfl _).symm.trans (congrArg ..) <;> simp +contextual [funext_iff, B]
  refine (Y'.integral_besselMeasure_eq_of_mean D.gradeOne).imp' (κ * · * z⁻¹) ?_; introv H Q F
  have C : Continuous ↿F := Q.rec (by simp [F, *]; fun_prop)
  have L r : Y.ratBessel.FixesLeft (F · r) := fun _ o ↦
    (by simp [F, Q.2 _ o, ← constTermAtT_rat_mul ⟨_, o⟩ 1 ·])
  have R g : Y'.ratBessel.FixesLeft (F g) := fun δ l r ↦ by
    simp [F, ← constTermAtT_rat_mul 1 ⟨_, l⟩ g r, ← constTermAtT_rat_mul ⟨_, l⟩ 1 r]
  simp_rw [fun r ↦
    K (L r) C.along_fst (fun n l ↦ by simp [F, mul_assoc n, -mul_assoc, Q.unipotent_mul_constTerm
    Y'.gradeOf_stringReversal l (Y.hasDegreeGe_two_of_odd O l) (Y.hasDegreeGe_neg_one_stringMap.mul
    (Y.hasDegreeGe_two_of_odd O l))]) (fun a ↦ ⟨⟨continuous_const, by simp⟩, quotMean_const
    (F (Y.inclX a) r)⟩) (by fun_prop) (by simp +contextual [L, ↓inclX_mem_ratBessel]), mul_assoc,
    ← integral_const_mul z⁻¹, mul_left_comm (P _), ← integral_const_mul (P _), integral_const_mul κ]
  rw [integral_integral_swap (integrable_of_cocompact
    (cocompact_prod Y'.isCocompact_ratBessel (stdSpace ..).exists_isCompact_of_definite)
    (by fun_prop) (by simp +contextual [*, ↓inclX_mem_ratBessel]))]; congr with x
  refine H (R _) C.along_snd (fun n o g ↦ ?_) (fun _ ↦ ⟨isContPeriodic_along_k .., by
    simp_rw [← Splitting.zeroTerm_apply, ← D.zeroTerm_splitting_tripleWeil, stackedT,
      homHeisOp_arrowProduct, ← arrowProduct_twistedPairWeil, pairWeil_homHeisOp,
      inclX_mul_stringMap_mul_inclX_inv, ← homHeisOp_arrowProduct, ← smul_eq_mul, ← map_smul,
      splitting, zeroTerm_comp]; rfl⟩) (by simp [tripleWeil, -circleChar_inv_apply]; fun_prop)
    (one_mul x ▸ by simp +contextual [↓theta_tripleWeil_rat_mul])
  rw [← θ_ϱ, ← zeroTerm_rho_iAdelic, ← zeroTerm_rho_kAdelic
    ((matToVec (stackedT Y Y' Y'' * (V'.ratCoordMatrix n - 1)) - _) ∘ val), (heisRep _).2,
    (by simp [D.homZeroPart.splitting.beta_eq_coords] : Heisenberg.β .. = 1), kAdelic_mulVec _ rfl,
    iAdelic, Space.ratMap, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_add, sub_add_cancel,
    x_inv_mulVec_matToVec, (heisRep _).2, ← homBicharacter, homBicharacter_eq, ← Matrix.mul_assoc]
  · simp [F, one_mul (Y.inclX x) ▸ Y.constTerm_mul Y'.gradeOf_stringReversal (.inr ⟨_,
      Y'.mem_unipotent.1 o⟩) _, one_mul (Y''.inclX k) ▸ Y'.constTerm_mul Y''.gradeOf_stringReversal
      (.inr ⟨o, Y''.mem_unipotent.1 _⟩) _ _, stackedT, ↓show ∀ A B, V'.formAdjoint (flipSum V V'')
      (A.fromRows B) = (-V'.formAdjoint V A).fromCols (V'.formAdjoint V'' B) by simp [formAdjoint,
      flipSpace], formAdjoint_stringMap_mul_stringMap, c, Matrix.mul_sub]
    simp [hz, ← homHeisOp_arrowProduct, formAdjoint_ratCoordMatrix_mul]
  intro p r; obtain h | ⟨⟨⟩, ⟨⟩⟩ := not_or_of_imp (D.homZeroPart.mem_range_index p).2
  · simp [D.homZeroPart.incl_eq_zero,
      h, ↓HasDegreeGe.mul (w'' := Y.gradeOf ⊕ᵥ Y''.gradeOf) (x := stackedT Y Y' Y'') (Sum.rec (by
      simp +contextual [stackedT, B, Y.hasDegreeGe_neg_one_stringMap _, add_comm])
      Y'.hasDegreeGe_neg_one_stringMap) (Y'.mem_unipotent.1 o) le_rfl p.1 p.2 (by omega)]
  simp [homZeroPart, GradeZeroPart.hom, D.stackedT_apply, homTarget, removePlanes, inclMatrix,
    Fintype.sum_prod_type, apply_ite toAdele, Finset.sum_mul,
    Finset.sum_comm, kAdelic, Matrix.mul_assoc]

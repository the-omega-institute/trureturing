/- GID: D5/S3/Zeros/GRH/Lib/Weil/CompactLift/RallisFormula
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/CompactLift/RallisFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.CompactLift.RallisFormula. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/CompactLift/RallisFormula.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.NeatLevel
import D5.S3.Zeros.GRH.Lib.LocalGL.Green.LabelIdempotents
import D5.S3.Zeros.GRH.Lib.CM.FormalGroup.FormalHeight
import D5.S3.Zeros.GRH.Lib.Weil.Periods.BesselIntegral
import D5.S3.Zeros.GRH.Lib.SiegelWeil.RallisInner.SharpData
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Mass.MassRatio
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Theta lift for a definite unitary pair as a class sum on algebraic modular forms.
The pair here is U(n)×U(n′) over a CM field with n < n′. The kernel is the matrix of Taylor
coefficients of the theta function against Schur polynomials, and the constant is left unspecified.
Source: B. Gross, Algebraic modular forms, Israel J. Math. 113 (1999); Kashiwara–Vergne 1978; R.
Howe, Transcending classical invariant theory, JAMS 2 (1989).

Known result: Seesaw identity for periods of theta lifts. The form here is for any two unitary pairs
whose kernels agree up to moderate factors for a spanning set of Fock polynomials. If finite sums of
periods of the lift are proportional to a fixed family of numbers at all real translates, so are
those of the descent. Source: S. Kudla, Seesaw dual reductive pairs, in Automorphic forms of several
variables (Katata 1983), Progr. Math. 46, Birkhäuser 1984, 244–268.

Known result: Non-vanishing of theta lifts in large rank. The form here is for unitary groups with
target rank more than twice the source rank and for finite data sharp at a level, and it uses no
L-functions. If the lift vanishes, the real matrix coefficient of the datum convolves the form to
zero. Source: S. Rallis, Injectivity properties of liftings associated to Weil representations,
Compositio 52 (1984); J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic
quotients, Crelle 428 (1992).

This file: Definite theta lift equals class-sum lift of algebraic forms; matching of parameters.
Seesaw: periods of a descent are read on periods of a lift. Rallis inner product formula for sharp
data; injectivity of the lift in Weil's range. -/
seal Finset.univ Finset.sum Finset.prod

open Set Fintype Matrix MeasureTheory NumberField Space Submodule

variable {E n n' : Type} [Field E]

/-- Theta correspondence of definite spaces of ranks n < n': if the diagrams κ fit and l is the
parameter of the weight (κ, ec), then l and l' match for a lift with weights ea, eb exactly when l'
is the parameter of (κ, ea). -/
lemma IsHCParam.paramsCorrespond_iff [NumberField E] [Fintype n] [Fintype n'] {κ : InfinitePlace E →
  _} {l : NumberField.InfinitePlace E → n → ℤ} {l' : NumberField.InfinitePlace E → n' → ℤ} {ea eb
  ec : NumberField.InfinitePlace E → ℤ} (h : IsHCParam κ ec l) (F : IsLiftWeight n n' κ eb ec) :
  ParamsCorrespond (n := n) (n' := n') ea eb l l' 1 1 ↔ IsHCParam κ ea l' := by
  have z w p := (Finset.sum_subset (f :=
    κ w) (Finset.Ioc_subset_Ioo_right (a := p) F.2.1) (by grind [IsLiftWeight])).symm
  use fun m w ↦ ⟨?_, fun r ↦ ((m w).3 r).elim (fun ⟨c, _⟩ ↦ ((h w).2 c).imp ?_) fun _ ↦ ⟨(ea w +
    (card n' - l' w r) / 2).toNat, ?_⟩⟩, fun h' w ↦ ⟨h'.hasGap .., (h.hasGap ..).neg, fun r ↦
    ((h' w).2 r).elim fun p _ ↦ (lt_or_ge p _).imp (h.exists_decrPosition_eq w · |>.imp ?_) ?_,
    fun c ↦ .inl (((h w).2 c).elim fun _ a ↦ (h'.exists_decrPosition_eq w (a.1.trans F.2.1)).imp
    ?_)⟩ <;> simp_all only [pairSign, hcParameter, IsMatchedPair, FockDualPair.centredParam,
    diagramWeight_apply, Pi.neg_apply, Pi.one_apply, Units.val_one, mul_one, IsLiftWeight] <;> grind
    [Finset.sum_Ioo_add_eq_sum_Ioc, Finset.Ioc_eq_empty, IsMatch, HasGap, ParamsCorrespond]

/-- For I_n, I_{n'} with fitting weights, corresponding parameters l, l' and scale c ≠ 0 there
is β such that, for every theta kernel at a level K of finite index in K₀ and φ with open
stabiliser, harmonic ⊗ f lifts F_φ to β[K₀:K]⁻¹F_{φ'}, φ' the algebraic lift.

Known result: Theta lift for a definite unitary pair as a class sum on algebraic modular forms. -/
lemma exists_lift_ofAlgForm_eq_smul [CMType E] [Fintype n] [Fintype n'] {κ l l' ea eb ec}
  [WeilData E] (h : IsHCParam κ ec l) (h' : IsHCParam κ ea l') (hκ :
  IsLiftWeight n n' κ eb ec) {c} (hc : c ≠ 0) : ∃ β : ℂ, ∀ {a b : AutChar E} {ψ ψ'} {ha :
  a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'} K [IsLevel K] k, thetaKernel hκ c ha hb K = k → ∀ f φ,
  lift (pairThetaKer (stdSpace ..) _ a b) (integrated _ (jointHarmonic ea eb l l' 1 1) f.1)
  (ofAlgForm l 1 φ) = (β / stdLevelIndex K) • ofAlgForm l' 1 (k.lift f φ) := by
  choose u U using fun w ↦ have m :=
      (h.paramsCorrespond_iff hκ).2 h' w; m.unique (Classical.epsilon_spec
    m.exists_isJointHarmonic).2.isPreJointHarmonic (staircase_harmonic_highest m.2.1 m.1.1
      (by tauto) (Pi.single 1 (κ w)) (by fin_cases · <;> simp_all [IsLiftWeight, FitsRanks])
      (by simp) (by simp [h'.lowestKType_eq, diagramWeight_apply, vacuumWeight])).isPreJointHarmonic
  have ⟨β, e⟩ : ∃ c : ℂ, c • schurCoeffPoly (highestVector κ l' ᵥ* weylGramOver)
    (highestVector κ l) = jointHarmonic ea eb l l' 1 1 := ⟨_, MvPolynomial.funext (by
    rw [MvPolynomial.smul_eval, eval_schurCoeffPoly hκ ·, ← smul_eq_mul, mul_smul,
      ← dotProduct_smul]
    erw [schur_mulVec_weylEval hκ.1, ← dotProduct_mulVec, ← PolyRep.eval_toPoly]
    simp [*, jointHarmonic, RingHom.map_det, Matrix.map, _root_.permArray, highestPoly, tableauPoly,
      ite_and,
     apply_ite, weylKernel, AlgHom.map_det, rowSubst, minor]; congr! 4; apply det_transpose)⟩
  let d := β / c ^ boxes κ (card n')
  use d / card (WeylIndex n κ); introv i
  choose J _ H using exists_level_pairWeil a b f.2; ext ⟨y, z⟩
  let L := d • gramForm (highestVector κ l') ∘ₗ conjWeylRep κ ea y⁻¹
  rw [lift, integral_mul_eq_classIntegral h K ((pairThetaKer ..).isAutomorphic J
    (by erw [pairWeil_integrated_fin, H · ·]; simp) _) (L.comp <| k.jetMatrix
    <| k.ω ⟨·, z⟩ f), map_classIntegral L 1 (k.integrand_mem_smoothInvariants f φ z)]
  iterate 2 simp [L, algFormCoeff, Kernel.lift, field]
  simp [← e, pairWeil_integrated_all, realPairWeil_schurCoeffPoly hκ, gramForm_apply, ← i,
    thetaKernel, star_highestVector, field, conjWeylRep,
    schurJet_jetSeries_eq_smul hκ c, ↓dotProduct_schurJet_mulVec, dotProduct_mulVec, -mulVec_mulVec]

/-- For ranks 0 < |n| < |n′|, weights as in `IsLiftWeight`, a level K, a scale c ≠ 0 and characters
of weights ea, eb, the lifts by the kernels `thetaKernel` are theta lifts in the sense of
`Space.IsThetaLift`.

Known result: Theta lift for a definite unitary pair as a class sum on algebraic modular forms. -/
lemma isThetaLift_thetaKernel [CMType E] [WeilData E] [Fintype n] [Fintype n'] {κ e ea eb} [Nonempty
  n] [Nonempty n'] {O a c} {K : Subgroup (Gf E n)} [IsLevel K] {hκ : IsLiftWeight n n' κ eb e} (hc :
  c ≠ 0) {ψ ψ' : O → _} {ha hb : ∀ _, _} : IsThetaLift κ e ea a fun o ↦ (thetaKernel hκ c
  (ha o : (a o n).HasWeight _ (ψ o)) (hb o : (a o n').HasWeight _ (ψ' o)) K).lift := fun P t ↦ by
  obtain ⟨g, k⟩ := isHCParam_hcParameter n κ e, isHCParam_hcParameter n' κ ea
  obtain ⟨r, rfl⟩ :=
    Finsupp.mem_span_range_iff_exists_finsupp.1 (FiniteDimensional.mem_span_of_iInf_ker_le_ker
    (L := (_ ∘ₗ conjWeylRep κ e ·)) (highestVector_cyclic (g · |>.1) e t · ∘ by aesop))
  apply Exists.intro (∑ x ∈ _,
    (strongIntegral _ (.mk <| (_ : ℂ) • _ ∘ₗ conjWeylRep κ ea ·⁻¹)).1); introv
  simp_rw [algFormCoeff_apply, Finsupp.sum, LinearMap.sum_apply, ← algFormCoeff_apply,
    Finset.mul_sum]
  rw [integral_finsetSum]; rcongr x
  have W := pairWeil_integrated (stdSpace E n) (stdSpace E n') (a o n) (a o n')
  have := W x 1 ↑(r x • P) Φ ▸ ((((g.paramsCorrespond_iff hκ).2
    k).isEdge_jointHarmonic.lift_isForm_and_eq_realConv _ (by simp [↓realPairWeil_polyVector,
    ← map_smul])).choose_spec (pairThetaKer ..) W (isForm_ofAlgForm g φ)).2
  rw [Prod.mk_one_one, ThetaKernel.lift_omega_left,
    (exists_lift_ofAlgForm_eq_smul g k hκ hc).choose_spec K _ rfl] at this
  erw [algFormCoeff_apply, strongIntegral_apply]
  simpa [realConv, algFormCoeff, ← mul_assoc, lift,
    mul_comm _ (r x)] using congr($this h); all_goals intros
  simpa using integrable_of_compactSpace
  any_goals apply_rules [(pairThetaKer ..).integrable_theta_mul, IsAutomorphic.mem_rapidFunctions,
    isAutomorphic_algFormCoeff] <;> simp

variable {E n m n' m' : Type} [Field E] [CMType E] [Fintype n] [Fintype m] [Fintype n']
  [Fintype m'] {s t s' t'} {S : Space E n s} {T : Space E m t} {S' : Space E n' s'}
  {T' : Space E m' t'}

lemma Space.height_reindex e he g : (S.reindex e he).height (.reindex (t := t) e he g) =
  S.height g := by simp [height, firstMinimum, image, reindex_equiv (e.piCongrLeft' _).symm,
  baseLattice, archCoords, ↓move_vecAtPoint, vecAtPoint, reindex,
  ← map_inv, PiLp.norm_eq_of_L2, sum_prod_type, mulVec_eq_sum, reindex_equiv e, funext_iff]

lemma Space.integrable_moderate_mul_forms {k d e r} (h : IsConjKernelPair k) (w :
  S.ModerateWeight T) (f : S.Form (k d)) (y : T.Form e) : Integrable (fun z ↦ w.weightFn z * f z * y
  (w.groupMap z * r)) S.quotMeasure := y.2.isBoundedMeasurable.integrable_mul_comp
  (((h.form_mem_rapidFunctions f).2.mul w.3).integrable (w.weightFn.2.mul f.2.continuous)) _

/-- The bilinear form (f, y) ↦ ∫ M(z) f(z) y(j(z)r) dz over [U(S)], for forms f on S, y on T,
continuous moderate M, continuous j and a real point r. -/
noncomputable def Space.periodPairing {k d e} (h : IsConjKernelPair k) (w : S.ModerateWeight T) (r :
  GInf E t) : S.Form (k d) →ₗ[ℂ] T.Form
  e →ₗ[ℂ] ℂ := by apply LinearMap.mk₂ ℂ (∫ z, w.weightFn z * · z * · (w.groupMap z *
  (r, 1)) ∂S.quotMeasure) <;> simp_intro .. [integrable_moderate_mul_forms h w, ← integral_add,
  ← integral_const_mul, ← mul_add, ← add_mul] <;> congr! 2 <;> erw [coe_smul] <;> simp [field]

/-- See-saw for edges S → T, T′ → S′, with ht(j′g) ≪ ht(g). Call p matched if N·kernel(p) along
j′ equals M·kernel(Q) along j and the sums Λ_o of M-periods of f against lifts of y, at each
real translate, are proportional to c_o. If matched p span, so are the Λ_o of N-periods of y
against descents of f.

Known result: Seesaw identity for periods of theta lifts. -/
lemma seesaw_periods [WeilData E]
    J {X Y : J → Type} {a a' 𝔪 W : ∀ _, _} {c : J → ℂ} {k l k' l' d d' Φ Φ' r} {Λ u
  ι y f N Ψ' : ∀ _ _, _} (hΛ : ∀ o (F : X o → ℂ), Λ o F = ∑ i ∈ W o, u o i * F (ι o (i : Y o))) (h :
  IsEdgeFamily a k l d Φ) (h' : IsEdgeFamily a' l' k' d' Φ') (H : ⊤ ≤ span ℂ {p | ∃ Q, ∃ Ψ M :
  ∀ _ _, _, (∀ r, ∃ β, ∀ o, (Λ o fun i ↦ periodPairing h'.2.1 (M o i) r (f o i) (modLift S T (a o) Φ
  (Ψ o i) (k d) (l d) (y o i))) = β * c o) ∧ ∀ o i g x, (N o i).weightFn g * modKernel T' S' (a' o
  m') (a' o n') (𝔪 o) (Ψ' o i) p ((N o i).groupMap g) x = (M o i).weightFn x * modKernel S T (a o n)
  (a o m) (𝔪 o) (Ψ o i) Q g ((M o i).groupMap x)}) : ∃ β, ∀ o, (Λ o fun i ↦ periodPairing h.1
  (N o i) r (y o i) (modDescent T' S' (a' o) Φ' (Ψ' o i) (k' !d') (l' !d') (f o i))) = β * c o := by
  obtain ⟨⟨_, _, _, _, ⟨⟩⟩, hf⟩ := h'.2.2, (h'.2.1.form_mem_rapidFunctions <| f · ·)
  have I o i := (pairThetaKer _ _ (a' o m') (a' o n')).swap.integrable_prod_weightFn (hf o i)
    (N o i) (h.1.form_mem_rapidFunctions (y o i))
  let L (v : ∀ _ _, _) := ContinuousLinearMap.pi fun o ↦ ∑ z ∈ W o, u o z •
    let i := ι o z; strongIntegral (S.quotMeasure.prod S'.quotMeasure) (fun (g, x) ↦
      ((N o i).weightFn g * y o i g) • (θ _).smulRight (f o i x) ∘L pairWeil T' S' (a' o m')
      (a' o n') ((N o i).groupMap g, x)) ∘L (integrated _).flip (v o z)
  replace H v G u : L v u ∈ ℂ ∙ c :=
    denseRange_polyVector.induction_on u ((closed_of_finiteDimensional
    _).preimage (L v).2) fun _ ↦ span_le (p := (ℂ ∙ c).comap ((L v).1 ∘ₗ polyVector _)).2 G (H ⟨⟩)
  simp_all [-integral_const_mul, L, periodPairing, subset_def, mem_span_singleton, funext_iff,
    strongIntegral_apply, integral_prod, lift, ↓lift_mul_right, h'.isArrow_modDatum.2.coe_formLift,
    modDatum, ← Prod.mk_one_one, pairWeil_integrated, ← integral_const_mul (_ * _)]
  refine (H _ (fun p Q Ψ M β hM ↦ ?_) _).imp fun _ ↦ (· · |>.symm)
  choose β H using β; choose α e using h.exists_lift_eq_realConv Q
  have K o i (U : T.Form (l d)) := U.2.isBoundedMeasurable.integrable_mul_comp (α.integrable (μ :=
    volume).mul_prod (((hf o i).2.mul (M o i).3).integrable ((hf ..).1.rec (by fun_prop)))) fun (r,
    x) ↦ (M o i).groupMap x * (r, 1)
  use ∫ r, α r * β r
  simp_rw [← integral_mul_const, mul_assoc (α _), ← H, Finset.mul_sum, mul_left_comm _ (u ..),
    ← integral_const_mul (α _), Pi.mul_def,
    integral_finsetSum _ fun _ _ ↦ (K ..).integral_prod_left.const_mul _] at *; congr!
  rw [integral_const_mul, integral_integral_swap (K ..), eq_comm, integral_integral_swap (I ..)]
  simp_rw [mul_left_comm (α _), integral_const_mul, ← realConv.eq_1, ← e, lift,
    ← integral_const_mul]
  congr! 4; erw [mul_mul_mul_comm, hM]; ac_rfl

attribute [local simp] measureReal_univ_ne_zero indicator partialIntegral mem_localLevel

variable [WeilData E]

variable {a b S₀ J c} {T : Space E m t} {F γ' ψ y} (hF : IsSharp b S₀ F J c) [hb : b.HasWeight γ' ψ]
  (v : PairFock E s t) (hJ : HasLevel y J) (hy : y ∈ S.rapidFunctions) (hM : 2 * card n < card m)
  (h0 : lift (pairThetaKer S T a b) (((S.hom T).integrated v) F) y = 0)

include ψ hF hJ in
/-- For F sharp of mass c, y right J-invariant, φ = v ⊗ F, u finite: c ≠ 0, and ∫⟨φ, ω(g)φ⟩⟨y',
R(ug)y⟩ over g integral off S₀ equals c∫⟨v, Ω(x)v⟩⟨y', R(xu)y⟩dx over real points x, with Ω
= `realPairWeil` γ γ'. -/
lemma IsSharp.partialIntegral_eq γ y' u : c ≠ 0 ∧ partialIntegral S₀ᶜ (weilMatrixCoeff b
  (integrated _ v F) * fun g ↦ S.petersson y' (rightRegular ℂ _ ℂ ((1, u) * g) y)) = c * ∫ x,
  realInner v (realPairWeil γ γ' (x, 1) v) * S.petersson y' (y <| · * (x, 1) * (1, u)) := by
  have o := J.isOpen_of_one_mem_interior ⟨_, ⟨isOpen_Kf.inter isOpen_ne.preimage_of_continuous,
    fun g k ↦ (ite_ne_right_iff.1 (mt (hF.coeffIntegrand_eq g (Kf_le_localLevel k.1)).trans
    k.2)).1.1⟩, by simp [weilMatrixCoeff, hF.self_ne_zero]⟩
  use by simp [← hF.mass_eq, hF.self_ne_zero, isCompact_Kf.relIndex_ne_zero o]
  rw [mul_comm c, ← (integral_indicator_const (μ := volume) (dataInner _ F F) (o.inter isOpen_Kf
    ).measurableSet).trans (hF.mass_eq.subst (by simp [measure_inter_eq_inv_relIndex isCompact_Kf o,
    Measure.real, field])), ← integral_prod_mul, partialIntegral,
    ← integral_indicator (isOpen_localLevel _).measurableSet]
  congr!
  rw [indicator, Pi.mul_apply, weilMatrixCoeff, pairWeil_integrated_all, dataInner_integrated,
    ← pairWeil_integrated_fin]
  simp_all [hF.mem_finitePart, hF.coeffIntegrand_eq, petersson, Prod.mul_def, ← mul_assoc,
    realPairWeil, mem_Kf_iff]
  grind

include ψ hF hJ hy hM h0 in
/-- Let S, T have ranks n, m with 2n < m, φ = v ⊗ F with F sharp for J, and y, y' automorphic
and rapidly decreasing, y fixed by J with zero lift by φ. With Ω = `realPairWeil` γ γ',
∫⟨v, Ω(x)v⟩⟨y', R(x)y⟩ dx =
0, x over real points.

Known result: Non-vanishing of theta lifts in large rank. -/
lemma integral_eq_zero_of_lift_eq_zero γ {y'} (hy' : y' ∈ S.rapidFunctions) : ∫ x,
  realInner v (realPairWeil γ γ' (x, 1) v) * S.petersson y' (y <| · * (x, 1)) = 0 := have P :=
    (inner_product_formula hM a b (hF.clean v) hy hy' ·)
  by simpa [by simpa using hF.partialIntegral_eq v hJ γ y' 1] using (tendsto_partialIntegral S₀
          (P (integrated _ v F)).1).congr (f₂ :=
    fun _ ↦ 0) (exists_dual_datum b hM (hF.vacuum_off _ v disjoint_sdiff_right)
    ·.finite_toSet.sdiff |>.elim fun f' _ ↦ by simpa [petersson, *, ↓← (integral_indicator
    (isOpen_localLevel _).measurableSet)] using (P f').2)

include ψ hF hJ hy hM h0 in
/-- Let rk T > 2 rk S, F sharp for J, y automorphic, rapidly decreasing, J-invariant, with zero
theta lift by v ⊗ F. If k(x) = ⟨v, Ω(x)v⟩ (Ω = `realPairWeil` γ γ') is integrable on the real
points, then ∫k(x)y(gx)dx = 0 for all g.

Known result: Non-vanishing of theta lifts in large rank. -/
lemma realConv_eq_zero_of_lift_eq_zero γ (hk : Integrable (realInner v <|
  realPairWeil γ γ' ⟨·, 1⟩ v)) : realConv (realInner v <| realPairWeil γ γ'
  ⟨·, 1⟩ v) y = 0 := have m := IsBoundedMeasurable.of hy.2.bounded hy.1.1
  let ⟨A, b⟩ := isAutomorphic_realConv _ m hy.1.2 hy.1.3.choose_spec hk
  A.eq_zero_of_petersson_self (b.memLp_top.mono_exponent le_top)
    (by simp [petersson_realConv_right m, ← conj_petersson (F' := realConv _ y),
    fun x ↦ m.comp (· * x), integral_eq_zero_of_lift_eq_zero hF v hJ hy hM h0 γ
    ⟨hy.1.comp_mul_right _, hy.2.comp_mul_right⟩, *])

/-- Rallis inner product formula, rk T > 2 rk S, v an edge from type e: there is A ≠ 0 such
that, for F sharp for J of mass c, the lift L by v ⊗ F kills no nonzero J-invariant form y,
and ⟨Ly', Ly⟩ = Ac∑ρ(γ)⟨y', R(γ)y⟩ over cosets off S₀ (`cosetTerm`).

Known result: Rallis inner product formula by doubling. -/
lemma rallis_inner_product_euler {γ v e e'} (K : IsEdge (realPairWeil γ γ') e e' v) (hM : 2 * card
  n < card m) : ∃ A ≠ 0, ∀ (a b : AutChar E) {ψ ψ' S₀ J F c} [a.HasWeight γ ψ] [b.HasWeight γ' ψ'],
  IsSharp b S₀ F J c → ∀ y : S.Form e, HasLevel y
  J → let L := formLift (pairThetaKer S T a b) e e' (integrated _ v F); (L y = 0 → y = 0) ∧ ∀ y',
    HasSum (A * c * cosetTerm (card m) b S₀ᶜ y' y ·) (T.petersson (L y') (L y)) :=
  ⟨T.quotMeasure.real univ * _, by simpa using K.inner_ne_zero, fun a b ↦
  fun hF y hJ ↦ have A := (K.isArrow a b hF.mem_finitePart).1
  by simp [A.coe_formLift]; use fun e ↦ by
       simpa [y.2.petersson_real_translate K.isCuspKernel_source y.2, ← mul_assoc, K.inner_ne_zero,
                            ← inner_eq_petersson] using (integral_eq_zero_of_lift_eq_zero hF v hJ
         (A y).1 hM (A.coe_formLift y ▸ congr($e.1)) γ (A y).1), fun y' ↦ (inner_product_formula hM
    _ _ (hF.clean v) (A y).1 (A y').1).rec fun I e ↦ e ▸ .congr_fun (.mul_left _ (by
    simpa [↓hF.partialIntegral_eq v hJ γ, y'.2.petersson_real_translate K.isCuspKernel_source
      (y.2.comp_mul_right _), ← mul_assoc] using hasSum_partialIntegral_coset ∅ cosetRep
      (hF.vacuum_off _ v disjoint_compl_right) I nofun (left_eq_inf.2 nofun) ((existsUnique_congr
      (by simp +contextual [cosetRep, Quotient.eq_mk_iff_out, QuotientGroup.leftRel_apply])).1 <|
      @existsUnique_eq _ ⟦·⟧))) fun _ ↦ by rw [cosetTerm]; ring!⟩

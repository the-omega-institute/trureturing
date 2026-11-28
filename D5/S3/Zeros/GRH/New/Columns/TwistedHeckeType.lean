/- GID: D5/S3/Zeros/GRH/New/Columns/TwistedHeckeType
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/TwistedHeckeType
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.TwistedHeckeType. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/TwistedHeckeType.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.TwistedHecke.ElementaryDivisors
import D5.S3.Zeros.GRH.New.Seesaw.LiftCharacters
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! A Frobenius-twisted Hecke operator has small elementary divisors. An integrally scaled Hecke
operator above p, on forms at tops linked in a circle by Frobenius and conjugation, has elementary
divisors of small mean exponent outside a small share, so using it once per theta lift to keep
divisibility when the partner of a top is a top costs little index. Integral scalings of Hecke
operators and, for GL(2) over Q and regular p, slopes of T_p of at most about k/(p+1) are known.
Related work: Arsovski, Limiting measures of supersingularities, 2019; Liu–Truong–Xiao–Zhao, Slopes
of modular forms and geometry of eigencurves, 2023; Fakhruddin–Pilloni, Hecke operators and the
coherent cohomology of Shimura varieties, 2021.

Trading denominators at the level prime for a column operator. On columns ramified at the level
prime N, a chain of lifts whose data have denominator N equals a scalar of controlled denominator
times a chain with data given mod N, applied after a power of a Gauss-sum-weighted Hecke operator at
N, so the chain loses little divisibility at N on a submodule of small index. Hecke-type operators
passing through a theta lift, for data with ramified characters at a split prime, are known. Related
work: Z. Liu, Test Schwartz functions at p for theta lifts of Hida families, 2025; Rallis,
Langlands' functoriality and the Weil representation, 1982.

This file: Valuation at N of character factors and of data given modulo N. Chain with denominators N
equals scalar times chain mod N after Gauss-sum operator. Valuation of the restricted chain at the
level prime N on a submodule. Scaled Hecke operator on algebraic forms has elementary divisors of
small mean exponent. -/
seal Finset.univ Finset.sum Finset.prod

open Ideal IsSplitLevel QuadField Matrix NumberField Parameters Real Ideal.Quotient Data Finset
  Space
variable {P} (D : Data P) (ϑ) [PadicPlace D.N] [l : IsSplitLevel D.nonInducedPlaces D.N]

lemma Data.norm_detCharAt_diagN_le {i} (hi : i ≤ 2 * D.m) k j S : ‖ιₚ (detCharAt
  (D.chainChar ϑ i).baseChange k (l.diagN (D.InitIndex j) S))‖ ≤ D.N ^ (2 * D.f * D.b) := by
  grw [norm_detCharAt_diagN_anti (n' := InitIndex _ j) bot_le, ← atPlaces_embedGL (diagN ..)]
  simp [detCharAt, -atPlaces_embedGL]
  erw [D.hasWeight_liftChar.norm_padic_eq_prod ιₚ _ (unitary _).one_mem.2,
    ← G.det_of_supportedOn (s := 1) disjoint_star
    (embedGL_mem_supportedOn _), mul_right_comm, rpow_mul_natCast (by simp), ← Finset.prod_const]
  gcongr
  erw [G.det_snd, ← star_star (det _), adeleExtension_star, ← det_conjTranspose,
    ← U.inv_val_eq_conjTranspose, RingHom.map_det, congr($(adeleExtension_map_diagN ..)⁻¹.1.det)]
  split <;> grw [← D.w_le_two_mul_b hi τ] <;> simp [norm_p_eq_inv, NeZero.one_le, one_le_pow₀]

/-- For ι : ℂ → ℂ_N and j < m, cut the j-th datum of x by the indicator of integral matrices
with last column ≡ the last basis vector at the primes `Data.nonInducedPlaces`. Its kernel
multiplies ι-gauges by at most N^{fb}. -/
lemma Data.name_lastColDatum_mem_raises x {j} (hj : j < D.m) :
  l.name (lastColDatum lastBasisVector) (translateDatum x j) ∈ (liftKernel ϑ j).raises 1 1
  (D.N ^ (D.f * D.b)) := let q := algebraMap (𝓞 P.K) (_ ⧸ (D.inducedPlace 1).1)
  have z x : q x = 0 ↔ ‖ιₚ x‖ < 1 := phi_algebraMap .. ▸ eq_zero_iff_mem.trans (mem_placeOfEmb ..)
  have ⟨c, _⟩ := mem_multiples_of_prime_card (g' :=
    q (c₀ _)) (by apply q_eq_of_modEq_one D.N_modEq_one (p_mem_inducedPlace ..)) one_ne_zero
  let a := c₀ P.d - c
  have o : 1 ≤ ‖ιₚ (star ↑a * P.d)‖ := by simpa using (z (star a * P.d)).2.mt (by simp [a]; grind
    [two_mul, map_sqrtNegDInt_sq q, (FinPlace.charP_quotient _ (D.p_mem_inducedPlace 1)).1,
    not_dvd_N₁_mul_d_of_modEq_one D.N_modEq_one])
  have ⟨𝔪, hS, hm⟩ :=
    exists_modulus_places_eq (ι := D.nonInducedPlaces) (w := (↑)) (by simp [star_notMem])
  have := (congrArg _ (by simp [IsSplitLevel.name, lastColDatum,
    IsSplitLevel.liftFn_eq_residueDatum, ← _root_.liftFn_eq_residueDatum hS, *]; rfl)).subst
    ((isAdmissibleComb_name _ 𝔪 (q := 1) (B := 0) (hm (by simpa using IsSplitLevel.natCast_mem)) (by
    grind [one_mem, zero_mem]) id rfl ⟨algebraMap (𝓞 D.E) _ (star (algebraMap _ _ a)), by
    simpa [eq_zero_iff_mem] using hm (by
      simp; simp [nonInducedPlaces, inducedPlace]; intro; erw [phi_algebraMap]; grind [map_natCast])
    ⟩).smul_mem (by simp) fun _ e ↦
    finHeisOp_mem_standardData (fun i w _ ↦ by simpa [one_notMem] using! e i w) (by
    erw [hS, Space.projOn_finHeisOp _ (by simp [intVacuum]), boxIndicator_apply]; split <;> simp
    use Submodule.subset_span ⟨_, fun i w _ ↦ mul_mem (w.coe_algebraMap_mem _ _
      (algebraMap _ _ a)) (idem_mul_mem_Ô.1 (by tauto) w (by simp_all [l.4])), rfl⟩))
  (inv_smul_smul₀ (by simp [NeZero.ne]) _).subst
    (Kernel.smul_mem_raises _ (mem_raises_of_standardData (by norm_num [·, a] at o) this) (by
  grw [norm_star_piG_le_one, ← o, absNorm_span_natCast, RingOfIntegers.rank,
    finrank_eq_two_mul_card_infinitePlace, ← pow_mul]
  simp [norm_p_eq_inv, ← rpow_natCast, ↓card_X, D.N_prime.one_lt]
  grw [D.n_mono hj, n_mono _ hj.le]; use D.le_of_hasLogBound))

seal liftKernel Kernel.lift SmoothForm

/-- Some t with ‖ι t‖ ≤ N^{4fb(ϱ+1)} serves all data v_j and ramified columns φ: the chain of ϱ+1
pairs `Data.pairTranslates` of projected v_j at φ is t times the chain with data ω(d_j,
d_{j+1})(𝐛 ⊗ v_j) at F^{ϱ+1}φ (`IsSplitLevel.lastColDatum` of the last basis vector,
`Data.diagPointN`, `IsSplitLevel.fourierOp`). -/
lemma Data.chain₂_pairTranslates_eq_smul_chain {P} (D : Data P) [PadicPlace _] ϑ (l :=
  D.isSplitLevel_nonInducedPlaces) : ∃ t, ‖ιₚ t‖ ≤ D.N ^
  (2 * D.m * D.f * D.b) ∧ ∀ᵉ (v : ∀ _, _) (φ ∈ D.ramifiedColumns),
  chain₂ (D.liftKernel ϑ) (D.pairTranslates (projOnFinPart _ D.piPlaces <| v ·)) (D.ϱ + 1) φ = t •
  chain (D.liftKernel ϑ) (fun j ↦ (D.liftKernel ϑ j).ω (D.diagPointN j, D.diagPointN _) <| l.name
  (lastColDatum lastBasisVector) (v j)) _ ((fourierOp (D.nonInducedRep 0) ^ (D.ϱ + 1)) φ) := by
  refine ⟨_, ?_, fun v φ a ↦ have o j f g k := eq_inv_smul_iff.2 (congr($(D.liftKernel_ω ϑ j) _ _
    ).trans (l.pairWeilFinite_name g f _ _ k (v j))).symm
    have w j a b Φ φ := by simpa using
      (D.liftKernel ϑ j).lift_equivariant a b Φ (smoothFormRep _ _ a⁻¹ φ)
    .trans (congrArg (compUpTo · _ _) (by ext; simp [TensorChain.liftInPairs,
      l.translateSum_eq_sum_name D.isSplitLevel_piPlaces, conjEmbedGL, diagN_eq_sdiff_mul
      D.piPlaces, pairTranslates, lastColDatum, charDatum, smul_sum, smul_smul, w,
      by simpa [↓spaceChar_rankTwist] using And.intro (o · · · 1) (o · · 1 ·⁻¹)]; rfl))
      (compUpTo_pairs_eq_smul D.nonInducedRep (L := fun j ↦ (D.liftKernel ϑ j).lift ∘ₗ _ ∘ₗ .applyₗ
      _ ∘ₗ name) (fun j ↦ ⟨fun b c f ↦ by simp [↓← funext (liftIntegralFn_mul (M := ·) l.reduction f
      b c), w, conjEmbedGL, by simpa [detCharAt_inclGL _ (D.charUnramifiedAt_rankTwist_of_N_mem _ _
      _ · <| l.natCast_mem _ ·)] using o j f (inclGL b) (inclGL c)⁻¹], fun φ ↦ by
    simp [← funext lastRowDatum_conj_u₀, lastRowDatum, w,
      conjEmbedGL, by simpa [↓spaceChar_rankTwist, ↓card_X] using (o j · l.diagNInv l.diagNInv)]
    exact (inv_smul_smul (_ : ℂˣ) _).symm⟩) (mem_ramified_of_mem_ramifiedColumns _ a) _)⟩
  simp; grw [norm_detCharAt_diagN_le, norm_detCharAt_diagN_le,
    IsUltrametricDist.norm_natCast_le_one, mul_inv_le_one_of_le₀] <;>
    (try gcongr) <;> simp [← rpow_mul_natCast, ← sq, m_eq_two_mul_varrho_add_two, prod_nonneg,
    norm_detCharAt_diagN_anti, D.n_mono _] <;> grind

open GeneralLinearGroup Function TwistingData Gf ComplexConjugate WithZero Fintype

/-- For ι : ℂ → ℂ_N, Ψ good for ϑ, and a ramified column φ with F^{ϱ+1}φ a column integral at
`Data.diagPointN` (F = `IsSplitLevel.fourierOp` of `Data.nonInducedRep`), B_μφ has ι-gauge at most
N^{3mfb} everywhere. -/
lemma Data.gaugeLe_Bmu_at_N {P} (D : Data P) [PadicPlace D.N] (l := D.isSplitLevel_nonInducedPlaces)
  {ϑ Ψ} (H : IsGoodDatum ϑ Ψ) {φ} (r : φ ∈ D.ramifiedColumns) (hφ : (fourierOp (D.nonInducedRep 0) ^
  (D.ϱ + 1)) φ ∈ integralFormsAt D.Column (D.diagPointN 0)) : GaugeLe 1 (D.N ^ (3 * D.m
  * D.f * D.b)) (Bμ ϑ Ψ φ) := (D.chain₂_pairTranslates_eq_smul_chain ϑ).rec fun t h ↦
  GaugeLe.restrictToY_of_diag D (D.adeleExtension_map_diagN _ _) fun g ↦ by
  have b := H.gaugeLe_chain ϑ.1.7.coprime_mul_left (fun j ↦ (D.liftKernel ϑ j).ω (_,
    _) ∘ₗ l.name (lastColDatum lastBasisVector)) (fun j x _ a b hb ↦ ?_) _ (φ := ⟨_, hφ.1⟩)
    (fun x _ _ h _ _ _ ↦ by simpa [Kernel.ω_ω] using name_lastColDatum_mem_raises _ _ x h ..) hφ.2 g
  · have := by simpa [*, smul_comm _ t, ← Ψ.smul_sum] using H.chain_at_N φ
    simp [weylGauge_smul, @id (_ = 2 * (_ + 1)) D.m_eq_two_mul_varrho_add_two ▸ this] at *
    grw [b, h.1]; simp [← rpow_add, NeZero.pos]; grind
  obtain ⟨⟨A, r, e⟩, B, s, f⟩ := D.atPlaces_conj_mem_mirabolic a,
    D.atPlaces_conj_mem_mirabolic ⟨b, hb⟩⁻¹; ext1
  simp [liftKernel_ω, lastColDatum,
    pairWeilFinite_name, -coe_units_inv]; congr 1; dsimp [IsSplitLevel.name, comp_def]
  rw [← atPlaces_embedGL (diagN ..), ← atPlaces_embedGL (diagN (InitIndex _ j) _),
    pairWeil_name_of_mem disjoint_star (hΨ := by
    simpa only [onHom_snd_inv_mulVec, vecToMat_matToVec, Matrix.map_mul, comp_def] using!
      (l.isSchwartzBruhat_liftFn _).comp_mulVec
      (G.onHom (s := 1) (s' := 1) ((1, _), 1, _)).2⁻¹.1) (levelOf_le_Kf a.2.1) (levelOf_le_Kf hb.1)]
  congr! 3; convert liftIntegralFn_mul l.reduction _ A B using 2 <;> simp [*, Matrix.mul_assoc,
    mul_apply_eq_vecMul, vecMul_transpose, -val_map_apply, show _ᵀ _ = _ from (mulVec_single_one ..
    ).symm.trans r, (mulVec_injective_of_isUnit (Units.isUnit _)).eq_iff' s] <;> norm_cast

attribute [local simp] mul_assoc QuotientGroup.eq atPlace_atSplit_of_ne mul_sum mul_mem_cancel_right

attribute [-simp] MonoidHom.coe_range

/-- Let l lie in a marked set Λ, T be twisting data on the tops inducing l or l̄, and `HeckeSizes`
hold. Then Y = `Data.IsMarked.markOperator` keeps the integral columns 𝒜, and [𝒜 : Y𝒜 + p^s𝒜] ∣ p^c,
c ≤ (z + xs + y)·dim.

A Frobenius-twisted Hecke operator has small elementary divisors. -/
lemma Columns.hasType_markOperator {P p} {D : Data P} [Fact p.Prime] [PadicPlace p] {Λ l N W ℓ x y z
  Q} [NeZero N] (L : D.IsMarked Λ) (a : l ∈ Λ) (hW : W = (l.valuation D.E).valuationSubring)
  (T : TwistingData N W embValRing) (hp : ¬IsUnit (T.p : embValRing)) (e : T.p = p) (t : _ ≃ Subtype
  Q) (hS : ∀ σ, Q σ ↔ σ ∈ D.tops ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l)) (hc : ∀ s x,
  T.ι s x = ite (T.isEven s) (Φ (t s).1) ((Φ (t s)).comp conj) x) (hA : markExponent l = D.a * #{s
  | T.isEven s}) (big : HeckeSizes T.P T.o₀ N D.k D.a (D.ceilLogM p) ℓ x y z) s : HasType ↑T.p
  D.integralColumns s (L.markOperator ⟨l, a⟩) ((z + x * s + y) * Module.finrank ℂ D.Column) := by
  have q : D.X 0 ≃ Fin D.k := equivFinOfCardEq (by simp [↓card_X, n])
  let P := parahoric W (twoBlock D.k (D.ceilLogM p))
  let ϖ : D.Eˣ := .mk0 p NeZero.out
  let d := diagGL (if q · < D.ceilLogM p then ϖ else 1)
  let jw := (GeneralLinearGroup.map W.subtype).comp (reindexGL q.symm).toMonoidHom
  let j v := GeneralLinearGroup.map (n := D.X 0) (algebraMap D.E (@LocField D.E _ _ v))
  have hM {v x} : j v x ∈ Kw .. ↔ x ∈ intGL _ (v.valuation D.E).valuationSubring.1 := by
    simp [mem_intGL, ← v_algebraMap_eq_valuation, -coe_units_inv]; rfl
  obtain ⟨rfl, _, ⟨ρ, hρ, hρ'⟩, hl, hv, hpl, hl', ⟨⟩⟩ := hW, T.finite_residueField,
    exists_reps_integralAbove (K := D.columnLevel 0) p, L.star_ne a,
    L.maxCompactAt_le_columnLevel a, L.p_mem a, L.valuation_p a, id big
  have hP {β} : j l (d⁻¹ * jw β * d) ∈ Kw .. ↔ β ∈ P := by
    have H β : (∀ i j, l.valuation _ ((d⁻¹ * jw β * d) i j) ≤ 1) ↔ β ∈ P := q.forall₂_congr q (by
      intros; dsimp [twoBlock]
      split_ifs <;> simp [*, d, jw, ← map_inv, field, ϖ, ↓OrderDual.toDual_lt_toDual,
        -WithZero.inv_exp, ← WithZero.exp_add, ← lt_mul_exp_iff_le, ↓Valuation.mem_maximalIdeal_iff]
          <;> first
        | use (β _ _).2.trans_lt (by trivial)
        | use (mul_le_one' (β _ _).2 (by trivial)).trans_lt (by trivial))
    erw [hM, mem_intGL, conj_inv, H, H β⁻¹]; simp
  choose ψ hψ using fun {τ b} (h : ite (τ ∈ D.tops) D.a 0 = b) ↦ schur_one_row_eq_symPowMatrix (k :=
    D.κ τ) (a := b) q.symm (by simp [↓card_X, n]; omega) (by grind only [card_X, κ, n])
  have hj v γ : ((stdSpace ..).embFin γ).atPlace v =
    j v γ := congr(.map (_root_.evalAt v) $(stdSpace_embFin γ))
  have hw' {x} : _ ↔ x ∈ jw.range := hM.trans (reindex_equiv (reindexGL _)).2.1
  have hD : j l d ∈ basicDoubleCoset _ l (D.ceilLogM p) := by convert (diagGL_mem_basicDoubleCoset
    (ϖ := ϖ.map _) ((v_algebraMap_eq_valuation _).trans hl') (q.finsetCongr.symm
    (Iio ⟨D.ceilLogM p, by omega⟩))).1 <;> simp [Units.ext_iff, j, d, Fin.lt_def, apply_ite,
      Equiv.finsetCongr]
  obtain ⟨_, r1, hKw⟩ := ofFinite (_ ⧸ P), (hρ' · ·), fun k : D.columnLevel 0 ↦
    mem_Kf_iff.1 (IsLevel.le k.2)
  let δ x β := ((ρ x).atPlace l)⁻¹ * (j l (jw β) * j l d)
  choose o γ u G using fun b : _ × _ ⧸ P ↦
    exists_eq_map_mul_rep_mul _ _ hρ (ρ b.1 * atSplit hl (δ b.1 b.2.out))
  have H b := eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq (G b).symm)
  choose g hg using fun b ↦ (@hw' ((jw b.2.out * d)⁻¹ * γ b)).1 (by simp [← hj, δ, *])
  have hγ b := eq_mul_of_inv_mul_eq (hg b).symm
  let ε : D.Column ≃ₗ[ℂ] _ := freeLevelEquiv _ _ 1 D.classAut_columnLevel_eq_bot hρ
  let f := ε.symm.1.restrictScalars _ ∘ₗ ((Algebra.linearMap embValRing ℂ).compLeft _).compLeft _
  let c := embValRing.subtype
  have hε F y : (f F).1.1 _ = c ∘ F y := congrFun (ε.4 _) y
  choose m hm using fun b (τ : Subtype (¬Q ·)) ↦ (if h : ↑τ ∈ D.tops then ((@hM (placeOfEmb
    (weightEmbedding ιₚ τ)) (γ b)).1 (by simp [← hj, r1 _ _ (natCast_mem_placeOfEmb _), by simpa [*,
    inducedPlace] using τ.2, H, hKw, placeOfEmb_comp_star, star_involutive.eq_iff])).elim (⟨.map
    (.restrict ((Φ τ).comp conj) _ _ fun _ ↦ (isEquiv_placeOfEmb _).le_one_iff_le_one.2) ·, · ▸
    rfl⟩) else ⟨1, Matrix.ext (by simp [by simpa using hψ (ite_eq_right h) 0])⟩ : ∃ m : GL _ _,
    schur (fun () ↦ D.κ τ) (fun _ ↦ (γ b).1.1.map (Φ τ ∘ conj)) = schur _ fun _ ↦ m.1.map c)
  convert T.hasType_twisted_hecke hp big f o g⁻¹ ((weylRep _ 0).toHomUnits ∘ m) (.trans
    (.piEquivPiSubtypeProd Q _) (.prodCongr (t.piCongr fun s ↦ (ψ (ite_eq_left ((hS _).1 (t
    s).2).1)).symm.trans (.piUnique _)).symm (.refl _))) ?_ (fun F ↦ eq_of_eq_on_class_reps hρ ?_) _
  refine le_antisymm (fun φ H ↦ ⟨fun c ↦ (⟨_, (weylGauge_le_one_iff _ (r1 c)).1
    (by simpa using H.2 _) ·⟩), ε.3 φ⟩) fun | _, ⟨F, rfl⟩ => ⟨by simp, fun g ↦ ?_⟩
  choose c γ k _ using exists_eq_map_mul_rep_mul _ _ hρ g
  simp [levelSpace_smoothFormRep_apply (f F).2, weylGauge_mul, -mul_assoc, ↓weylGauge_embFin,
    weylGauge_le_one_iff, mem_localLevel, *]; use (F c · |>.2)
  simp [finrank_levelSpace_smoothFormRep D.classAut_columnLevel_eq_bot]
  simp_intro b b' h
  use (eq_and_eq_one_of_doubleCoset_rep hρ ((map_eq_one_iff _ Fact.out).1 <|
    (D.classAut_columnLevel_eq_bot _).le ⟨⟨·, rfl⟩, ·⟩) (γ b * (γ b')⁻¹) ((mul_mem_cancel_right
    ((u b')⁻¹ * u b).2).1 (hv ((and_congr_left mem_Kf_iff_of_supportedOn).2 ⟨by
    simp [← mul_assoc, *, -H, -hg, -hM]
    simpa [mul_mem_cancel_left, hw', r1, hpl, (Units.ext (diagonal_transpose _) : invTransposeGL d =
      d⁻¹)] using! hM.2 ((invTransposeGL_mem_intGL _).2 (hM.1 (hP.2 h.2))), by simp +contextual [H,
    h]⟩)))).elim fun e f ↦ Prod.ext e (Quotient.out_equiv_out.1 (QuotientGroup.leftRel_apply.2 (hP.1
    (hw'.2 ⟨g b * (g b')⁻¹, by simp [hg, mul_inv_eq_one.1 f]⟩))))
  ext x; dsimp [IsMarked.markOperator]; erw [(heckeFun_eq_sum_pullback (J :=
    P) _ ((mem_sphericalAt_iff hl).1 (levelSpace_anti hv (f
    F).2)) univ (δ x) (fun z h ↦ ?_) (by simp [δ, ← hP]) _).2] <;> simp [δ, *, -hM, -map_mul]
  congr with b; erw [G (x, b)]
  simp [levelSpace_smoothFormRep_apply (f F).2, stdSpace_weightRep_apply, weylRep, lastEntry,
    mulVec, dotProduct, ← mul_assoc, hε]
  congr! 2; rw [pow_mul', ← prod_const, prod_filter, ← prod_pow, schur_apply_eq_prod .refl,
    schur_apply_eq_prod .refl, ← prod_subtype_mul_prod_subtype Q, ← t.prod_comp, ← mul_rotate',
    diagonal_pow_depth, map_prod]
  simp_rw [letterRep_apply, ← kroneckerPi_mul, ← map_mul, ← prod_mul_distrib, kroneckerPi, of_apply,
    map_prod]
  refine congr((∏ τ, $((hm ..).trans (schur_map .refl ..)) _ _) * ∏ s, $((hψ ..).trans
    (congrFun₂ ((congrArg _ ?_).trans (symPowMatrix_map c _)) ..))); clear * - hc hγ e
  have := NeZero.ne p
  cases _ : T.isEven s <;> ext <;> (try apply congr(p * Φ _ ($(@id ((γ _).1⁻¹.1 =
    _) (U.inv_val_eq_conjTranspose _)) _ _)).symm.trans) <;> simp [*, letterMatrix, deepIndicator,
    mul_apply, diagonal, ← map_inv, jw, d, reindex_equiv q,
    -sum_sum_type] <;> congr with <;> split_ifs <;> simp [*, ϖ, c, field] <;> omega
  choose k₁ _ _ _ h using by simpa [basicDoubleCoset_eq hD, DoubleCoset.mem_doubleCoset] using h
  choose γ a b using exists_mul_mem_integralAbove p (ρ x * atSplit hl k₁) (atSplit hl (j l d)⁻¹)
  choose β _ using hw'.1 (by simpa [*] using a l hpl)
  use β⁻¹; simpa [← mul_assoc, *] using b l hpl

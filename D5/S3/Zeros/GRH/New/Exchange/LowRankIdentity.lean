/- GID: D5/S3/Zeros/GRH/New/Exchange/LowRankIdentity
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/LowRankIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.LowRankIdentity. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/LowRankIdentity.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Tower.LargeSideConstantTerm
import D5.S3.Zeros.GRH.New.Exchange.StandardCoefficients
import D5.S3.Zeros.GRH.New.Exchange.NonnegativeVanishing
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: Orbit terms of theta kernel with standard ramified datum at parabolic points. Slice of
the standard datum factors over the two summands. Equal-rank theta integral is constant; exchange
identity at top of the tower. -/

open Fintype MatMul Matrix MeasureTheory Prod SemilocalField Space WeilData Splitting

variable {E : Type} [Field E] [CMType E] [WeilData E] {n} {a : Type} {b m} [Fintype n] [Fintype a]
  [Fintype b] [Fintype m] {s t r} {X : Space E m r} (W₁ : Space E n s) (D : X.Splitting W₁ b)
  (V : Space E a t) [IsBaseAdapted D] {W : Space E a t} (D₁ : X.Splitting W Unit) {μ} (𝔠 :
  SplitTameChar E μ)

/-- The functional v ↦ θ(ϱ(x)ω_{α,γ}(p)(v ⊗ F)) on real data of the pair (W₁,V), for a vector F,
an adelic matrix x and a point p. -/
noncomputable def thetaOnRealData α γ F x p :=
  θ _ ∘L ϱ _ (matToVec x) ∘L pairWeil W₁ V α γ p ∘L (integrated _).flip F

/-- For an adapted splitting, rapid v and Schwartz–Bruhat Φ(y) = ε·1_O(y)χ⁻¹(det y(K|I)N), the
terms of the theta kernel of v ⊗ Φ at a point n(c,z)m(q,g) are integrable, and each is an
explicit factor times `thetaOnRealData` of a finite and a real slice, or 0. -/
lemma thetaTerm_stdDatum_spec {P A π} [Nontrivial (@LocProd E _ _ P)] (h : ReadsAt A π) {Φ U v β β'}
  γ χ ε (N : Matrix (b ⊕ n) a (LocProd P)) (hΦ : Φ ∈ schwartzBruhat U) (e : Φ =
  (adaptedFrame h D).stdDatum fun y : Matrix a _ (LocProd P) ↦ ε * invOnUnits χ (y * N).det) (hv :
  IsRapidDatum v) (hβ : β' = β * upsilonU1 ^ card b) c z q g : let f := localDatum X V v Φ h;
    let p := D.radicalElt c z * D.levi (q, g); (D.HasIntegrableTerms V β' γ f p ∧ ∀ x x' (Y :
      Matrix a b (𝔸 E)), V.x⁻¹.1 * Matrix.map x toAdele = x' → x' * q.1 = scaleIdele E • Y →
      ∀ k, let y := k.2⁻¹.1.1 * Y.map snd; (delta% D.thetaTerm V β' γ f p x k) = stdAddChar E
        (toAdele 2⁻¹ * (z * (xᴴ * V.J * x).map toAdele).trace) * (((γ.spaceChar (card a)).1
        q.det : ℂ)⁻¹ * √(ideleAbs q.det) ^ card a * (ite (IsIntMatrix (Ô E) y) (vacuumFactor
        (isAdapted_homSource D V)).1 0 * thetaOnRealData W₁ V β γ (namedVector _ V (fun y' ↦
        ite (IsIntMatrix O y') (ε * invOnUnits χ (fromCols (y.map π) y' * N).det) 0) h) (x' * cᴴ *
        stdForm E s) (g, k) (realSlice D V (k⁻¹.mat * Y) v)))) ∧ ∀ t' T, ¬RepresentedBy t'
      (T.map toAdele) → (∀ x, realSlice D V x v ≠ 0 → RepresentedBy t' (xᴴ * stdForm E t * x)) →
      D.centreCoeff ((j : E) • T) (thetaIntegral X V β' γ f) p = 0 := by
  intro f p; refine (fun O ↦ ⟨O, fun _ T hT hv ↦ ?_⟩) ⟨D.hasIntegrableTerms_integrated_name _ _ _
    h.1 (h.isSchwartzBruhat hΦ) π hv fun y i ↦ ?_, fun x x' Y hx hY k ↦ ?_⟩
  convert ← D.centreCoeff_integral_eq_tsum O.1 T; simp [thetaIntegral]; convert tsum_zero with ⟨x,
    ⟨⟩⟩
  convert integral_zero .. with h; obtain ⟨q, ⟨⟩⟩ := MulAction.surjective (scaleIdele E) q
  rw [O.2 x _ _ rfl (Matrix.mul_smul ..), hT.imp_symm fun o u ↦ (hv _ o u).imp' (· * atRealPlace
    q⁻¹.1 u) fun y e ↦ .trans ?_ congr($(gram_inv_of_gram_eq rfl).map (evalInf u))]; simp; swap
  rw [Matrix.map_mul, Matrix.map_mul, gram_mul, e, gram_mul, G.mat_preserves_stdForm, gram_mul,
    gram_at_point_eq_map]; rfl
  simp [e, IntegralFrame.stdDatum, invOnUnits, χ.apply_eq_zero_iff, -mul_fromCols] at i
  erw [← fromCols_map, ← (?_ : X.coordMatrix p (D.k.fromCols D.i) * fromBlocks q _ 0 _ =
    D.kAdelic.fromCols _), Matrix.map_mul] at i
  exact ⟨_, by simpa [← Matrix.mul_assoc] using
                 congr($(mul_nonsing_inv _ i.2.2.choose_spec.2.2.2)ᵀ)⟩
  erw [Matrix.mul_assoc, G.mat, map_inv, coe_units_inv, inv_mul_eq_iff_eq_mul_of_invertible]
  simp [p, G.ofMat, radicalElt, Splitting.levi, ↓mul_fromCols]
  simp [kAdelic, iAdelic, Space.ratMap]; ac_rfl
  rw [hβ, ← one_mul k, ← mk_mul_mk, ← rep_apply_apply, sourceTerm_radicalElt, gram_at_point_eq_map,
    hx, sourceTerm_levi, k⁻¹.mat.mul_assoc, hY,
    Matrix.mul_smul, h.sourceTerm_localDatum D V hΦ _ _ (imp_intro congr($e ·))]
  simp_rw [one_mul, map_smul, Matrix.map_mul]; rfl

/-- For the target V′ ⊕ W₁ and product data, the theta term at the map (c; 0) is the term for V′ at
c times the theta kernel of (W₁, W₁). -/
lemma thetaOnRealData_boxProd_eq_mul {E n b} {s t'} [Field E] [CMType E] [WeilData E] [Fintype n]
  [Fintype b] {W₁ : Space E n s} (V' : Space E b t') α β f F c g u φ v l : thetaOnRealData W₁
  (V'.sum W₁) α (α * β) (Space.boxProd homSigns_sum_target f F) (.fromRows c 0) (g, .sum (u, l))
  (realBoxProd (realSigns_comp_split homSigns_sum_target) φ v) =
  thetaOnRealData W₁ V' α β f c (g, u) φ * pairTheta W₁ W₁ α α (integrated _ v F) (g, l) := by
  dsimp [thetaOnRealData]; erw [← boxProd_integrated, mul_comm, pairWeil_boxProd_target,
    rho_boxProd, theta_boxProd_target, Heisenberg.Rep.rho_zero_apply] <;> bound

/-- Equal rank: if X has even rank and an adapted splitting along an isotropic line, and v is rapid,
the theta integral for (X, X) with a tame character and finite datum χ⁻¹∘det is constant in g. -/
lemma thetaLarge_eq_apply_one_of_even_rank [IsBaseAdapted D₁] {v} (hn : 2 ∣ card m) (hv :
  IsRapidDatum v) g :
  thetaLarge X X 𝔠 v (stdColDatum 𝔠.χ 1) g = thetaLarge X X 𝔠 v (stdColDatum 𝔠.χ 1) 1 := by
  obtain ⟨⟨_, _, _, _, L⟩, _, _, R, H⟩ := exists_constant_term_thetaLarge D₁ D₁ (.emptySum Empty _)
    (.emptySum ..) (by grind [D₁.card_eq]) μ,
    exists_isEquivariantLift X X (stdSpace E Empty) 𝔠 (.emptySum ..) hn hv isRapidDatum_vacVector 0
  obtain ⟨O,
    e⟩ := by simpa using H (.of_discrete _) (isPartner_stdRowDatum_stdColDatum (s := 0) _ nofun)
  erw [← e, (R.isAutFunction O).apply_eq_apply_one D₁ 𝔠.nonempty (by convert (R.law_on
    O · · |>.2) <;> simp [← ext_iff, MulChar.inv_apply_eq_inv']) (R.law_off _ O) fun N ↦
    ⟨_, fun t g ↦ by simpa [← e, N,
    (by ext <;> simp : .scalar _ t.det = t)] using (L 𝔠).choose_spec.2.2 v hv 0 nofun t.det g⟩]

/-- The real number |λ(v)|²/Π(rk V/2), with λ(v) the value at 1 of the theta integral `thetaLarge`
for (V, V), real datum v, finite datum χ⁻¹∘det, and Π = `lValueProdInt`. -/
noncomputable def equalRankThetaRatio v := ‖thetaLarge V V 𝔠 v (stdColDatum 𝔠.χ 1) 1‖ ^ 2 /
  lValueProdInt 𝔠 (card a / 2)

/-- v, y are rapid, and for some real C each tame character 𝔠 of weight μ has c with I(v) =
cI′(y) on standard pairs and C|c|² = Π(rk V − rk X/2)·ℓ(𝔠); I = `thetaLarge`, I′ = `thetaSmall`,
Π = `lValueProdInt`. -/
def StdExchange {t' r} (X : Space E m r) (V : Space E n s) (V' : Space E b t') μ σ v y (ℓ :
  _ → ℝ) := IsRapidDatum v ∧ IsRapidDatum y ∧ ∃ C, ∀ 𝔠 : SplitTameChar E μ, ∃ c : ℂ, C * ‖c‖ ^ 2 =
  lValueProdInt 𝔠 (card n - card m / 2) * ℓ 𝔠 ∧ ∀ z, IsIntMatrix O z →
  thetaLarge X V 𝔠 v (stdRowDatum σ 𝔠.χ z) = c • thetaSmall X V' 𝔠 y (stdColDatum 𝔠.χ z)

attribute [local simp] IsIntMatrix blockGL mem_integralBox

attribute [local simp↓] Circle.coe_ne_zero mul_eq_zero ne_eq pow_eq_zero_iff'

variable (X) {W₁} {t'} (D₁ : W₁.Splitting W Unit) (V' : Space E b t')

/-- `StdExchange` holds for X, V′ ⊕ W₁, V′ and ℓ = |l|²/Π(rk W₁/2) if the splittings are
adapted, rk W₁ is even, v, v′ are rapid, slices of v integrate over [U(W₁)] to ρ·l(𝔠) times
those of v′ up to the Levi factor (ρ ≥ 0, non-zero near 1), and a support or sign condition
holds. -/
lemma stdExchange_of_periods [IsBaseAdapted D₁] {σ' v v'} (l : _ → ℂ) (hn : 2 ∣ card n) {ρ :
  GInf E (t' ⊕ᵥ s) → ℝ} (h₀ : 0 ≤ ρ) (h₁ : ∀ᶠ h in nhds 1, ρ h ≠ 0) (hv : IsRapidDatum v) (hv' :
  IsRapidDatum v') (hc : ∀ 𝔠 : SplitTameChar E μ, let γ := rankTwist 𝔠.ν⁻¹ n; ∀ h, ∃ p,
    ∀ (B : GL b _) (z : _ˣ), (det <| atRealPlace B.1 ·) = z.1 → ∀ β f x g
    y, ∫ l, thetaOnRealData W₁ (V'.sum W₁) γ (γ * β) (boxProd homSigns_sum_target f
    (namedVector W₁ W₁ (stdColDatum 𝔠.χ 1) 𝔠.readsAt)) (fromRows x 0) (g, .sum (y, l))
    (realPairWeil (card n / 2 - μ ·) 0 (1, (G.sum p).1 * h) (realSlice D (V'.sum W₁) (G.mat ((G.sum
    p).1 * h, 1)⁻¹ * fromRows (m₂ := n) B.1 0) v)) ∂W₁.quotMeasure = ρ h * l 𝔠 / (𝔠.ν.baseChange.1
    (z.map (.inl ..)) * √(ideleAbs (z.map (.inl ..))) ^ card n) * thetaOnRealData W₁ V' γ β f x (g,
    y) (realSlice D V' B v')) (hz : (∀ x, realSlice D (V'.sum W₁) x v ≠ 0 → RepresentedBy t'
  (xᴴ * stdForm E (t' ⊕ᵥ s) * x)) ∨ t' = -1 ∧ ∃ i, s i = 1 ∧ 2 * negCount s ≤ card n) :
  StdExchange X (V'.sum W₁) V' μ σ' v v' fun 𝔠 ↦ ‖l 𝔠‖ ^ 2 / lValueProdInt 𝔠 (card n / 2) := by
  obtain ⟨R, hR, H⟩ :=
    exists_integral_stages_eq_mul W₁.Γ volume volume volume _ G.isClosedEmbedding_sum (fun
    g ↦ ite (∃ l, U.blockSumOne l * g.2 ∈ Kf ..) (ρ g.1) 0) (by bound) ((h₁.prod_nhds
    (isOpen_Kf.mem_nhds (one_mem _))).mono fun _ ⟨_, _⟩ ↦ by rwa [ite_eq_left ⟨1, by simpa⟩])
  let a := (scaleIdele E • V'.x).det
  let κ : ℂ := vacuumFactor (isAdapted_homSource D (V'.sum W₁)) / vacuumFactor
    (isAdapted_homSource D V') * √(ideleAbs a) ^ card n
  use hv, hv', ‖R * κ‖⁻¹ ^ 2, fun 𝔠 ↦ ?_
  obtain ⟨r, ⟨_, N⟩, ε, _, P⟩ := 𝔠.readsAt, hn,
    (adaptedFrame 𝔠.readsAt D).exists_stdRowDatum_eq_stdDatum (χ := 𝔠.χ) σ'
  obtain ⟨r', L, _, _, h, K⟩ := r.star, (adaptedFrame r D).blocks_spec.1, exists_isEquivariantLift X
    (V'.sum W₁) V' 𝔠 σ' (D.card_eq ▸ by omega) hv hv' (R * (κ * ε * 𝔠.ν.baseChange.1 a * l 𝔠))
  obtain ⟨S', S, e⟩ := (stdColDatum_mem_schwartzBruhat 𝔠.χ L).transpose_mem_schwartzBruhat,
    K (stdColDatum_mem_schwartzBruhat _ L).1 (isPartner_stdRowDatum_stdColDatum _ L)
  refine ⟨_, by simp [*, D.card_eq, field]; clear * -; grind [lValueProdInt_pos], fun _ i ↦
    sub_eq_zero.1 ((K (stdColDatum_mem_schwartzBruhat _ i).1 (isPartner_stdRowDatum_stdColDatum _
    i)).2 ▸ h.apply_stdColDatum_eq_zero D D₁ V' (fun _ c z q g t ↦ .trans (by
    simpa [e] using! (centreCoeff_sub
      (r.isTargetBounded hv (stdRowDatum_mem ..)).isAutFunction_thetaIntegral (r'.isTargetBounded
      hv' S').isAutFunction_thetaIntegral _ 1).2 ..) (sub_eq_zero.2 ?_)) S σ' i)⟩
  obtain ⟨⟨⟨i, O⟩, Z⟩, ⟨⟨i', O'⟩, Z'⟩, ⟨Y, k, hk, ⟨⟩, u, ⟨⟩⟩ | ⟨d, T⟩⟩ := thetaTerm_stdDatum_spec _
    D (V'.sum W₁) r _ _ ε 1 (stdRowDatum_mem ..) (by simpa) hv (rankTwist_eq_mul_of_splitting D) c z
    q g, thetaTerm_stdDatum_spec _ D V' r' _ _ 1 (fromRows 1 0) S' (funext fun y ↦ if_congr
    forall_comm (by rw [← det_transpose]; simp [adaptedFrame, lCoord, stdForm]; congr with; simp;
                    rfl) rfl) hv' (rankTwist_eq_mul_of_splitting D) c z q g, t
  specialize O (fromRows 1 0) (fromRows V'.x.2 0) (fromRows Y 0) (by simp [sum]) (by simp)
  obtain ⟨⟨v, I, H₂⟩, -, -, J⟩ := D.centreCoeff_eq_integral_stabilizer i (x₀ :=
    fromRows 1 0) (by simp) (S := W₁.Γ.map (G.sum.comp (.inr ..))) fun _ ↦
    .symm ((exists_congr fun γ ↦ and_congr_left' (.trans (by simp [entrywise]) (U.mem_range_sum rfl
    (g := γ).2 V'.isUnit_J).symm)).trans (by simp [Γ, sum_ratEmbed, -Subtype.exists])),
    D.centreCoeff_eq_integral_stabilizer i' (x₀ := 1) (by simp) (S := ⊥) (by simp [eq_comm])
  simp only [mul_one, conjTranspose_one, one_mul, quotMeasure_bot, Splitting.thetaTerm] at *
  erw [J, mul_assoc R, ← H _ (by fun_prop) v I _ fun ⟨h, l⟩ ↦ ?_, ← H₂]; simp; rfl
  split_ifs with hl
  obtain ⟨⟨⟨p, q⟩, hc⟩, ⟨l, m⟩, hl⟩ := hc 𝔠 h, hl; use ((p.1, l), q.1, m)
  simp_rw [← integral_const_mul]; congr with y
  let B := y⁻¹.toUnitary * Y
  let x := y.2⁻¹ * Y.map (.snd ..)
  conv_lhs => enter [2, l']; rw [show (_, _ * _) = ((_ : G ..), G.sum (y, l') * (_, 1)) * (1, 1, _)
    by simp [mul_assoc]; trivial, ← rep_apply_apply, pairWeil_stdRowDatum_eq_self σ' L ‹_›,
    O, show _ * Matrix.map _ _ =
    fromRows x 0 by simp [G.sum, U.sum, x], (by simp : IsIntMatrix .. ↔ IsIntMatrix (Ô E) x.1)]
  simp_rw [O' 1 _ Y rfl (by simp), show _ * Y.1.map snd = x by rfl, integral_const_mul]
  split_ifs with i
  have o : x.det ∈ _ := coe_idelesUnitOff_empty.ge ⟨i.det_mem, ((mul_mem_cancel_right hk).1
    (mem_Kf (g :=
    ⟨x * k, by simp [x, mul_assoc, mul_mem, u]⟩).2 (i.mul hk.isIntMatrix))).isIntMatrix_inv.det_mem⟩
  rw [(_ : namedVector .. = (ε * invOnUnits 𝔠.χ (evalPlaces _ x.det)) • _), (_ : namedVector .. =
    invOnUnits 𝔠.χ (evalPlaces _ (star x.det)) • _), rankTwist_eq_mul_of_splitting D]
  conv in (thetaOnRealData ..) _ => rw [thetaOnRealData, ← mul_one g, ← mk_mul_mk]; simp [↓map_mul,
    ← map_inv, pairWeil_integrated_right, -θ_apply]
  erw [integral_const_mul, hc B (B.det.map (.fst ..)) (funext (evalInf · |>.map_det _)).symm,
    ← mul_inv_eq_of_eq_mul (_ : B.det = .map _ _ * finIdeleIncl x.det)]
  simp [thetaOnRealData, HeckeChar.finPart, ↓← eq_of_div_eq_one (𝔠.invOnUnits_mul_div_star o),
    rankTwist, pairWeil, AutChar.spaceChar, (congr(𝔠.ν.1 ⟨_ *
    $(star_star _), _⟩) : 𝔠.ν.baseChange.1 (Unitary.toUnits _) = 𝔠.ν.1 (_ * _)), (Units.ext rfl :
    y.toUnitary.1.det = Unitary.toUnits y.det), ideleAbs_eq_one_of_mem_unitary, κ, N, B, G.mat,
    (ideleAbs_eq_prod_of_v_eq_one (mem_idelesUnitOff.1 o · id) : ideleAbs (finIdeleIncl x.det) = _)]
  field (disch := simp)
  ext : 2 <;> simp; exact ((RingHom.snd ..).map_det B.1).trans congr(det $Matrix.map_mul)
  on_goal 3 => rw [boxProd_name _ r.1 (Ψ := boxIndicator _ 𝔠.S) (hΨ' :=
    r.isSchwartzBruhat (stdColDatum_mem_schwartzBruhat _ .one)) rfl]
  rw [name_boxIndicator r.1, projOn_vacElem, ← projOn_vacElem, ← name_boxIndicator r'.1]
  iterate 2 rw [smul_name, namedVector]; congr with; swap
  simp [r'.mem_iff, -RingHom.coe_comp]
  erw [← RingHom.map_det]; rfl
  simp [← r.mem_iff, stdColDatum, ← ite_and, mul_assoc]
  erw [← fromBlocks_toBlocks (fromCols _ _), det_fromBlocks_zero₂₁', ← (evalPlaces _).map_det x.1]
  exact if_ctx_congr and_comm (congrArg _ <| invOnUnits_mul (evalPlaces_mem_O _ i.det_mem) <|
    IsIntMatrix.det_mem ·.1) (by simp)
  ring
  use 1; conv_lhs => enter [2, y, 2, _]; rw [O, ite_eq_right fun i ↦ hl
    (let w := ((y.2⁻¹ * ⟨_, u⟩ :), (1 : U 1))
    (witt_Ohat_of_orthonormal (congr($((l⁻¹ * U.blockSumOne w).2).toBlocks₁₁).trans
      (by simp [← fromBlocks_one'])) (by simp) (by simpa [w, G.sum, U.sum,
      ← fromCols_fromRows_eq_fromBlocks] using i.mul hk.isIntMatrix) (by
    simp [ite_mem])).elim fun k ⟨_, e⟩ ↦ ((U.mem_range_sum fromBlocks_one' (g := k * _).2
    isUnit_one).2 e).elim fun m f ↦ ⟨(1, m) / w, by simpa [↓map_div, f, ← mul_assoc]⟩)]
  simp [↓zero_mul]
  erw [hz.elim (Z _ _ T) fun ⟨e, _, a, l⟩ ↦ centreCoeff_eq_zero_of_not_negative (.inr _)
    (by simp [N]; linarith [negCount_neg_add s, 𝔠.weight_pos ·]) a (by simp [e])
    (rankTwist_eq_mul_of_splitting D) d (e ▸ T) i, Z' _ _ T fun _ _ ↦ (⟨_, gram_map_real _ ·⟩),
    mul_zero]

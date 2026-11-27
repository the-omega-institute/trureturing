/- GID: D5/S3/Zeros/GRH/New/Exchange/AlgebraicPartDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/AlgebraicPartDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.AlgebraicPartDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/AlgebraicPartDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Forms.AuxiliaryPair
import D5.S3.Zeros.GRH.New.Trace.GoodIdempotent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Weights, Harish-Chandra parameters and ranks of the spaces fit the lift hypotheses. Theta
lift of the trivial character of U(1); the splitting carries the Hecke character. Names for the lift
of a pair's character, its denominator and normalised norm. -/
seal Finset.univ Finset.sum Finset.prod

open Finset PolyRep Matrix MvPolynomial Space

attribute [-grind] Data.m_even

attribute [local grind] Data.auxPair Data.signsW mem_attachFin Fintype.card_subtype
  units_ne_neg_self

variable {P} (D : Data P) (j : D.LiftIndex) {E n : Type} [Field E] [CMType E] [Fintype n]

lemma Data.card_Y_le {j} (hj : j ≤ D.m) :
    Fintype.card (D.Y j) ≤ D.n D.m := by simp [n]; grw [hj]; grind

/-- At each infinite place the doubled parameter on Y_m has distinct entries, each an entry of
twice the Harish-Chandra parameter of the weight (`Data.columnsY`, `Data.lastEntry` m). -/
lemma Data.isHCParam_Y : IsHCParam D.columnsY (D.lastEntry D.m)
  (D.paramY D.m) := have ⟨k, _⟩ := Nat.exists_eq_add_one.2 D.k_pos
  have hL {T} x := ((@finProdFinEquiv D.m T x).natAdd k).2
  by refine fun τ ↦ ⟨(hasGap_gridParam ..).1,
    (?_ : _ = Fintype.card (D.Y _)) ▸ ((@gridBlockEquiv _ _ D false 0).forall_congr' fun _ ↦
    exists_congr fun _ ↦ and_congr_right (hcParameter_eq_of_steps τ (fun p ↦ 2 * (D.rowParameter
    τ (p ⊓ k) - p.sub k) - (D.h - D.t.succ) * (2 * ((p - k) / D.t.succ) + (p - k) % D.t.succ ⊓ 1 :))
    (fun p ↦ dite (p < k) ?_ ?_) (hL (⟨_, D.m_eq_two_mul_varrho_add_two.ge⟩, ⊤)) ?_
    _ · |>.congr_right)).mpr fun | .inl (.inl ⟨y, _⟩) => if _ : y ≤
    k then ⟨y, ?_⟩ else ⟨_, hL (⟨y - k, ?_⟩, 0), ?_⟩ | .inr (a, b) => ⟨_, hL (a,
    b.succ), ?_⟩⟩ <;> simp_intro .. [*, tsub_eq_zero_of_le, le_of_lt, columnsY, κ, keptColumns,
    Nat.succ_div, Nat.succ_sub, rowParameter, reducedHalfGap, w, hcParameter, lastEntry, n,
    Nat.add_mul_div_left, paramY, m_eq_two_mul_varrho_add_two, gridParam, Nat.dvd_iff_mod_eq_zero,
    Nat.mod_eq_of_lt, Nat.div_eq_of_lt] <;> grind [sum_eq_zero, diagramWeight_apply]

lemma Data.card_V : Fintype.card (D.RowIndex ⊕ Fin D.t) = D.r + D.t := by simp [↓card_rowIndex]

lemma Data.card_filter_basisNumber {q} [DecidablePred q] a b (hq : ∀ x, q x ↔
  ↑(D.basisNumber x) ∈ Ico a b) (h : b ≤ D.r) :
  #{x | q x} = b - a := by rw [← Nat.card_Ico, card_equiv D.basisNumber _, card_attachFin] <;> grind

lemma Data.varsigma_strictAnti τ :
  StrictAnti (D.rowParameter τ) := by grind [strictAnti_nat_of_succ_lt, rowParameter]

lemma Data.paramW_lt_iff τ {a b} : D.paramW τ a < D.paramW τ b ↔
  D.basisNumber b < D.basisNumber a := by simp [paramW, (varsigma_strictAnti ..).lt_iff_gt]

/-- For 1 ≤ j ≤ m, exactly m − j basis indices of W_j have sign −1. -/
lemma Data.card_neg_signsW : negCount (D.signsW j) =
  D.m - j := by grind [negCount, D.card_filter_basisNumber (D.posRank j) D.r]

/-- For 1 ≤ j ≤ m the real types match: the auxiliary pair (W_j, V_j) satisfies `AuxPair.FitsParams`
for the doubled parameter `Data.paramW` on W_j. -/
lemma Data.fitsParams_auxPair ϑ (j : D.LiftIndex) : (D.auxPair ϑ j).FitsParams D.paramW := by
  have := D.card_V; let a := D.posRank j; let u p := ite (p < a) 0 D.t
  have L τ x : (D.auxPair ϑ j).paramV τ x = _ := hcParameter_eq_of_steps τ (fun p ↦
    D.r + 2 * ite (u p ≤ p - a) (D.rowParameter τ (p - u p) + D.w j τ - a) (D.t / 2 - p))
    (fun p ↦ by clear x; grind [D.varsigma_strictAnti τ (p - u p).lt_add_one]) (q :=
    a) (by grind) (by rw [hcParameter, diagramWeight_apply, sum_subset_zero_on_sdiff,
    sum_Ico_reflect ((D.auxPair ϑ j).colsMinus τ) 1 this.le.step] <;> grind) _ (by lia)
  refine ⟨fun τ ↦ ⟨(AuxPair.isHCParam_paramV _).hasGap .., (hasGap_paramW ..).neg.mono
    (this ▸ D.le_of_hasLogBound), ?_, fun c ↦ .inl ⟨(Fintype.equivFin _).symm ⟨D.basisNumber c + u
    (D.basisNumber c), ?_⟩, ?_⟩⟩, by intros; dsimp [auxPair, signsW]; split <;> simp [paramW_lt_iff,
    tsub_tsub] <;> rw [card_filter_basisNumber] <;>
    first | rw [tsub_zero] | grind, ?_, ?_⟩ <;> simp [↓L, auxPair, ↓card_rowIndex, pairSign,
    IsMatchedPair, reindex_equiv D.basisNumber.symm, Fin.exists_iff, paramW, signsW,
    apply_ite] <;> grind [D.card_filter_basisNumber 0 a, card_neg_signsW]

/-- On a standard space V, with l the parameter of the weight (κ,e), the class sum inner product
of two algebraic forms is the index of the level in K₀, times the cardinality of `WeylIndex` n
κ, times the Petersson product of the associated functions. -/
lemma LevelPlaces.LevelForm.inner_eq_petersson {s} (V : Space E n s) {κ e l} [i : V.IsStd] (h :
  IsHCParam κ e l) {S : LevelPlaces E} {H χ}
  (φ φ' : S.LevelForm H χ κ e) : inner ℂ φ φ' = (levelOf _ H).relIndex (Kf E n) * Fintype.card
  (WeylIndex n κ) * V.petersson (ofAlgForm l s φ.1) (ofAlgForm l s φ'.1) := by
  erw [petersson,
    integral_mul_eq_classIntegral h (Kf ..) (isForm_ofAlgForm h _).conj.1 _ (star_ofAlgForm i.1)]
  simp [mul_assoc, -Fintype.card_pi, gramForm_apply, ← toLinearMap₂'_apply']; rfl'

/-- For a non-empty index set n, an embedding of the one-point set into n, chosen once: a choice
of one basis index. -/
noncomputable def chosenIndexEmb [h : Nonempty n] : Unit ↪ n := (h.map .punit).some

/-- Data for a lift from U(1) to the definite U(n), |n| > 1: chosen places, jet degrees dg =
`jetDeg`, and
a character of weight −(dg + ⌊|n|/2⌋) unramified off these places. -/
structure LValueData (E n : Type) [Field E] [CMType E] [Fintype n] extends LevelPlaces E where
  jetDeg : _ → ℕ
  μ : AutChar E
  (ψ) hasWeight : μ.HasWeight (fun τ ↦ -(jetDeg τ + Fintype.card n / 2 : ℕ)) ψ
  one_lt_card : 1 < Fintype.card n
  unramified : ∀ w ∉ toLevelPlaces.places, ψ w = 1

unseal Finset.univ in
/-- The data `AuxPair` attached to X: W is the definite line I_1, and the weight has one row of
length dg τ at each τ. -/
noncomputable abbrev LValueData.auxPair (X : LValueData E n) := AuxPair.mk _ 1 (stdSpace ..)
    (@chosenIndexEmb n (Fintype.card_pos_iff.1 X.one_lt_card.le)) 0 (Pi.single 1 <|
  X.jetDeg ·) 0 _ _ _ X.hasWeight X.unramified X.one_lt_card

variable [WeilData E] (X : LValueData E n) (x : GInf E X.auxPair.signs) {D : Data P} (p :
  @Data.Pair P D)

/-- The jets of the one-row weight of X, derivatives scaled by c, of the datum f moved by the
finite points (g, h) of U(1) × U(n). -/
noncomputable def LValueData.kernelValue c f g h :=
  schurJet X.auxPair.κ (jetSeries _ c (X.auxPair.pairThetaKernel.ω ((1, g), 1, h) f)) *ᵥ 1

attribute [local simp] Kernel.ω_ω LValueData.kernelValue AuxPair.κ detPow mixedWeight weylRep
  rep_apply_apply

omit [WeilData E] in
lemma LValueData.isLiftWeight : IsLiftWeight Unit n X.auxPair.κ
  (-X.jetDeg ·) 0 := by simp_all [IsLiftWeight, FitsRanks, X.one_lt_card, le_of_lt, ne_of_gt]; rfl

instance LValueData.a_hasWeight : X.auxPair.a.HasWeight X.auxPair.detExp 1 :=
  (WeilData.hasWeight_upsilonU1_pow _).of_weight_eq (by simp [funext_iff])

instance LValueData.b_hasWeight : X.auxPair.b.HasWeight (-X.jetDeg ·) X.ψ :=
  X.hasWeight.hasWeight_rankTwist.of_weight_eq (by simp)

/-- The theta kernel `thetaKernel` from I_1 to I_n for the weight and characters of the
auxiliary pair of X, with scale 1 and level all of U(1)(𝔸_f). -/
noncomputable abbrev LValueData.liftKernel :=
  thetaKernel X.isLiftWeight 1 X.a_hasWeight X.b_hasWeight ⊤

omit [WeilData E] in
@[simp] lemma LValueData.conjWeylRep_eq_one :
  conjWeylRep X.auxPair.κ 0 x = 1 := by simp_all [conjWeylRep, schur_eq_one]

/-- For fixed g in U(1), the function h ↦ `LValueData.kernelValue` of the datum Υ at (g, h), as an
algebraic form on V = I_n; Υ = `AuxPair.auxDatum`. -/
noncomputable def LValueData.kernelForm (g : Gf E Unit) : X.auxPair.FormV :=
  have t k := by ext1; simpa using! congr(X.kernelValue 1 $(X.auxPair.pairWeil_upsilon 1 ⟨k, _⟩ _
                   (by aesop)) g _);
  ⟨⟨X.kernelValue 1 X.auxPair.auxDatum g, mem_smoothFunctions_of_eigen _ isOpen_levelOf t,
    fun γ h ↦ by simpa using! X.liftKernel.3 1 γ (X.liftKernel.ω (g, h) X.auxPair.auxDatum) 1⟩,
    (Subtype.ext <| t ·)⟩

/-- The principal level on the finite adelic U(1) at the chosen places indexed by M: integral
elements with reduction 1 at each of these places. -/
noncomputable abbrev LValueData.chosenLevel := levelOf (n := Unit) X.chosenPlace ⊥

/-- The lift Ξ of the trivial character: the class sum of `LValueData.kernelForm` over U(1) at the
principal level at the chosen places indexed by M. -/
noncomputable def LValueData.trivialLift := stdClassSum X.chosenLevel X.kernelForm

/-- The kernel `LValueData.kernelForm` of X, as a function of the finite point g of U(I₁), is
invariant under rational points on the left and, on the right, under elements of K₀ that reduce to 1
at the places of M. -/
lemma LValueData.kernelForm_invariant : stdRatPoints.FixesLeft X.kernelForm ∧ X.chosenLevel ≤
  rightStab X.kernelForm := by
  constructor <;> rintro _ ⟨k, e⟩ g <;> simp only [kernelForm] <;> congr 2 with h : 1
  simpa [e, weightRep] using! X.liftKernel.3 k 1 (X.liftKernel.ω (g, h) X.auxPair.auxDatum) 1
  have := congr(X.kernelValue 1 $(X.auxPair.pairWeil_upsilon k 1 1 (by simp_all)) g h); aesop

lemma LValueData.trivialLift_eq_stdClassSum_translate g : X.trivialLift = stdClassSum X.chosenLevel
  (X.kernelForm <| · * g) := by rw [stdClassSum, classSum_eq_relIndex_smul le_rfl g _
  fun _ ↦ X.kernelForm_invariant.elim apply_doubleCoset_out _] <;> simp [trivialLift,
  SetLike.ext_iff, mul_comm' g]

omit [WeilData E] in
/-- The polynomial `toPoly` of a coordinate vector η is obtained from the polynomial that
the auxiliary pair data of X attach to η by renaming each variable c to the variable with row index
(c.1, c.2.1) and column 0. -/
lemma LValueData.toPoly_eq_rename_harmonicPoly η : toPoly _ _ η =
  rename (fun c ↦ (⟨c.1, c.2.1⟩, 0)) (X.auxPair.harmonicPoly η) :=
  congr($(ext_schur_weylEval (rowPos _) (L' := (rename _).toLinearMap ∘ₗ _) fun g ↦ by
  have := (mixedCartan n X.auxPair.colsPlus 0).intertwines g
  simp_all [AuxPair.harmonicPoly, -mulVec_mulVec, MixedCartanEmbedding.top, letterPoly,
    weylKernel, ↓rowSubst_highestPoly, rowSubst, fockLetters, X.one_lt_card]) η)

omit [WeilData E] in
lemma LValueData.harmonicPoly_eq_schurCoeffPoly η : X.auxPair.harmonicPoly η =
  schurCoeffPoly (η ᵥ* weylGramOver) 1 := funext fun z ↦ by
  simpa +contextual [eval_schurCoeffPoly X.isLiftWeight, eval_rename, show minor (h := 1) ℂ _ =
    _ from det_unique _, weylEval, entrywise, nablaBasis_eq_one, weylGram_isSymm.apply,
    ← mulVec_transpose] using! (schur_mulVec_weylEval X.isLiftWeight.1 (z ⟨·, ·, ·⟩) 1 ▸
    X.toPoly_eq_rename_harmonicPoly η ▸ eval_toPoly .. :).trans (dotProduct_comm ..)

lemma LValueData.theta_pairWeil_fockDatum η y g h :
  θ _ (X.auxPair.pairThetaKernel.ω ((x, g), y, h) (X.auxPair.fockDatum η)) = gramForm (star η)
  (conjWeylRep _ X.auxPair.detExp y⁻¹ (X.kernelForm g h)) := by
  erw [pairWeil_integrated_all, gramForm_apply, mulVec_mulVec, dotProduct_mulVec,
    dotProduct_schurJet_mulVec]
  simp [harmonicPoly_eq_schurCoeffPoly, realPairWeil_schurCoeffPoly X.isLiftWeight]

/-- If all jet degrees vanish, every coordinate of `LValueData.kernelForm` at finite points g, h is
the theta kernel `modKernel` with characters 1 and b, polynomial 1 and the datum
`AuxPair.resDetDatum` modulo M²Q. -/
lemma LValueData.kernelForm_of_jetDeg_eq_zero g h (k : X.jetDeg = 0) i : X.kernelForm g h i =
  modKernel (stdSpace ..) (stdSpace ..) 1 X.auxPair.b
  (X.levelModulus 2) (X.auxPair.resDetDatum fun i ↦ ·.map (levelResidueAt i)) 1 (1, g) (1, h) := by
  simp [kernelForm, mulVec_apply_eq_sum]
  erw [← LinearMap.sum_apply, ← map_sum, jet_jetSeries_eq_theta,
    ← pairWeil_integrated_fin]; congr; simp [AuxPair.a]
  apply C_injective; simpa [nablaBasis_eq_one, schurDetExp, k, smul_eq_C_mul] using
    sum_schur_smul_nablaBasis X.isLiftWeight.1 ..

lemma LValueData.theta_eq_inner_kernelForm y g' : X.auxPair.θ y (x, g') =
  inner ℂ (X.kernelForm g') y := by simp [inner, LevelPlaces.LevelForm.innerAt_eq_stdClassSum,
  AuxPair.θ, AuxPair.conjKernel, pairTheta, X.theta_pairWeil_fockDatum, conj_gramForm]

/-- Adjointness: for a form Ξ' and a finite point z of U(I₁), the inner product of
`LValueData.trivialLift` with Ξ' is the class sum over U(I₁), at principal level at the places of M,
of u ↦ (θΞ')(1, uz), θ the descent `AuxPair.θ`. -/
lemma LValueData.inner_trivialLift g y : inner ℂ X.trivialLift y = stdClassSum X.chosenLevel
  (X.auxPair.θ y ⟨1, · * g⟩) := by simpa [theta_eq_inner_kernelForm,
  trivialLift_eq_stdClassSum_translate _ g] using map_classSum (innerSLFlip ℂ y) _

omit [WeilData E] in
/-- The hook constant of the weight κ of the auxiliary pair data of X, in rank |n| at every place,
equals the product over infinite places τ of (dg τ)!. -/
lemma LValueData.hookNumber_eq_prod_factorial : hookNumber X.auxPair.κ (rankAt n) = ∏ τ,
  (X.jetDeg τ).factorial := by rw [hookNumber, (?_ : highestPoly .. =
  ∏ y ∈ .image (⟨⟨·, 0, X.one_lt_card.le⟩, 0⟩) ⊤, .X y ^ X.jetDeg y.1.1), prod_X_pow,
  fockPairing_monomial, Finsupp.prod_indicator_index] <;> simp [highestPoly, tableauPoly, minor,
  @Fin.val_inj _ _ ⟨1, X.one_lt_card⟩, Function.Injective]; rfl

namespace Data.Pair

/-- The index set n has 2z elements and z ≥ 2, for the pair p = (ν, z). -/
abbrev HasLiftRank {D} (p : @Pair P D) n [Fintype.{0} n] := Fintype.card n = 2 * p.z ∧ 2 ≤ p.z

/-- For the pair p = (ν, z) of weight −c: c(τ) = z at every infinite place τ, the index set n
has 2z elements, and z ≥ 2. -/
abbrev IsFlat n [Fintype n] := (∀ τ, p.c τ = p.z) ∧ p.HasLiftRank n

/-- The natural number g^(4fz) · (gd)^deg, with deg = Σ_τ (c_τ − z); it clears the denominators
of the lift Ξ. -/
noncomputable def denomBound := D.gProd ^ (2 * D.f * (2 * p.z)) * (D.gProd * P.d) ^ ∑ τ,
  (p.c τ - p.z)

variable {p} {n : Type} [Fintype n] (H : p.HasLiftRank n) (ϑ)

/-- The data `LValueData` for the pair p = (ν, z) twisted by ϑ: the chosen places of ϑ, jet
degrees c_τ − z and character νϑ. -/
noncomputable abbrev lValueData := (⟨D.levelPlaces ϑ, (p.c · - p.z), _,
  _, by simpa [H, le_c] using p.hasWeight.mul ϑ.hasWeight, by lia, by
    simp_all [levelPlaces, ϑ.5, ψ_eq_one, range_chosen]⟩ : LValueData _ n)

/-- The lift Ξ_ϑ of the trivial character from the definite U(1) to the definite U(2z) for νϑ, at
scale (π̄·per)^{Σ_τ (c_τ − z)} (π = `Data.piG`, per = `Parameters.jetScale`), times κ₀^|n|,
κ₀ = `Parameters.vacuumScale`. -/
noncomputable def trivialLift := (P.vacuumScale D.s ^ Fintype.card n *
  (star ↑D.piG * P.jetScale D.s) ^ ∑ τ, (p.c τ - p.z)) • (lValueData H ϑ).trivialLift

/-- The normalised value Mk · den² · ‖Ξ_ϑ‖² / Nm(Q)^(|n|−1), with Q the set of places of ϑ and
Mk = `Data.chosenGroupOrder`, den = `Data.Pair.denomBound`. -/
noncomputable def intAlgPart : ℂ := ↑(D.chosenGroupOrder * p.denomBound ^ 2) * ‖trivialLift H
  ϑ‖ ^ 2 / ϑ.levelNorm ^ (Fintype.card n - 1)

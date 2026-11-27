/- GID: D5/S3/Zeros/GRH/New/Exchange/GridModuli
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/GridModuli
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.GridModuli. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/GridModuli.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.FitTwists
import D5.S3.Zeros.GRH.New.Rows.LineCoordinates
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Lifts are killed by the Hecke polynomial at smallest root; real data exist. Orders,
weights, gaps and numerical bounds for the proof's spaces. Support of the proof's moduli and
tameness of its characters. -/

variable {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] {O : AuxPair E r n} {w}
  (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure) {P} (D : Data P) (j :
  D.LiftIndex) {c : ℕ} [NeZero c] (ϑ : D.MFoldTwist)

lemma LValueData.fitsParams_auxPair (X : LValueData E n) : X.auxPair.FitsParams 0 := by
  refine' .mk (fun w ↦ ⟨X.auxPair.isHCParam_paramV.hasGap .., .mk .., _, fun _ ↦
    .inl ((X.auxPair.isHCParam_paramV.exists_decrPosition_eq w X.one_lt_card.le).imp
    _)⟩) .. <;> simp [AuxPair.paramV, hcParameter, diagramWeight_apply, AuxPair.detExp,
    IsMatchedPair, pairSign, Function.Injective] <;> grind [X.one_lt_card]

/-- Let w be split, w and w̄ off M and Q, r = rk W. If a form y on V satisfies `AuxPair.Lifts`, so
is spherical at every such place
with Hecke eigenvalue ∏_{0≤l<n−r}(1 − q_w^l νX)·p(X), ν = `AutChar.frobValue` a r w, the Hecke
polynomial at X = `AuxPair.testValue` w kills y. -/
lemma AuxPair.heckePolyOnForms_testValue_eq_zero [WeilData E] {y z} (h : O.Lifts y z) :
  O.heckePolyOnForms hw hS (O.testValue w) y = 0 := by
  cases Nat.exists_eq_add_of_lt O.rank_lt
  simp [O.heckePolyOnForms_eq_smul _ _ (h w hw hS), testValue, rankDiff, *, Finset.prod_range_succ,
    add_assoc, field, AutChar.frobValue, HeckeChar.atUnif]

namespace Data

/-- The natural number N_* = 2ft³, where f is the number of infinite places of E and t = 5r. -/
noncomputable abbrev nStar := D.f * (2 * D.t ^ 3)

lemma nStar_bounds : 2 * D.r ≤ D.b ∧ 300 * nStar D + D.t ≤ D.h₂ ∧ 0 < nStar D :=
  ⟨D.le_of_hasLogBound, D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound⟩

variable {D}

/-- The integer-valued order on the basis of W_j, −1 − ord(c) on positive and ord(c) on negative
vectors: positive vectors first, in reversed order. -/
noncomputable def orderW c :=
  ite (D.signsW j c = 1) (-1 - (untwistedAuxPair j).ord c : ℤ) ((untwistedAuxPair j).ord c)

/-- The weight Λ = λ + ρ − 2ρ_c (`HCParam.lowestKType`) for the signs of W_j, with λ = −ς at τ,
minus the row parameter. -/
noncomputable abbrev conjHolWeight τ := (toHCParam (D.signsW j) (-D.paramW τ)).lowestKType

/-- The weight `staircaseWeight` at τ for the pair (W_j, V°), with the diagram k⁻ of
`Data.untwistedAuxPair` in the negative letters, none in the positive ones, and shift j − m/2. -/
noncomputable def kernelWeight τ := staircaseWeight D.SmallIndex (D.signsW j)
  (untwistedAuxPair j).ord (Pi.single (-1) ((untwistedAuxPair j).colsMinus τ)) (-(D.m / 2 - j))

attribute [local grind .] card_rowIndex auxPair orderW signsW rowParameter Fintype.card_fin
  Fintype.card_sum units_ne_neg_self

attribute [local simp] kernelWeight paramW_lt_iff vacuumWeight staircaseWeight

lemma rank_bounds_card_bigIndex : 6 * D.r ≤ D.n D.m ∧ 100 * D.m + 9 < D.k ∧ D.r + 1 = D.k + D.m ∧
  D.t = 5 * D.r ∧ Fintype.card D.RowIndex = D.r ∧ Fintype.card (BigIndex j) = D.r + 9 * D.m + 1 :=
  ⟨D.nat_le_of_hasLogBound, D.nat_lt_of_hasLogBound, by grind⟩

lemma two_mul_card_detIndex_add_le τ :
  (2 * (Fintype.card (DetIndex j τ) + Fintype.card (BigIndex j) + D.m) : ℕ) ≤ 5 * D.b := by
  grw [(?_ : _ + D.m ≤ D.w j τ)] <;> grind [card_detIndex_add_bigCharExp, w_le_two_mul_b]

/-- For 1 ≤ j ≤ m, the lowest K-type Λ at τ for the signs of W_j and the parameter −ς is the
weight of `Data.fNatural` (a staircase weight for V″) plus the weight `Data.kernelWeight` of the
kernel on V°. -/
@[local simp↓] lemma conjHolWeight_eq_add_kernelWeight τ : conjHolWeight j τ = staircaseWeight
  (BigIndex j) (D.signsW j) (untwistedAuxPair j).ord (Pi.single 1 ((untwistedAuxPair j).colsPlus τ))
  (-(bigCharExp j + -D.w j τ)) + kernelWeight j τ := by
  ext c; erw [conjHolWeight, eq_comm,
    (D.fitsParams_auxPair .one j).exists_isJointHarmonic.choose_spec.2.2]
  cases Int.units_eq_one_or (D.signsW j c) <;> simp [*, -Fintype.card_sum, auxPair] <;>
    rw [Finset.sum_subset (s₂ := .Ioo ((untwistedAuxPair j).ord c) (6 * D.r))] <;> grind

lemma conjHolWeight_kernelWeight_bounds τ : let s := D.signsW j; let k := conjHolWeight j τ; (∀ i,
      |↑(k i)| ≤ 5 * D.b) ∧ IsKDominant s (orderW j) k ∧ IsKDominant s (orderW j) (kernelWeight j
      τ) ∧ HasHolGap s k (300 * nStar D) ∧ HasHolGap s (kernelWeight j τ) (300 * nStar D) := by
  and_intros <;> repeat intro
  grw [← Int.cast_abs, abs_lowestKType_le (D.hasGap_paramW _ τ).neg (L := 2 * D.w (D.m + 1) τ)
    (by grind [Pi.neg_apply, paramW]), card_rowIndex]; simp; grind [nStar_bounds, w_le_two_mul_b]
  iterate 2 cases Int.units_eq_one_or (D.signsW j ‹_›) <;> simp_all
    [orderW, -tsub_le_iff_right] <;> gcongr
  all_goals simp [*, -Nat.cast_sum]; grw [← Finset.single_le_sum (f := (untwistedAuxPair
    j).colsMinus τ) (a := D.m - j)] <;> grind [-Sum, Int.ofNat_le.2 D.nStar_bounds.2.1]

variable {j}

lemma isPosFirstOrder_orderW : IsPosFirstOrder (D.signsW j) (orderW j) := by grind [IsPosFirstOrder,
  Function.Injective, D.basisNumber.injective]

lemma paramW_lt_of_orderW_lt τ a b : D.signsW j a = D.signsW j b → orderW j a < orderW j b →
  D.paramW τ a < D.paramW τ b := by simp; grind

instance instFactNeRingOfIntegersEHPowGbOfNat (c) : Fact (D.piGBar ^ c ≠ 0) := ⟨by simp⟩

/-- For c ≠ 0 and a tame character ϑ, the finite places of E dividing the modulus M^c·Q attached
to ϑ are exactly the chosen places (`Data.IsChosen`) together with the places in the set Q of
ϑ. -/
lemma places_modulus_eq_union ϑ : (D.𝔪 ϑ c).places =
  {w | D.IsChosen w} ∪ ϑ.Q := by simp [places_levelModulus, levelPlaces, range_chosen]

lemma isTameFor_of_hasWeight {ν γ ψ} (ϑ : D.Twist) (H : ν.HasWeight γ (ψ * ϑ.ψ)) (b : ∀ w, ψ w ≠ 1 ↔
  D.IsChosen w) : IsTameFor (D.𝔪 ϑ c) ν γ (Modulus.charOfTamePart _ (ψ * ϑ.ψ)) :=
  ⟨nonempty_modulus_places, _, H, by grind [places_modulus_eq_union, Pi.mul_def, Twist, TameChar,
  IsChosen, → levelNorm_mem_and_notMem_of_mem_Q], rfl⟩

/-- For 1 ≤ j ≤ m, c ≥ 1 and a twist ϑ, the character χ^j·ϑ has weight 0 and is tame
(`IsTameFor`) for the modulus (π̄₀π̄₁)^c·Q, with the character ∏_w ω_w^j ϑ_w of the
residue ring. -/
lemma isTameFor_twistedChi j (ϑ : D.Twist) :
    IsTameFor (D.𝔪 ϑ c) (twistedChi ϑ j) 0 (Modulus.charOfTamePart _ (D.liftTamePart ϑ j)) :=
  isTameFor_of_hasWeight _ (twistedChi_hasWeight ..) (omega_zpow_ne_one j (by grind))

instance instNeZeroNatB₁ : NeZero D.b₁ := .of_pos D.nat_le_of_hasLogBound

/-- The integer π̄^{b₁} of E, with π̄ = `Data.piGBar`. -/
noncomputable abbrev gridLevelGen := D.piGBar ^ D.b₁

/-- The modulus 𝔪 = 𝔟Q of the twist ϑ: the product of the chosen places above g to the power b₁,
times Q(ϑ). -/
noncomputable abbrev gridModulus := D.𝔪 ϑ D.b₁

/-- For the trivial twist, the ideal of the modulus `Data.gridModulus` is the principal ideal of O_E
generated by π̄^{b₁}, π the integer of K of norm g₀g₁. -/
lemma gridModulus_one_ideal : (gridModulus 1).ideal = .span {D.gridLevelGen} :=
  D.ideal_untwistedModulus_eq_span ▸ by rfl'

/-- The modulus of the triangle z: MQ for the twist ϑ if z is false, M^{b₁}Q for the trivial
twist if true; M, Q are the products of the chosen places over g and of the twist. -/
noncomputable abbrev triangleModulus z (ϑ : D.MFoldTwist) := D.𝔪 (cond z 1 ϑ :) (cond z D.b₁ 1)

/-- Reduction from the residue ring of `Data.gridModulus` = 𝔟Q to that of `Data.triangleModulus`,
which is MQ for z false and 𝔟 = M^{b₁} for z true, M the product of the chosen places. -/
noncomputable abbrev reduceToTriangle z := Ideal.Quotient.factor
    (z.rec (Ideal.mul_mono_left (Ideal.pow_le_pow_right NeZero.one_le)) (Ideal.mul_mono_right
    (by with_unfolding_all use Ideal.le_of_dvd (one_dvd _))) : (gridModulus ϑ).ideal ≤
  (triangleModulus z ϑ).ideal)

lemma piGBar_dvd_gridLevelGen : D.piGBar ∣ gridLevelGen := by simp [NeZero.ne]

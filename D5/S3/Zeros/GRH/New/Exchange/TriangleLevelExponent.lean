/- GID: D5/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.TriangleLevelExponent. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/TriangleLevelExponent.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.ExchangeTheorem
import D5.S3.Zeros.GRH.New.Exchange.CharacterLiftNorm
import D5.S3.Zeros.GRH.New.Rows.LineArithmetic
import D5.S3.Zeros.GRH.New.Seesaw.PairTensorData
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

Also holds known results stated on this proof's data: Critical Hecke L-values of CM fields as
squared norms of theta lifts from U(1) (known result; see Lib.SiegelWeil.RallisInner.SharpData).

Also holds known results stated on this proof's data: Integral group-ring elements interpolating
twisted Hecke L-values, with norm relations (known result; see New.Selmer.ValueFamilies).

This file: Integrality of the lift; integral group-ring element interpolating tame twists of
L-values. Normalised squared norm of a character's theta lift is constant times Hecke L-value.
Exchange constant for a twist rewritten through L-value ratios and conductor norms. Spaces and
characters of the triangle of lifts. -/

open Circle Complex Finset Fintype LValueData Parameters LevelPlaces

variable {P D} (ϑ : D.TameChar) {p : @Data.Pair P D}

/-- F(ϑ′) = Σ c_a ϑ′(u_a) for all tame ϑ′ with the modulus Q of ϑ, for finitely many points u_a
of U(1)(𝔸) and c_a integral at all l prime to Q. -/
def Data.TameChar.IsIntegralMeasure (F : D.TameChar → ℂ) :=
  ∃ (α : Type) (_ : Fintype α) (u c : α → _),
  (∀ a, c a ∈ integralAway ϑ.levelNorm) ∧ ∀ ϑ', ϑ'.Q = ϑ.Q → F ϑ' = ∑ a, c a * ϑ'.toAutChar.1 (u a)

/-- If the function F of tame characters is an integral measure for ϑ
(`Data.TameChar.IsIntegralMeasure`), then so is ψ ↦ |F(ψ)|². -/
lemma Data.TameChar.IsIntegralMeasure.norm_sq {F} : ϑ.IsIntegralMeasure F →
  ϑ.IsIntegralMeasure (‖F ·‖ ^ 2) := fun ⟨α, _, u, c, a, b⟩ ↦ ⟨_,
  inferInstance, fun (x, y) ↦ u x * (u y)⁻¹, _, fun x ↦ mul_mem (a x.1) fun l ↦ (a x.2 l · <| ·.comp
  _), fun _ e ↦ by simp [*, ← mul_conj', univ.sum_mul_sum, sum_prod_type, ↓coe_inv_eq_conj]; ac_rfl⟩

/-- If F is an integral measure (`Data.TameChar.IsIntegralMeasure`) at the trivial tame character 1,
then
|ι F(1)| ≤ 1 for every prime l and every isomorphism ι from ℂ to the algebraic closure of
ℚ_l. -/
lemma Data.TameChar.IsIntegralMeasure.norm_apply_one_le {F l} [Fact l.Prime]
  (ι : ℂ ≃+* PadicAlgCl l) : (@one P D).IsIntegralMeasure F → ‖ι (F one)‖ ≤ 1 := fun ⟨_, _, _, _, a,
  b⟩ ↦ by simpa [b, twist_one_spec, ← map_sum] using!
    ((@embValRing l _ ⟨complexToCp ι⟩).sum_mem fun _ _ ↦
  a _ l (by simp [levelNorm, twist_one_spec]) (complexToCp ι))

namespace Data.Pair

instance {l} [D.HasLogUpper D.t l] : D.HasLogUpper p.z l := D.hasLogUpper_of_le p.7.2

variable {n} [Fintype n] (H : p.HasLiftRank n) (ϑ : D.TameChar) (s : ℤˣ)

/-- κ₀^|n| times the indicator modulo MQ (`AuxPair.levelIndicator`) of integral vectors congruent to
the chosen basis vector e_ι at M and with ι-th coordinate 1 at Q, on the vacuum; κ₀ =
`Parameters.vacuumScale`. -/
noncomputable def pointDatum := P.vacuumScale D.s ^ card (n × Unit) • vacuumDatum (stdSpace ..)
  (stdSpace ..) _ (lValueData H ϑ).auxPair.levelIndicator

/-- The jets `LValueData.kernelValue` of the pair p twisted by ϑ, at scale π̄·per, on the point
datum `Data.Pair.pointDatum`: a function on U(1) × U(2z) at finite points. Here π =
`Data.piG` and per = `Parameters.jetScale`. -/
noncomputable abbrev pointKernel :=
  (lValueData H ϑ).kernelValue (star ↑D.piG * P.jetScale D.s) (pointDatum H ϑ)

/-- For |n| = 2z ≥ 4, Ξ_ϑ(h) is the sum of the jets `Data.Pair.pointKernel` at (u·k_A, h), over
representatives u of the classes of U(1) at principal level at the chosen places above g and
A in ∏_{w∈Q} k_w^×, with k_A = `LevelPlaces.twistLift` A. -/
lemma trivialLift_apply h : trivialLift H ϑ h = ∑ c : StdClasses (n :=
  Unit) D.chosenLevel × TwistGL _ Unit, pointKernel H ϑ (c.1.out * (D.levelPlaces ϑ).twistLift c.2)
  h := by erw [apply_eq_evalForm, map_smul, map_classSum, classSum,
  funext (D.classAut_eq_bot_of_le_chosenLevel
  le_rfl (by simpa using D.nat_le_of_hasLogBound))]; simp [smul_sum, kernelValue, pointDatum,
  schurJet_jetSeries_eq_smul (isLiftWeight _) (_ * _), sum_prod_type, smul_smul, rep_apply_apply,
  kernelForm, Matrix.sum_mulVec, boxes, AuxPair.upsilon_eq_sum,
  ↓← apply_eq_evalForm]; simp [AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card]; rfl

/-- If the prime l is coprime to the norm of every place in Q(ϑ), then
`Data.Pair.denomBound` times the jet
`Data.Pair.pointKernel` at (g, h) is integral at h: its gauge `weylGauge` for any embedding j of ℂ
in ℂ_l is at most 1. -/
lemma weylGauge_pointKernel_le_one {l} [Fact l.Prime] {j : PadicPlace l} g h (hl :
  l.Coprime ϑ.levelNorm) : weylGauge _ 0 h ((p.denomBound : ℂ)
  • pointKernel H ϑ g h) ≤ 1 := by simpa +contextual [weylGauge, weylRep, schur_eq_one] using!
  (mem_raises_of_dvd (pointDatum H ϑ) (hκ := isLiftWeight _) (ha := a_hasWeight _) (hb :=
  b_hasWeight _) (K := ⊤) (smul_vacuumDatum_mem_standardData norm_mul_gProd_pow_mem_modulus
  (by grind -abstractProof [AuxPair.levelIndicator, one_mem, zero_mem]) hl) norm_star_piG_le_one
  (by simp [denomBound, boxes, AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card, ← H.1]) _ _ 1)

/-- One group ring element gives all twists of a modulus: the normalised values
`Data.Pair.intAlgPart` at the tame characters ϑ′ of modulus Q(ϑ) are Σ c_a ϑ′(u_a), with u_a,
c_a free of ϑ′ and c_a integral at primes prime to Q.

Known result: Integral group-ring elements interpolating twisted Hecke L-values, with norm
relations. -/
lemma isIntegralMeasure_intAlgPart : ϑ.IsIntegralMeasure (intAlgPart H) := let g (a : StdClasses
    (n := Unit) D.chosenLevel × TwistGL _ Unit) := a.1.out * (D.levelPlaces ϑ).twistLift a.2
  ⟨_ × _, _, fun x ↦ G.det (s := 1) ((1, g x.2) / (1, g x.1)), _, fun x l _ hl j ↦
    (@embValRing _ _ ⟨j⟩).1.mul_mem (smul_classSum_mem _ (D.card_classAut_dvd_chosenGroupOrder (K :=
    (lValueData H ϑ).auxPair.levelGroup) (H.1.trans_le D.nat_le_of_hasLogBound) levelOf_le_Kf)
    (gramForm_mem_embValRing _ (weylGauge_pointKernel_le_one H (ϑ.pow 0) (g x.2) _ hl) <|
    weylGauge_pointKernel_le_one H _ (g x.1) · hl))
    (by simp [hl.norm_natCast_eq_one, -Nat.cast_prod] : ‖j (ϑ.levelNorm ^ (card n - 1))⁻¹‖ ≤ 1), by
  rintro ⟨⟩ rfl
  rw [sum_prod_type]; simp [intAlgPart, ← coe_algebraMap, ← inner_self_eq_norm_sq_to_K, inner,
    LevelForm.innerAt_eq_stdClassSum, mul_sum, sum_div, classSum_sum, ← coe_inv_eq_conj,
    ← mul_classSum, trivialLift_apply, TameChar.pow, kernelValue, pairWeil_apply,
    rankTwist, ↓map_div]
  congr with; congr with; ring!⟩

attribute [local simp] intAlgPart denomBound finite_isChosen twist_one_spec Finset.prod_eq_zero_iff
  NeZero.ne mul_div_mul_left

/-- For a pair p = (ν, z) with z ≥ 2 there is A ≠ 0 such that `Data.Pair.intAlgPart` at every tame
character ϑ equals A·L(z, (νϑ)⁻¹), without Euler factors at the chosen places, the places of
Q(ϑ) and their conjugates. -/
lemma intAlgPart_eq_mul_L : ∃ A ≠ 0, ∀ ϑ, intAlgPart H ϑ =
  A * (p.ν * ϑ.toAutChar)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z := by
  have h ϑ := (lValueData H ϑ).inner_trivialLift_self_eq_L H.1.symm H.2
  refine ⟨_, ?_,
    fun ϑ ↦ by simp_all [trivialLift, norm_smul, div_eq_iff, mul_pow, range_chosen, levelPlaces,
    ← ϑ.Q.prod_coe_sort, ← mul_assoc, -Fintype.card_pi]; dsimp +instances [levelPlaces, AuxPair.κ]⟩
  simpa [ne_of_gt, -Fintype.card_pi, H] using (h .one).1

/-- For a pair p, a tame character ϑ of modulus Q and a sign s = ±1, the ratio `Data.Pair.ratio` of
twisted to untwisted L-values at ϑ^s and Q is non-zero and real. -/
lemma ratio_ne_zero_and_real : let r := p.ratio ϑ s; r ≠ 0 ∧ star r =
    r := by simp (disch := simp [funext_iff] <;> grind [p.8 1, Pair]) [ratio,
  ((ϑ.4.zpow s).inv.mul p.hasWeight.inv).L_ne_zero, p.hasWeight.inv.L_ne_zero]

/-- The ratio ρ(ϑ) of the twisted to the untwisted L-value of the pair p = (ν, z) equals
`Data.Pair.intAlgPart` at ϑ divided by its value at the trivial twist. -/
lemma ratio_eq_intAlgPart_div : p.ratio ϑ = intAlgPart H ϑ / intAlgPart H .one :=
  (intAlgPart_eq_mul_L H).elim fun _ ⟨_, h⟩ ↦ by
    simpa [*, ratio] using congr((‖$(h ϑ) / $(h .one)‖ : ℂ)).symm

/-- For a pair p, an index set n fitting p and a tame character ϑ, the normalised value
`Data.Pair.intAlgPart` at ϑ is a non-zero complex number. -/
@[simp] lemma intAlgPart_ne_zero : intAlgPart H ϑ ≠ 0 := by grind [ratio_eq_intAlgPart_div H ϑ,
  ratio_ne_zero_and_real]

/-- For a pair (ν, z) with z ≥ 2 and every tame character ϑ, the form Ξ (`Data.Pair.trivialLift`)
lifted from the definite U(1) to the definite U(2z) with the character νϑ is non-zero. -/
@[simp] lemma trivialLift_ne_zero : trivialLift H ϑ ≠ 0 := by simpa using intAlgPart_ne_zero H ϑ

end Data.Pair

namespace Data

/-- Let the twists θ(ι) satisfy `Data.IsFitFamily`. If y has height at most c ≤ c' (`HeightLe`) and
each non-zero y'(ι) is y(ι) times an integer power of the norm of the modulus of θ(ι), then y' has
height at most c'. -/
lemma IsFitFamily.heightLe_of_eq_zpow_mul {c c' y y' θ} (o : D.IsFitFamily θ) (h :
  HeightLe c y) (hc : c ≤ c') (hy : ∀ ι, y' ι ≠ 0 → ∃ k : ℤ, y' ι = (θ ι).levelNorm ^ k * y ι) :
  HeightLe c' y' := h.mono hc fun ι ↦
  (not_or_of_imp (hy ι)).elim (by aesop) (by simp_all [(o.1 ι).norm_natCast_eq_one, -Nat.cast_prod])

variable (p)

/-- The pair with the same character as p whose point is z clamped to the interval from 1 to the
point of p. -/
def Pair.lowerPoint z :=
  {p with z := 1 ⊔ z ⊓ p.z, z_mem := by grind [Pair], le_c := by grind [Pair, le_c]}

/-- Let Π be `lValueProd`, (ν, z) a pair, ϑ tame of modulus Q, s = ±1. Then Π(z) for (νϑ^s)⁻¹
away from the chosen places and Q is N(Q)^{z²} times Π(z) for ν⁻¹ away from the chosen
places times ∏_{1≤z'≤z} ρ_{z'}², ρ_{z'} the L-value ratio `Data.Pair.ratio`. -/
lemma Pair.lValueProd_eq (s : ℤˣ) (ϑ : D.TameChar) :
  lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.ν * ϑ.toAutChar ^ s.1)⁻¹ p.z = ϑ.levelNorm ^ p.z ^ 2 *
  (lValueProd {w | D.IsChosen w} p.ν⁻¹ p.z * ∏ z ∈ .Icc 1 p.z, (p.lowerPoint z).ratio ϑ s ^ 2) :=
  by rw [lValueProd, lValueProd, finprod_mem_union, finprod_mem_coe_finset, Nat.mul_comm]
     push_cast [mul_pow, mul_assoc, ← prod_mul_distrib]; congr!
     cases (p.lowerPoint ‹_›).ratio_ne_zero_and_real ϑ s
     repeat simp_all [ratio, lowerPoint, field, Set.disjoint_right, IsChosen,
       levelNorm_mem_and_notMem_of_mem_Q _ ϑ, ↓finite_isChosen]

instance (D : Data P) (z) : NeZero (cond z D.b₁ 1) := z.rec .one D.instNeZeroNatB₁

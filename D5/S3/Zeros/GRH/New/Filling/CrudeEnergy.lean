/- GID: D5/S3/Zeros/GRH/New/Filling/CrudeEnergy
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/CrudeEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.CrudeEnergy. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/CrudeEnergy.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.BlockBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Incoherent and degenerate pairs are negligible. The second moment of the Poincaré series expands
over pairs of rational elements congruent mod g, and discriminant gains, lattice counts and a
weighted Schur test isolate the main term by showing that degenerate terms and pairs with different
Levi parts are negligible and that the rest shrink where frames meet mod g. Discarding small cells
and off-diagonal terms of Petersson-type and relative trace formulas by congruences and counts is
known. Related work: Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023;
Kowalski–Saha–Tsimerman, Local spectral equidistribution for Siegel modular forms, 2012; Blomer,
Density theorems for GL(n), 2023.

Part of: Agreeing characters force shared vectors up the flag (see New.Filling.BoxPartition).

This file: Agreeing characters with vanishing discriminant force a level; disagreeing terms
contribute zero. Energy of a stable set: incoherent and degenerate pairs of terms are negligible. -/

open Fin Classical ENNReal Matrix MeasureTheory MulAction Set

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰}

/-- Under the standing hypotheses, if T is stable under the rational points of 𝖴 on both sides
and no γ in T satisfies `Filling.CharsAgree` (agreement of the finite characters on 𝖴 ∩ γ𝖴γ⁻¹),
then the sum of amplitudes of T over every (c, s, c') vanishes. -/
lemma Filling.amplitudeSum_eq_zero_of_not_charsAgree [StablyUnram E]
    [S.IsAdmissible] [Side] {T} (hT :
  S.IsStable T) (h : ∀ γ ∈ T, ¬S.CharsAgree γ) c s c' : S.amplitudeSum T c s c' = 0 := by
  choose φ _ w _ q using (S.exists_cutoff_classUnip <| stabilizer _ (α := _ ⧸ S.classUnip c') ·)
  choose a e using @Quotient.mk_out _ (orbitRel (S.classUnip c) (_ ⧸ S.classUnip c'))
  refine (hasSum_amplitudeSum_change_of_weight hT c s _ (fun γ ↦ (S.classCutoff c' (S.ratToInf
    γ)⁻¹ * indicator {x | x = a x • x} 1 γ) • φ γ) fun γ _ y ↦ ?_).1.unique (hasSum_zero.congr_fun
    fun γ ↦ (h _ γ.2.1).imp_symm fun n _ a _ b e ↦ eq_of_inv_mul_eq_one (n.imp_symm fun z ↦ ?_))
  simp [tsum_classCutoff_eq_one, show ∀ u : S.classUnip c, ↑(u * γ) =
    u • (γ : _ ⧸ S.classUnip c') by tauto]
  erw [← (Equiv.mulRight (a γ)).tsum_eq, ← w (a γ • γ) (S.ratToInf (a γ) * y),
    tsum_subtype _ fun u : S.classUnip c ↦ φ _ (S.ratToInf u * _)]
  simp +contextual [indicator, *, mul_assoc, mul_smul]
  simp [mul_smul, integral_smul, (fun i ↦ ((q γ).integral_orbitMeasure i).symm.trans
    (integral_quotMeasure_eq_zero_of_twist volume (i ⟨·, ·⟩) continuous_besselKernel
    (by simp [unipotentChar]) z (mul_inv_eq_of_eq_mul e ▸ besselKernel_besselU_mul a b γ))) fun ⟨_,
    u, h, rfl⟩ y ↦ by simp [besselKernel, mul_assoc, besselFn_mul_of_mem_classUnip u,
    ← besselFn_mul_of_mem_classUnip ⟨_, QuotientGroup.eq.1 h.symm⟩ (_ * y)]]

/-- If γ satisfies `Filling.CharsAgree` and the frames f, γf share a vector with leading
coefficients
c, c' at index a, then cc̄ = c'c̄' and they share such a vector at every index b ≥ a. -/
lemma Filling.hasCommonFlagVector_of_le {γ} (hr : S.CharsAgree γ) a c c' (h : HasCommonFlagVector γ
  c c' a) : c * star c = c' * star c' ∧ ∀ b ≥ a, HasCommonFlagVector γ c c' b := by
  induction' a using reverseInduction with a i <;> have ⟨x, y, _⟩ := h
  grind [star_mul_last_eq_of_frameImage_eq]
  have := exists_mulVec_eq_of_annihilator (frameImage 1) (frameImage γ) (Iio a.succ) (Iio a.succ)
    (cons 0 (init x)) (cons 0 (init y)) fun l h k ↦
    (algebraMap E (𝔸f E)).injective (eq_of_ψf (denseRange_algebraMap_finAdele.eq fun t ↦ ?_))
  grind [i (this.imp (by simp [forall_fin_succ, init]; grind))]
  have ⟨v, Z⟩ := exists_star_vecMul_eq S.ratGram (l ᵥ* γ)
  let r := S.g * S.ϖ * -t
  obtain ⟨⟨u, a, _⟩, w, b, _⟩ := exists_mem_besselU_eq_eichlerMap _ x r (by simp [star_mulVec,
    ← U.form_mul_inv_eq, ← Z ▸ vecMul_vecMul ..] : star (γ *ᵥ v) ᵥ* S.ratGram =
    l ᵥ* 1) (by grind) h, exists_mem_besselU_eq_eichlerMap _ y r Z (by grind) k
  simpa [*, r, unipotentChar, gIdele, selfDualChar, ratToFin, simpleRootSum_adelicToFin, ← map_mul,
    mul_assoc, Circle.ext_iff, -vecMul_one] using! hr u a w b (by ext : 2; simp [*, ext_iff_mulVec,
    U.form_mulVec_mulVec, ← mulVec_mulVec, frameImage_mulVec γ.1.1, eichlerMap_mulVec, mulVec_sub])

/-- If γ satisfies `Filling.CharsAgree` (the finite characters agree on 𝖴 ∩ γ𝖴γ⁻¹) and 𝗀(γ) = 0,
then γ has level j, in the sense of `Filling.HasLevel`, for some j ≤ ϱ.

Agreeing characters force shared vectors up the flag. -/
lemma Filling.CharsAgree.exists_hasLevel {γ} (hr : S.CharsAgree γ) (h : S.termDisc γ = 0) : ∃ j,
  S.HasLevel j γ := (exists_minimal_of_wellFoundedLT (IsNormalForm ·.1 γ) ⟨⊤, 1, by simp; lia⟩).imp
  fun j m ↦ have M x y (e : frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y) (z : ∀ i, j ≤ i.castSucc →
    y i = 0) : ∀ a, x a = 0 ∧ y a = 0 :=
    WellFoundedGT.fix fun a _ ↦ by grind [IsNormalForm, Minimal, star_one, star_eq_zero,
    fun s ↦ hasCommonFlagVector_of_le hr a (s⁻¹ * x a) (s⁻¹ * y a) ⟨s⁻¹ • x, s⁻¹ • y, by aesop⟩]
  (fun d ↦ ⟨m.1, d, iff_of_false ((exists_mulVec_eq_single_det (S.frameProducts γ)).elim fun y a e ↦
    d (last_le_iff.1 e ▸ (by grind [frameDisc, star_eq_zero, (norm_sq_middle_part_eq a.1 rfl).2
    _, by simpa using congr(‖Φ ofNonempty $(sub_eq_zero.1 h)‖)] : (S.frameProducts γ).det = 0)))
    (· h)⟩) ((exists_mulVec_eq_zero_iff.2 ∘ det_paddedLeading.trans).mt fun ⟨y, Z⟩ ↦ by
  simp [funext_iff, paddedLeading, (of _).mulVec_apply_eq_sum, ← mulVec_apply_eq_sum] at Z
  grind [sq_nonneg, by simpa using (norm_sq_middle_part_eq (D := 0) (.trans (dotProduct_eq_zero
    (S.frameProducts γ *ᵥ y) fun w ↦ (exists_frameImage_eq_of_isNormalForm m.1.inv (star w)).elim
    fun _ ⟨_, _, e⟩ ↦ by grind [dotProduct, Pi.star_apply, star_star, Finset.sum_eq_zero, by
    simpa [star_mulVec_dotProduct] using congr(star $(frameProducts_mulVec_of_frameImage_eq e) ⬝ᵥ
      y)]) (by simp)) rfl).2 ofNonempty])

attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono
  IdemSemiring.toMulRightMono

attribute [local instance high] Side.cut

attribute [local irreducible] Filling.classGauge Filling.mainEnergy Filling.saturationIndex
  Filling.termPosition Filling.frameValueIndex link

variable [StablyUnram E]

variable [ok : S.IsAdmissible] {C w : ℝ} (hC : 0 ≤ C) {Ω : Set _} {T X} (hT : S.IsStable T)
  (h₁ : (∃ γ ∈ T, ∃ c c', ∃ s ∈ Ω, γ ∈ S.termsOver c s c' ∧ IsNormalForm 0 γ) →
  S.tailScale ^ 20 * S.besselEnergy ≤ C)
  (hx : X ≠ 0) (hq : ∀ s ∈ Ω, S.FixesNormAtLeast s X) (hw : 0 ≤ w) (hz : S.besselEnergy ≤ C)

include hC hT h₁ hx hq hw hz

/-- Put 𝖽₁ = `Filling.besselEnergy`, 𝖽 = `Filling.mainEnergy`, τ = `Filling.tailScale`, ν =
`Filling.unipCovolume`; "s fixes X" is `Filling.FixesNormAtLeast` s X.
T stable of level j, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, ≥ τ²⁰𝖽₁ if a term has `IsNormalForm`
0, ≥ τ¹²𝖽/X^|κ| if j > ϱ and R omits a link. If cut `Filling.linkEnergy` ≤ wν², the cut energy
is ≤ w + C/(b³⁰4^(ϱ+1−j)).

Incoherent and degenerate pairs are negligible. -/
lemma Filling.energy_le_of_level_pairs j R (hc : ∀ γ ∈ T, S.HasLevel j γ) (h₂ : 𝔰.ϱ < j →
  (∃ Λ, Λ ∉ R) → S.tailScale ^ 12 / X ^
  𝔰.k * S.mainEnergy ≤ C) (h : linkEnergy T Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) : energy
  (S.amplitudeSum T) Ω ≤ w + C / S.b ^ 30 / 4 ^ j.rev.1 := S.of_size_bounds fun g t u z v y ↦ by
  intros; simp_rw [energy, ← Finset.sum_div]; grw [div_le_iff₀, ← ofReal_le_ofReal_iff, add_mul,
    ofReal_add, ← h, ← (?_ : ∑ c, ∑ c', ∑' (a) (b),
    .ofReal (C / S.tailScale ^ 3 * S.unipCovolume ^ 2) * (S.pairWeight j c
    c' b a + S.pairWeight j c c' a b) ≤ .ofReal _), linkEnergy] <;> try positivity
  simp (disch := intros; positivity) [← Finset.sum_subtype_eq_sum_filter, ofReal_sum_of_nonneg]
  have m {α β : Type} (f : α → ℝ≥0∞) g : tsum f * tsum g = ∑' p : α × β, f p.1 * g p.2 := by simp
  have B Λ := enorm_amplitudeSum_le_classSize (T :=
    T ∩ link ⁻¹' {Λ}) (by grind [IsStable, link_besselU_mul]) (hc · ·.1)
  simp_rw [amplitudeSum, ← ((summable_amplitude T ..).hasSum.tsum_fiberwise (link ∘ (·.1))).tsum_eq]
  grw [enorm_tsum_le_tsum_enorm]; simp_rw [← tsum_image _ injOn_subtype_val, tsum_subtype
    (_ '' _), preimage_comp, Subtype.image_preimage_coe, T.inter_right_comm _ (_ ⁻¹' _),
    ← tsum_subtype, ← amplitudeSum.eq_1, sq, m, ← ENNReal.summable.tsum_add_tsum_compl
    (s := Function.diag '' R) (by simp), Finset.sum_add_distrib]
  gcongr; exact ((Equiv.Set.image _ R fun _ _ ↦ by simp).tsum_eq _).ge
  grw [ENNReal.sum_le_tsum, B, B]; simp_rw [m, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_sigma]
  refine (ENNReal.tsum_le_tsum fun ⟨s, π, ⟨γ, ⟨⟨m, e⟩, a⟩, n⟩, γ', ⟨⟨m', e'⟩, a'⟩, _⟩ ↦ ?_).trans
    (tsum_comp_le_tsum_of_injective (f := fun ⟨_, _, a, b⟩ ↦ ⟨a, b⟩) ?_ _);
  (iterate 2 rintro ⟨⟨⟩, ⟨⟨⟩⟩, ⟨_, ⟨⟨⟨_, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩⟩⟩, _, ⟨⟨⟨_, ⟨⟩⟩⟩⟩⟩); rintro ⟨⟩; rfl; dsimp
  have k := hc _ m; apply hc at m'; specialize hq _ s.2; obtain ⟨⟨i, r, l, L⟩, ⟨-, ⟨d⟩⟩, ⟨-, ⟨d'⟩⟩,
    ⟨⟨_, p⟩, -⟩, ⟨⟨-, q⟩⟩⟩ := pairInvariant_mul_le n.1 a k hq a' m',
    one_le_xRowsIndex_and_saturationIndex a k, one_le_xRowsIndex_and_saturationIndex a' m',
    exists_link_split_le_classGauge n.1 a k hq γ', exists_link_split_le_classGauge n.1 a' m' hq γ
  unfold pairWeight termWeight invPowWeight pairInvariant commonLink classSize countWeight at *; set
    D := ite (𝔰.ϱ < j) S.mainEnergy _
  have H : S.tailScale ^ 4 * D * (2 * S.tailScale ^ 2) ^ (j - 𝔰.ϱ) * S.codimFactor ^ i / ite
    (𝔰.ϱ < j ∧ i = 0) X 1 ^ 𝔰.k ≤ C / S.tailScale ^ 3
  · clear * - t u v y h₂ h₁ l k m a e e' hz
    induction' j using lastCases with j <;> simp [Nat.sub_eq_zero_of_le, D, is_le, ← not_le]
    · cases i; · grw [← h₂ (by simp) ⟨π.1.1, by grind⟩, t]; simp [field]; bound
      grw [pow_le_of_le_one _ codimFactor_le_one, ← hz, ← ok.mainEnergy_le,
        t] <;> simp [field] <;> bound
    grw [codimFactor_le_one]; rcases j with ⟨⟨⟩⟩
    · grw [← h₁ ⟨_, m, _, _, _, s.2, a, k.1⟩]; simp [field]
    grw [← hz, ← le_self_pow₀] <;> simp [field] <;> bound
  repeat rw [ite_eq_left (by simp [*]; use s)]
  rw [inf_comm (link γ')] at *; have M := L; grw [z] at L
  nth_grw 1 [← show 1 ≤ ite _ X 1 by lia, ← d, ← d', ← g, ← p, ← q] at M; grw [tsub_le_iff_left.2
    (r.trans_eq (add_assoc ..)), ← H, mul_add, ← (ENNReal.pow_le_pow_left_iff (by simp)).1 (.trans
    ?_ ((mul_le_mul' le_self_add le_add_self).trans (sq _).ge))]; simp (disch := positivity) only
    [D, ← ofReal_mul, ← ofReal_pow, ← div_le_iff₀'] at *; nth_grw 2 [pow_succ _ 𝔰.k, ← M]
  grw +useKAbstract [← L]; simp (disch := positivity) only [mul_pow, div_pow, Real.sq_sqrt,
    (submoduleIndex ..).cast_mul, submoduleIndex_smul_intVectors S.gIdele_mem, Fintype.card_subtype,
    card_filter_val_lt, S.gIdele_val ▸
    genIndex_natCast _]; congr! 1; field; any_goals nlinarith only [t]
  simp [ENNReal.tsum_add, ← Finset.mul_sum]
  grw [ENNReal.tsum_comm.le, sum_pairWeight_le]
  simp (disch := positivity) only [← ofReal_mul, ← ofReal_add, ofReal_le_ofReal_iff, field]
  ring_nf; grw +useKAbstract [show 4 ≤ S.b by linarith, ← pow_le_tailScale (e := 𝔰.ϱ + 1 - j + 31)
    (le_mul_of_le_of_one_le (by lia) NeZero.one_le)]; ring_nf; rfl

omit hw in
/-- Letters as in `Filling.energy_le_of_level_pairs`.
T stable, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, and ≥ τ²⁰𝖽₁ if a term has `IsNormalForm` 0. If each γ
∈ T with `Filling.CharsAgree` has a level below n ≤ ϱ+1, the cut energy is ≤ C/(b³⁰4^(ϱ+1−n)). -/
lemma Filling.energy_le_of_level_lt n (h : ∀ γ ∈ T, S.CharsAgree γ → ∃ j < n, S.HasLevel j γ) :
    energy (S.amplitudeSum T) Ω ≤ C / S.b ^ 30 / 4 ^ n.rev.1 := by
  induction' n using induction with j ih generalizing T
  · simp [energy, amplitudeSum_eq_zero_of_not_charsAgree hT (by grind)]; positivity
  grw [amplitudeSum_split _ {γ | S.HasLevel j.castSucc γ}, energy_add_le one_pos, ih,
    energy_le_of_level_pairs hC _ _ hx _ le_rfl _ j.castSucc ∅ (h := by simp [linkEnergy])]
  simp [rev_castSucc, pow_succ, field]; all_goals grind [IsStable, S.isStable_hasLevel j.castSucc]

/-- Crude estimate (letters as in `Filling.energy_le_of_level_pairs`):
T stable, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, ≥ τ²⁰𝖽₁ if a term has `IsNormalForm`
0, ≥ τ¹²𝖽/X^|κ| if R omits a link. If cut `Filling.linkEnergy` (𝗀 ≠ 0) ≤ wν², the full energy
is ≤ (1+b⁻⁴)²w + b⁻¹²C.

Incoherent and degenerate pairs are negligible. -/
lemma Filling.energy_le_of_linkEnergy_le R (h₂ : (∃ Λ, Λ ∉ R) →
  S.tailScale ^ 12 / X ^ 𝔰.k * S.mainEnergy ≤ C)
  (h : linkEnergy (T ∩ {γ | S.termDisc γ ≠ 0}) Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) :
  energy (S.amplitudeSum (σ := .full) T) Ω ≤ (1 + (S.b ^ 4)⁻¹) ^ 2 * w + (S.b ^ 12)⁻¹ * C := by
  obtain ⟨⟨y, _, e⟩, p⟩ := exists_nonneg_add_of_le S.thousand_le_b,
    (by bound [S.thousand_le_b] : 0 < S.b ^ 4)
  grw [← sub_add_cancel (S.amplitudeSum (σ := _) T) (S.amplitudeSum T), energy_add_le p,
    energy_sub_cut_le, amplitudeSum_split, energy_add_le p, energy_le_of_level_pairs hC _ _ hx _ _ _
    (last _) R _ _ h, energy_le_of_level_lt hC _ _ hx _ _ (last _), hz, ← e, ← sub_nonneg]
  simp [field, -sub_nonneg]; ring_nf; positivity
  all_goals grind [CharsAgree.exists_hasLevel, HasLevel, IsStable, frameDisc_frameGram_besselU_mul,
    hasLevel_last]

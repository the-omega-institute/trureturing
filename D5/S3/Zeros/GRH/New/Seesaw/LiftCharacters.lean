/- GID: D5/S3/Zeros/GRH/New/Seesaw/LiftCharacters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/LiftCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.LiftCharacters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/LiftCharacters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.JetDivisibility
import D5.S3.Zeros.GRH.New.Columns.ChainValuation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Trading denominators at the level prime for a column operator (see
New.Columns.TwistedHeckeType).

This file: Column level at N read as conjugated mirabolic group; restriction keeps valuation, size.
Index bound at N for preimage of the lattice under the Gauss-sum operator power. Splitting
characters of the chain: unramified above the level prime, double splitting. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Fintype Gf IsSplitLevel Matrix NeZero Valued WithZero Equiv

attribute [-simp] WithZero.inv_exp

variable {P} (D : Data P) {p : ℕ} [Fact p.Prime] [PadicPlace p]

lemma Data.GaugeLe.restrictToY_of_diag {d : Gf _ _} (hs : ∀ τ, .map (adeleExtension (weightEmbedding
  ιₚ τ)) d.1 = diagGL (ite ·.isLeft 1 (ite (star (inducedPlace τ) ∈ D.piPlaces) (.mk0 ↑D.N out) 1)))
  {c φ} (h : GaugeLe d c φ) : GaugeLe 1 c (D.restrictToY φ) := fun g ↦
  ((one_mul _).trans_le (h (D.borderU g))).trans' (Eq.trans_le (by
  erw [mulVec_mulVec, D.branching.2.1 _ _ fun τ ↦ (d.1.map (adeleExtension (weightEmbedding ιₚ
    τ))).det⁻¹, smul_mulVec, ← mulVec_mulVec, Units.smul_def, norm_smul, weylGauge_smul]
  use congr($(?_) * ‖_ *ᵥ $(funext (by simp [mulVec_eq_sum]))‖)
  simpa [hs, apply_ite, @starRingEnd_apply D.E, branchExp] using congr(∏ τ :
    D.Φ, $((isEquiv_placeOfEmb
    (weightEmbedding ιₚ τ)).eq_iff (s := ite _ D.N 1) |>.2 (by split <;> simp_all
    [inducedPlace, placeOfEmb_comp_star, ← v_algebraMap_eq_valuation, v_algebraMap_eq_intValuation,
    intValuation_pi, D.isSplitLevel_piPlaces.3, piPlaces])).1⁻¹ ^ D.branchExp τ)
  simp [← map_inv, ← ext_iff, borderU, PolyRep.blockScalar, hs _ ▸ map_inv ..])
    (norm_mulVec_le (by simp [IsUltrametricDist.norm_intCast_le_one]) _))

/-- Let p ≠ N be prime and ι : ℂ → ℂ_p. If the gauge at ι of φ(g) on the lattice of g is at most
c for all g, the same holds for the restriction of φ to Y_m. -/
lemma Data.GaugeLe.restrictToY (hp : p ≠ D.N) {c φ} :
    GaugeLe 1 c φ → GaugeLe 1 c (D.restrictToY φ) :=
  restrictToY_of_diag D (by simp [D.notMem_piPlaces_of_ne hp, p_mem_inducedPlace, Units.ext_iff])

lemma Data.weylNormSq_restrictToY_le (σ : ℂ →+* ℂ) φ h : weylNormSq (σ ∘ (D.restrictToY φ).1 h) ≤
  .exp (D.x ^ 70 - (∑ τ, D.branchExp τ : ℝ) * .log D.N) * weylNormSq (σ ∘ φ.1 (D.borderU h)) := by
  have k (τ : D.Φ) := congr(‖weightEmbedding σ τ $D.π_mul_star‖.log)
  erw [weylNormSq_comp_smul]
  simp [← sq, Function.comp_def, σ.map_mulVec, -RingHom.coe_comp] at *
  grw [D.branching.2.2.1 _ (sum_mono fun _ ↦ (sum_le_card_nsmul _ _ (D.n D.m * D.h) ?_).trans
    (mul_le_mul_left (c := D.n D.m) ?_ _)), ← mul_assoc, ← Real.le_exp_of_log_le]
  all_goals simp_all [Real.log_prod, Real.log_mul, @starRingEnd_apply D.E,
    sum_mul, mul_sum, mul_left_comm (2 : ℝ), card_congr D.lastIndexEquiv, prod_eq_zero_iff, -not_or]
  exacts [D.le_of_hasLogBound, by intros; gcongr <;> grind [columnsY, κ, keptColumns,
    reducedHalfGap], by lia]

/-- The set of complex conjugates of the primes `Data.inducedPlace` τ of E above p, as τ runs over
the embeddings in the CM type Φ. -/
noncomputable def Data.nonInducedPlaces := univ.image fun τ ↦ star (D.inducedPlace τ)

lemma Data.isSplitLevel_nonInducedPlaces [PadicPlace D.N] : IsSplitLevel D.nonInducedPlaces
  D.N := by use (by simpa [nonInducedPlaces, ← inducedPlace_mul] using fun τ ↦ (P.smul_ne_star
  D.N_modEq_one (D.p_mem_inducedPlace τ) (v := · / τ))) <;> grind [P.q_eq_of_modEq_one
  D.N_modEq_one, v_N_eq_exp_neg_one, p_mem_inducedPlace, mem_star_place, star_natCast, star_star, =_
  inducedPlace_mul, nonInducedPlaces, P.exists_smul_eq_or_star (D.p_mem_inducedPlace 1)]

variable [PadicPlace D.N] [l : IsSplitLevel D.nonInducedPlaces D.N]

/-- The finite adelic unitary point on X_j supported on S ∪ S̄, with component diag(1, …, 1, N)
at the w in S dividing π and 1 at the other w in S; S = `Data.nonInducedPlaces` above N. -/
noncomputable abbrev Data.diagPointN j := l.embedGL (diagN (D.InitIndex j) D.piPlaces)

/-- The homomorphism from GL(∏_{w∈S} E_w) to the finite adelic unitary group of X_j given by
`IsSplitLevel.embedGL` followed by conjugation g ↦ dgd⁻¹, d = `Data.diagPointN` j. -/
noncomputable def Data.conjEmbedGL j := (MulAut.conj (D.diagPointN j)).toMonoidHom.comp l.embedGL

/-- The representation of the general linear group over ∏_{w∈S} E_w on smooth forms of stage j,
by right translation through the conjugated embedding `Data.conjEmbedGL`. -/
noncomputable abbrev Data.nonInducedRep j :=
  Rep.of (X := D.Stage j) ((smoothFormRep ..).comp (D.conjEmbedGL j))

lemma Data.adeleExtension_map_diagN j S τ : .map (adeleExtension (weightEmbedding ιₚ τ))
  (l.embedGL (diagN (D.InitIndex j) S)).1 = diagGL (ite ·.isLeft 1
  (ite (star (inducedPlace τ) ∈ S) (.mk0 ↑D.N out) 1)) := congr($(atPlace_atSplits star_notMem _
  ⟨_, by simp [nonInducedPlaces, inducedPlace, placeOfEmb_comp_star]⟩).map _).trans
  (by simp [diagN, inducedPlace, placeOfEmb_comp_star, Units.ext_iff]; aesop)

lemma Data.lastColDatum_conj_ne_zero_iff {j} (k : Gf _ (D.X j)) : l.lastColDatum lastBasisVector
  (atPlaces _ ((D.diagPointN j)⁻¹ * k * D.diagPointN j)).1 ≠ 0 ↔ ∀ w ∈ D.nonInducedPlaces, (∀ b c,
  v (k.atPlace w b c) ≤ 1) ∧ (star w ∈ D.piPlaces → ∀ b, v (((k⁻¹.atPlace (star w)).1 - 1) (.inr ())
  b) ≤ exp (-1)) ∧ (w ∈ D.piPlaces → ∀ b, v (((k.atPlace w).1 - 1) (.inr ()) b) ≤ exp (-1)) := by
  simp [Subtype.forall', l.3, liftFn_apply, mem_O_locProd, ← map_inv, ZMod.val_one, diagN,
    lastColDatum, ← forall_and, @forall_comm _ D.nonInducedPlaces, div_le_one₀, -Subtype.forall,
    reduction_eq_iff, @funext_iff (_ ⊕ _), k⁻¹.atPlace_star rfl, show ∀ b c w,
    atPlaces D.nonInducedPlaces k b c w = k.atPlace w b c by tauto]
  congr! 1; split <;> simp [inv_mul_cancel_of_invertible, *, l.3, inv_mul_le_one₀, mul_right_comm,
    D.isSplitLevel_piPlaces.1, ((D.isSplitLevel_piPlaces.4 _).1 (l.natCast_mem ..)).resolve_left]
  grind [mul_le_one', show exp (-1) ≤ 1 by tauto]
  simp [← v_conjLoc rfl (k.atPlace _ _ _ - 1)]

lemma Data.atPlaces_conj_mem_mirabolic {j} (k : D.columnLevel j) :
  atPlaces _ ((D.diagPointN j)⁻¹ * k.1 * D.diagPointN j) ∈ l.mirabolic :=
  have B (k) := (D.lastColDatum_conj_ne_zero_iff _).2 fun w _ ↦ ⟨(mem_Kf_iff.1 (levelOf_le_Kf k.2.1)
    w).isIntMatrix, (D.mem_columnLevel.1 k⁻¹.2).2 _, (D.mem_columnLevel.1 k.2).2 w⟩
  (exists_inclGL_eq (B k) (by simpa [mul_assoc] using! B k⁻¹)).imp (by simp [Units.smul_def, col])

lemma Data.mem_ramified_of_mem_ramifiedColumns {φ} (r : φ ∈ D.ramifiedColumns) :
  φ.1 ∈ l.ramified (D.nonInducedRep 0) := fun w ↦ by
  obtain a | a := (D.isSplitLevel_piPlaces.4 _).1 (IsSplitLevel.natCast_mem _ w.2) <;> peel
    exists_embedGL_scalar_eq_scalarFin (n := D.X 0) w ((D.exists_centralGen ⟨_,
    a⟩).choose_spec.1.imp_right (by aesop)) <;> exact (D.exists_eq_sub_centralGen ⟨_, a⟩ r).imp' (↑)
    (by simp_all [conjEmbedGL, ← (commute_scalarFin _).eq, centralGen])

/-- The operator F = `IsSplitLevel.fourierOp` of the representation `Data.nonInducedRep` on smooth
forms of stage 0 sends columns to columns. -/
lemma Data.fourierOp_mem_column {φ} (r : φ ∈ D.Column) :
  fourierOp (D.nonInducedRep 0) φ ∈ D.Column := fun k ↦ have G := D.atPlaces_conj_mem_mirabolic k
  by refine (mirabolic_fix_fourierOp (π :=
    D.nonInducedRep 0) (smoothFormRep _ _ k) G fun a b e ↦ have := mul_mem e (inv_mem G)
    Iff.mpr ?_ ((fun B C o ↦ r (⟨D.conjEmbedGL 0 a * k * D.conjEmbedGL 0 b * k.1⁻¹,
      D.mem_columnLevel.2 ⟨D.mem_chosenLevel_of_supportedOn l.natCast_mem
      ⟨(mem_Kf_iff_of_supportedOn o).2 fun w h ↦ mem_intGL.2 ⟨(B w h).1, (C w h).1⟩, o⟩, fun w x ↦
      ((l.4 w).1 (D.isSplitLevel_piPlaces.natCast_mem _ x)).rec (B w · |>.2.2 x) fun y ↦
      star_star w ▸ (C _ y).2.1 (by simpa)⟩⟩ * k)) ((D.lastColDatum_conj_ne_zero_iff _).1
      (lastColDatum_ne_zero ?_)) ((D.lastColDatum_conj_ne_zero_iff (_ * _)⁻¹).1
      (lastColDatum_ne_zero (inv_mem_iff.1 ?_))) ?_)).trans ?_ <;> simp_all [conjEmbedGL,
    mem_supportedOn.1 (embedGL_mem_supportedOn _), mul_assoc]

/-- At an embedding ι : ℂ → ℂ_N, the ι-integral columns have index (`IndexDvd`) dividing N^e, for
some e ≤ 4mfb·dim(columns), relative to the smooth forms that F^{ϱ+1} sends to columns
integral at `Data.diagPointN`; F = `IsSplitLevel.fourierOp` of `Data.nonInducedRep`. -/
lemma Data.exists_indexDvd_fourierOp_pow {P} {D : Data P} [PadicPlace _] (l :=
  D.isSplitLevel_nonInducedPlaces) : ∃ e : ℕ, e ≤ 4 * D.m * D.f * D.b * Module.finrank ℂ D.Column ∧
  IndexDvd (integralFormsAt D.Column 1) ((integralFormsAt D.Column (D.diagPointN 0)).comap
  ((fourierOp (D.nonInducedRep 0) ^ (D.ϱ + 1)).restrictScalars _)) (D.N ^ e) := by
  let t a := ∑ i : StdClasses (D.columnLevel 0) × WeylIndex (D.X 0) D.κ, ∑ τ, tableauWeight i.2 τ a
  let d S := (l.embedGL (diagN (D.InitIndex 0) S))⁻¹
  have h b : IndexDvd (integralFormsAt D.Column (D.diagPointN 0 * d b))
    (integralFormsAt D.Column (D.diagPointN 0)) (D.N ^ t (.inr ()))
  choose γ h h' using fun c ↦ exists_mul_mem_integralAbove D.N (c * (D.diagPointN 0 * d b)) (d b)
  use ((IndexDvd.of_det_dvd (det_diagonal.trans (prod_pow_eq_pow_sum ..)).dvd le_rfl).map
    ((Algebra.linearMap
    ..).compLeft _) le_sup_left le_rfl).comap ⟨⟨fun φ x ↦ φ.1 (stdEmbFin (γ x.1.out) * x.1.out)
    x.2, by tauto⟩, by tauto⟩ (fun _ H ↦ ⟨(⟨_, (weylGauge_le_one_iff _ (by simp_all [mul_assoc])).1
    (H.2 _) ·.2⟩), ⟨⟩, rfl⟩) fun φ ⟨H, _⟩ ⟨_, ⟨y, _, rfl⟩, e⟩ ↦ ⟨H, fun g ↦ ?_⟩
  obtain ⟨c, _, k, rfl⟩ := exists_eq_map_mul_rep_mul stdEmbFin (D.columnLevel 0) Quotient.out_eq g
  erw [levelSpace_smoothFormRep_apply H, one_smul, mul_assoc, mul_assoc, weylGauge_embFin,
    ← weylGauge_embFin, ← φ.2.2 (γ c.out), ← weylGauge_mul _ (inv_mem (mul_mem (h' c.out)
    (mem_integralAbove_of_inclGL_eq (D.atPlaces_conj_mem_mirabolic k).choose_spec.2))), weylGauge,
    show ιₚ ∘ _ = schur _ (fun _ ↦ diagonal (1 ⊕ᵥ D.N)) *ᵥ (ιₚ <| y ⟨c, ·⟩) by
    ext; simpa [schur_diagonal, prod_pow_eq_pow_sum] using congr(ιₚ ($e (c, _))).symm]
  simp [weylRep, lastEntry, mul_assoc, d, adeleExtension_map_diagN, -coe_units_inv]
  grw [norm_schur_mulVec_le .refl, pi_norm_le_iff_of_nonempty]; use (y ⟨c, ·⟩ |>.2)
  intro; split <;> simp [← map_inv, diagonal_apply, apply_ite (‖·‖ ≤ 1), norm_p_lt_one.le,
    NeZero.ne]
  use t (.inr ()) * (D.ϱ + 1 + 1), ?_
  induction _ + 1; simpa [d] using! h D.piPlaces
  simp [pow_succ', mul_add, pow_add] at *
  use .trans ‹_› ((h D.nonInducedPlaces).comap _ (fun _ H ↦ ?_) (by tauto)); use
    D.fourierOp_mem_column H.1; intro
  conv in fourierOp .. => unfold fourierOp
  simp; apply weylGauge_sum_le; simp; intros
  erw [weylGauge_smul, P.norm_map_psi₀,
    ← weylGauge_mul _ (mem_integralAbove_of_inclGL_eq (l.atPlaces_embedGL _).symm)]
  simpa [conjEmbedGL, ← mul_assoc] using! H.2 (_ / D.diagPointN 0)
  have s a b : t a = t b := by simpa [t, schur_diagonal, prod_pow_eq_pow_sum, swap_apply_eq_iff,
    ← submatrix_mul, Fintype.sum_prod_type] using det_mul_comm (schur D.κ fun _ ↦ (diagonal (if · =
    a then (2 : ℤ) else 1)).submatrix id (swap a b)) (schur _ fun _ ↦ submatrix 1 (swap a b) id)
  have a : ∑ a, t a ≤ _ := sum_comm_cycle.ge.trans (by grw
    [(sum_tableauWeight · · |>.trans_le (sum_height_mul_kappa_le ..))])
  simp [finrank_levelSpace_smoothFormRep, classAut_columnLevel_eq_bot, ↓card_X, n, ← @Nat.cast_le ℝ,
    ← le_div_iff₀', -Fintype.card_pi, -MonoidHom.coe_range, s _ (.inr ())] at *
  grw [a]; field; use D.le_of_hasLogBound

lemma Data.charUnramifiedAt_rankTwist_of_N_mem {P} (D : Data P) ϑ j n [Fintype n] w (h :
  ↑D.N ∈ w.1) : CharUnramifiedAt (rankTwist (D.chainChar ϑ j) n).baseChange.finPart w := by apply
  AutChar.HasWeight.charUnramifiedAt <;> simp [liftTamePart, not_isChosen_of_N_mem, ϑ.5,
  (D.levelNorm_mem_and_notMem_of_mem_Q ϑ ∘ .inl).mt, *, TameChar.pow]

/-- For the character ν of lift i and twist ϑ, applying `rankTwist` for X_j and then
`AutChar.spaceChar` in rank |X_j| gives the Hecke character x ↦ ν(x/x̄). -/
lemma Data.spaceChar_rankTwist {P} (D : Data P) ϑ j i :
  (rankTwist (D.chainChar ϑ i) (D.X j)).spaceChar (Fintype.card (D.X j)) =
  (D.chainChar ϑ i).baseChange := _root_.spaceChar_rankTwist (Even.two_dvd (by grind [card_X, n]))

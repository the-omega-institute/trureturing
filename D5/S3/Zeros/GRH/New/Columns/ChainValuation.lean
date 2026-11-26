/- GID: D5/S3/Zeros/GRH/New/Columns/ChainValuation
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Columns/ChainValuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Columns.ChainValuation. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Columns/ChainValuation.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Trace.GoodIdempotent
import D5.S3.Zeros.GRH.New.Columns.JetExponentBound
import D5.S3.Zeros.GRH.New.Rows.MemberKernels
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Also holds known results stated on this proof's data: Integral group-ring elements interpolating
twisted Hecke L-values, with norm relations (known result; see New.Selmer.ValueFamilies).

Part of: Short columns span; size of all conjugates of the chain (see New.Columns.LocalStatement).

This file: Determinant theta class sum: twist-free expansion and norm relation on adding a place.
Short integral algebraic forms span; ramified columns have nearly full dimension. Record of a good
finite datum: support, integrality, invariance, shape at N. The chain as a sum over classes;
good data are standard at p. Valuation gains of single lifts add along the chain with modified
data. -/
seal Finset.univ Finset.sum Finset.prod

open Module Finset Fintype Matrix MvPolynomial NumberField Representation Space Submodule Valued

variable {E : Type} (n : Type) [Field E] [CMType E] [WeilData E] [Fintype n] (α : AutChar E) (c :
  NumberField.InfinitePlace E → ℕ) (𝔪 : Modulus E) (ψ : (w : FinPlace E) → MulChar (ResField w) ℂ)

/-- The function h ↦ θ_{α,α}[Ψ, ∏_τ det^{c_τ}](1,h) of finite adelic h, for the pair (I_n, I_n)
and a function Ψ on matrices modulo 𝔪. -/
noncomputable def detKernel Ψ :=
  (modKernelI (stdSpace E n) α α 𝔪 Ψ (∏ τ, letterMinor τ id id ^ c τ) 1 ·)

/-- The class sum at level K₀ of `detKernel` for Ψ = χ∘det, χ the character modulo 𝔪 with
local components ψ. -/
noncomputable def detPeriod := stdClassSum (Kf ..) (detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det))

variable {n α c 𝔪 ψ}

/-- For a character α of weight −c, the function `detKernel` attached to α, c, 𝔪 and Ψ on the
finite adelic points of U(I_n) is invariant under left multiplication by rational points. -/
lemma detKernel_embFin_mul [h : α.HasWeight (-c ·) ψ] Ψ γ g : detKernel n α c 𝔪 Ψ (stdEmbFin γ * g)
  = detKernel n α c 𝔪 Ψ g := by simpa [stackedDetProd, stackedDet, ← det_submatrix_equiv_self (.symm
  (.emptySum ..)), ← modKernelBilin_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply,
  prod_ne_zero_iff] using! (twoSidedSubst_stackedDetProd
  (ι := (Fin <| c ·)) (.emptySum Empty n) 0 .. ▸ modKernel_embFin_mul h h _ _ _ 1 .. :)

/-- If α has tame part ψ trivial off 𝔪, then `detPeriod` is the class sum at level K₀ of g ↦
Σ_y `detKernel`(1₁)(gỹ), over y in GL_n(O_E/𝔪), with ỹ the lift `liftMod` and 1₁ the
indicator of the unit matrix. -/
lemma detPeriod_eq_stdClassSum_sum [h : α.HasWeight (-c ·) ψ] (hψ : ∀ w ∉ 𝔪.places, ψ w = 1) :
    detPeriod n α c 𝔪 ψ = stdClassSum (Kf E n) fun g ↦ ∑ y : GL n 𝔪.ResRing,
  detKernel n α c 𝔪 (Pi.single 1 1) (g * liftMod y) := by rw [detPeriod, pi_eq_sum_univ fun _ ↦ _,
  ← sum_of_injective _ Units.val_injective _ _ _ (by tauto)] <;> simp +contextual +unfoldPartialApp
  [detKernel, ← modKernelBilin_apply, ↓modKernel_mul_Kf_right, h.apply_det_eq_charOfTamePart hψ,
  -coe_units_inv, ← IsUnit.eq_1, MulChar.map_nonunit, isUnit_iff_isUnit_det]

open Fint in
/-- Let α have weight −c and tame part ψ trivial off 𝔪, and let 𝔪' have exactly one more prime
v. If X is the inverse of `AutChar.frobValue` α n v, then `detPeriod` for 𝔪' is ∏_{l<n}(1 −
q_v^l X) times that for 𝔪. -/
lemma detPeriod_insert {𝔪' : Modulus E} [h : α.HasWeight (-c ·) ψ] (hψ : ∀ w ∉ 𝔪.places, ψ w = 1) v
  (hv : v ∉ 𝔪.places) (hS : 𝔪'.places = insert v 𝔪.places) : detPeriod n α c 𝔪' ψ = trivialHecke v.q
  (card n) (α.frobValue n v)⁻¹ * detPeriod n α c 𝔪 ψ := have d := hS ▸ 𝔪'.disjoint_places_star
  have hw := d.notMem_of_mem_left (by simp) ∘ .inl
  have u := h.charUnramifiedAt (hψ v hv) (by simp_all)
  have l 𝔪 := by simpa [← RingHom.mapMatrix_apply, ← RingHom.map_det] using
    (liftFn_eq_residueDatum (𝔪 := 𝔪) Subtype.range_coe.symm fun S ↦ ∏ᶠ w, ψ _ (det (n := n) (S w)))
  have H P := (sum_heckePolyCoeff_smul_pairWeil u u hw (f := modDatum (stdSpace ..) (stdSpace E n) 𝔪
    (𝔪.charOfTamePart ψ ·.det) P) (by grind [modDatum, projOn_integrated, projOn_name_vacElem])
    _).1.trans (c := modDatum _ _ _ (𝔪'.charOfTamePart ψ ·.det) P) (by
    simp [modDatum, integrated_name]
    erw [inv_mul_cancel₀ (by simp [AutChar.frobValue, HeckeChar.atUnif]),
      ← name_union (S := {v}) _ d (by simpa)
      (hΨ := Set.range_const (ι := Unit) ▸ isSchwartzBruhat_residueDatum _ (by simpa)), l, l]
    simp +unfoldPartialApp [residueDatum, hS, Pi.mul_def, ← ite_and, finprod_eq_prod_of_fintype,
      reindex_equiv ((Set.equivOfEq hS).trans (Set.subtypeInsertEquivOption hv)).symm]
    congr!; bound; show _ = ψ v (det (.map _ (residueOrZero ∘ evalAt v)))
    erw [hψ v hv, MulChar.trivial_apply]
    split <;> simp_all [rank_of_isUnit, card_sub_rank, prod_eq_zero (i := 0), zero_lt_iff,
      coe_mulVecLin, LinearMap.ker_eq_bot, mulVec_injective_iff_isUnit, ↓← isUnit_iff_isUnit_det])
  have s {𝔪} (u : ∀ w ∉ 𝔪.places, ψ w = 1) : Kf .. ≤ rightStab
    (detKernel n α c 𝔪 (𝔪.charOfTamePart ψ ·.det)) := Subtype.forall'.2 (by simp [detKernel,
    modKernel_mul_Kf_right, Pi.smul_def, h.apply_det_eq_charOfTamePart u, ←map_mul, ← det_mul])
  by rw [detPeriod, stdClassSum, ← classIntegral_eq_classSum (s (by simp_all)),
    classIntegral_sum univ (.mulLeft <| heckePolyCoeff (α.frobValue n v)⁻¹ ·)
    (atSplit hw <| transposeGL <| basicCosetRep ·) fun _ ↦ ⟨Set.forall_mem_range.2
    (detKernel_embFin_mul _), Subgroup.isOpen_mono (s hψ) isOpen_Kf⟩] <;> simp [detKernel,
    modKernel, ← H, pairTheta, rep_apply_apply, detPeriod, classIntegral_eq_classSum (s hψ),
    ← sum_mul, ← card_ResField, by simpa using q_binomial_submodule n (ResField v) ⊤]

variable {E n : Type} [Field E] [CMType E] [Fintype n] {κ} {e :
  InfinitePlace E → ℤ} {P} (D : Data P) {j : ℕ} (w :
  D.piPlaces) {K} [IsLevel (E := E) (n := n) K] (ϑ)

/-- All values φ(g) are integral for Weyl's lattice at g at every p-adic embedding, and all
their conjugates under Aut(ℂ) have squared norm at most B. -/
def IsShort B (φ : AlgForm n κ e) := (∀ p [Fact p.Prime] [PadicPlace p], GaugeLe 1 1 φ) ∧
  ∀ (σ : ℂ ≃+* ℂ) g, weylNormSq (σ ∘ φ.1 g) ≤ B

lemma IsShort.sub_translate {B k} {φ : AlgForm n κ e} (h : IsShort B φ) (hk : k ∈ Kf ..) : IsShort
  (4 * B) (φ - algFormRep _ _ k φ) := ⟨fun p _ _ ↦ ((integralFormsAt ⊤ 1).sub_mem ⟨⟨⟩, h.1 p⟩
  ⟨⟨⟩, fun g ↦ by simpa [weylGauge_mul, Kf_le_localLevel hk] using h.1 p (g * k)⟩).2, fun σ g ↦ by
  have := weylNormSq_nonneg (σ ∘ (φ.1 g + φ.1 (g * k)))
  simp [weylNormSq, mulVec_sub] at *
  linarith! [h.2 σ g, h.2 σ (g * k)]⟩

open Norms.L2Operator in
/-- Let K be a level with trivial stabilisers, n ≥ 1, N ≥ 1 in the different of E, nf +
`boxes` κ n ≤ M, (6N(fn)²)^{6M} ≤ B (f infinite places). Then B-short forms span those
of weight (κ, e), level K. -/
lemma span_isShort_eq_top [Nonempty n] (free : ∀ g, classAut stdRatPoints K g = ⊥) {N M} [NeZero N]
  (h : ↑N ∈ differentIdeal ℤ (𝓞 E)) (hM : Fintype.card n * Fintype.card (InfinitePlace E) + boxes κ
  (Fintype.card n) ≤ M) {B} (hB : (shortBasisConst E n N : ℝ) ^ (6 * M) ≤ B) :
  span ℂ {φ : levelSpace (algFormRep κ e) K | IsShort B φ.1} =
  ⊤ := top_unique fun φ _ ↦ (freeLevelEquiv _ _ 1 free).3 φ ▸ sum_mem fun c _ ↦ by
  choose Y b hZ using exists_short_basis_stdSpace (n := n) h
  let A {R} [NormedField R] (f : ℂ →+* R) := (∏ τ, ((Y (c.out ^ e τ)).map
    (weightEmbedding f τ)).det) • weylRep κ 0 ((Y c.out).map <| weightEmbedding f ·)
  use (ker_mkQ _).le ((A (.id _)).mulVecLin.range_le_ker_iff (g := mkQ _ ∘ₗ deltaForm ..).2
    (PolyRep.ext_weylEval 0 (fun y o _ ↦ (ker_mkQ _).ge (subset_span ?_))
    ((Set.Ioi_infinite 0).preimage (⟨_, Complex.isPrimitiveRoot_exp · ·.ne' |>.eq_orderOf.symm⟩)))
    (mulVec_surjective_iff_isUnit.2 (((Group.isUnit _).map _).smul _) _))
  have m {R} [NormedField R] (f : ℂ →+* R) : f ∘ (A (.id _) *ᵥ weylEval n κ y) =
    A f *ᵥ weylEval n κ (f ∘ y)
    ∧ ∀ x, ‖f _‖ ≤ 1 := ⟨by simp [funext_iff, A, Units.smul_def, f.map_det, weylRep_map, weylEval,
    mulVec_apply_eq_sum, map_eval], fun x ↦ (f.isOfFinOrder (by simpa using o x)).norm_eq_one.le⟩
  use fun p _ _ g ↦ ?_, fun σ g ↦ ?_
  grw [mul_one, weylGauge_deltaForm_le (by simp)]; erw [weylGauge, (m _).1]; simp [weylRep,
    Units.smul_def, A,
    -map_inv, norm_smul, ← mul_assoc, ← prod_mul_distrib, ← map_zpow, -coe_units_zpow]
  grw [Finset.prod_le_one₀ (by bound) fun τ ↦ ?_, norm_schur_mulVec_le .refl fun τ ↦ by
    simpa [mul_apply] using (norm_adeleExtension_le_one (weightEmbedding ιₚ τ) <| b c.out · ·)]
  simpa [pi_norm_le_iff_of_nonneg, weylEval, ← map_nablaBasis (Int.castRingHom ℂ_[p]),
    -map_nablaBasis] using! fun _ ↦ eval₂_mem (s := NormedField.valuation.integer) (by simp) (m _).2
  simpa [mul_comm, ↓RingHom.map_det, Function.comp_def, -coe_units_zpow] using!
    norm_adeleExtension_le_one (weightEmbedding ιₚ τ) (b _).det_mem
  set R := (shortBasisConst E n N : ℝ)
  have r : Fintype.card n ≤ R :=
    Nat.mono_cast (Nat.le_of_dvd Fin.pos' (by simp [sq, Dvd.dvd.mul_left]))
  have : 1 ≤ R := Nat.one_le_cast.2 Fin.pos'
  choose ρ hρ H using weylNormSq_schur_le (κ := κ) .refl (PolyRep.squarePart (PolyRep.rowPos n) _)
  grw [weylNormSq_deltaForm_le (by simp)]; erw [free, (m σ.toRingHom).1, smul_mulVec,
    weylNormSq_smul]; simp [weylRep]
  grw [schur_mulVec_weylEval_of_detExp_zero .refl (by simp), ← PolyRep.schur_squarePart_mulVec, H,
    PolyRep.weylNormSq_weylEval_permArray, ← hB, ← hM]
  simp [pow_add, ← FitsRanks.refl.sum_diagramWeight_eq_boxes, ← prod_pow_eq_pow_sum, pow_mul,
    ← prod_pow, prod_prod_type, prod_range]
  erw [← prod_const]; gcongr
  grw [norm_det_le_norm_pow, l2_opNorm_le_of_apply (by apply hZ _ (weightEmbedding σ _)), ← sq,
    r]; linear_combination
  grw (transparency := default) [(NNReal.coe_mono (single_le_sum_of_canonicallyOrdered (by
    simp))).trans (hρ _), norm_sum_le, norm_mul_le, hZ _ (weightEmbedding σ _), (m σ.toRingHom).2]
  simp [field]; bound

/-- The representation of the norm-one finite adeles, acting by translation by scalar matrices,
on algebraic forms of weight (κ, e) on which J acts through χ. -/
noncomputable def algFormCentralRep {J χ} := subrepresentation ((algFormRep ..).comp (scalarFin n))
    (levelSpace (algFormRep κ e) J χ) fun _ _ ↦
  (map_mem_levelSpace_of_commute · fun _ ↦ (commute_scalarFin _).symm.map _)

namespace Data

lemma not_isChosen_of_N_mem {w} : ↑D.N ∈ w.1 → ¬D.IsChosen w ∧ ¬D.IsChosen (star w) := by
  grind [isChosen_iff, (D.nat_lt_of_hasLogBound.ne : D.g _ ≠ D.N), q_eq_g,
    P.q_eq_of_modEq_one D.N_modEq_one, q_star]

lemma mem_columnLevel {k} : k ∈ D.columnLevel j ↔ k ∈ chosenLevel ∧ ∀ w ∈ D.piPlaces, ∀ b,
  v (((k.atPlace w).1 - 1) (.inr ()) b) ≤ .exp
  (-1) := and_congr_right fun h ↦ (and_iff_right (levelOf_le_Kf h)).trans ((forall₂_congr fun _ _ ↦
  sub_one_mem_span_iff_atPlace (levelOf_le_Kf h)).trans (by grind [mem_piPlaces, intValuation_pi]))

lemma mem_chosenLevel_of_supportedOn {S} (h : ∀ w ∈ S, ↑D.N ∈ w.1) :
    Kf .. ⊓ Gf.supportedOn (D.X j) S ≤ D.chosenLevel := (inf_supportedOn_le_principalLevel
  (D.not_isChosen_of_N_mem <| h · ·)).trans (D.principalLevel_le_chosenLevel dvd_rfl)

/-- For a prime w dividing π there is an integral norm-one finite adele ν, equal to 1 at all
places other than w and w̄, such that every i with ν_w^i ≡ 1 modulo w is divisible by N −
1. -/
lemma exists_centralGen : ∃ ν : unitary _, (ν.1 ∈ Ô _ ∧ ∀ u ≠ w.1, star u ≠ w → ν.1 u = 1) ∧ ∀ i,
  v (ν.1 w ^ i - 1) < 1 → D.N - 1 ∣ i := ((LocInt _).surjective_unitGroupToResidueFieldUnits
  |>.exists.1 (@IsCyclic.exists_ofOrder_eq_natCard (ResField w.1)ˣ _ _)).elim fun x h ↦
  ⟨divStar (locIdele w x), by
  simp +contextual [coe_divStar, ← map_inv, mem_Ô, ← card_ResField, mem_idelesUnitOff.1
    (locIdele_mem_idelesUnitOff (S := ∅) _), (v.mem_unitGroup_iff ..).1 x.2,
    ← D.isSplitLevel_piPlaces.2 w, ← Nat.card_units,
    ← h, (ne_of_mem_of_not_mem _ (D.isSplitLevel_piPlaces.star_notMem _ w.2)).symm]
  use fun i b ↦ orderOf_dvd_of_pow_eq_one (Units.ext (residue_eq_iff_valuation_sub_lt_one.2 b))⟩

/-- A chosen integral norm-one finite adele, equal to 1 away from w and w̄, whose w-component
has order divisible by N − 1 (so generates the units) modulo w (`Data.exists_centralGen`). -/
noncomputable def centralGen := (D.exists_centralGen w).choose

lemma scalarFin_centralGen_mem n [Fintype n] : scalarFin n (D.centralGen w) ∈ maxCompactAt n w := by
  have := (D.exists_centralGen w).choose_spec.1
  simp_all [mem_Kf, Units.ext_iff, centralGen]; simp_all [scalarFin, diagonal_apply, ite_mem]

/-- The representation of the norm-one finite adeles U(1)(𝔸_f) on columns, by right translation
by scalar matrices. -/
noncomputable def centralRep : Representation ℂ (unitary (𝔸f D.E)) D.Column := algFormCentralRep

/-- For a set s of primes dividing π, the operator ∏_{w∈s}(1 − z_w) on columns, z_w the
translation by the scalar `Data.centralGen` at w. -/
noncomputable def ramifyingOp s :=
  D.centralRep.asAlgebraHom (∏ w ∈ s, (1 - .of _ _ (D.centralGen w)))

/-- The ramified columns: the image on columns of ∏_{w∣π}(1 − z_w), z_w the translation by the
scalar `Data.centralGen` at w. -/
noncomputable def ramifiedColumns := (D.ramifyingOp univ).range

/-- For each prime w dividing π, every ramified column φ has the form ψ − z_wψ for some column
ψ, where z_w acts by right translation by the scalar matrix of the central unit
`Data.centralGen` at w. -/
lemma exists_eq_sub_centralGen {φ} : φ ∈ D.ramifiedColumns → ∃ ψ : D.Column, φ.1 =
  ψ.1 - algFormRep _ _ (scalarFin _ (D.centralGen w)) ψ := fun ⟨_, h⟩ ↦
  ⟨_, by simp [← h, ramifyingOp, ↓prod_eq_mul_prod_compl w]; rfl⟩

lemma sum_height_mul_kappa_le τ : ∑ h ∈ range (Fintype.card (D.X 0)), h * D.κ τ h ≤ D.a := by
  grind [sum_eq_ite 1, card_X, n, κ]

lemma finrank_ker_one_sub_centralGen_le : finrank ℂ (1 - D.centralRep (D.centralGen w)).ker ≤
  (D.N - 1 : ℝ)⁻¹ * finrank ℂ D.Column :=
  let K := D.columnLevel 0 ⊔ .zpowers (scalarFin _ (D.centralGen w))
  have a : K ≤ _ := sup_le inf_le_left (by simp [D.mem_chosenLevel_of_supportedOn _
    (scalarFin_centralGen_mem ..), D.isSplitLevel_piPlaces.natCast_mem])
  have :=
    IsLevel.mk (a.trans levelOf_le_Kf) (Subgroup.isOpen_mono le_sup_left D.isLevel_columnLevel.2)
  (Subgroup.exists_pow_mem_of_relIndex_ne_zero (this.isCompact.relIndex_ne_zero
    D.isLevel_columnLevel.2) (Subgroup.zpowers_le.1 le_sup_right)).elim fun i ⟨o, b, e, _⟩ ↦ by
  grw [le_inv_mul_iff₀ (by simp [Fact.out]), ← Nat.cast_pred Fin.pos', ← finrank_map_subtype_eq,
    finrank_mono (t := levelSpace (smoothFormRep ..) K)
    (map_le_iff_le_comap.2 fun v h k ↦ by ext; simp [sup_le (c := rightStab v.1) (fun _ k ↦
    (by simpa using levelSpace_smoothFormRep_apply v.2 1 · ⟨_, k⟩)) (Subgroup.zpowers_le.2
    (congr($(sub_eq_zero.1 h).1.1 ·).symm)) k.2 _]), Nat.le_of_dvd o
    ((exists_centralGen ..).choose_spec.2 i (by simpa [← map_pow] using!
    ((D.mem_columnLevel.1 e).2 _ w.2 (.inr ())).trans_lt (by decide))), b]
  rify [finrank_levelSpace_smoothFormRep, classAut_columnLevel_eq_bot, card_classes_eq_classSum,
    classSum_one_of_le (K := K) le_sup_left, implies_true,
    D.classAut_eq_bot_of_le_chosenLevel a (by grind [card_X, n]), mul_assoc, le_rfl]

/-- Let T = ∏_{w∈s}(1 − z_w) (`Data.ramifyingOp`), s a set of primes dividing π. For a subspace p of
columns, dim T⁻¹p ≤ dim p + |s|·dim(columns)/(N − 1), and T makes B-short columns 4^{|s|}B-short. -/
lemma ramifyingOp_finrank_comap_and_short s p : finrank ℂ (Submodule.comap (D.ramifyingOp s) p) ≤
  finrank ℂ p + #s * (D.N - 1 : ℝ)⁻¹ *
  finrank ℂ D.Column ∧ ∀ B φ, IsShort B φ.1 → IsShort (4 ^ #s * B) (D.ramifyingOp s φ).1 := by
  induction' s using cons_induction with w s _ a generalizing p
  rw [(by simp [ramifyingOp] : D.ramifyingOp ∅ = 1)]; simp; rfl
  erw [card_cons, ramifyingOp, prod_cons, map_mul, map_sub, map_one, asAlgebraHom_of,
    p.comap_comp (D.ramifyingOp s)]
  use by grw [(a _).1, (by simpa [↓← finrank_eq_rank, ← Nat.cast_add] using
    (1 - D.centralRep (D.centralGen w)).lift_rank_comap_le :), Nat.cast_add,
    finrank_ker_one_sub_centralGen_le]; grind, by simpa [pow_succ', mul_assoc] using!
    ((a p).2 · · · |>.sub_translate (scalarFin_centralGen_mem ..).1)

/-- The ramified columns (`Data.ramifiedColumns`) are spanned over ℂ by those that are exp(fa(log
b)³)-short (`IsShort`): integral at every p-adic place, with all conjugates of all values of squared
norm at most that bound. -/
lemma span_short_ramifiedColumns : span ℂ {φ : D.ramifiedColumns | IsShort D.budget.exp φ.1.1} =
  ⊤ := comap_injective_of_surjective (D.ramifyingOp _).surjective_rangeRestrict (eq_top_mono
  (span_le.2 fun φ h ↦ subset_span (by simpa [card_piPlaces, mul_div_cancel₀] using!
  (D.ramifyingOp_finrank_comap_and_short univ ⊥).2 _ φ h))
  (span_isShort_eq_top D.classAut_columnLevel_eq_bot P.cycloConductor_mem_different (by grw [boxes,
  sum_height_mul_kappa_le]) (B := _ / 4 ^ D.f)
  (by simpa [le_div_iff₀', ↓card_X, n] using Real.le_exp_of_log_le D.le_of_hasLogBound)))

variable [Fact j.Prime] {Ψ : Data.Translations (P := P) (D := D) →₀ ℂ} (D' : Data P) {D : Data P}
  {p : ℕ} [Fact p.Prime] [PadicPlace p] {ϑ : D.Twist} {Ψ : Data.Translations (P := P) (D := D) →₀ ℂ}

/-- The sum over y mod N at the places dividing π of v_{2i} translated by last column −y/N, tensored
with v_{2i+1} translated by last row −conj(y/N) (`translateSum`). -/
noncomputable def pairTranslates (v : ∀ j, (homX j).finitePart) i :=
  translateSum _ _ D.piPlaces D.N _ (v (2 * i) ⊗ₜ v _)

/-- The tuples t such that, at each place w not dividing q, all entries of `piG`·t_k are integral,
so t_k itself is integral at w unless w or w̄ divides `Data.piGBar`. -/
def admissibleTranslations q := {t : D.Translations | ∀ k, t k ∈ translations _ q (star D.piGBar)}

/-- Ψ is a finite combination of tuples in `Data.admissibleTranslations` for q = N∏_{w∈Q} Nw, with
coefficients integral away from ∏ Nw, of total size at most exp(x^60) if Q is empty, jointly
invariant, whose chain of 2(ϱ+1) lifts equals the paired chain with data `Data.pairTranslates` of
the projections `Space.projOnFinPart`. -/
structure IsGoodDatum (ϑ : D.Twist) (Ψ) extends IsAdmissibleCoeffs
  (admissibleTranslations (ϑ.levelNorm * D.N)) ϑ.levelNorm 1 (ϑ.Q = ∅) (.exp (D.x ^ 60)) Ψ where
  joint_invariant : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support (Ψ · • .id) translateDatum
  chain_at_N φ : chainComb ϑ Ψ translateDatum _ φ = Ψ.sum fun x ↦ (· • chain₂ (D.liftKernel ϑ)
    (D.pairTranslates (projOnFinPart _ D.piPlaces <| D.translateDatum x ·)) (D.ϱ + 1) φ)

lemma notMem_piPlaces_of_ne (hp : j ≠ D'.N) {w} (hw : ↑j ∈ w.1) : ↑D'.N ∉ w.1 ∧
  star w ∉ D'.piPlaces := by simp_all [(D'.isSplitLevel_piPlaces.natCast_mem _).mt,
  Nat.prime_dvd_prime_iff_eq, Fact.out, w.natCast_mem_iff_dvd hw]

/-- Let x be a tuple of translations admissible away from q, and δ an integer of K. Then δx_j is
integral on any set S of places w prime to q where δ = `Data.piG` or the conjugate of w is not
chosen. -/
lemma mem_integralAfter {q x j δ S} (hx : x ∈ admissibleTranslations q) (h : ∀ w, S w → ↑q ∉ w.1 ∧
  (δ = D'.piG ∨ ¬D'.IsChosen
  (star w))) : x j ∈ Parameters.integralAfter δ S := fun i w a ↦ (hx j i w (h w a).1).trans' (by
  cases (h w a).2 <;> simp_all [IsChosen, w.valuation_eq_one_iff_notMem.2]
  rfl; exact mul_le_of_le_one_left' (w.valuation_le_one (algebraMap _ _ δ)))

lemma projOn_translateDatum (D : Data P) {x j S} (h :
  x j ∈ Parameters.integralAfter 1 (· ∈ Set.conjClosure S)) : projOn _ S (translateDatum x
  j).1 = (D.translateDatum x j).1 := by simp_all [translateDatum, projOn_finHeisOp,
  Parameters.intVacuum, mem_integralBox, idem_mul_mem_Ô, Parameters.integralAfter]

/-- The chain is a plain sum. Let ∑Ψ(x)⊗Φ_x be jointly invariant, each kernel multiply sizes N_j
by at most r_j ≥ 0, N_0(φ) ≤ B. Then ∑Ψ(x)·chain(Φ_x)φ(g) = ∑_i∑_x Ψ(x)β_i(⊗Φ_x), β_i
linear, one per tuple of classes, N_m(β_i(⊗Φ_x)) ≤ B∏r_j. -/
lemma exists_chain_eq_sum {Φ} (H : IsJointlyInvariant (D.liftKernel ϑ) D.m Ψ.support (Ψ · • .id) Φ)
  (N : ∀ _, _ → _ → ℝ) {r} (hr : ∀ j, 0 ≤ r j) (hs : ∀ x ∈ Ψ.support, ∀ j < D.m, ∀ g h v,
  N _ h ((D.liftKernel ϑ j).jetMatrix ((D.liftKernel ϑ j).ω (g, h) (Φ x j)) v) ≤ r j * N j g v) {φ :
  D.Column} {B} (hB : ∀ g, N 0 g (φ.1.1 g) ≤ B) g : ∃ β : Fin (∏ j ∈ range D.m, .card (StdClasses
  (D.columnLevel j))) → _ →ₗ[ℂ] _, (∀ i, ∀ x ∈ Ψ.support, N _ g (β i (TensorChain.pure (Φ x) _)) ≤
  (range D.m).prod r * B) ∧ ∑ i, ∑ x ∈ Ψ.support, Ψ x • β i (TensorChain.pure (Φ x) D.m) =
  (chainComb ϑ Ψ Φ D.m φ).1 g := by simpa [Finsupp.sum, ↓Set.mem_nsmul_iff_sum,
  Set.image, Classical.skolem, forall_and, ← _root_.funext_iff] using!
  (H.sum_chain_mem_nsmul _ (fun j h ↦ D.classAut_eq_bot_of_le_chosenLevel
  inf_le_left (by grind [card_X, D.n_mono h.le])) φ.2 (fun j ↦ (N j · · ≤ (range j).prod r * B))
  (by intros; grw [hs, prod_range_succ_comm, mul_assoc] <;> bound) (by simpa) (Set.mapsTo_image ..))

lemma IsGoodDatum.translateDatum_mem_standardData (H : IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm)
  (hp : p ≠ D.N) {x} (hx : x ∈ Ψ.support) j {δ} (h : δ = D.piG ∨ ¬p ∣ D.gProd) :
  (translateDatum x j).1 ∈ Parameters.standardData _ δ := subset_span ⟨_, D.mem_integralAfter
  (H.support_subset x hx) fun w _ ↦ by simp_all [← piGBar_mul_star, IsChosen,
  ← w.natCast_mem_iff_dvd, w.2.mul_mem_iff_mem_or_mem, D.notMem_piPlaces_of_ne hp,
  or_and_left, -Nat.cast_prod, w.2.notMem_of_isCoprime_of_mem hQ.cast], rfl⟩

/-- Let Ψ be good, twist primes prime to p, and t_j operators commuting with the levels on the
data. If each modified datum multiplies gauges by at most p^{r_j} from d_j to d_{j+1}, the
modified chain sends columns integral at d_0 to forms of gauge ≤ p^{∑r_j} at d_m. -/
lemma IsGoodDatum.gaugeLe_chain (H : IsGoodDatum ϑ Ψ) (hQ : p.Coprime ϑ.levelNorm) (t : ∀ _,
  End ℂ _) (ht : ∀ᵉ (j) (x ∈ Ψ.support) (a : D.columnLevel j) (b ∈ D.columnLevel _),
  (D.liftKernel ϑ j).ω (a, b) (t j (translateDatum x j)) = t j ((D.liftKernel ϑ j).ω (a,
  b) (translateDatum x j))) (d : ∀ _, _) {r : ℕ → ℝ} (h : ∀ᵉ (x ∈ Ψ.support) (j < D.m),
  t j (translateDatum x j) ∈ (D.liftKernel ϑ j).raises (d j) (d _) (p ^ r j)) {φ : D.Column} (hφ :
  GaugeLe (d 0) 1 φ.1) : GaugeLe (d _) (p ^ ∑ j ∈ .range D.m,
  r j) (chainComb ϑ Ψ (fun x j ↦ t j (translateDatum x j)) D.m φ) := (exists_chain_eq_sum
  (by simpa +contextual [*] using H.joint_invariant · · <| · ∘ₗ TensorChain.map ..)
  (fun j g ↦ weylGauge _ (D.lastEntry j) (g * d j)) (by simp) h hφ · |>.rec fun _ b ↦ b.2 ▸ by
    repeat grw [weylGauge_sum_le]; bound; intros
    grw [weylGauge_smul, b.1, ← one_nsmul (Ψ _), nsmul_eq_mul, H.integral _ _ hQ] <;>
      simp [Real.rpow_nonneg, Real.rpow_sum_of_pos, NeZero.pos, *])

lemma norm_star_piG_le_one :
    ‖ιₚ (star D.piG)‖ ≤ 1 := norm_le_one_of_isIntegral (ιₚ.comp (starRingEnd _)) D.piG.2.algebraMap

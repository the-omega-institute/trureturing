/- GID: D5/S3/Zeros/GRH/New/Filling/FixedLines
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/FixedLines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.FixedLines. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/FixedLines.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.GlobalToLocal
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: A group Z between K(g) and K for which `Level.floorZeroForm` Z, divided by the measure of
Z, is smaller than for K by b^(6|κ|) for each given place above q₀ where a frame vector is fixed. -/

open Pi Subgroup Classical ENNReal Finset Fintype Matrix MeasureTheory IntegralPlace

namespace Filling

variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} [S.IsAdmissible] {T T₀ :
  Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)] {F} [h :
  S.IsFillingLevel T F] (Sg : Finset (S.chosenPlaces 0))

omit [S.IsAdmissible] in
/-- If every place of T is a chosen place above g or the conjugate of one, then b⁹ ≥ 2 and the
non-units of the integers R at T have volume at most b⁻⁹. -/
lemma volume_nonunits_le (k : T ⊆ univ.biUnion fun p : Σ i, S.chosenPlaces i ↦
  {p.2.1, star p.2.1}) : 2 ≤ ENNReal.ofReal (S.b ^ 9) ∧
  volume (P.R \ P.intUnits) ≤ (.ofReal (S.b ^ 9))⁻¹ := by
  have b := S.thousand_le_b
  refine ⟨by grw [← b]; bound, .trans' ?_ (measure_mono_ae (t := ⋃ w, {x | (MulEquiv.piUnits.symm
    (mulSingle w (uniformizer _)) : (LocProd T)ˣ)⁻¹.1 * x ∈ R}) (P.ae_isUnit.mono fun x ⟨y, u⟩ ⟨a,
    n⟩ ↦ by_contra (n ⟨a, y, mem_O_locProd.2 fun j ↦ by_contra fun _ ↦ · ⟨_, ⟨j, rfl⟩,
    mem_O_locProd.2 fun i ↦ by obtain rfl | _ := (eq_or_ne i j) <;> simp_all [mem_O_locProd,
    v_uniformizer_inv_mul_le_one_iff, -map_mul, one_lt_inv_iff₀]⟩, u⟩)))⟩
  grw [measure_iUnion_fintype_le, sum_le_card_nsmul _ _ (.ofReal (S.b ^ 10)⁻¹) fun w _ ↦ ?_,
    card_univ, card_coe, k, card_biUnion_le_card_mul _ _ 2 (by grind),
    ← ofReal_nsmul, ← ofReal_inv_of_pos (by bound)]
  gcongr; simp [S.card_chosenPlaces, field]; bound [S.f_le_b]
  rw [volume_setOf_mul_mem, md_eq_inv_genIndex, genIndex_eq_inv_prod_norm,
    Fintype.prod_eq_single w] <;> simp +contextual [norm_locField_eq_q_zpow, -FinPlace.q_bounds]
  cases' mem_biUnion.1 (k w.2) with p; grw [S.le_levelPrime p.1]; grind [chosenPlaces_q, q_star]

/-- Let 1/g be integral off T₀, and T = T₀ ∩ {w, w̄} if o is a place w ∈ Sg. Some K(g) ≤ Z ≤ K
over T contains k_T for all k reducing into `Filling.fixingSet` Sg d, and kk(Z)·M(K)·c ≤
kk(K)·M(Z), where c = b^(6|κ|), or 1 if o is empty; kk = `Level.floorZeroForm`,
M = `Level.groupMeasure`. -/
lemma IsFillingLevel.exists_intermediateGroup_one_prime (o : Option Sg) d (hT :
  ↑S.gIdele⁻¹ ∈ integralOff T₀) (f : ∀ w ∈ o, ∀ j, j ∈ T ↔ j ∈ T₀ ∧ (j = w
  ∨ star j = w)) : ∃ Z : F.IntermediateGroup,
  (∀ k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ let K := unitaryLevel R 1 _
  F.floorZeroForm Z * F.groupMeasure K * o.elim 1 (fun _ ↦ .ofReal (S.b ^ (6 * 𝔰.k))) ≤
    F.floorZeroForm K * F.groupMeasure Z := by
  let p := (S.toPlaces T).comp S.latStabilizer.subtype
  have r : p.range = unitaryLevel R 1 _ :=
    ext (exists_toPlaces_eq · |>.elim (by simp [p, mem_latStabilizer_iff (T := T)]; aesop))
  obtain _ | ⟨w, m⟩ := o
  use ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩; simp [← r, p]
  obtain ⟨c, o, B⟩ := S.pow_chain, S.one_le_b, S.volume_nonunits_le (by aesop_cat : T ⊆ _)
  let H := (vectorFixer w (d w)).comap S.reduction
  have z r := by simpa [-reduceAt_eq_zero, ← mul_smul_comm, idem_mul_mem_Ô, reduceAboveG] using
    ((S.inv_gIdele_smul_mem_iff (⟨_, idem_mem_Ô {w.1}⟩ * r)).1 · (⟨0, w⟩, false))
  have q : F.congGroup.comap p ≤ H :=
    fun k e ↦ by simp [H, vectorFixer, show S.reduction k .. = 1 from intGL.map_eq_one.2 fun i j ↦
    z _ (by simpa [h.g_eq, apply_ite, ite_apply] using! e.2 i j ⟨w, by_contra
    fun _ ↦ by simpa [Units.smul_def, (mem_integralOff _).1 hT w (by aesop)] using z 1⟩ ⟨⟩)]
  let Z : F.IntermediateGroup := ⟨H.map p, by grw [← q,
    map_comap_eq_self (r ▸ unitaryLevel_le_unitaryLevel_one)], r ▸ H.map_le_range _⟩
  use Z, (⟨·, ·.1 w m, rfl⟩)
  intro K
  -- Z and the non-units are rare, so the form is small against that of K
  nth_grw 1 [Option.elim, pow_le_pow_right₀ o (?_ : _ ≤ 9 * _), pow_mul, ofReal_pow (by bound),
  h.floorZeroForm_le_main_term Z (𝔰.k - 10 ^ 10 * 𝔰.n ^ 4) (by omega), B.2,
    h.inv_two_pow_le_groupMeasure B, mul_right_comm, mul_assoc _ (_ + _),
    (?_ : (_ + _) * _ ≤ F.groupMeasure K), Level.floorZeroForm, ← setLIntegral_le_lintegral,
    h.floorZeroForm_on_congGroup ⟨K, unitaryLevel_le_unitaryLevel_one, le_rfl⟩]
  ring; rfl
  grw [← ENNReal.mul_le_mul_iff_left two_ne_zero (by simp), mul_two (F.groupMeasure K), B.1,
    mul_assoc, ← pow_succ, add_mul, mul_comm, (?_ : _ * _ ≤ F.groupMeasure K), mul_right_comm,
    ← mul_pow, ENNReal.inv_mul_le_one, one_pow, one_mul]
  grw [← relIndex_mul_measure_inf unitaryLevel_open_compact.2 Z.isOpen, inf_of_le_left Z.2.2, ← (r ▸
    index_comap _ p :), comap_map_eq_self (q.trans' (p.ker_le_comap _)), index_comap_of_surjective _
    IsAdmissible.reduction_surjective, vectorFixer, index_comap_of_surjective _ fun g ↦ ⟨mulSingle 0
    (mulSingle w ((S.idOrInvAdjoint (d w).1).symm g)), by simp⟩, index_stabilizer_GL_vector
    (by simpa using (inclMatrix_mulVecLin_injective ⟨_, besselFrame_injective⟩ _).ne (d w).2.2),
    card_resField_eq_levelPrime, Nat.le_succ 9, le_levelPrime]; gcongr
  exact_mod_cast
    (pow_lt_pow_right₀ (S.levelPrime_prime 0).1.one_lt (by simp; clear * - c; lia)).le_pred
  omega

/-- Let Sg be a set of chosen places above q₀, and 1/g integral off T. Some group K(g) ≤ Z ≤ K
contains k_T whenever k reduces into `Filling.fixingSet` Sg d, and kk(Z)·M(K)·b^(6|κ||Sg|) ≤
kk(K)·M(Z), kk = `Level.floorZeroForm`, M = `Level.groupMeasure`. -/
lemma IsFillingLevel.exists_intermediateGroup_lines [WeilData E]
    d [hT : Fact (↑S.gIdele⁻¹ ∈ integralOff T)] :
  ∃ Z : F.IntermediateGroup,
  (∀ k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ let K := unitaryLevel R 1 _
  F.floorZeroForm Z * F.groupMeasure K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg ≤
    F.floorZeroForm K * F.groupMeasure Z := by
  choose f hf using show ∀ w, ∃ o, ∀ s : Sg, o = some s ↔ w = s.1.1 ∨ star w = s by
    simp [Option.exists]; grind [star_notMem_chosenPlaces]
  let T' i := {w ∈ T | f w = i}; have _ i : (T' i).StarStable :=
    ⟨by simp +contextual [T', fT.1, hf, or_comm, @Option.ext_iff _ _ i]⟩
  let e i : LocProd T →+* LocProd (T' i) := .pi fun w ↦ evalRingHom _ (⟨w, by grind⟩ : T)
  have A {p : T → Prop} : (∀ w, p w) ↔ ∀ i (w : T' i), p ⟨w, by grind⟩ := by aesop
  choose P' F' h' using (S.exists_isFillingLevel <| T' ·)
  choose Z b c using fun i ↦ (h' i).exists_intermediateGroup_one_prime Sg i d hT.1 (by aesop)
  let φ := MonoidHom.pi fun i ↦ U.map (e i) (by tauto) (S.map_splitGram_latMiddle _)
  have ψ x : S.charOnPlaces T x = ∏ i, S.charOnPlaces _ (e i x) := by
    with_unfolding_all refine
      (congrArg S.selfDualChar ?_).trans (map_sum S.selfDualChar.toAddMonoidHom ..)
    ext1 w; erw [map_sum (evalAt w)]; show dite .. = ∑ i, dite ..; split <;> simp [T', e, *]
  have su : (⇑φ).Surjective := fun y ↦ by
    let M := of fun a b (w : T) ↦ (y (f w)).1.1 a b ⟨w, by simp [T']⟩
    have k i : M.map (e i) = (y i).1.1 := by ext a b ⟨w, k⟩; cases (mem_filter.1 k).2; rfl
    refine ⟨U.of IsHermUnit.isUnit M (funext₃ fun a b ↦ A.2 fun i w ↦ ?_), by ext : 3; apply k⟩
    simpa [← k, ← S.map_splitGram_latMiddle (e i),
      ← map_conjTranspose_mul_mul (e i) (by tauto)] using! congr($((y i).2) a b w)
  have em := (continuous_pi (f := φ) fun i ↦ by
    simpa [φ] using! U.continuous_map (continuous_precomp' _)).measurableEmbedding
    fun x y k ↦ by ext : 3; exact funext (A.2 fun i w ↦ congr(($k i).1.1 _ _ w))
  let Q Z := (Subgroup.pi .univ Z).comap φ
  have K u : unitaryLevel R u _ = Q fun i ↦ unitaryLevel R (u.map (e i)) _ := by
    ext; simp [Q, unitaryLevel, Subgroup.mem_pi, mem_intGL, IsIntMatrix, mem_O_locProd, ↓A,
      Units.smul_def, forall_and, ite_apply, -coe_units_inv, -Sum.forall, ↓@forall_comm (Option _)]
    rfl
  have B x : x ∈ besselU ↔ ∀ i, φ x i ∈ besselU := by simp [mem_besselU, φ, U.map,
          funext_iff, ↓A, e, ite_apply, @forall_comm (Option _), -Sum.forall]
  have w a x : phase a x = ∏ i, phase (a.map (e i)) (φ x i) := by
    by_contra! n; obtain ⟨u, hu, k⟩ := (n.ne_or_ne 0).elim exists_besselU_of_phase_ne_zero
      fun k ↦ by simpa [*, Q, Subgroup.mem_pi, forall_and, ↓skolem, su.exists] using!
      (exists_besselU_of_phase_ne_zero <| prod_ne_zero_iff.1 k · (by simp))
    simp [phase_eq hu k, h.psi_eq, (h' _).psi_eq, ψ, simpleRootSum, φ,
      U.map, -Units.val_inv_eq_inv_val, ↓fun i ↦
      phase_eq (y := φ x i) ((B u).1 hu i) (by simpa using! (K _).le k i ⟨⟩)] at n
  have _ i := (h' i).isHaarMeasure_groupMeasure.sigmaFinite
  obtain ⟨t, ht⟩ := exists_eq_smul_haar (.pi (F' · |>.groupMeasure)) ⟨su.forall.2 fun g ↦
    ((em.2.measurePreserving
    F.groupMeasure).of_semiconj (measurePreserving_mul_right _ g) (map_mul _ · g) (by fun_prop)).2⟩
  have H Z : F.floorZeroForm (Q Z) = ‖t.toReal‖ₑ ^ 2 * t * ∏ i, (F' i).floorZeroForm (Z i) ∧
      F.groupMeasure (Q Z) = t * ∏ i, (F' i).groupMeasure (Z i) := by
    simp [Q, ← em.map_apply, ht, coe_pi, Level.floorZeroForm, enorm, -prod_option]
    rw [← lintegral_pi_prod _ (by fun_prop), mul_assoc, ← smul_eq_mul t, ← lintegral_smul_measure,
      ← ht, em.lintegral_map, ← lintegral_const_mul' _ _ (by simp)]
    norm_cast
    simp_rw [prod_pow, ← mul_pow, ← nnnorm_prod, ← nnnorm_smul, ← integral_fintype_prod_eq_prod,
      ← integral_smul_measure, ← Measure.restrict_pi_pi, ← Measure.restrict_smul, ← ht]
    simp [em.setIntegral_map, w, g_eq]; rfl
  use ⟨Q (Z ·), ?_⟩ <;> simp only [K, map_one, H, mul_mul_mul_comm _ _ t, ← prod_mul_distrib]
  use fun k j i _ ↦ b i k j, by grw [← prod_le_prod' fun i _ ↦ c i]; simp [mul_assoc]
  constructor <;> intro _ k i <;> cases (Z i).2 <;> simp only [Level.congGroup, g_eq] at * <;> tauto

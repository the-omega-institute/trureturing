/- GID: D5/S3/Zeros/GRH/New/Exchange/StandardCoefficients
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/StandardCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.StandardCoefficients. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/StandardCoefficients.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.ExchangeDifference
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.EquivariantCoefficients
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Exchange theorem for theta integrals of complementary rank (see
New.Exchange.ExchangeTheorem).

This file: If coefficients at unimodular indices vanish, all standard ramified data are killed. -/

open G Gf MatMul Matrix RingHom SemilocalField WeilData Space.Splitting

attribute [local simp] conjTranspose_nonsing_inv isUnit_iff_isUnit_det Matrix.map_neg map_smul'
  Units.smul_def add_mul mul_add mul_assoc mul_sub smul_smul star_idem star_invDifferentIdele_inv

/-- Assume `IsEquivariantLift` for M, 𝒟, nested adapted splittings, the standard Ψ of the frame in
M, and that ȷT-coefficients of 𝒟Ψ vanish on the parabolic for T = J_{V′} at unimodular
lattices and for invertible T off the real class of V′. Then 𝒟 kills every standard datum of
an integral z. -/
lemma IsEquivariantLift.apply_stdColDatum_eq_zero {E} [Field E] [CMType E] [H : WeilData E] {n a b
  m} [Fintype n] [Fintype a] [Fintype b] [Fintype m] {s t r μ} {𝔠 : SplitTameChar E μ} {ρ} {X :
  Space E m r} {W₁ : Space E n s} {W : Space E a t} {M 𝒟} (h : IsEquivariantLift 𝔠 X ρ M 𝒟) (D :
  X.Splitting W₁ b) (D₁ : W₁.Splitting W Unit) [IsBaseAdapted D] [IsBaseAdapted D₁] {t'} (V' : Space
  E b t') (h₀ : ∀ T c z q g, (∃ Y, ∃ k ∈ intGL b (Ô E), scaleIdele E • V'.x * Y = q ∧ Y.map (.snd
  ..) * k ∈ U 1 ∧ V'.J = T) ∨ IsUnit T ∧ ¬RepresentedBy t' (T.map toAdele) → D.centreCoeff (H.j • T)
  (𝒟 (stdColDatum 𝔠.χ (adaptedFrame 𝔠.readsAt D).L')) (D.radicalElt c z * D.levi (q, g)) = 0) (hΨ :
  stdColDatum 𝔠.χ (adaptedFrame 𝔠.readsAt D).L' ∈ M) (σ : b ⊕ b ⊕ n ≃ m) {z} (i : IsIntMatrix O z) :
  𝒟 (stdColDatum 𝔠.χ z) = 0 := ((adaptedFrame 𝔠.readsAt D.symm).partner_mem_of_unimodular_vanishing
  h.comp_mul_mem_ker (fun _ ↦ (h.le_schwartzBruhat ·.1)) (stdColDatum_mem_schwartzBruhat _ i).1
  (isPartner_stdRowDatum_stdColDatum σ i) 𝔠.readsAt.hasIntegralConductor_psi
  (by simpa using! ((h.exists_linear_centreCoeff D 0 1).choose_spec _ hΨ).2 · |>.1) fun Ψ w c ↦
  have k := h.isAutFunction w; ⟨w, funext ((X.weak_approximation 𝔠.S.finite_toSet).eq (fun ⟨γ, g,
    hg⟩ ↦ .trans (by simp [k.2]) (IsDualFamily.eq_zero_of_coeff (D.isContPeriodic_radicalCentre k
    (1, g)) (fun T p ↦ (h.exists_linear_centreCoeff ..).elim fun _ L ↦ (L _ w).1.symm.trans
    (c _ _ (by simpa [-map_smul', atPlaces_of_mem_trivialOn hg, fun x ↦ (id rfl : (mat x).map
    (componentsAt 𝔠) = (atPlaces _ _).1)] using! (L _ hΨ).2 · |>.2) fun P ↦ (L _ hΨ).1.trans (by
obtain ⟨hT, a, d, A, _, e', -⟩ := eq_neg_of_add_eq_zero_left (isDualFamily_ratMatrices.6 (Tᴴ + T)
  fun X ↦ by simpa [↓isDualFamily_ratMatrices.2, ↓isDualFamily_ratMatrices.3,
  ← stdAddChar_half (trace _), ← trace_conjTranspose, add_comm,
  X.trace_mul_comm, Xᴴ.trace_mul_comm] using p (Xᴴ + X) 1 (by intro; simp; congr! 2; exact
  (ext_mat (by simp [add_sub_add_comm])))), h.isAutFunction hΨ, (by simpa [← mapMatrix_apply,
  ← map_det, ·] using (isPrimitiveMatrix_iff_isIntegralUnit_det.1 P).2 : T.det ≠ 0),
  exists_isBaseAdapted_stage (D.comp D₁) (.sumComm ..)
refine freitag (supportedOn_compl.substr (h.law_off _ hΨ)) a A _ congr(toCols₂ $(congr(_ * ($e').map
  _).symm.trans (comp_kAdelic ..))) d (.star 𝔠.nonempty) (fun A e g w _ ν _ _ p q ↦
  (h.exists_linear_centreCoeff ..).elim fun _ l ↦ have k : (adaptedFrame 𝔠.readsAt D).L' =
    ((removePlanes b W).lCoord * A.iCoord * (ν * g).mat).map (componentsAt 𝔠) := ?_; .trans (l _
    hΨ).1.symm ((h.centreCoeff_shear _ _ hΨ (by simpa [Prod.star_def] using q) p _).elim fun a c
  ↦ shear_invariant (adaptedFrame _ D).blocks_spec.1 ?_ h.le_schwartzBruhat (fun Ψ a z ↦ ?_) hΨ a ▸
    (l _ a).1 ▸ c.trans (by simp))) (fun x γ
  v ⟨y, _, y', _⟩ ↦ ?_) (by clear * -; aesop (add simp idem_apply)) (supportedOn_compl.ge hg)
funext i j ⟨u, h⟩
simpa [lCoord.eq_1 D, componentsAt, adaptedFrame, 𝔠.star_notMem, *, ↓mat_preserves_stdForm] using
  congr((($wᴴ * stdForm E r * g.mat) i j).2 u)
simp [*, ← Matrix.map_mul, ← mat_mul, ← (mat _).mul_assoc]
simpa [k, trace, mul_apply, comp_kAdelic] using ((l _ a).2 ((fromCols 0 z).fromRows 0)).2
let τ := (invDifferentIdele E)⁻¹ • (GeneralLinearGroup.mkOfDetNeZero T d).map toAdele
obtain ⟨hτ, l, z, q, g, rfl, o⟩ := (by simp [*, τ] : τ.1ᴴ = τ), D.exists_eq_radicalElt_mul_levi v
have i {M N : Matrix b ..} (hN : Nᴴ = N) (a : IsIntMatrix (closureIntegers _) M) (c :
  IsIntMatrix O (N.map (componentsAt 𝔠))) : let e : 𝔸 E := idemAdele (Set.conjClosure
    𝔠.S)ᶜ.conjClosure; IsIntMatrix (Ô E) ((e • M + (1 - e) • N).map Prod.snd) :=
  fun i j ↦ add_mem (a i j) (by simpa [← idem_compl, idem_mul_mem_Ô] using (fun v h _ ↦ by_cases
  (c i j ⟨v, ·⟩ ⟨⟩) fun l ↦ hN ▸ (v_star_apply ..).trans_le (c j i ⟨_, h l⟩ ⟨⟩)))
have ⟨k, K, e⟩ := exists_orthonormal_Ô ⟨by simp [← conjTranspose_map _ Prod.snd_star,
  siegelBracket, *], isPrimitiveMatrix_iff.1 ⟨i hτ y P.1, _,
  i ?_ y' ((isPrimitiveMatrix_iff_mem_intGL (τ.map _)).1 P).isIntMatrix_inv, ?_⟩⟩
rw [show _ + _ = siegelBracket T q.1 by simp [o, siegelBracket, τ, mul_comm], siegelBracket] at e
obtain ⟨⟨β, rfl⟩, q, rfl⟩ := MulAction.surjective₀ H.j_ne_zero T,
  MulAction.surjective (scaleIdele E) q
simp [show scaleIdele E * (toAdele H.j * star (scaleIdele E).1) =
  invDifferentIdele E by simp [invDifferentIdele, mul_left_comm]] at d e ⊢
by_cases R : RepresentedBy t' (β.map toAdele)
obtain ⟨c, w, rfl : _ = β, f, -⟩ := V'.exists_eq_move ⟨β, _, gram_mkAdelicGL (b := q.map (.snd ..) *
  k) (fun v ↦ gram_inv_of_gram_eq (x := (isUnit_of_mul_isUnit_right ((R v).choose_spec.substr
  (.map (mapMatrix _) (by simpa)))).unit) (R v).choose_spec) (by simpa [← coe_snd] using! e)⟩
rw [← smul_mul, ← mul_smul_comm, ← centreCoeff_rat_mul _ a _ (levi_mem_Γ _ _ (one_mem _)) _
  (levi_mul_kAdelic ..), ← mul_assoc, levi_conj_radicalElt, mul_assoc, ← map_mul, h₀]
refine .inl ⟨V'.x⁻¹ * (c.map toAdele * q), _, K, Units.ext (by simp), ?_, rfl⟩
convert w.2.2; simpa using! congr($(inv_mul_eq_of_eq_mul f).map _)
all_goals simp [← coe_snd, ← Matrix.map_mul, sub_mul, *]))) 0)) k.1)⟩).2

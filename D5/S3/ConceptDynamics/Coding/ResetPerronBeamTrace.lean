/- GID: D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetPerronBeamTrace
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Original Reset beam Perron trace excludes negative scalar history actions. -/
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
import D5.S3.TotalVariation.ParryResetLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetPerronBeamTrace
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S3.TotalVariation.TwistedResetPaths (suffixWeight)
open D5.S3.TotalVariation.ParryResetLaw
open ResetNumberedHistories ResetStandardBeamGeometry
open StandardBeamGeometry StandardBeamCoordinates StandardBeamEndpointRows StandardBeamColimitCuts
open InertGroupBlockConjugacy
  (DimensionGroup VertexModule transition vertex stationaryTransition groupAction)
open scoped BigOperators Matrix

local instance originalNativeIntModule (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

abbrev beta (q : ℕ) := dbonacciPerronRoot q

def weight (q : ℕ) (i : Fin q) : ℝ := suffixWeight q (beta q)⁻¹ i

private lemma beta_pos (q : ℕ) (hq : 2 ≤ q) : 0 < beta q :=
  lt_trans zero_lt_one (one_lt_dbonacciPerronRoot q hq)

private lemma weight_pos (q : ℕ) (hq : 2 ≤ q) (i : Fin q) : 0 < weight q i := by
  have h := parry_stationary_law q hq
  have hp : 0 < parryParameter q := by linarith [h.1.1]
  simpa [weight, parryParameter, hq] using lt_of_lt_of_le hp (h.2.1 i).1

private lemma weight_zero (q : ℕ) (hq : 2 ≤ q) : weight q ⟨0, by omega⟩ = 1 := by
  have h := (parry_stationary_law q hq).1.2.2
  simpa [weight, suffixWeight, rootSum, parryParameter, hq] using h

/-- Both absolute Sign labels receive the same suffix weight. -/
def rowWeight (q : ℕ) : (Fin q × Sign → ℤ) →ₗ[ℤ] ℝ where
  toFun v := ∑ p, (v p : ℝ) * weight q p.1
  map_add' v w := by simp [Int.cast_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [Int.cast_mul, mul_assoc, Finset.mul_sum, zsmul_eq_mul]

private lemma rowWeight_single (q : ℕ) (p : Fin q × Sign) :
    rowWeight q (Pi.single p 1) = weight q p.1 := by
  classical
  simp [rowWeight, Pi.single_apply]

private lemma rowTransition_single (q : ℕ) (hq : 2 ≤ q) (i : Fin q) (g : Sign) :
    rowTransition (ResetGraph q) (Pi.single (i,g) 1) =
      Pi.single (⟨0, by omega⟩, g * Multiplicative.ofAdd true) 1 +
      if hi : i.val + 1 < q then Pi.single (⟨i.val+1,hi⟩,g) 1 else 0 := by
  classical
  rw [graph_rowTransition_eq]
  funext p
  rcases p with ⟨j,t⟩
  change NativeIntegralRowTransport.rowTransition (resetMatrix q)
    (NativeIntegralRowTransport.rowVertex i g) (j,t) = _
  rw [NativeIntegralRowTransport.rowTransition_vertex]
  rw [matrix_coefficient]
  by_cases hi : i.val+1 < q
  · simp only [dif_pos hi, Pi.add_apply]
    by_cases hj : j.val = 0 <;> by_cases hs : j.val = i.val+1 <;>
      by_cases ht : t = g * Multiplicative.ofAdd true <;> by_cases hg : t = g
    all_goals simp_all [Pi.single_apply, Prod.ext_iff, Fin.ext_iff, inv_mul_eq_iff_eq_mul]
  · have hs : j.val ≠ i.val+1 := by omega
    simp [hi, hs, Pi.single_apply, Prod.ext_iff, Fin.ext_iff, inv_mul_eq_iff_eq_mul, eq_comm]

/-- Actual right-row transition compatibility, with no change of matrix orientation. -/
theorem rowWeight_transition (q : ℕ) (hq : 2 ≤ q) (v : Fin q × Sign → ℤ) :
    rowWeight q (rowTransition (ResetGraph q) v) = beta q * rowWeight q v := by
  classical
  have he : (rowWeight q).comp (rowTransition (ResetGraph q)) = beta q • rowWeight q := by
    apply (Pi.basisFun ℤ (Fin q × Sign)).ext
    intro p
    rcases p with ⟨i,g⟩
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    change rowWeight q (rowTransition (ResetGraph q) (Pi.single (i,g) 1)) =
      beta q * rowWeight q (Pi.single (i,g) 1)
    rw [rowTransition_single q hq, map_add, rowWeight_single, weight_zero q hq,
      rowWeight_single]
    have hb := (beta_pos q hq).ne'
    by_cases hi : i.val+1 < q
    · rw [dif_pos hi, rowWeight_single]
      have hr := suffixWeight_succ q (beta q)⁻¹ i hi
      change weight q i = (beta q)⁻¹ + (beta q)⁻¹ * weight q ⟨i.val+1,hi⟩ at hr
      rw [hr]
      field_simp
    · rw [dif_neg hi, map_zero, add_zero]
      have hr := suffixWeight_last q (beta q)⁻¹ i hi
      change weight q i = (beta q)⁻¹ at hr
      rw [hr, mul_inv_cancel₀ hb]
  exact LinearMap.congr_fun he v

private lemma rowWeight_power (q : ℕ) (hq : 2 ≤ q) (n : ℕ) (v : Fin q × Sign → ℤ) :
    rowWeight q ((rowTransition (ResetGraph q) ^ n) v) = beta q ^ n * rowWeight q v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, rowWeight_transition q hq, ih, pow_succ]
    ring

private def weightedStage (q N : ℕ) : (Fin q × Sign → ℤ) →ₗ[ℤ] ℝ :=
  beta q ^ (-(N : ℤ)) • rowWeight q

private lemma weightedStage_compatible (q : ℕ) (hq : 2 ≤ q) (i j : ℕ) (hij : i ≤ j)
    (v : Fin q × Sign → ℤ) :
    weightedStage q j (stationaryTransition (rowTransition (ResetGraph q)) i j hij v) =
      weightedStage q i v := by
  change beta q ^ (-(j : ℤ)) * rowWeight q ((rowTransition (ResetGraph q) ^ (j-i)) v) = _
  rw [rowWeight_power q hq]
  change beta q ^ (-(j : ℤ)) * (beta q ^ (j-i) * rowWeight q v) =
    beta q ^ (-(i : ℤ)) * rowWeight q v
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (beta_pos q hq).ne']
  congr 2
  omega

private def graphTrace (q : ℕ) (hq : 2 ≤ q) : RowLimit (ResetGraph q) →ₗ[ℤ] ℝ :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => Fin q × Sign → ℤ)
    (stationaryTransition (rowTransition (ResetGraph q)))
    (weightedStage q) (weightedStage_compatible q hq)

private lemma graphTrace_stage (q : ℕ) (hq : 2 ≤ q) (N : ℕ) (v : Fin q × Sign → ℤ) :
    graphTrace q hq (stage (rowTransition (ResetGraph q)) N v) =
      beta q ^ (-(N : ℤ)) * rowWeight q v :=
  Module.DirectLimit.lift_of (weightedStage q) (weightedStage_compatible q hq) v

private lemma graphTrace_intStage (q : ℕ) (hq : 2 ≤ q) (m : ℤ) (v : Fin q × Sign → ℤ) :
    graphTrace q hq (intStage (rowTransition (ResetGraph q)) m v) =
      beta q ^ (-m) * rowWeight q v := by
  change graphTrace q hq (stage (rowTransition (ResetGraph q)) m.toNat
    ((rowTransition (ResetGraph q) ^ (-m).toNat) v)) = _
  rw [graphTrace_stage, rowWeight_power q hq]
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (beta_pos q hq).ne']
  congr 2
  omega

/-- Literal direct-limit lift transported through the same-stage row equivalence. -/
def tau (q : ℕ) (hq : 2 ≤ q) : DimensionGroup (resetMatrix q) →ₗ[ℤ] ℝ :=
  ((graphTrace q hq).toAddMonoidHom.comp (resetRowLimitEquiv q).symm.toAddMonoidHom).toIntLinearMap

/-- The inverse-stage factor on the original native coefficients. -/
theorem tau_stage (q : ℕ) (hq : 2 ≤ q) (N : ℕ) (v : VertexModule Sign q) :
    tau q hq (ResetFullStandardBeamRepresentation.nativeStage q N v) =
      beta q ^ (-(N : ℤ)) * ∑ i : Fin q, ∑ g : Sign, ((v i).coeff g : ℝ) * weight q i := by
  have he := resetRowLimitEquiv_stage q N (NativeIntegralRowTransport.decode v)
  rw [show NativeIntegralRowTransport.basisEquiv q (NativeIntegralRowTransport.decode v) = v
    from NativeIntegralRowTransport.encode_decode v] at he
  change tau q hq (stage (transition (resetMatrix q)) N v) = _
  rw [← he]
  change graphTrace q hq ((resetRowLimitEquiv q).symm (resetRowLimitEquiv q _)) = _
  rw [LinearEquiv.symm_apply_apply, graphTrace_stage]
  congr 1
  exact Fintype.sum_prod_type _

/-- Intrinsic Parts count pasts separately, including pasts with the same endpoint. -/
theorem tau_beam_atCut (q : ℕ) (hq : 2 ≤ q) (U : Beam (ResetGraph q)) (m : ℤ)
    (hm : AtCut (ResetGraph q) U.val m) :
    letI : Finite (Parts (ResetGraph q) U.val m) := hm.1
    letI : Fintype (Parts (ResetGraph q) U.val m) := Fintype.ofFinite _
    tau q hq (resetBeamCoordinate q U) = beta q ^ (-m) *
      ∑ P : Parts (ResetGraph q) U.val m, weight q (RayAt.endpoint (ResetGraph q) P.val).1 := by
  classical
  letI : Finite (Parts (ResetGraph q) U.val m) := hm.1
  letI : Fintype (Parts (ResetGraph q) U.val m) := Fintype.ofFinite _
  change graphTrace q hq ((resetRowLimitEquiv q).symm
    (resetRowLimitEquiv q (beamCoordinate (ResetGraph q) U))) = _
  rw [LinearEquiv.symm_apply_apply, beamCoordinate_at (ResetGraph q)
    (Alternating.reset_expanded_essential q (by omega)) U m hm]
  change graphTrace q hq (intStage (rowTransition (ResetGraph q)) m
    (endpointRow (ResetGraph q) U.val m)) = _
  rw [graphTrace_intStage]
  congr 1
  simp only [endpointRow, map_sum, rowWeight_single]

/-- Nonnegative on every beam, and strictly positive exactly on nonempty beams. -/
theorem tau_beam_positive (q : ℕ) (hq : 2 ≤ q) (U : Beam (ResetGraph q)) :
    0 ≤ tau q hq (resetBeamCoordinate q U) ∧
      (0 < tau q hq (resetBeamCoordinate q U) ↔ U.val.Nonempty) := by
  classical
  obtain ⟨m,hm⟩ := U.property
  letI : Finite (Parts (ResetGraph q) U.val m) := hm.1
  letI : Fintype (Parts (ResetGraph q) U.val m) := Fintype.ofFinite _
  rw [tau_beam_atCut q hq U m hm]
  have hp : 0 < beta q ^ (-m) := zpow_pos (beta_pos q hq) _
  have hw (P : Parts (ResetGraph q) U.val m) :
      0 < weight q (RayAt.endpoint (ResetGraph q) P.val).1 := weight_pos q hq _
  constructor
  · exact mul_nonneg hp.le (Finset.sum_nonneg fun P _ => (hw P).le)
  · rw [mul_pos_iff_of_pos_left hp]
    constructor
    · intro hs
      obtain ⟨P,_,_⟩ := (Finset.sum_pos_iff_of_nonneg (fun P _ => (hw P).le)).mp hs
      obtain ⟨x,hx⟩ := RayAt.nonempty (ResetGraph q) P.val
      exact ⟨x,P.property hx⟩
    · rintro ⟨x,hx⟩
      let P : Parts (ResetGraph q) U.val m := ⟨rayAt (ResetGraph q) x m, hm.2 x hx⟩
      exact Finset.sum_pos' (fun P _ => (hw P).le) ⟨P,Finset.mem_univ _,hw P⟩


private lemma tau_graph (q : ℕ) (hq : 2 ≤ q) (z : RowLimit (ResetGraph q)) :
    tau q hq (resetRowLimitEquiv q z) = graphTrace q hq z := by
  change graphTrace q hq ((resetRowLimitEquiv q).symm (resetRowLimitEquiv q z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Forward native time multiplies the trace by beta. -/
theorem tau_theta (q : ℕ) (hq : 2 ≤ q) (x : DimensionGroup (resetMatrix q)) :
    tau q hq (resetTheta q x) = beta q * tau q hq x := by
  obtain ⟨y,rfl⟩ := (resetRowLimitEquiv q).surjective x
  obtain ⟨N,v,rfl⟩ := Module.DirectLimit.exists_of y
  change tau q hq (resetTheta q (resetRowLimitEquiv q
    (stage (rowTransition (ResetGraph q)) N v))) = _
  rw [resetRowLimitEquiv_stage]
  change tau q hq (resetTheta q (Module.DirectLimit.of _ _ _ _ N _)) = _
  rw [resetTheta_apply_of, ← NativeIntegralRowTransport.transport_transition]
  change tau q hq (stage (transition (resetMatrix q)) N
    (NativeIntegralRowTransport.basisEquiv q
      (NativeIntegralRowTransport.rowTransition (resetMatrix q) v))) =
      beta q * tau q hq (resetRowLimitEquiv q
        (stage (rowTransition (ResetGraph q)) N v))
  rw [← resetRowLimitEquiv_stage, ← graph_rowTransition_eq, tau_graph, tau_graph,
    graphTrace_stage, graphTrace_stage, rowWeight_transition q hq]
  ring

/-- The actual absolute-sign action has trace factor one. -/
theorem tau_sign (q : ℕ) (hq : 2 ≤ q) (x : DimensionGroup (resetMatrix q)) :
    tau q hq (groupAction (resetMatrix q) (Multiplicative.ofAdd true) x) = tau q hq x := by
  classical
  obtain ⟨N,v,rfl⟩ := Module.DirectLimit.exists_of x
  have he : groupAction (resetMatrix q) (Multiplicative.ofAdd true)
      (ResetFullStandardBeamRepresentation.nativeStage q N v) =
      ResetFullStandardBeamRepresentation.nativeStage q N
        (InertGroupBlockConjugacy.leftTranslation (Multiplicative.ofAdd true) v) := by
    dsimp only [groupAction, InertGroupBlockConjugacy.induced,
      ResetFullStandardBeamRepresentation.nativeStage, stage]
    exact Module.DirectLimit.map_apply_of (R := ℤ) (ι := ℕ)
      (G := fun _ : ℕ => VertexModule Sign q) (G' := fun _ : ℕ => VertexModule Sign q)
      (f := stationaryTransition (transition (resetMatrix q)))
      (f' := stationaryTransition (transition (resetMatrix q)))
      (fun _ : ℕ => InertGroupBlockConjugacy.leftTranslation
        (n := q) (Multiplicative.ofAdd true)) _ v
  change tau q hq (groupAction _ _ (ResetFullStandardBeamRepresentation.nativeStage q N v)) =
    tau q hq (ResetFullStandardBeamRepresentation.nativeStage q N v)
  rw [he, tau_stage, tau_stage]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [InertGroupBlockConjugacy.leftTranslation, MonoidAlgebra.coeff_single_mul_apply,
    one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (Multiplicative.ofAdd true : Sign)) _ _
    (fun g => by simp [show (Multiplicative.ofAdd true : Sign)⁻¹ =
      Multiplicative.ofAdd true from by decide])

/-- The literal stage-zero ray representing Phi(1). -/
def generatorRay (q : ℕ) (hq : 0 < q) : Beam (ResetGraph q) :=
  resetRayBeam q hq (resetBasisHistory q hq (⟨0,hq⟩,1) 0) 0

private lemma generator_coordinate (q : ℕ) (hq : 0 < q) :
    resetBeamCoordinate q (generatorRay q hq) = ResetNativeIntegerChart.nativeIntEquiv q hq 1 := by
  rw [(ResetNativeIntegerChart.native_presentation q hq).1]
  rw [generatorRay, resetBeamCoordinate_ray]
  simp only [resetBasisHistory, vertexHistory_endpoint]
  change intStage (transition (resetMatrix q)) (0 : ℤ) (vertex ⟨0,hq⟩ 1) = _
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, intStage_nat]
  rfl

/-- Normalization is at the original basis ray, rather than at an ordered inverse chart. -/
theorem tau_one (q : ℕ) (hq : 2 ≤ q) :
    tau q hq (ResetNativeIntegerChart.nativeIntEquiv q (by omega) 1) = 1 := by
  rw [← generator_coordinate q (by omega)]
  unfold generatorRay
  rw [resetBeamCoordinate_ray]
  simp only [resetBasisHistory, vertexHistory_endpoint]
  change tau q hq (stage (transition (resetMatrix q)) 0
    (vertex ⟨0,by omega⟩ 1)) = _
  have hv : NativeIntegralRowTransport.basisEquiv q
      (Pi.single (⟨0,by omega⟩,1) 1) = vertex ⟨0,by omega⟩ 1 := by
    change NativeIntegralRowTransport.basisEquiv q
      (NativeIntegralRowTransport.rowVertex ⟨0,by omega⟩ 1) = _
    rw [← NativeIntegralRowTransport.decode_vertex]
    exact NativeIntegralRowTransport.encode_decode _
  rw [← hv, ← resetRowLimitEquiv_stage, tau_graph, graphTrace_stage, rowWeight_single,
    weight_zero q hq]
  simp

/-- Every original full homeomorphism sends the actual generator ray to a nonempty beam. -/
theorem original_action_positive (q : ℕ) (hq : 2 ≤ q) (h : ResetFullAut q) :
    0 < tau q hq (ResetFullStandardBeamRepresentation.rho q (by omega) h
      (ResetNativeIntegerChart.nativeIntEquiv q (by omega) 1)) := by
  classical
  let hp : 0 < q := by omega
  let alpha := resetBasisHistory q hp (⟨0,hp⟩,1) 0
  let U := generatorRay q hp
  have hmem : alpha ∈ U.val := self_mem_ray (ResetGraph q) alpha 0
  have hnonempty : (resetImageBeam q hp h U).val.Nonempty :=
    ⟨h.val alpha, ⟨alpha,hmem,rfl⟩⟩
  obtain ⟨a,b,c,d,hab,hcd⟩ := StandardBeamHomeomorphisms.fullAut_has_two_windows (ResetGraph q) h
  have hm : AtCut (ResetGraph q) (resetImageBeam q hp h U).val (d : ℤ) := by
    change AtCut (ResetGraph q) (h.val '' ray (ResetGraph q) alpha 0) (d : ℤ)
    simpa only [zero_add] using StandardBeamHomeomorphisms.image_ray_atCut (ResetGraph q)
      (Alternating.reset_expanded_essential q hp) h hab hcd alpha 0
  rw [← generator_coordinate q hp, ResetFullStandardBeamRepresentation.rho_beam_image]
  have hpositive := (tau_beam_positive q hq (resetImageBeam q hp h U)).2.mpr hnonempty
  rw [tau_beam_atCut q hq _ (d : ℤ) hm] at hpositive ⊢
  exact hpositive

/-- Scalar minus identity is never induced by an actual original full history action. -/
theorem rho_ne_neg_id (q : ℕ) (hq : 2 ≤ q) (h : ResetFullAut q) :
    (ResetFullStandardBeamRepresentation.rho q (by omega) h).toLinearMap ≠
      -(LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) := by
  intro he
  have ht := original_action_positive q hq h
  rw [show ResetFullStandardBeamRepresentation.rho q (by omega) h
      (ResetNativeIntegerChart.nativeIntEquiv q (by omega) 1) =
      -ResetNativeIntegerChart.nativeIntEquiv q (by omega) 1 from
    LinearMap.congr_fun he _, map_neg, tau_one] at ht
  norm_num at ht

private lemma tau_shift (q : ℕ) (hq : 2 ≤ q) (x : DimensionGroup (resetMatrix q)) :
    tau q hq (ResetFullStandardBeamRepresentation.rho q (by omega)
      (StandardBeamHomeomorphisms.unitShift (ResetGraph q)) x) = beta q * tau q hq x := by
  change tau q hq ((ResetFullStandardBeamRepresentation.rho q (by omega)
    (StandardBeamHomeomorphisms.unitShift (ResetGraph q))).toLinearMap x) = _
  rw [ResetFullStandardBeamRepresentation.rho_unitShift, tau_theta]

private lemma tau_equiv_pow (q : ℕ) (hq : 2 ≤ q)
    (e : DimensionGroup (resetMatrix q) ≃ₗ[ℤ] DimensionGroup (resetMatrix q)) (c : ℝ)
    (he : ∀ x, tau q hq (e x) = c * tau q hq x) (k : ℕ) (x : DimensionGroup (resetMatrix q)) :
    tau q hq ((e ^ k) x) = c ^ k * tau q hq x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, he, ih, pow_succ']; ring

/-- All integral forward-time powers, including negative exponents. -/
theorem tau_time_zpow (q : ℕ) (hq : 2 ≤ q) (n : ℤ) (x : DimensionGroup (resetMatrix q)) :
    tau q hq ((ResetFullStandardBeamRepresentation.rho q (by omega)
      (StandardBeamHomeomorphisms.unitShift (ResetGraph q)) ^ n) x) =
      beta q ^ n * tau q hq x := by
  let t := ResetFullStandardBeamRepresentation.rho q (by omega)
    (StandardBeamHomeomorphisms.unitShift (ResetGraph q))
  have hpos := beta_pos q hq
  have hinv (x : DimensionGroup (resetMatrix q)) : tau q hq (t⁻¹ x) =
      (beta q)⁻¹ * tau q hq x := by
    have ht := tau_shift q hq (t⁻¹ x)
    change tau q hq (t (t⁻¹ x)) = beta q * tau q hq (t⁻¹ x) at ht
    change tau q hq (t (t.symm x)) = beta q * tau q hq (t⁻¹ x) at ht
    rw [LinearEquiv.apply_symm_apply] at ht
    rw [ht]
    field_simp
  cases n with
  | ofNat k => exact tau_equiv_pow q hq t (beta q) (tau_shift q hq) k x
  | negSucc k =>
    change tau q hq ((t ^ Int.negSucc k) x) = _
    rw [zpow_negSucc, ← inv_pow, tau_equiv_pow q hq t⁻¹ (beta q)⁻¹ hinv]
    simp [zpow_negSucc, inv_pow]

/-- Any supplied signed time/Sign expression has trivial negative scalar bit.
The existence of such an expression is not asserted. -/
theorem rho_negative_bit (q : ℕ) (hq : 2 ≤ q) (h : ResetFullAut q)
    (a b : Fin 2) (n : ℤ)
    (he : (ResetFullStandardBeamRepresentation.rho q (by omega) h).toLinearMap =
      ((-1 : ℤ) ^ a.val) •
        ((groupAction (resetMatrix q) (Multiplicative.ofAdd true) ^ b.val) *
          (ResetFullStandardBeamRepresentation.rho q (by omega)
            (StandardBeamHomeomorphisms.unitShift (ResetGraph q)) ^ n).toLinearMap)) :
    a = 0 := by
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha with ha | ha
  · exact Fin.ext ha
  · let y := ResetNativeIntegerChart.nativeIntEquiv q (by omega) 1
    let t := ResetFullStandardBeamRepresentation.rho q (by omega)
      (StandardBeamHomeomorphisms.unitShift (ResetGraph q))
    have heval : ResetFullStandardBeamRepresentation.rho q (by omega) h y =
        ((-1 : ℤ) ^ a.val) •
          ((groupAction (resetMatrix q) (Multiplicative.ofAdd true) ^ b.val) ((t ^ n) y)) :=
      LinearMap.congr_fun he y
    rw [ha, pow_one, neg_one_smul] at heval
    have ht : 0 < tau q hq
        (-((groupAction (resetMatrix q) (Multiplicative.ofAdd true) ^ b.val) ((t ^ n) y))) :=
      lt_of_lt_of_eq (original_action_positive q hq h) (congrArg (tau q hq) heval)
    have hb : b.val = 0 ∨ b.val = 1 := by omega
    rcases hb with hb | hb
    · simp only [hb, pow_zero, Module.End.one_apply, map_neg] at ht
      change 0 < -(tau q hq ((t ^ n) y)) at ht
      rw [tau_time_zpow, tau_one] at ht
      linarith [zpow_pos (beta_pos q hq) n]
    · simp only [hb, pow_one, map_neg, tau_sign] at ht
      change 0 < -(tau q hq ((t ^ n) y)) at ht
      rw [tau_time_zpow, tau_one] at ht
      linarith [zpow_pos (beta_pos q hq) n]

end D5.S3.ConceptDynamics.Coding.ResetPerronBeamTrace

/- GID: D5/S3/Zeros/GRH/New/Selmer/RankOneDenominator
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/RankOneDenominator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.RankOneDenominator. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/RankOneDenominator.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.LevelPlacesChosen
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: general results applied to the objects of this proof.

Part of: A twist with few congruences for each prime (see New.Selmer.FitTwistsExist).

This file: Rank-one denominator bound for test forms by averaging over classes of U(1). -/

variable {P} {D : Data P} {n} [Fintype n] (Y : LValueData D.E n) (z)

/-- The representation of the finite adelic group U(1) on the forms on V of the auxiliary pair
`LValueData.auxPair`, with z acting by right translation by the central scalar `scalarFin` z. -/
noncomputable def LValueData.centralRep : Representation ℂ (Gf D.E Unit) Y.auxPair.FormV :=
  algFormCentralRep.comp (U.det (by simp))

/-- The operator on forms on V equal to `LValueData.centralRep` z multiplied by the value of the
character `AuxPair.b` at det(1, z), for z in the finite adelic U(1). -/
noncomputable def LValueData.twistedCentralOp := (Y.auxPair.b.1 (detFin 1 z)).1 • Y.centralRep z

lemma LValueData.inner_twistedCentralOp x y : inner ℂ x (Y.twistedCentralOp z y) =
  inner ℂ (Y.twistedCentralOp z⁻¹ x) y := by with_unfolding_all simpa [twistedCentralOp,
  ← Circle.coe_inv_eq_conj, ← MonoidHom.inr_apply, field] using!
  (congr(_ * $(smoothPairing_formTranslation _ _ (Y.centralRep z⁻¹ x).toSmoothForm
  y.toSmoothForm)) : (Y.centralRep z (Y.centralRep z⁻¹ x)).innerAt 1 (Y.centralRep z y) = _)

/-- For a lift datum Y and z in U(1)(𝔸_f), the operator `LValueData.twistedCentralOp` at z⁻¹ carries
the kernel form `LValueData.kernelForm` at g to the kernel form at gz. -/
lemma LValueData.twistedCentralOp_kernelForm g : Y.twistedCentralOp z⁻¹ (Y.kernelForm g) =
  Y.kernelForm (g * z) := Subtype.ext
  (by ext k : 2; let ν := U.det (by simp) z⁻¹; simpa [kernelValue, ← mul_apply_eq_comp, ← map_mul,
  eq_inv_smul_iff₀, show scalarFin _ ν = z⁻¹ by ext; simp [ν, Gf.atPlace, scalarFin, U.det]] using!
  congr(Y.kernelValue 1 ($(pairWeilFinite_scalarFin Y.auxPair.a Y.auxPair.b ν ν) _).1 (g * z) k))

lemma LValueData.twistedCentralOp_trivialLift : Y.twistedCentralOp z Y.trivialLift =
  Y.trivialLift := (map_classSum ..).trans (by simp [Y.trivialLift_eq_stdClassSum_translate z⁻¹,
  ← twistedCentralOp_kernelForm])

open LValueData

/-- Let the line spanned by the lift `Y.trivialLift` from U(1) have denominator ≤ β at ι, and U(1)
have trivial stabilisers and h' classes at principal level at the chosen places. Then test forms at
ℓ satisfy ‖ι(h'⟨Ξ, pr Ξ'⟩)‖ ≤ e^β, pr projecting orthogonally onto that line. -/
lemma DenominatorLe.rank_one_bound {l : PrimePadicIso} {β} (h :
  DenominatorLe l.2 Y.auxPair (tupleIdem _ fun _ ↦ .X - 1) (ℂ ∙ Y.trivialLift) β)
  (hA : ∀ g, classAut stdRatPoints Y.chosenLevel g = ⊥) {Ξ Ξ'} (hΞ :
  Y.auxPair.IsTestForm l.1 Ξ) (hΞ' : Y.auxPair.IsTestForm l.1 Ξ') : ‖l.2 (Nat.card
  (StdClasses Y.chosenLevel) * inner ℂ Ξ ((ℂ ∙ Y.trivialLift).starProjection Ξ'))‖ ≤ .exp β := by
  by_cases Y.trivialLift = 0; simp [*, Real.exp_nonneg]
  choose s hs _ using exists_reps_integralAbove (K := Y.chosenLevel) l.1
  simpa [inner_sum, inner_twistedCentralOp, twistedCentralOp_trivialLift,
    Submodule.starProjection_singleton ℂ, field] using h _ (finrank_span_singleton ‹_›) _ ![∑ i,
    Y.twistedCentralOp (s i)⁻¹ Ξ'] (fun _ ↦ hΞ.1) fun 0 ↦ ⟨sum_mem fun _ _ _ ↦ by
    erw [weylGauge_smul, Y.b_hasWeight.norm_padic_det, one_mul, ← weylGauge_mul]; apply hΞ'.1
    all_goals simp_rw [mem_localLevel, mem_intGL, ← map_inv] at *
              simp_all [scalarFin, U.det, Matrix.diagonal, apply_ite, Gf.atPlace, -map_inv], fun _
    hw hS _ ⟨⟨E, hH⟩, m⟩ ↦ by simp [inner_sum, inner_twistedCentralOp, ← sum_inner]; exact hΞ'.2 _
                                hw hS _ ⟨sum_mem fun _ _ ↦ Submodule.smul_mem _ _
    ⟨AuxPair.range_groupAlgAction_mem_invtSubmodule _ (fun _ _ ↦ (map_smul ..).trans congr(_ •
    $((commute_scalarFin _).map (algFormRep ..)) _)) E, Subtype.ext ((map_heckePolyOp
    (algFormRep _ _ _) _ fun _ _ ↦ by simpa using congr($((commute_scalarFin _).map (algFormRep ..))
                                        _)).symm.trans congr((Y.centralRep _
    $hH).1))⟩, funext fun ⟨_, g⟩ ↦ by simpa [hA, twistedCentralOp_kernelForm, mul_comm' g,
    theta_eq_inner_kernelForm, sum_inner, inner_twistedCentralOp, trivialLift,
    classSum, (hs · ▸ Y.kernelForm_invariant.elim apply_doubleCoset_out _), -MonoidHom.coe_range,
    Submodule.mem_orthogonal_singleton_iff_inner_right] using
    (Y.twistedCentralOp_trivialLift g⁻¹ ▸ m :)⟩⟩

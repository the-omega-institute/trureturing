/- SOURCE ONLY. UNCOMPILED. The original h, its two windows, its Word,
its endpoint unit U, and Q=(tau^-1)^N*U are chosen ONCE below.
Both periodwise computations consume that same witness; both actual unit
factors are rewritten. Numerical bodies are retained source, not assumptions
or an executed certificate. The complete root is proved locally for EVERY h below, then used for
intrinsic descent through the literal Fix(T^6) restriction. This is an unnamed
transient application; every finite computation remains local and UNEXECUTED.
-/
import D5.S3.ConceptDynamics.Coding.PresentationTimeCochain
import D5.S3.ConceptDynamics.Coding.CentralizerTimePowers
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
import D5.S3.ConceptDynamics.Coding.CountedSignedGyrationEvaluator
import D5.S3.ConceptDynamics.Coding.ActualWordEnumeratedLoop
import D5.S3.ConceptDynamics.Coding.OriginalPositiveWordAssembly
import D5.S3.ConceptDynamics.Coding.OriginalResponseTableIntake
import D5.S3.ConceptDynamics.Coding.PositiveWordFullAction
import D5.S3.ConceptDynamics.Coding.ResetQ4LocalizedGyrationCharacter

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding
open EssentialWordRealization FiniteWindowTableCriterion
open TwoSidedFiniteInduction TypedPositiveSplitWord
open StandardBeamCoordinates StandardBeamColimitCuts StandardBeamHomeomorphisms
open StandardTaggedBeams StandardBeamIdentification ResetNumberedHistories
open ResetStandardBeamGeometry ResetFullStandardBeamRepresentation
open OriginalResponseTableIntake ResponseTwoSidedConsumer OriginalPositiveWordAssembly
open ResetNativeIntegralDefect
open ActualPositiveWordPeriodicCochain ActualWordLocalizedComparison
open CountedOrderTypeGyration (dyadicGyration integerGyrationValue)
open CountedOrderTypeGyration.SignedSupport
  (prunedShard integerGyrationValue_eq_supportedEvaluator
    supportedEvaluator_eq_pruned prunedEvaluator_eq_shards)
open ResetQ4OriginalLocalizedCubes (T VertexIndex DyadicMatrix)
open ResetQ4LocalizedGyrationCharacter
  (originalRows vertexEquiv originalRows_mul originalRows_one columnGyration
    columnGyration_triangle gamma Gamma originalAdjacency onePlusSignedFactor
    gamma_time_signed_evaluation gamma_onePlus_signed_evaluation)
open TwistedPeriodicHistories
open SourceOnly.ActualWordMatrixPath (D vertex presentationBasis endpointMap timeMap)
open SourceOnly.ActualWordEnumeratedLoop
open SourceOnly.BasedLoopCoordinateTransport
open SourceOnly.KernelRSSquareGyration (rows value)
open SourceOnly.FiniteKernelLadder (Mat rowUnit)
open scoped BigOperators Matrix

local instance nativeIntModule (q : ℕ) :
    Module ℤ (InertGroupBlockConjugacy.DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

set_option maxRecDepth 100000 in
example :
    let G := ResetGraph 4
    let P := original G (Alternating.reset_expanded_essential 4 (by omega))
    let psi := fun f : ResetFullAut 4 =>
      Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
        (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
          (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
            (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
            (ResetHistoryKernel.rho_time 4 (by decide) f)))
    let chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
      ResetQ4UnitCubes.residueQuotientCharacter
        (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
        ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
            (psi f)))
    (∀ h : ResetFullAut 4,
      (∀ (p : ℕ) [NeZero p] (hp : 3 ∣ p),
        ZMod.castHom hp (ZMod 3)
          (historyGyration (F := P) h.val.toEquiv (commute_translate G h) p) =
        Multiplicative.toAdd (gamma p hp (ResetQ4OriginalLocalizedCubes.originalImage h))) ∧
      (Fintype.card (Orbit P 3) = 2 ∧ Fintype.card (Orbit P 6) = 7) ∧
      (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
        reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6) =
        Multiplicative.toAdd (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h))) ∧
      chi_add h = 2*Multiplicative.toAdd
        (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) ∧
      chi_add h = 2*(historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
        reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6))) ∧
    (fun h : ResetFullAut 4 => chi_add h).FactorsThrough
      (fun h : ResetFullAut 4 =>
        fun x : {x : ResetHistory 4 // (shift (ResetGraph 4))^[6] x = x} =>
          h.val x.val) := by
  classical
  let G := ResetGraph 4
  let P := original G (Alternating.reset_expanded_essential 4 (by omega))
  let psi := fun f : ResetFullAut 4 =>
    Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
      (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
        (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
          (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
          (ResetHistoryKernel.rho_time 4 (by decide) f)))
  let chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
    ResetQ4UnitCubes.residueQuotientCharacter
      (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
      ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
          (psi f)))
  have fullroot : ∀ h : ResetFullAut 4,
    (∀ (p : ℕ) [NeZero p] (hp : 3 ∣ p),
      ZMod.castHom hp (ZMod 3)
        (historyGyration (F := P) h.val.toEquiv (commute_translate G h) p) =
      Multiplicative.toAdd (gamma p hp (ResetQ4OriginalLocalizedCubes.originalImage h))) ∧
    (Fintype.card (Orbit P 3) = 2 ∧ Fintype.card (Orbit P 6) = 7) ∧
    (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
      reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6) =
      Multiplicative.toAdd (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h))) ∧
    chi_add h = 2*Multiplicative.toAdd
      (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) ∧
    chi_add h = 2*(historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
      reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6)) := by
    intro h
    classical
    dsimp only
    let G := ResetGraph 4
    let hG := Alternating.reset_expanded_essential 4 (by omega)
    let P := original G hG
    let σ : VertexIndex ≃ P.V := {
      toFun := fun v => (v.1,v.2)
      invFun := fun v => ⟨v.1,v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    let e := vertexEquiv.trans σ
    let b0 := coefficientBasis σ
    let c := coefficientBasis e
    have hbc (i : Fin 8) : c i = b0 (vertexEquiv i) := by
      ext v
      rw [coefficient_apply, coefficient_apply] <;> rfl
    -- This compares the ACTUAL coefficient maps. No finite 8x8 numerical
    -- certificate and no assertion that the P1 chart is the fixed chart.
    have hrows (f : Module.End D (P.V → D)) :
        originalRows (LinearMap.toMatrix b0 b0 f) = rows c c f := by
      ext i j
      change b0.repr (f (b0 (vertexEquiv i))) (vertexEquiv j) =
        c.repr (f (c i)) j
      rw [coefficient_repr, coefficient_repr, hbc] <;> rfl
    have hb0 (j : VertexIndex) : b0 j = Pi.single (j.1,j.2) (1 : D) := by
      ext v
      rw [coefficient_apply]
      simp [σ, Pi.single_apply, eq_comm]
    have hT : LinearMap.toMatrix b0 b0 (vertex P).time = T := by
      ext i j
      change b0.repr (timeMap G (b0 j)) i = algebraMap ℤ D
        ((LinearMap.toMatrix
          (InertGroupBlockConjugacy.vertexBasis (H := Sign) (n := 4))
          (InertGroupBlockConjugacy.vertexBasis (H := Sign) (n := 4))
          (InertGroupBlockConjugacy.transition (resetMatrix 4))) i j)
      rw [coefficient_repr, hb0, LinearMap.toMatrix_apply]
      simp only [InertGroupBlockConjugacy.vertexBasis, Pi.basis_repr,
        Pi.basis_apply, MonoidAlgebra.basis_apply]
      change timeMap G (Pi.single (j.1,j.2) (1 : D)) (i.1,i.2) =
        algebraMap ℤ D (((InertGroupBlockConjugacy.transition (resetMatrix 4)
          (InertGroupBlockConjugacy.vertex j.1 j.2)) i.1).coeff i.2)
      rw [InertGroupBlockConjugacy.actual_expansion_adjacency]
      unfold timeMap
      rw [Matrix.toLinearMapRight'_apply, Matrix.single_vecMul]
      simp only [one_smul, Matrix.row, Matrix.map_apply, expanded_adjacency_eq] <;> rfl
    -- Recover an actual inverse of graph time from the EXISTING literal T
    -- unit. This uses no private proof body and no invertible intermediate.
    let τ := (ResetQ4OriginalLocalizedCubes.time : DyadicMatrixˣ)
    let τinv : Module.End D (P.V → D) :=
      (LinearMap.toMatrix b0 b0).symm (↑τ⁻¹ : DyadicMatrix)
    have hτ : LinearMap.toMatrix b0 b0 (vertex P).time = (τ : DyadicMatrix) :=
      hT.trans ResetQ4OriginalLocalizedCubes.time_val.symm
    let t : (Module.End D (P.V → D))ˣ := {
      val := (vertex P).time
      inv := τinv
      val_inv := by
        apply (LinearMap.toMatrix b0 b0).injective
        change LinearMap.toMatrix b0 b0 ((vertex P).time.comp τinv) =
          LinearMap.toMatrix b0 b0 LinearMap.id
        rw [LinearMap.toMatrix_comp, hτ, LinearMap.toMatrix_id]
        change (τ : DyadicMatrix) * (LinearMap.toMatrix b0 b0)
          ((LinearMap.toMatrix b0 b0).symm ↑τ⁻¹) = 1
        rw [LinearEquiv.apply_symm_apply, Units.mul_inv]
      inv_val := by
        apply (LinearMap.toMatrix b0 b0).injective
        change LinearMap.toMatrix b0 b0 (τinv.comp (vertex P).time) =
          LinearMap.toMatrix b0 b0 LinearMap.id
        rw [LinearMap.toMatrix_comp, hτ, LinearMap.toMatrix_id]
        change (LinearMap.toMatrix b0 b0)
          ((LinearMap.toMatrix b0 b0).symm ↑τ⁻¹) * (τ : DyadicMatrix) = 1
        rw [LinearEquiv.apply_symm_apply, Units.inv_mul] }
    have ht : IsUnit (vertex P).time := ⟨t,rfl⟩
    obtain ⟨a,b,c',d,hab,hcd⟩ := fullAut_has_two_windows G h
    let pair := tables G hG h a b c' d hab hcd
    let witness := actualWitness G hG h hab hcd
    obtain ⟨w,hletters,hhistory⟩ := positive_word G hG pair witness
    let s : ℤ := -(a:ℤ)-(((a+c')+(b+d+1):ℕ):ℤ)
    obtain ⟨u,hu,hcomm,hC,hCinv,hCent,hf,hb,hsr,hrs,hw⟩ := word_rebased w ht e
    let U := columnUnit b0 u
    have hU : (U : DyadicMatrix) = LinearMap.toMatrix b0 b0 (endpointMap w) := by
      change LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D)) = _
      rw [hu]
    have hcommU : Commute (U : DyadicMatrix) T := by
      change LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D)) * T =
        T * LinearMap.toMatrix b0 b0 (u : Module.End D (P.V → D))
      rw [← hT, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
      exact congrArg (LinearMap.toMatrix b0 b0) hcomm.eq
    have hR : originalRows (U : DyadicMatrix) = (rowUnit c u : Mat 8 8) :=
      hrows (u : Module.End D (P.V → D))
    have hI : originalRows (↑U⁻¹ : DyadicMatrix) = (↑(rowUnit c u)⁻¹ : Mat 8 8) :=
      hrows (↑u⁻¹ : Module.End D (P.V → D))
    have hA : originalRows T = rows c c (vertex P).time := by
      rw [← hT]
      exact hrows _
    have hOrder : T * (↑U⁻¹ : DyadicMatrix) = (↑U⁻¹ : DyadicMatrix) * T := by
      have hi := inverse_time_order u (vertex P).time hcomm
      have hi' := congrArg (LinearMap.toMatrix b0 b0) hi
      simpa only [Module.End.mul_eq_comp, LinearMap.toMatrix_comp, hT] using hi'
    -- REAL new consumer of the exported ORIGINAL originalRows_mul body.
    -- COLUMN T*U^{-1} becomes ROW U^{-1}*A. Commutation justifies changing
    -- the COLUMN target factor to U^{-1}*T used by the original character.
    have hS : originalRows (↑U⁻¹*T) =
        (↑(rowUnit c u)⁻¹ : Mat 8 8) * originalRows T := by
      rw [← hOrder, originalRows_mul, hI]
    have hrho (z : RowLimit G) :
        rho 4 (by omega) h (resetRowLimitEquiv 4 z) =
          resetRowLimitEquiv 4 (SignedBeamCutTranslation.cutShift (rowTransition G) s
            (PositiveWordBeamTransport.rowEquiv w z)) := by
      let x := (beamRowEquiv G hG).symm z
      have hz : F G hG x = z := (beamRowEquiv G hG).apply_symm_apply z
      have hc := PositiveWordFullAction.full_action_coordinate P h w s hhistory x
      rw [hz] at hc
      calc
        _ = rho 4 (by omega) h (nativeEquiv 4 (by omega) x) := by
          congr 1
          change resetRowLimitEquiv 4 z = resetRowLimitEquiv 4 (F G hG x)
          rw [hz]
        _ = nativeEquiv 4 (by omega) (resetFullBeamRepresentation 4 (by omega) h x) :=
          rho_nativeEquiv 4 (by omega) h x
        _ = _ := congrArg (resetRowLimitEquiv 4) hc
    have hstage (z : P.V → ℤ) :
        rho 4 (by omega) h (resetRowLimitEquiv 4 (stage (rowTransition G) 0 z)) =
          resetRowLimitEquiv 4 (intStage (rowTransition G) (-s)
            (PositiveWordBeamTransport.endpointMap w z)) := by
      rw [hrho, ← intStage_nat (rowTransition G) 0 z,
        PositiveWordBeamTransport.rowEquiv_intStage,
        SignedBeamCutTranslation.cutShift_intStage]
      simp only [zero_sub]
    -- Signed-cut extraction uses STAGE ZERO and the actual native inverse,
    -- rather than inferring cochain equality from an equality of beam actions.
    let N : ℕ := a+((a+c')+(b+d+1))
    have hsN : -s = (N : ℤ) := by dsimp [s,N]; omega
    let vb := InertGroupBlockConjugacy.vertexBasis (H := Sign) (n := 4)
    let E := NativeIntegralRowTransport.basisEquiv 4
    let fZ : Module.End ℤ (InertGroupBlockConjugacy.VertexModule Sign 4) :=
      E.toLinearMap.comp ((PositiveWordBeamTransport.endpointMap w).comp E.symm.toLinearMap)
    let Rho : Module.End ℤ (InertGroupBlockConjugacy.VertexModule Sign 4) :=
      (((resetNativeEquiv 4 (by omega)).symm.trans
        ((rho 4 (by omega) h).trans (resetNativeEquiv 4 (by omega)))).toLinearMap)
    have hzero (z : InertGroupBlockConjugacy.VertexModule Sign 4) :
        resetRowLimitEquiv 4 (stage (rowTransition G) 0 (E.symm z)) =
          (resetNativeEquiv 4 (by omega)).symm z := by
      rw [resetRowLimitEquiv_stage, E.apply_symm_apply] <;> rfl
    have hNative : Rho = (resetInverse 4 (by omega)^N).comp fZ := by
      ext z
      have hz := hstage (E.symm z)
      rw [hzero, hsN, intStage_nat, resetRowLimitEquiv_stage] at hz
      have hn := congrArg (resetNativeEquiv 4 (by omega)) hz
      rw [resetNativeEquiv_stage] at hn
      exact hn
    have hEcoeff (z : P.V → ℤ) (i : VertexIndex) :
        vb.repr (E z) i = z (i.1,i.2) := by
      change (NativeIntegralRowTransport.encode z i.1).coeff i.2 = _
      exact NativeIntegralRowTransport.encode_coeff z i.1 i.2
    have hEvertex (j : VertexIndex) : E.symm (vb j) = Pi.single (j.1,j.2) (1 : ℤ) := by
      change NativeIntegralRowTransport.decode (vb j) = _
      simpa only [vb, InertGroupBlockConjugacy.vertexBasis, Pi.basis_apply,
        MonoidAlgebra.basis_apply, NativeIntegralRowTransport.rowVertex] using
          NativeIntegralRowTransport.decode_vertex j.1 j.2
    have hEndpoint : (LinearMap.toMatrix vb vb fZ).map (algebraMap ℤ D) =
        (U : DyadicMatrix) := by
      rw [hU]
      ext i j
      change algebraMap ℤ D (vb.repr (E
        (PositiveWordBeamTransport.endpointMap w (E.symm (vb j)))) i) =
          b0.repr (endpointMap w (b0 j)) i
      rw [hEcoeff, hEvertex, coefficient_repr, hb0]
      have hc := congrFun (SourceOnly.ActualWordMatrixPath.endpointMap_cast w
        (Pi.single (j.1,j.2) (1 : ℤ))) (i.1,i.2)
      simpa [Pi.single_apply] using hc.symm
    let J : DyadicMatrix :=
      (LinearMap.toMatrix vb vb (resetInverse 4 (by omega))).map (algebraMap ℤ D)
    have hTJ : T*J = 1 := by
      change ((LinearMap.toMatrix vb vb
        (InertGroupBlockConjugacy.transition (resetMatrix 4))).map (algebraMap ℤ D)) *
          ((LinearMap.toMatrix vb vb (resetInverse 4 (by omega))).map (algebraMap ℤ D)) = 1
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp]
      change (LinearMap.toMatrix vb vb
        (InertGroupBlockConjugacy.transition (resetMatrix 4) * resetInverse 4 (by omega))).map
          (algebraMap ℤ D) = 1
      rw [(reset_transition_inverse 4 (by omega)).2, LinearMap.toMatrix_id, Matrix.map_one]
    have hJ : J = (↑τ⁻¹ : DyadicMatrix) := by
      calc
        J = (↑τ⁻¹ : DyadicMatrix) * ((τ : DyadicMatrix)*J) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = (↑τ⁻¹ : DyadicMatrix) := by
          rw [← hτ, hT, hTJ, mul_one]
    have hPower (n : ℕ) :
        (LinearMap.toMatrix vb vb (resetInverse 4 (by omega)^n)).map (algebraMap ℤ D) = J^n := by
      induction n with
      | zero =>
          change (LinearMap.toMatrix vb vb LinearMap.id).map (algebraMap ℤ D) = 1
          rw [LinearMap.toMatrix_id, Matrix.map_one]
      | succ n ih =>
          rw [pow_succ', Module.End.mul_eq_comp, LinearMap.toMatrix_comp, Matrix.map_mul, ih]
          exact (pow_succ' J n).symm
    have hSigned : ResetQ4OriginalLocalizedCubes.rhoD h =
        (↑(τ⁻¹^N) : DyadicMatrix) * (U : DyadicMatrix) := by
      change (LinearMap.toMatrix vb vb Rho).map (algebraMap ℤ D) = _
      rw [hNative, LinearMap.toMatrix_comp, Matrix.map_mul, hPower, hEndpoint, hJ]
      simp only [Units.val_pow_eq_pow_val]

    let Q : DyadicMatrixˣ := (τ⁻¹)^N*U
    have hImage : (ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ) = Q := by
      apply Units.ext
      rw [ResetQ4OriginalLocalizedCubes.originalImage_val]
      exact hSigned
    -- Equality of units transports BOTH factors, including the inverse.
    have hForward :
        ((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ) : DyadicMatrix) =
          (Q : DyadicMatrix) :=
      congrArg (fun V : DyadicMatrixˣ => (V : DyadicMatrix)) hImage
    have hInverse : (ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ)⁻¹ = Q⁻¹ :=
      congrArg (fun V : DyadicMatrixˣ => V⁻¹) hImage
    have hBackwardFactor :
        (↑((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ)⁻¹) : DyadicMatrix)*T =
          (↑Q⁻¹ : DyadicMatrix)*T :=
      congrArg (fun V : DyadicMatrixˣ => (V : DyadicMatrix)*T) hInverse
    have hτval : (τ : DyadicMatrix) = T := hτ.symm.trans hT
    have hcal (p : ℕ) [NeZero p] (hp : 3 ∣ p) :
        columnGyration p (τ : DyadicMatrix) (↑τ⁻¹*T) =
          (Fintype.card (Orbit P p) : ZMod 3) := by
      have hi : (↑τ⁻¹ : DyadicMatrix)*T = 1 := by
        rw [← hτval]
        exact Units.inv_mul τ
      change dyadicGyration p (originalRows (τ : DyadicMatrix))
        (originalRows (↑τ⁻¹*T)) = _
      rw [hτval, hi, originalRows_one, hA]
      exact (SourceOnly.PresentationTimeCochain.time_calibration P c p hp).2
    have hQvalue (p : ℕ) [NeZero p] (hp : 3 ∣ p) :
        columnGyration p (Q : DyadicMatrix) (↑Q⁻¹*T) =
          columnGyration p (U : DyadicMatrix) (↑U⁻¹*T) +
            (Fintype.card (Orbit P p) : ZMod 3)*(s : ZMod 3) := by
      have he := SourceOnly.CentralizerTimePowers.translated_value T
        (columnGyration p) (columnGyration_triangle hp) τ U hτval s
      rw [hcal p hp] at he
      have hs : s = -(N : ℤ) := by omega
      have hpow : τ^s = (τ⁻¹)^N := by
        simp only [hs, zpow_neg, zpow_natCast, inv_pow]
      rw [hpow, mul_comm (s : ZMod 3)] at he
      exact he
    have hperiod (p : ℕ) [NeZero p] (hp : 3 ∣ p) :
        ZMod.castHom hp (ZMod 3)
          (historyGyration (F := P) h.val.toEquiv (commute_translate G h) p) =
        Multiplicative.toAdd (gamma p hp (ResetQ4OriginalLocalizedCubes.originalImage h)) := by
      have hweight := hw p hp
      rw [← hR, ← hA, ← hS] at hweight
      have hhistoryValue := corrected_localized_word w s h.val.toEquiv
        (commute_translate G h) hhistory p hp
      rw [hweight.2] at hhistoryValue
      change ZMod.castHom hp (ZMod 3)
        (historyGyration (F := P) h.val.toEquiv (commute_translate G h) p) =
          columnGyration p
            ((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ) : DyadicMatrix)
            (↑((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ)⁻¹)*T)
      rw [hForward, hBackwardFactor]
      exact hhistoryValue.trans (hQvalue p hp).symm

    let C := resetMatrix 4
    let u : MonoidAlgebra ℕ Sign := MonoidAlgebra.single (Multiplicative.ofAdd true) 1
    have hu : u * u = 1 := by
      simp only [u, MonoidAlgebra.single_mul_single,
        show (Multiplicative.ofAdd true : Sign) * Multiplicative.ofAdd true = 1 from rfl,
        one_mul, MonoidAlgebra.one_def]

    /- Actual reset rows: reset to (0,!sign), or increment with unchanged sign.
    Every displayed 1 is the sole numbered edge of that allowed transition. -/
    have hC : C = !![u, 1, 0, 0; u, 0, 1, 0; u, 0, 0, 1; u, 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [C, resetMatrix, u, MonoidAlgebra.one_def]
    have hC2 : C ^ 2 =
        !![1+u, u, 1, 0; 1+u, u, 0, 1; 1+u, u, 0, 0; 1, u, 0, 0] := by
      rw [pow_two, hC]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, hu] <;> ring
    have hC3 : C ^ 3 =
        !![2+2*u, 1+u, u, 1; 2+2*u, 1+u, u, 0;
           2+u, 1+u, u, 0; 1+u, 1, u, 0] := by
      rw [show C^3 = C^2*C from pow_succ C 2, hC2, hC]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, add_mul, mul_add, hu] <;> ring
    have ht1 : (∑ i : Fin 4, (C^1) i i) = (0 : MonoidAlgebra ℕ Sign)+1*u := by
      rw [pow_one, hC]
      simp [Fin.sum_univ_succ]
    have ht2 : (∑ i : Fin 4, (C^2) i i) = (1 : MonoidAlgebra ℕ Sign)+2*u := by
      rw [hC2]
      simp [Fin.sum_univ_succ] <;> ring
    have ht3 : (∑ i : Fin 4, (C^3) i i) = (3 : MonoidAlgebra ℕ Sign)+4*u := by
      rw [hC3]
      simp [Fin.sum_univ_succ] <;> ring
    have ht6 : (∑ i : Fin 4, (C^6) i i) = (25 : MonoidAlgebra ℕ Sign)+26*u := by
      rw [show C^6 = C^3*C^3 from pow_add C 3 3, hC3]
      simp [Matrix.mul_apply, Fin.sum_univ_succ, add_mul, mul_add, mul_assoc, hu] <;>
        ring_nf <;> simp only [pow_two, hu] <;> ring

    have coeff_affine (a b : ℕ) :
        ((a : MonoidAlgebra ℕ Sign)+b*u).coeff 1 = a := by
      have hn : (Multiplicative.ofAdd true : Sign) ≠ 1 := by
        intro e
        exact Bool.noConfusion (congrArg Multiplicative.toAdd e)
      change ((MonoidAlgebra.single 1 a) +
        (MonoidAlgebra.single 1 b) *
          (MonoidAlgebra.single (Multiplicative.ofAdd true) 1)).coeff 1 = a
      simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_add,
        MonoidAlgebra.coeff_single, hn, eq_comm]

    /- Identity twist is literally the original fixed-period set. The two
    signs are actual initial coordinates, not a quotient or multiplicity premise. -/
    have fixed_card (n : ℕ) (hn : 0 < n) :
        Nat.card (Periodic P n) = 2 * ((∑ i : Fin 4, (C^n) i i).coeff 1) := by
      have hunit (x : History (expandedGraph C)) : groupHistory C 1 x = x := by
        apply Subtype.ext
        funext t
        exact Prod.ext rfl (one_mul _)
      let e : Periodic P n ≃ TwistedPeriod C 1 n := {
        toFun := fun x => ⟨x.val, by rw [hunit]; exact x.property⟩
        invFun := fun x => ⟨x.val, by simpa only [hunit] using x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      letI := twistedPeriodFintype C 1 hn
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, twistedPeriod_card C 1 hn]
      have hsign : Fintype.card Sign = 2 := by
        simp only [Sign, Fintype.card_multiplicative, Fintype.card_bool]
      calc
        _ = ∑ i : Fin 4, 2 * (((C^n) i i).coeff 1) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [mul_one, inv_mul_cancel, Finset.sum_const,
            Finset.card_univ, hsign, nsmul_eq_mul]
        _ = 2 * (∑ i : Fin 4, ((C^n) i i).coeff 1) := (Finset.mul_sum _ _ _).symm
        _ = _ := by
          congr 1
          simp [Fin.sum_univ_succ, MonoidAlgebra.coeff_add]

    have hp1 : Nat.card (Periodic P 1) = 0 := by
      rw [fixed_card 1 (by omega), ht1, coeff_affine 0 1]
      norm_num
    have hp2 : Nat.card (Periodic P 2) = 2 := by
      rw [fixed_card 2 (by omega), ht2, coeff_affine 1 2]
      norm_num
    have hp3 : Nat.card (Periodic P 3) = 6 := by
      rw [fixed_card 3 (by omega), ht3, coeff_affine 3 4]
      norm_num
    have hp6 : Nat.card (Periodic P 6) = 50 := by
      rw [fixed_card 6 (by omega), ht6, coeff_affine 25 26]
      norm_num

    let primitiveCount (d : ℕ) := Nat.card (Primitive P d)
    have split_card (n : ℕ) [NeZero n] :
        Nat.card (Periodic P n) = ∑ d ∈ n.divisors, primitiveCount d := by
      let f := shift P.graph
      have periodic_iff (x : Hist P) :
          Function.IsPeriodicPt f n x ↔ Function.minimalPeriod f x ∈ n.divisors := by
        rw [Function.isPeriodicPt_iff_minimalPeriod_dvd, Nat.mem_divisors]
        exact (and_iff_left (NeZero.ne n)).symm
      letI (d : {d : ℕ // d ∈ n.divisors}) :
          Finite {x : Hist P // Function.minimalPeriod f x = d.val} := by
        let e : {x : Hist P // Function.minimalPeriod f x = d.val} ↪ Periodic P n :=
          Subtype.impEmbedding (fun x hx => (periodic_iff x).mpr (hx ▸ d.property))
        exact Finite.of_injective e e.injective
      calc
        _ = Nat.card (Σ d : {d : ℕ // d ∈ n.divisors},
            {x : Hist P // Function.minimalPeriod f x = d.val}) :=
          Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype
            (Function.minimalPeriod f) periodic_iff).symm
        _ = ∑ d : {d : ℕ // d ∈ n.divisors},
            Nat.card {x : Hist P // Function.minimalPeriod f x = d.val} := Nat.card_sigma
        _ = _ := by rw [Finset.sum_coe_sort]; rfl
    have hd6 : (6 : ℕ).divisors = {1,2,3,6} := by
      ext m
      constructor
      · intro hm
        have hd := Nat.dvd_of_mem_divisors hm
        have hpos := Nat.pos_of_mem_divisors hm
        have hle := Nat.le_of_dvd (by omega : 0 < 6) hd
        interval_cases m <;> norm_num at hd ⊢
      · intro hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hm | hm | hm | hm <;> subst m <;> norm_num [Nat.mem_divisors]
    have hs1 : Nat.card (Periodic P 1) = primitiveCount 1 := by
      simpa only [Nat.divisors_one, Finset.sum_singleton] using split_card 1
    have hs2 : Nat.card (Periodic P 2) = primitiveCount 1 + primitiveCount 2 := by
      simpa [Nat.prime_two.divisors] using split_card 2
    have hs3 : Nat.card (Periodic P 3) = primitiveCount 1 + primitiveCount 3 := by
      simpa [Nat.prime_three.divisors] using split_card 3
    have hs6 : Nat.card (Periodic P 6) = primitiveCount 1 + primitiveCount 2 + primitiveCount 3 + primitiveCount 6 := by
      simpa [hd6, add_assoc] using split_card 6
    have hq1 : primitiveCount 1 = 0 := by omega
    have hq2 : primitiveCount 2 = 2 := by omega
    have hq3 : primitiveCount 3 = 6 := by omega
    have hq6 : primitiveCount 6 = 42 := by omega
    have n3 : Fintype.card (Orbit P 3) = 2 := by
      have hc := primitivePath_card_eq_period_mul_orbit_card (matrix P) 3
      rw [Fintype.card_congr (primitiveChart P 3),
        Fintype.card_congr (orbitChart P 3)] at hc
      change Nat.card (Primitive P 3) = 6 at hq3
      rw [Nat.card_eq_fintype_card] at hq3
      omega
    have n6 : Fintype.card (Orbit P 6) = 7 := by
      have hc := primitivePath_card_eq_period_mul_orbit_card (matrix P) 6
      rw [Fintype.card_congr (primitiveChart P 6),
        Fintype.card_congr (orbitChart P 6)] at hc
      change Nat.card (Primitive P 6) = 42 at hq6
      rw [Nat.card_eq_fintype_card] at hq6
      omega


    -- The separate period contributions are 2*s and 7*s. They cancel
    -- only after the actual period-3 and period-6 orbit counts are proved.
    have hcancel :
        (Fintype.card (Orbit P 3) : ZMod 3)*(s : ZMod 3) +
          (Fintype.card (Orbit P 6) : ZMod 3)*(s : ZMod 3) = 0 := by
      rw [n3,n6]
      change (2 : ZMod 3)*(s : ZMod 3) + (1 : ZMod 3)*(s : ZMod 3) = 0
      rw [← add_mul, show (2 : ZMod 3)+1 = 0 by decide, zero_mul]
    have hsumcancel (x y : ZMod 3) :
        (x+(Fintype.card (Orbit P 3) : ZMod 3)*(s : ZMod 3)) +
          (y+(Fintype.card (Orbit P 6) : ZMod 3)*(s : ZMod 3)) = x+y := by
      calc
        _ = (x+y) + ((Fintype.card (Orbit P 3) : ZMod 3)*(s : ZMod 3) +
          (Fintype.card (Orbit P 6) : ZMod 3)*(s : ZMod 3)) := by abel
        _ = x+y := by rw [hcancel,add_zero]
    have hsum :
        historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
          reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6) =
        Multiplicative.toAdd (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) := by
      have hweight3 := (hw 3 (by decide)).2
      have hweight6 := (hw 6 (by decide)).2
      rw [← hR, ← hA, ← hS] at hweight3 hweight6
      have hh3 := corrected_localized_word w s h.val.toEquiv
        (commute_translate G h) hhistory 3 (by decide)
      have hh6 := corrected_localized_word w s h.val.toEquiv
        (commute_translate G h) hhistory 6 (by decide)
      have hid : ZMod.castHom (dvd_refl 3) (ZMod 3) = RingHom.id (ZMod 3) :=
        ZMod.castHom_self
      rw [hid,RingHom.id_apply,hweight3] at hh3
      rw [hweight6] at hh6
      have hhistorySum :
          historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
            reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6) =
          columnGyration 3 (U : DyadicMatrix) (↑U⁻¹*T) +
            columnGyration 6 (U : DyadicMatrix) (↑U⁻¹*T) := by
        change _ + ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3) _ = _
        rw [hh3,hh6]
        exact hsumcancel _ _
      have himageSum :
          Multiplicative.toAdd (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) =
          columnGyration 3 (U : DyadicMatrix) (↑U⁻¹*T) +
            columnGyration 6 (U : DyadicMatrix) (↑U⁻¹*T) := by
        change columnGyration 3
          ((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ) : DyadicMatrix)
          (↑((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ)⁻¹)*T) +
          columnGyration 6
            ((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ) : DyadicMatrix)
            (↑((ResetQ4OriginalLocalizedCubes.originalImage h : DyadicMatrixˣ)⁻¹)*T) = _
        rw [hForward,hBackwardFactor,hQvalue 3 (by decide),hQvalue 6 (by decide)]
        exact hsumcancel _ _
      exact hhistorySum.trans himageSum.symm
    let psi := fun f : ResetFullAut 4 =>
      Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
        (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
          (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
            (ResetFullStandardBeamRepresentation.rho 4 (by decide) f)
            (ResetHistoryKernel.rho_time 4 (by decide) f)))
    let chi_add : ResetFullAut 4 → ZMod 3 := fun f =>
      ResetQ4UnitCubes.residueQuotientCharacter
        (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
        ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
            (psi f)))
    obtain ⟨i,j,v,hfactor,hnative⟩ :=
      ResetQ4OriginalLocalizedCubes.original_character_factorization h
    have hnativeValue : chi_add h = (j.val : ZMod 3) := by
      change ResetQ4UnitCubes.residueQuotientCharacter
        (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4)))
        ResetQ4OriginalLocalizedCubes.original_time_residue (Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.zpowers (psi (StandardBeamHomeomorphisms.unitShift (ResetGraph 4))))
          (Units.map (ResetIntegralGluing.rplus 4).toMonoidHom
            (Units.map (ResetIntegralGluing.plus 4).toMonoidHom
              (ResetNativeUnitNormalForm.scalarUnit 4 (by decide)
                (rho 4 (by decide) h) (ResetHistoryKernel.rho_time 4 (by decide) h)))))) = _
      rw [ResetQ4UnitCubes.residueQuotientCharacter_plus]
      exact hnative
    -- Actual time and I+T calibrations are local to this universal root.
    -- These retained decide +kernel bodies have not been executed.
    have hGammaTime :
        Multiplicative.toAdd (Gamma ResetQ4OriginalLocalizedCubes.time) = (0 : ZMod 3) := by
      have hR : ∀ i j : Fin 8,
          originalAdjacency i j = 0 ∨ originalAdjacency i j = 1 := by decide
      have hS : ∀ i j : Fin 8,
          (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = -1 ∨
          (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = 0 ∨
          (1 : Matrix (Fin 8) (Fin 8) ℤ) i j = 1 := by decide
      have h3Shard (i : Fin 8) :
          prunedShard 2 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
            (![-4,0,0,0,0,0,0,0] : Fin 8 → ℤ) i := by
        fin_cases i <;> decide +kernel
      have h6Shard (i : Fin 8) :
          prunedShard 5 originalAdjacency (1 : Matrix (Fin 8) (Fin 8) ℤ) i =
            (![-35,0,0,0,0,0,0,0] : Fin 8 → ℤ) i := by
        fin_cases i <;> decide +kernel
      have h3 :
          integerGyrationValue 3 originalAdjacency 1 = -4 := by
        rw [integerGyrationValue_eq_supportedEvaluator 3 _ _ hR hS,
          supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 2]
        simp_rw [h3Shard]
        norm_num [Fin.sum_univ_succ]
      have h6 :
          integerGyrationValue 6 originalAdjacency 1 = -35 := by
        rw [integerGyrationValue_eq_supportedEvaluator 6 _ _ hR hS,
          supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 5]
        simp_rw [h6Shard]
        norm_num [Fin.sum_univ_succ]
      change Multiplicative.toAdd (gamma 3 (by decide) ResetQ4OriginalLocalizedCubes.time) +
          Multiplicative.toAdd (gamma 6 (by decide) ResetQ4OriginalLocalizedCubes.time) = 0
      rw [gamma_time_signed_evaluation, gamma_time_signed_evaluation,
        h3, h6]
      norm_num

    have hGammaOnePlus :
        Multiplicative.toAdd
            (Gamma ResetQ4OriginalLocalizedCubes.onePlusTime) = (2 : ZMod 3) := by
      have hR : ∀ i j : Fin 8,
          (1 + originalAdjacency) i j = 0 ∨ (1 + originalAdjacency) i j = 1 := by
        decide
      have hS : ∀ i j : Fin 8,
          onePlusSignedFactor i j = -1 ∨ onePlusSignedFactor i j = 0 ∨
            onePlusSignedFactor i j = 1 := by
        decide
      have h3Shard : ∀ i : Fin 8,
          prunedShard 2 (1 + originalAdjacency) onePlusSignedFactor i =
            (![(-1 : ℤ), -1, -1, -2, -1, -2, 0, 0] : Fin 8 → ℤ) i := by
        intro i
        fin_cases i <;> decide +kernel
      have h6Shard : ∀ i : Fin 8,
          prunedShard 5 (1 + originalAdjacency) onePlusSignedFactor i =
            (![(-31 : ℤ), -10, -8, 2, -5, 3, -4, 0] : Fin 8 → ℤ) i := by
        intro i
        fin_cases i <;> decide +kernel
      have h3 :
          integerGyrationValue 3 (1 + originalAdjacency) onePlusSignedFactor = -8 := by
        rw [integerGyrationValue_eq_supportedEvaluator 3 _ _ hR hS,
          supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 2]
        simp_rw [h3Shard]
        norm_num [Fin.sum_univ_succ]
      have h6 :
          integerGyrationValue 6 (1 + originalAdjacency) onePlusSignedFactor = -53 := by
        rw [integerGyrationValue_eq_supportedEvaluator 6 _ _ hR hS,
          supportedEvaluator_eq_pruned, prunedEvaluator_eq_shards 5]
        simp_rw [h6Shard]
        norm_num [Fin.sum_univ_succ]
      change Multiplicative.toAdd
          (gamma 3 (by decide) ResetQ4OriginalLocalizedCubes.onePlusTime) +
          Multiplicative.toAdd
            (gamma 6 (by decide) ResetQ4OriginalLocalizedCubes.onePlusTime) = 2
      rw [gamma_onePlus_signed_evaluation, gamma_onePlus_signed_evaluation, h3, h6]
      norm_num

    have hGamma : Multiplicative.toAdd
        (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) = (j.val : ZMod 3)*2 := by
      rw [hfactor, map_mul, map_mul, map_pow, map_pow, map_pow]
      change i.val • Multiplicative.toAdd (Gamma ResetQ4OriginalLocalizedCubes.time) +
        j.val • Multiplicative.toAdd (Gamma ResetQ4OriginalLocalizedCubes.onePlusTime) +
        3 • Multiplicative.toAdd (Gamma v) = (j.val : ZMod 3)*2
      rw [hGammaTime, hGammaOnePlus]
      simp [nsmul_eq_mul]
    have hcharacter : chi_add h = 2*Multiplicative.toAdd
        (Gamma (ResetQ4OriginalLocalizedCubes.originalImage h)) := by
      rw [hnativeValue, hGamma]
      have hfour : (2 : ZMod 3)*2 = 1 := by decide
      calc
        (j.val : ZMod 3) = 1*(j.val : ZMod 3) := (one_mul _).symm
        _ = 2*((j.val : ZMod 3)*2) := by rw [← hfour]; ring
    refine ⟨hperiod, ⟨n3,n6⟩, hsum, hcharacter, ?_⟩
    rw [hsum]
    exact hcharacter
  refine ⟨fullroot, ?_⟩
  intro h k hag
  have hagree (x : ResetHistory 4)
      (hx : (shift (ResetGraph 4))^[6] x = x) : h.val x = k.val x :=
    congrFun hag ⟨x, hx⟩
  have hg3 :
      historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 =
        historyGyration (F := P) k.val.toEquiv (commute_translate G k) 3 := by
    apply historyGyration_congr_on_primitive
    intro x
    have hx3 : Function.IsPeriodicPt (shift (ResetGraph 4)) 3 x.val := by
      simpa only [x.property] using
        Function.isPeriodicPt_minimalPeriod (shift P.graph) x.val
    -- The original FORWARD shift cubed fixes x; iterating that equality
    -- twice puts the same original history in the literal Fix(T^6) domain.
    exact hagree x.val (hx3.mul_const 2)
  have hg6 :
      historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6 =
        historyGyration (F := P) k.val.toEquiv (commute_translate G k) 6 := by
    apply historyGyration_congr_on_primitive
    intro x
    have hx6 : Function.IsPeriodicPt (shift (ResetGraph 4)) 6 x.val := by
      simpa only [x.property] using
        Function.isPeriodicPt_minimalPeriod (shift P.graph) x.val
    exact hagree x.val hx6
  calc
    chi_add h = 2*(historyGyration (F := P) h.val.toEquiv (commute_translate G h) 3 +
        reduceSix (historyGyration (F := P) h.val.toEquiv (commute_translate G h) 6)) :=
      (fullroot h).2.2.2.2
    _ = 2*(historyGyration (F := P) k.val.toEquiv (commute_translate G k) 3 +
        reduceSix (historyGyration (F := P) k.val.toEquiv (commute_translate G k) 6)) := by
      rw [hg3, hg6]
    _ = chi_add k := ((fullroot k).2.2.2.2).symm
end D5.S3.ConceptDynamics.Coding

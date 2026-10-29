import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Reg.Support.DependentFamily

/-! Faithful source telescopes for the strict Euler root-correction audit. -/

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.EulerLayerRootCorrection

open _root_.D5.S3.Arith.Robin.EulerLayerRootCorrection
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

/- The complete original telescopes below reconstruct the third-layer bound,
   third-layer vanishing, uniform second-layer limit and final root correction.
   A Contract.Registration requires a dependent-family law on the actual
   factorization/prime-mass readouts, an exact sourceSelection, a rejected
   realization, whole-family variation and sensitivity with other roles fixed,
   and nonconstant actual observational dependence. These additional proofs
   are not supplied by the source reconstructions; no declared_validated
   four-slot registration is claimed. -/

abbrev primeNumberLimitsScope := type_of% prime_number_limits

theorem source_prime_number_limits : primeNumberLimitsScope := prime_number_limits

abbrev primeLimitSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def primeLimitActual : Realization primeLimitSignature :=
  realize primeLimitSignature (fun _ _ t => t) (fun e => nomatch e)

def primeLimitRejected : Realization primeLimitSignature :=
  realize primeLimitSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev primeLimitArena : Arena where
  signature := primeLimitSignature
  Law R := Filter.Tendsto (fun t : ℝ => Chebyshev.psi t / R.readout () () t)
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto (fun t : ℝ => Chebyshev.theta t / t) Filter.atTop (nhds 1)

theorem prime_limit_source_bridge : primeNumberLimitsScope ↔
    primeLimitArena.Law primeLimitActual := Iff.rfl

theorem prime_limit_actual_law : primeLimitArena.Law primeLimitActual := prime_number_limits

private theorem prime_limit_rejected : ¬ primeLimitArena.Law primeLimitRejected := by
  intro h
  have hone : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 1) := by
    simpa [primeLimitRejected, realize] using h.1
  have hzero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at hbad

def primeLimitFamily : Registration primeLimitArena primeNumberLimitsScope where
  actual := primeLimitActual
  bridge := prime_limit_source_bridge
  variation := ⟨prime_number_limits, primeLimitRejected, prime_limit_rejected⟩
  sensitivity := ⟨fun i => ⟨primeLimitRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, prime_limit_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [primeLimitActual, realize]⟩

/-- The first limit's denominator varies; its numerator and the complete second
limit stay literal in the full original conjunction. -/
def primeLimitAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_number_limits) (Realization primeLimitSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerRootCorrection.primeLimitFamily
  realizationSource := none
  generated := false
  arena := .source ⟨primeLimitArena⟩
  objectArena := .source ⟨primeLimitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source primeLimitArena ⟨primeLimitFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize primeLimitSignature primeLimitActual.readout primeLimitActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerRootCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev thirdLayerBoundScope := type_of% (@strict_inventory_third_layer_bound)
theorem source_third_layer_bound : thirdLayerBoundScope :=
  @strict_inventory_third_layer_bound

abbrev thirdLayerVanishingScope := type_of% (@strict_inventory_third_layer_vanishing)
theorem source_third_layer_vanishing : thirdLayerVanishingScope :=
  @strict_inventory_third_layer_vanishing

abbrev secondLayerLimitScope := type_of% (@strict_inventory_second_layer_limit)
theorem source_second_layer_limit : secondLayerLimitScope :=
  @strict_inventory_second_layer_limit

abbrev rootCorrectionScope : Prop := strict_inventory_root_correction_statement
theorem source_root_correction : rootCorrectionScope := @strict_inventory_root_correction

abbrev rootSignature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature :=
  realize rootSignature
    (fun _ t U => (Real.log U - Chebyshev.psi t) / Real.sqrt t)
    (fun e => nomatch e)

/-- The law retains every binder and the complete strict inventory condition. -/
abbrev rootArena : Arena where
  signature := rootSignature
  Law V := ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |V.readout () t U - (Real.sqrt 2 - 1)| < ε

theorem root_source_bridge : rootCorrectionScope ↔ rootArena.Law rootActual := Iff.rfl

theorem root_actual_law : rootArena.Law rootActual := strict_inventory_root_correction

def rootRejected : Realization rootSignature :=
  realize rootSignature (fun _ _ _ => Real.sqrt 2) (fun e => nomatch e)

theorem root_rejected_law : ¬ rootArena.Law rootRejected := by
  intro h
  obtain ⟨T, hT, hbad⟩ := h (1 / 2) (by norm_num)
  have hprice : 0 < 1 / (T * Real.log T) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos hT))
  obtain ⟨U, hU, hcounts, _⟩ := optimal_layer_count_spec hprice
  have hh := hbad T le_rfl U (by omega) (fun q _ => hcounts q)
  change |Real.sqrt 2 - (Real.sqrt 2 - 1)| < (1 / 2 : ℝ) at hh
  have heq : Real.sqrt 2 - (Real.sqrt 2 - 1) = 1 := by ring
  norm_num [heq] at hh

theorem root_actual_dependence : ObservationalDependence rootSignature rootActual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (Real.log (1 : ℕ) - Chebyshev.psi 1) / Real.sqrt 1 ≠
    (Real.log (2 : ℕ) - Chebyshev.psi 1) / Real.sqrt 1
  simp only [Nat.cast_one, Nat.cast_ofNat, Real.log_one, Real.sqrt_one, div_one]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

def rootFamily : Registration rootArena rootCorrectionScope where
  actual := rootActual
  bridge := root_source_bridge
  variation := ⟨root_actual_law, rootRejected, root_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rootRejected,
    fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), root_rejected_law⟩, fun i => nomatch i⟩
  dependence := root_actual_dependence

/- rootFamily supplies the mathematical whole-family obligations. The outer
   Contract.Registration is unfinished: the readout occurrence is inside the
   definition strict_inventory_root_correction_statement, so its exact
   sourceSelection must reconstruct that definition and all its dependent
   binder coordinates. No sourceSelection/current binding certificate is
   supplied, and no declared_validated audit is asserted. The other three
   source reconstructions do not supply dependent-family registrations. -/

#print axioms rootFamily

/- The scale audits vary one literal denominator argument. All positive scale
parameters, limits and the numerators remain in the original telescopes. -/
abbrev scaleSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def scaleActual : Realization scaleSignature :=
  realize scaleSignature (fun _ _ t => t) (fun e => nomatch e)

def thetaScaleRejected : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 0) (fun e => nomatch e)

def logScaleRejected : Realization scaleSignature :=
  realize scaleSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev thetaScaleArena : Arena where
  signature := scaleSignature
  Law R := ∀ {c : ℝ}, 0 < c → Filter.Tendsto
    (fun t : ℝ => Chebyshev.theta (c * Real.sqrt t) / Real.sqrt (R.readout () () t))
    Filter.atTop (nhds c)

abbrev logScaleArena : Arena where
  signature := scaleSignature
  Law R := ∀ {c : ℝ}, 0 < c → Filter.Tendsto
    (fun t : ℝ => Real.log (c * Real.sqrt t) / Real.log (R.readout () () t))
    Filter.atTop (nhds (1 / 2 : ℝ))

private theorem theta_scale_rejected : ¬ thetaScaleArena.Law thetaScaleRejected := by
  intro h
  have hone : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 1) := by
    simpa [thetaScaleRejected, realize] using h (c := 1) (by norm_num)
  have hzero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have hbad := tendsto_nhds_unique hzero hone
  norm_num at hbad

private theorem log_scale_rejected : ¬ logScaleArena.Law logScaleRejected := by
  intro h
  have hhalf : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa [logScaleRejected, realize] using h (c := 1) (by norm_num)
  have hzero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  have hbad := tendsto_nhds_unique hzero hhalf
  norm_num at hbad

def thetaScaleFamily : Registration thetaScaleArena (type_of% (@theta_sqrt_scale)) where
  actual := scaleActual
  bridge := Iff.rfl
  variation := ⟨@theta_sqrt_scale, thetaScaleRejected, theta_scale_rejected⟩
  sensitivity := ⟨fun i => ⟨thetaScaleRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, theta_scale_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [scaleActual, realize]⟩

def logScaleFamily : Registration logScaleArena (type_of% (@log_sqrt_scale)) where
  actual := scaleActual
  bridge := Iff.rfl
  variation := ⟨@log_sqrt_scale, logScaleRejected, log_scale_rejected⟩
  sensitivity := ⟨fun i => ⟨logScaleRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, log_scale_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [scaleActual, realize]⟩

def thetaScaleAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@theta_sqrt_scale) (Realization scaleSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerRootCorrection.theta_sqrt_scale.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerRootCorrection.thetaScaleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨thetaScaleArena⟩
  objectArena := .source ⟨thetaScaleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source thetaScaleArena ⟨thetaScaleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scaleActual.readout scaleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerRootCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def logScaleAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_sqrt_scale) (Realization scaleSignature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerRootCorrection.log_sqrt_scale.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerRootCorrection.logScaleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logScaleArena⟩
  objectArena := .source ⟨logScaleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logScaleArena ⟨logScaleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scaleSignature scaleActual.readout scaleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerRootCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.EulerLayerRootCorrection

import D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
import Reg.Support.UnitSixO.Common

/-! Magnetic moments, the hyperbolic kernel, and electric rates as dependent readouts. -/

open Filter Set LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
open _root_.Reg.Support.UnitSixO (operandSignature)

namespace Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.ProperTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindProperTime% " theoremId:ident groupId:ident ar:term:max fam:term:max
    headId:ident : term => do
  let owner := `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
  let unit := owner ++ theoremId.getId ++ `__information_unit
  let familyName :=
    (`Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.ProperTime ++ groupId.getId ++ `family)
  `({ unitName := $(Lean.quote unit)
      realizationName := $(Lean.quote familyName)
      realizationSource := none
      generated := false
      arena := .source ⟨$ar⟩
      objectArena := .source ⟨$ar⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $ar ⟨$fam⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some (unitObserve% $headId)
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D
        definition := none
        coordinates := #[]
        readouts := #[{
          path := unitPath% $theoremId $headId 0 0
          stateBinder := 0
          functionOperand := true
          stateOperand := none
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

namespace Magnetic

abbrev arena : Arena where
  signature := operandSignature ℝ ℝ
  Law R := ∀ (e m B : ℝ), 0 < m →
    R.readout () () m = 1 / m ^ 4 ∧
    let α := e ^ 2 / (4 * Real.pi)
    let C := ((e * B) ^ 4 / (360 * Real.pi ^ 2)) * R.readout () () m
    C = (2 * α ^ 2 / (45 * m ^ 4)) * B ^ 4 ∧
    eulerHeisenbergLagrangian α m (0 : Fin 3 → ℝ) ![0, 0, B] = -(B ^ 2) / 2 + C

def family : Registration arena (type_of% (@euler_heisenberg_proper_time_quartic_coeff)) :=
  unitFamily% arena (@euler_heisenberg_proper_time_quartic_coeff)
    (unitObserve% magneticProperTimeMoment) (unitObserve% (fun _ : ℝ => (0 : ℝ)))
    (by
      intro h
      have hh := (h 1 1 1 (by norm_num)).1
      norm_num [realize] at hh)
    (by
      refine ⟨(), 1, 2, fun h => ?_⟩
      change magneticProperTimeMoment 1 = magneticProperTimeMoment 2 at h
      rw [(euler_heisenberg_proper_time_quartic_coeff 1 1 1 (by norm_num)).1,
        (euler_heisenberg_proper_time_quartic_coeff 1 2 1 (by norm_num)).1] at h
      norm_num at h)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@euler_heisenberg_proper_time_quartic_coeff)
    (Realization (operandSignature ℝ ℝ)) Unit Unit :=
  bindProperTime% euler_heisenberg_proper_time_quartic_coeff Magnetic arena family
    magneticProperTimeMoment

end Magnetic

namespace Hyperbolic

abbrev arena : Arena where
  signature := operandSignature ℝ ℝ
  Law R := Tendsto (fun x => R.readout () () x) (𝓝[≠] 0) (𝓝 (-(1 / 45)))

def family : Registration arena (type_of% (@euler_heisenberg_coth_quartic_limit)) :=
  unitFamily% arena (@euler_heisenberg_coth_quartic_limit)
    (unitObserve% cothQuarticQuotient) (unitObserve% (fun _ : ℝ => (0 : ℝ)))
    (by
      intro h
      have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_const_nhds
      have h' := tendsto_nhds_unique hzero h
      norm_num at h')
    (by
      have h : ∃ x, cothQuarticQuotient x ≠ 0 := by
        by_contra! h
        have hc : cothQuarticQuotient = fun _ => 0 := funext h
        have ht := euler_heisenberg_coth_quartic_limit
        rw [hc] at ht
        have hzero : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 0) :=
          tendsto_const_nhds
        have h' := tendsto_nhds_unique hzero ht
        norm_num at h'
      obtain ⟨x, hx⟩ := h
      exact ⟨(), x, 0, by simpa [realize, cothQuarticQuotient, Real.sinh_zero] using hx⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@euler_heisenberg_coth_quartic_limit) (Realization (operandSignature ℝ ℝ)) Unit Unit :=
  bindProperTime% euler_heisenberg_coth_quartic_limit Hyperbolic arena family cothQuarticQuotient

end Hyperbolic

namespace Electric

abbrev signature : Signature := operandSignature ℝ (ℝ → ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e m : ℝ), 0 < e → 0 < m →
    (∀ E : ℝ, 0 < E →
      Summable (schwingerSummand e m E) ∧
      ((e * E) ^ 2 / (4 * Real.pi ^ 3)) * Real.exp (-(Real.pi * m ^ 2 / (e * E))) ≤
        R.readout () () e m E ∧
      R.readout () () e m E ≤
        ((e * E) ^ 2 / (24 * Real.pi)) * Real.exp (-(Real.pi * m ^ 2 / (e * E)))) ∧
    ∀ k : ℕ, Tendsto (fun E => R.readout () () e m E / E ^ k) (𝓝[>] 0) (𝓝 0)

private theorem rate_pos : 0 < schwingerRate 1 1 1 := by
  have h := (schwinger_pair_production_series_and_essential_singularity
    1 1 (by norm_num) (by norm_num)).1 1 (by norm_num)
  exact (by positivity : 0 < ((1 * 1) ^ 2 / (4 * Real.pi ^ 3)) *
    Real.exp (-(Real.pi * 1 ^ 2 / (1 * 1)))).trans_le h.2.1

def family :
    Registration arena (type_of% (@schwinger_pair_production_series_and_essential_singularity)) :=
  unitFamily% arena (@schwinger_pair_production_series_and_essential_singularity)
    (unitObserve% schwingerRate) (unitObserve% (fun _ _ _ : ℝ => (0 : ℝ)))
    (by
      intro h
      have hh := ((h 1 1 (by norm_num) (by norm_num)).1 1 (by norm_num)).2.1
      exact (not_le_of_gt (by positivity : 0 < ((1 * 1) ^ 2 / (4 * Real.pi ^ 3)) *
        Real.exp (-(Real.pi * 1 ^ 2 / (1 * 1))))) hh)
    (by
      refine ⟨(), 1, 0, fun h => ?_⟩
      have hh := congrFun (congrFun h 1) 1
      change schwingerRate 1 1 1 = schwingerRate 0 1 1 at hh
      have hz : schwingerRate 0 1 1 = 0 := by simp [schwingerRate]
      exact rate_pos.ne' (hh.trans hz))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@schwinger_pair_production_series_and_essential_singularity)
    (Realization signature) Unit Unit :=
  bindProperTime% schwinger_pair_production_series_and_essential_singularity Electric
    arena family schwingerRate

end Electric

end
end Reg.D5.S3.Quantum.Gauge.DiracLandauEulerHeisenberg4D.ProperTime

import D5.S3.Analytic.Resolvent.PoissonKernelTail
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! The reciprocal-square tail reads the actual weight family in its total-mass bound. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail

open _root_.D5.S3.Analytic.Resolvent.PoissonKernelTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

universe v

abbrev signature : Signature where
  Params := Type v
  State ι := ι → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := ι → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature.{v} (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature.{v} (fun _ _ _ _ => 4096) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {ι : Type v} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (_hw : ∀ i, T < |g i| → 0 ≤ w i)
    (_hu : ∀ i, T < |g i| → 0 < w i → 0 ≤ u i)
    (_hT : 32 < T)
    (_hbound : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2),
    (∀ J : Finset ι,
      (∑ i ∈ J, massRatio (u i) * tailTerm g T w i ≤ tailBound q T -
        (finiteCorrection q T (fun i => 1 * g i) w J +
          finiteCorrection q T (fun i => -1 * g i) w J)) ∧
      tailBound q T - (finiteCorrection q T (fun i => 1 * g i) w J +
        finiteCorrection q T (fun i => -1 * g i) w J) < tailBound q T) ∧
    Summable (fun i => massRatio (u i) * tailTerm g T w i) ∧
    (∑' i, massRatio (u i) * tailTerm g T (R.readout () ι w) i) ≤ tailBound q T ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 →
      (∀ J : Finset ι,
        (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
          tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
          tailBound q T / 2) ∧
      Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
      (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ≤
        tailBound q T / 2) ∧
    ((∀ i, T < |g i| → 0 < w i → 0 < u i ∧ u i ≤ 2) →
      (∀ J : Finset ι,
        (∑ i ∈ J, tailTerm g T w i) ≤
          (∑ i ∈ J, massRatio (u i) * tailTerm g T w i)) ∧
      Summable (tailTerm g T w) ∧
      (∑' i, tailTerm g T w i) ≤ tailBound q T ∧
      (∀ s : ℝ, s = 1 ∨ s = -1 →
        (∀ J : Finset ι,
          (∑ i ∈ J, positiveTerm (fun i => s * g i) T w i) ≤
            (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i)) ∧
        Summable (positiveTerm (fun i => s * g i) T w) ∧
        (∑' i, positiveTerm (fun i => s * g i) T w i) ≤ tailBound q T / 2))

private theorem rejected_law : ¬ arena.{v}.Law rejected.{v} := by
  intro h
  have hh := h (ι := ULift.{v} Unit) (fun _ => 2) (fun _ => 34) 0 33
    (fun _ => 0) (by intro i; norm_num) (by intro i; norm_num) (by norm_num)
    (by intro s hs t ht J hJ; norm_num)
  have ht := hh.2.2.1
  have hc : 1 < 2 * Real.arctan 8 := by
    have h := Real.arctan_mono (show (1 : ℝ) ≤ 8 by norm_num)
    rw [Real.arctan_one] at h
    linarith [Real.pi_gt_three]
  have hb : tailBound 0 33 < 1 := by
    convert (inv_lt_one₀ (by linarith : 0 < 2 * Real.arctan 8)).2 hc using 1
    norm_num [tailBound, mul_inv_rev]
  have hr : massRatio 2 = 1 := by
    unfold massRatio
    norm_num only [show (16 : ℝ) / 2 = 8 by norm_num]
    exact div_self (by linarith)
  norm_num [tailTerm, rejected, realize, tsum_fintype, hr] at ht
  linarith

private theorem dependence : ObservationalDependence signature.{v} actual.{v} := by
  intro i
  refine ⟨ULift.{v} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (ULift.up ())
  norm_num [actual, realize] at hh

def family : Registration arena.{v} (type_of% @reciprocalSquare_tail_bound.{v}) where
  actual := actual.{v}
  bridge := Iff.rfl
  variation := ⟨@reciprocalSquare_tail_bound.{v}, rejected.{v}, rejected_law.{v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{v}, ?_, rfl, rejected_law.{v}⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{v}

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reciprocalSquare_tail_bound.{v}) (Realization signature.{v}) Type Unit where
  unitName :=
    `D5.S3.Analytic.Resolvent.PoissonKernelTail.reciprocalSquare_tail_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{v}⟩
  objectArena := .source ⟨arena.{v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{v} ⟨family.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.PoissonKernelTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev sideArena : Arena where
  signature := signature.{v}
  Law R := ∀ {ι : Type v} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (s : ℝ) (_hs : s = 1 ∨ s = -1)
    (_hw : ∀ i, T < s * g i → 0 ≤ w i)
    (_hu : ∀ i, T < s * g i → 0 < w i → 0 < u i ∧ u i ≤ 2)
    (_hT : 32 < T)
    (_hbound : ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2),
    (∀ J : Finset ι,
      (∑ i ∈ J, positiveTerm (fun i => s * g i) T w i) ≤
        (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
      (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
      tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
        tailBound q T / 2) ∧
    Summable (positiveTerm (fun i => s * g i) T w) ∧
    (∑' i, positiveTerm (fun i => s * g i) T (R.readout () ι w) i) ≤ tailBound q T / 2 ∧
    Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
    (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ≤
      tailBound q T / 2

private theorem sideRejected_law : ¬ sideArena.{v}.Law rejected.{v} := by
  intro h
  have hh := h (ι := ULift.{v} Unit) (fun _ => 1) (fun _ => 34) 0 33
    (fun _ => 0) 1 (Or.inl rfl) (by intro i; norm_num) (by intro i; norm_num) (by norm_num)
    (by intro t ht J hJ; norm_num)
  have ht := hh.2.2.1
  have hc : 1 < 2 * Real.arctan 8 := by
    have h := Real.arctan_mono (show (1 : ℝ) ≤ 8 by norm_num)
    rw [Real.arctan_one] at h
    linarith [Real.pi_gt_three]
  have hb : tailBound 0 33 < 1 := by
    convert (inv_lt_one₀ (by linarith : 0 < 2 * Real.arctan 8)).2 hc using 1
    norm_num [tailBound, mul_inv_rev]
  norm_num [positiveTerm, rejected, realize, tsum_fintype] at ht
  linarith

def sideFamily : Registration sideArena.{v} (type_of% @reciprocalSquare_side_bound.{v}) where
  actual := actual.{v}
  bridge := Iff.rfl
  variation := ⟨@reciprocalSquare_side_bound.{v}, rejected.{v}, sideRejected_law.{v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{v}, ?_, rfl, sideRejected_law.{v}⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{v}

def sideAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reciprocalSquare_side_bound.{v}) (Realization signature.{v}) Type Unit where
  unitName :=
    `D5.S3.Analytic.Resolvent.PoissonKernelTail.reciprocalSquare_side_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail.sideFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sideArena.{v}⟩
  objectArena := .source ⟨sideArena.{v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source sideArena.{v} ⟨sideFamily.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.PoissonKernelTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev massSideArena : Arena where
  signature := signature.{v}
  Law R := ∀ {ι : Type v} (u g : ι → ℝ) (q T : ℝ)
    (w : ι → ℝ) (s : ℝ) (_hs : s = 1 ∨ s = -1)
    (_hw : ∀ i, T < s * g i → 0 ≤ w i)
    (_hu : ∀ i, T < s * g i → 0 < w i → 0 ≤ u i)
    (_hT : 32 < T)
    (_hbound : ∀ t : ℝ, T - 16 ≤ t → ∀ J : Finset ι,
      (∀ i ∈ J, T < s * g i) →
      ∑ i ∈ J, w i * kernel (u i) (g i) (s * t) ≤
        (Real.log (q * (t + 3)) + 1) / 2),
    (∀ J : Finset ι,
      (∑ i ∈ J, massRatio (u i) * positiveTerm (fun i => s * g i) T w i ≤
        tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J) ∧
      tailBound q T / 2 - finiteCorrection q T (fun i => s * g i) w J <
        tailBound q T / 2) ∧
    Summable (fun i => massRatio (u i) * positiveTerm (fun i => s * g i) T w i) ∧
    (∑' i, massRatio (u i) * positiveTerm (fun i => s * g i) T (R.readout () ι w) i) ≤
      tailBound q T / 2

private theorem massSideRejected_law : ¬ massSideArena.{v}.Law rejected.{v} := by
  intro h
  have hh := h (ι := ULift.{v} Unit) (fun _ => 2) (fun _ => 34) 0 33
    (fun _ => 0) 1 (Or.inl rfl) (by intro i; norm_num) (by intro i; norm_num) (by norm_num)
    (by intro t ht J hJ; norm_num)
  have ht := hh.2.2
  have hc : 1 < 2 * Real.arctan 8 := by
    have h := Real.arctan_mono (show (1 : ℝ) ≤ 8 by norm_num)
    rw [Real.arctan_one] at h
    linarith [Real.pi_gt_three]
  have hb : tailBound 0 33 < 1 := by
    convert (inv_lt_one₀ (by linarith : 0 < 2 * Real.arctan 8)).2 hc using 1
    norm_num [tailBound, mul_inv_rev]
  have hr : massRatio 2 = 1 := by
    unfold massRatio
    norm_num only [show (16 : ℝ) / 2 = 8 by norm_num]
    exact div_self (by linarith)
  norm_num [positiveTerm, rejected, realize, tsum_fintype, hr] at ht
  linarith

def massSideFamily :
    Registration massSideArena.{v} (type_of% @reciprocalSquare_mass_side_bound.{v}) where
  actual := actual.{v}
  bridge := Iff.rfl
  variation := ⟨@reciprocalSquare_mass_side_bound.{v}, rejected.{v}, massSideRejected_law.{v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{v}, ?_, rfl, massSideRejected_law.{v}⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence.{v}

def massSideAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reciprocalSquare_mass_side_bound.{v}) (Realization signature.{v}) Type Unit where
  unitName :=
    `D5.S3.Analytic.Resolvent.PoissonKernelTail.reciprocalSquare_mass_side_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail.massSideFamily
  realizationSource := none
  generated := false
  arena := .source ⟨massSideArena.{v}⟩
  objectArena := .source ⟨massSideArena.{v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source massSideArena.{v} ⟨massSideFamily.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.PoissonKernelTail
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "fn", "arg",
        "fn", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Continuity

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => cauchyKernel w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ x => if x = 0 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : ℝ, Continuous (R.readout () () w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : Continuous (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) := h 0
  have ho := hc.isOpen_preimage (Set.Ioi (1 / 2 : ℝ)) isOpen_Ioi
  have he : (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) ⁻¹' Set.Ioi (1 / 2) =
      {0} := by
    ext x
    by_cases hx : x = 0 <;> norm_num [hx]
  rw [he] at ho
  exact not_isOpen_singleton (0 : ℝ) ho

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize, cauchyKernel] at hh

def family : Registration arena (type_of% cauchyKernel_continuous) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cauchyKernel_continuous, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    cauchyKernel_continuous (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.Resolvent.PoissonKernelTail.cauchyKernel_continuous.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => cauchyKernel w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.PoissonKernelTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuity

namespace WindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => Real.arctan t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Real.pi - 1 / 4 < 2 * R.readout () () 8

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change Real.pi - 1 / 4 < 2 * (-1) at h
  linarith [Real.pi_gt_three]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp only [actual, realize, Real.arctan_zero, Real.arctan_one]
  exact ne_of_lt (div_pos Real.pi_pos (by norm_num))

def family : Registration arena (type_of% windowMass_gt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨windowMass_gt, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    windowMass_gt (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Analytic.Resolvent.PoissonKernelTail.windowMass_gt
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail.WindowMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.arctan t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Resolvent.PoissonKernelTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WindowMass

end Reg.D5.S3.Analytic.Resolvent.PoissonKernelTail

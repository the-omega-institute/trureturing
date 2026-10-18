import D5.S3.TotalVariation.RandomKernelExtremum
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.RandomKernelExtremum
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.RandomKernelExtremum

namespace Simplex

abbrev signature : Signature where
  Params := ℕ
  State d := Fin d → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Fin d → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d) (s : Fin d → ℝ)
    (_hs : ∀ i, 0 ≤ s i) (_hm : ∑ i, s i = 1),
    1 - rho d ≤ ∑ i, overlap (beta d) (1 - rho d) (r.readout () d s i)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 2) (by decide) (fun _ => 1/2) (fun _ => by norm_num) (by simp)
  have hr : rho 2 = 1/4 := by norm_num [rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton]
  have hb : beta 2 = 1/4 := by norm_num [rho] at hr; exact hr
  norm_num [rejected, realize, overlap, hr, hb] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, Pi.single (0 : Fin 2) 1, Pi.single (1 : Fin 2) 1, ?_⟩
  intro h
  have he := congrFun h (0 : Fin 2)
  norm_num [actual, realize, Pi.single_apply] at he

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.sharp_simplex_overlap_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.sharp_simplex_overlap_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.sharp_simplex_overlap_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Simplex.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Simplex.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Simplex

namespace Active

abbrev signature : Signature where
  Params := ℕ
  State d := Fin d × Fin d → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Fin d × Fin d → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d) (p : Fin d × Fin d → ℝ)
    (_hp : ∀ z, 0 ≤ p z) (_hm : ∑ z, p z = 1),
    totalVariation (optimalActive (r.readout () d p))
      (fun z => (∑ j, p (z.1,j)) * (∑ i, p (i,z.2))) ≤ rho d

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Fin 2 × Fin 2 → ℝ := Pi.single (0,0) 1
  have hp : ∀ z, 0 ≤ p z := by intro z; simp [p, Pi.single_apply]; positivity
  have hh := h (d := 2) (by decide) p hp (by simp [p])
  have hc : (Finset.univ.filter (fun x : Fin 2 => x = 0)).card = 1 := by decide
  norm_num [hc, rejected, realize, optimalActive, firstOutput, totalVariation,
    Fintype.sum_prod_type, Fin.sum_univ_two, p, Pi.single_apply, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, Pi.single ((0,0) : Fin 2 × Fin 2) 1,
    Pi.single ((1,1) : Fin 2 × Fin 2) 1, ?_⟩
  intro h
  have he := congrFun h ((0,0) : Fin 2 × Fin 2)
  norm_num [actual, realize, Pi.single_apply] at he

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.active_joint_upper_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.active_joint_upper_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.active_joint_upper_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Active.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Active.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Active

namespace Upper

abbrev signature : Signature where
  Params := ℕ
  State d := Option (Fin d × Fin d) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Option (Fin d × Fin d) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d),
    ((∀ x y, 0 ≤ optimalKernel d x y) ∧ ∀ y, ∑ x, optimalKernel d x y = 1) ∧
    ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput (optimalKernel d) (r.readout () d p)) (completion p) ≤ rho d

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Option (Fin 2 × Fin 2) → ℝ := Pi.single (some (0,0)) 1
  have hp : ∀ z, 0 ≤ p z := by intro z; simp [p, Pi.single_apply]; positivity
  have hh := (h (d := 2) (by decide)).2 p hp (by simp [p])
  have hc : (Finset.univ.filter (fun x : Fin 2 => x = 0)).card = 1 := by decide
  norm_num [hc, rejected, realize, kernelOutput, completion, totalVariation,
    Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two, p,
    Pi.single_apply, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, Pi.single (none : Option (Fin 2 × Fin 2)) 1,
    Pi.single (some ((0,0) : Fin 2 × Fin 2)) 1, ?_⟩
  intro h
  have he := congrFun h (none : Option (Fin 2 × Fin 2))
  norm_num [actual, realize, Pi.single_apply] at he

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_upper_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_upper_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "arg", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_upper_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Upper.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Upper.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Upper

namespace Attains

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => rho d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d),
    (∀ i j : Fin d, totalVariation
      (kernelOutput (optimalKernel d) (Pi.single (some (i,j)) 1))
      (completion (Pi.single (some (i,j)) 1)) = rho d) ∧
    worstError (optimalKernel d) = r.readout () () d

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (d := 2) (by decide)).2
  have ht := (optimal_kernel_attains (d := 2) (by decide)).2
  rw [ht] at hh
  norm_num [rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton] at hh
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 4, ?_⟩
  norm_num [actual, realize, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton]

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_attains)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_attains, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "arg", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.optimal_kernel_attains) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Attains.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Attains.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Attains

namespace Lower

abbrev signature : Signature where
  Params := ℕ
  State d := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d)
    (K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ) (e : ℝ)
    (_he : ∀ p : Option (Fin d × Fin d) → ℝ,
      (∀ z, 0 ≤ p z) → (∑ z, p z = 1) →
      totalVariation (kernelOutput K p) (completion p) ≤ e),
    ((d : ℝ) - 1) / (2 * d) ≤ r.readout () d e

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 2) (by decide) (optimalKernel 2) (rho 2)
    (optimal_kernel_upper_bound (d := 2) (by decide)).2
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, (1/4 : ℝ), 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.uniform_kernel_lower_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.uniform_kernel_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "arg"]
    stateBinder := 3
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.uniform_kernel_lower_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Lower.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Lower.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Lower

namespace Limit

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => rho d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := Filter.Tendsto (r.readout () ()) Filter.atTop (nhds 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) := tendsto_const_nhds
  have hh : (0 : ℝ) = 1 := tendsto_nhds_unique hc h
  norm_num at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 4, ?_⟩
  norm_num [actual, realize, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton]

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.rho_tendsto_one)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelExtremum.rho_tendsto_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelExtremum
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["fn", "fn", "arg"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelExtremum.rho_tendsto_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Limit.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelExtremum.Limit.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Limit


/-- The five literal window constructors are the actual d=2 sample alphabet:
zero, low, high, ends are the four endpoint pairs; middle is the blocking atom. -/
def fiveModeEncoding :
    _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window ≃ Option (Fin 2 × Fin 2) where
  toFun w := match w with
    | .zero => some (0,0)
    | .low => some (1,0)
    | .high => some (0,1)
    | .ends => some (1,1)
    | .middle => none
  invFun z := match z with
    | none => .middle
    | some (i,j) => if i = 0 then (if j = 0 then .zero else .high)
      else (if j = 0 then .low else .ends)
  left_inv w := by cases w <;> decide
  right_inv z := by
    cases z with
    | none => rfl
    | some z => rcases z with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> decide

/-- This occurrence retains the complete real source-law carrier at every d. -/
def upperAnalysisSource : Analysis.Source (@optimal_kernel_upper_bound) :=
  Analysis.Source.ofRegistration _ Upper.registration .exact Upper.selection

/-- A whole-fiber law correspondence, with the explicit substitution d=2.
It preserves all five masses and retains the full original source occurrence. -/
def fiveModeFiber : Analysis.Domain upperAnalysisSource where
  parameter := (2 : ℕ)
  State := _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window → ℝ
  readout := fun _ p z => p (fiveModeEncoding.symm z)
  scope := .whole (Equiv.arrowCongr fiveModeEncoding (Equiv.refl ℝ)) (fun _ _ => rfl)

def upperAnalysis : AuricFib.Contract.Application (@optimal_kernel_upper_bound) where
  evidence := .typed {
    source := upperAnalysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .infinite fiveModeFiber.parameter (by
      change Infinite (Option (Fin 2 × Fin 2) → ℝ)
      let e := Equiv.arrowCongr fiveModeEncoding (Equiv.refl ℝ)
      apply Infinite.of_injective (fun r : ℝ => e (fun _ => r))
      intro a b h
      have hh := congrFun (e.injective h)
        _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window.zero
      exact hh) }

#print axioms fiveModeEncoding
#print axioms upperAnalysis

end Reg.D5.S3.TotalVariation.RandomKernelExtremum

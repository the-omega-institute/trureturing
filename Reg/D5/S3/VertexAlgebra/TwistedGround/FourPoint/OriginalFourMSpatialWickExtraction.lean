import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction
import Reg.Support.FactorialFockMetric
import Reg.Support.UniverseSingleReadout
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Readouts for disjoint coordinate extraction and its finite Wick recursion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction hiding DependsOn
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWick (spatialCoefficient)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic (coefficient)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction

private abbrev supportedBy {X : Type u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction.DependsOn X

abbrev listSignature : Signature :=
  signature (Type u) List (fun X => List X → Prop)

def listEqual : Realization listSignature.{u} :=
  realize _ (fun _ _ xs ys => xs = ys) (fun e => nomatch e)

def listRejected : Realization listSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem listDependence : ObservationalDependence listSignature.{u} listEqual.{u} := by
  intro role
  refine ⟨PUnit.{u+1}, [], [PUnit.unit], ?_⟩
  intro same
  have impossible : [PUnit.unit] = ([] : List PUnit.{u+1}) :=
    Eq.mp (congrFun same []) rfl
  simp at impossible

abbrev supportSignature : Signature :=
  signature (Type u) Set
    (fun X => ((X → ℂ) → ℂ) → Prop)

def supportLaw : Realization supportSignature.{u} :=
  realize _ (fun _ _ s f => supportedBy s f) (fun e => nomatch e)

def supportRejected : Realization supportSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem supportDependence :
    ObservationalDependence supportSignature.{u} supportLaw.{u} := by
  intro role
  let f : (PUnit.{u+1} → ℂ) → ℂ := fun z => z PUnit.unit
  refine ⟨PUnit.{u+1}, Set.univ, ∅, ?_⟩
  intro same
  have full : supportedBy Set.univ f := by
    intro _ _ agree
    exact agree (Set.mem_univ PUnit.unit)
  have empty : supportedBy (∅ : Set PUnit.{u+1}) f := Eq.mp (congrFun same f) full
  exact zero_ne_one (empty (u := fun _ => 0) (v := fun _ => 1) (by simp))

abbrev germSignature : Signature :=
  signature (Σ X : Type u, Fintype X)
    (fun P => (P.1 → ℂ) → ℂ) (fun P => (P.1 → ℂ) → Prop)

def germAnalytic : Realization germSignature.{u} :=
  realize _ (fun _ P f z => letI : Fintype P.1 := P.2; AnalyticAt ℂ f z) (fun e => nomatch e)

def germRejected : Realization germSignature.{u} :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem germDependence : ObservationalDependence germSignature.{u} germAnalytic.{u} := by
  intro role
  let E := PUnit.{u+1} → ℂ
  let normGerm : E → ℂ := fun z => (‖z PUnit.unit‖ : ℝ)
  refine ⟨⟨PUnit.{u+1}, inferInstance⟩, fun _ => 0, normGerm, ?_⟩
  intro same
  have h : AnalyticAt ℂ normGerm 0 := Eq.mp (congrFun same (0 : E)) analyticAt_const
  let diagonal : ℂ →L[ℂ] E := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℂ ℂ)
  have hc : DifferentiableAt ℂ (fun z : ℂ => (‖z‖ : ℂ)) 0 := by
    change DifferentiableAt ℂ (normGerm ∘ diagonal) 0
    exact h.differentiableAt.comp 0 diagonal.differentiableAt
  have hr : DifferentiableAt ℝ (fun z : ℂ => (‖z‖ : ℝ)) 0 := by
    simpa [Function.comp_def] using Complex.reCLM.differentiableAt.comp 0 hc.real_of_complex
  exact not_differentiableAt_norm_zero ℂ hr

namespace spatialCoefficient_mul_filter

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [DecidableEq X] (n : X → ℕ) (l : List X) (p : X → Bool)
    (f g : (X → ℂ) → ℂ) (_hf : supportedBy {a | p a = true} f)
    (_hg : supportedBy {a | p a = false} g) (u : X → ℂ),
    R.readout () () (spatialCoefficient n l (fun v => f v * g v) u)
      (spatialCoefficient n (l.filter p) f u *
        spatialCoefficient n (l.filter fun a => !p a) g u)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) 0 [] (fun _ => false) 0 0
    (by intro _ _ _; rfl) (by intro _ _ _; rfl) 0

def family : Registration arena.{u} (type_of% (@spatialCoefficient_mul_filter.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@spatialCoefficient_mul_filter.{u}, complexFalse, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spatialCoefficient_mul_filter.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_filter.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_filter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end spatialCoefficient_mul_filter

namespace partition_eq_filters

abbrev arena : Arena where
  signature := listSignature
  Law R := ∀ {X : Type u} [DecidableEq X] (l : List X) (p : List X × List X)
    (_hl : l.Nodup) (_hp : p ∈ partitions l),
    R.readout () X (l.filter fun a => decide (a ∈ p.1)) p.1 ∧
      l.filter (fun a => !(decide (a ∈ p.1))) = p.2

private theorem rejectedLaw : ¬ arena.{u}.Law listRejected := by
  intro h
  exact (h (X := PUnit.{u+1}) [] ([], []) (by simp) (by simp [partitions])).1

def family : Registration arena.{u} (type_of% (@partition_eq_filters.{u})) where
  actual := listEqual
  bridge := Iff.rfl
  variation := ⟨@partition_eq_filters.{u}, listRejected, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law listEqual listRejected rejectedLaw
  dependence := listDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@partition_eq_filters.{u}) (Realization listSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.partition_eq_filters.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.partition_eq_filters.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize listSignature listEqual.readout listEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end partition_eq_filters

namespace spatialCoefficient_mul_partition

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [DecidableEq X] (n : X → ℕ) (l : List X)
    (_hl : l.Nodup) (p : List X × List X) (_hp : p ∈ partitions l)
    (f g : (X → ℂ) → ℂ) (_hf : supportedBy {a | a ∈ p.1} f)
    (_hg : supportedBy {a | a ∈ p.2} g) (u : X → ℂ),
    R.readout () () (spatialCoefficient n l (fun v => f v * g v) u)
      (spatialCoefficient n p.1 f u * spatialCoefficient n p.2 g u)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) 0 [] (by simp) ([], []) (by simp [partitions])
    0 0 (by intro _ _ _; rfl) (by intro _ _ _; rfl) 0

def family : Registration arena.{u} (type_of% (@spatialCoefficient_mul_partition.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@spatialCoefficient_mul_partition.{u}, complexFalse, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spatialCoefficient_mul_partition.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_partition.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_mul_partition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end spatialCoefficient_mul_partition

namespace wick_dependsOn

abbrev arena : Arena where
  signature := supportSignature
  Law R := ∀ {X : Type u} (A : X → X → ℂ → ℂ → ℂ) (μ : X → ℂ → ℂ) (l : List X),
    R.readout () X {a | a ∈ l}
      (fun u => wick (Matrix.of fun i j => A i j (u i) (u j)) (fun i => μ i (u i)) l)

private theorem rejectedLaw : ¬ arena.{u}.Law supportRejected := by
  intro h
  exact h (X := PUnit.{u+1}) 0 0 []

def family : Registration arena.{u} (type_of% (@wick_dependsOn.{u})) where
  actual := supportLaw
  bridge := Iff.rfl
  variation := ⟨@wick_dependsOn.{u}, supportRejected, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law supportLaw supportRejected rejectedLaw
  dependence := supportDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_dependsOn.{u}) (Realization supportSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.wick_dependsOn.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.wick_dependsOn.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize supportSignature supportLaw.readout supportLaw.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end wick_dependsOn

namespace spatialCoefficient_add

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [DecidableEq X] [Fintype X]
    (n : X → ℕ) (l : List X) {f g : (X → ℂ) → ℂ}
    (_hf : AnalyticAt ℂ f 0) (_hg : AnalyticAt ℂ g 0),
    R.readout () () (spatialCoefficient n l (fun u => f u + g u) 0)
      (spatialCoefficient n l f 0 + spatialCoefficient n l g 0)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) 0 [] (f := fun _ => 0) (g := fun _ => 0)
    analyticAt_const analyticAt_const

def family : Registration arena.{u} (type_of% (@spatialCoefficient_add.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@spatialCoefficient_add.{u}, complexFalse, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spatialCoefficient_add.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_add.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_add.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end spatialCoefficient_add

namespace wick_analytic

abbrev arena : Arena where
  signature := germSignature
  Law R := ∀ {X : Type u} [Fintype X] (A : (X → ℂ) → Matrix X X ℂ) (μ : (X → ℂ) → X → ℂ)
    (_hA : ∀ i j, AnalyticAt ℂ (fun u => A u i j) 0)
    (_hμ : ∀ i, AnalyticAt ℂ (fun u => μ u i) 0) (l : List X),
    R.readout () ⟨X, inferInstance⟩ (fun u => wick (A u) (μ u) l) 0

private theorem rejectedLaw : ¬ arena.{u}.Law germRejected := by
  intro h
  exact h (X := PUnit.{u+1}) (fun _ _ _ => 0) (fun _ _ => 0)
    (fun _ _ => analyticAt_const) (fun _ => analyticAt_const) []

def family : Registration arena.{u} (type_of% (@wick_analytic.{u})) where
  actual := germAnalytic
  bridge := Iff.rfl
  variation := ⟨@wick_analytic.{u}, germRejected, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law germAnalytic germRejected rejectedLaw
  dependence := germDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wick_analytic.{u}) (Realization germSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.wick_analytic.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.wick_analytic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize germSignature germAnalytic.readout germAnalytic.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end wick_analytic

namespace spatialCoefficient_list_sum

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [DecidableEq X] [Fintype X] {J : Type v}
    (n : X → ℕ) (l : List X) (terms : List J) (f : J → (X → ℂ) → ℂ)
    (_hf : ∀ j ∈ terms, AnalyticAt ℂ (f j) 0),
    R.readout () () (spatialCoefficient n l (fun u => (terms.map fun j => f j u).sum) 0)
      ((terms.map fun j => spatialCoefficient n l (f j) 0).sum)

private theorem rejectedLaw : ¬ arena.{u, v}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) (J := PUnit.{v+1}) 0 [] [] (fun _ _ => 0)
    (fun _ _ => analyticAt_const)

def family : Registration arena.{u, v} (type_of% (@spatialCoefficient_list_sum.{u, v})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@spatialCoefficient_list_sum.{u, v}, complexFalse, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spatialCoefficient_list_sum.{u, v}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_list_sum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_list_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end spatialCoefficient_list_sum

namespace spatialCoefficient_wick

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [DecidableEq X] [Fintype X]
    (A : X → X → ℂ → ℂ → ℂ) (μ : X → ℂ → ℂ)
    (_hA : ∀ i j, AnalyticAt ℂ (fun u : X → ℂ => A i j (u i) (u j)) 0)
    (_hμ : ∀ i, AnalyticAt ℂ (fun u : X → ℂ => μ i (u i)) 0)
    (n : X → ℕ) (l : List X) (_hl : l.Nodup),
    R.readout () () (spatialCoefficient n l (fun u => wick
      (Matrix.of fun i j => A i j (u i) (u j)) (fun i => μ i (u i)) l) 0)
      (wick (Matrix.of fun i j => coefficient (n j) (fun v => coefficient (n i) (fun u => A i j u v)))
        (fun i => coefficient (n i) (μ i)) l)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) 0 0 (fun _ _ => analyticAt_const)
    (fun _ => analyticAt_const) 0 [] (by simp)

def family : Registration arena.{u} (type_of% (@spatialCoefficient_wick.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@spatialCoefficient_wick.{u}, complexFalse, rejectedLaw⟩
  sensitivity := sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spatialCoefficient_wick.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_wick.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction.spatialCoefficient_wick.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickExtraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end spatialCoefficient_wick

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickExtraction

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.CompactSmoothPostcomposition

/-!
# Original smooth-postcomposition source families

The exact source telescopes retain independent domain and scalar universes,
the max-universe derivative family, all differentiability orders, empty
compact domains and zero spaces. These source bindings and the source
family bridges are partial audit evidence. No four-slot registration is
asserted: whole-family variation, sensitivity, actual observational dependence
and raw source-coordinate reconstruction remain to be supplied for each
original public theorem. Unknown continuation cannot replace those proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ContinuousMap ContDiff

noncomputable section

namespace Reg.D5.S3.Topology.CompactSmoothPostcomposition

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev evaluationScope.{u, v, a, b} :=
  type_of% (@ContinuousMap.applyContinuousLinearMap_apply.{a, b, u, v})
abbrev derivativeScope.{u, v, a, b} := type_of% (@ContinuousMap.hasFDerivAt_postcomp.{u, v, a, b})
abbrev smoothnessScope.{u, v, a, b} := type_of% (@ContinuousMap.contDiff_postcomp.{u, v, a, b})

theorem evaluation_actual.{u, v, a, b} : evaluationScope.{u, v, a, b} :=
  @ContinuousMap.applyContinuousLinearMap_apply.{a, b, u, v}

theorem derivative_actual.{u, v, a, b} : derivativeScope.{u, v, a, b} :=
  @ContinuousMap.hasFDerivAt_postcomp.{u, v, a, b}

theorem smoothness_actual.{u, v, a, b} : smoothnessScope.{u, v, a, b} :=
  @ContinuousMap.contDiff_postcomp.{u, v, a, b}

/-- All original types and dictionaries are parameters of the source family. -/
structure Inputs.{u, v, a, b} where
  K : Type a
  topK : TopologicalSpace K
  compactK : @CompactSpace K topK
  k : Type b
  field : NontriviallyNormedField k
  realLike : letI := field; IsRCLikeNormedField k
  E : Type u
  groupE : NormedAddCommGroup E
  spaceE : letI := field; letI := groupE; NormedSpace k E
  F : Type (max u v)
  groupF : NormedAddCommGroup F
  spaceF : letI := field; letI := groupF; NormedSpace k F
  f : letI := groupE; letI := groupF; C(E, F)

abbrev domain.{u, v, a, b} (P : Inputs.{u, v, a, b}) :=
  letI := P.topK
  letI := P.groupE
  C(P.K, P.E)

abbrev codomain.{u, v, a, b} (P : Inputs.{u, v, a, b}) :=
  letI := P.topK
  letI := P.groupF
  C(P.K, P.F)

def postcompose.{u, v, a, b} (P : Inputs.{u, v, a, b}) : domain P → codomain P :=
  letI := P.topK
  letI := P.groupE
  letI := P.groupF
  fun g => P.f.comp g

abbrev signature.{u, v, a, b} : Signature where
  Params := Inputs.{u, v, a, b}
  State := domain
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => codomain
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u, v, a, b} : Realization signature.{u, v, a, b} :=
  realize signature.{u, v, a, b} (fun _ P g => postcompose P g) (fun e => nomatch e)

abbrev arena.{u, v, a, b} : Arena where
  signature := signature.{u, v, a, b}
  Law R := ∀ (P : Inputs.{u, v, a, b}),
    let := P.topK
    let := P.compactK
    let := P.field
    let := P.realLike
    let := P.groupE
    let := P.spaceE
    let := P.groupF
    let := P.spaceF
    ∀ n : ℕ∞, ContDiff P.k (n : ℕ∞ω) P.f →
      ContDiff P.k (n : ℕ∞ω) (R.readout () P)

theorem source_bridge.{u, v, a, b} :
    smoothnessScope.{u, v, a, b} ↔ arena.{u, v, a, b}.Law actual.{u, v, a, b} := by
  constructor
  · intro h P
    let := P.topK
    let := P.compactK
    let := P.field
    let := P.realLike
    let := P.groupE
    let := P.spaceE
    let := P.groupF
    let := P.spaceF
    exact fun n => h n P.f
  · intro h K tK cK k fK rK E gE sE F gF sF n f hf
    exact h ⟨K, tK, cK, k, fK, rK, E, gE, sE, F, gF, sF, f⟩ n hf

theorem actual_positive.{u, v, a, b} : arena.{u, v, a, b}.Law actual.{u, v, a, b} :=
  source_bridge.mp smoothness_actual

abbrev derivativeArena.{u, v, a, b} : Arena where
  signature := signature.{u, v, a, b}
  Law R := ∀ (P : Inputs.{u, v, a, b}),
    letI := P.topK
    letI := P.compactK
    letI := P.field
    letI := P.realLike
    letI := P.groupE
    letI := P.spaceE
    letI := P.groupF
    letI := P.spaceF
    ∀ (hf : ContDiff P.k 1 P.f) (g : domain P),
      HasFDerivAt (R.readout () P)
        (ContinuousMap.applyContinuousLinearMap
          ((⟨fderiv P.k P.f, hf.continuous_fderiv one_ne_zero⟩ :
            C(P.E, P.E →L[P.k] P.F)).comp g)) g

theorem derivative_source_bridge.{u, v, a, b} :
    derivativeScope.{u, v, a, b} ↔ derivativeArena.{u, v, a, b}.Law actual.{u, v, a, b} := by
  constructor
  · intro h P
    let := P.topK
    let := P.compactK
    let := P.field
    let := P.realLike
    let := P.groupE
    let := P.spaceE
    let := P.groupF
    let := P.spaceF
    exact h P.f
  · intro h K tK cK k fK rK E gE sE F gF sF f hf g
    exact h ⟨K, tK, cK, k, fK, rK, E, gE, sE, F, gF, sF, f⟩ hf g

theorem derivative_positive.{u, v, a, b} :
    derivativeArena.{u, v, a, b}.Law actual.{u, v, a, b} :=
  derivative_source_bridge.mp derivative_actual

structure EvaluationInputs.{u, v, a, b} where
  K : Type a
  topK : TopologicalSpace K
  compactK : @CompactSpace K topK
  k : Type b
  field : NontriviallyNormedField k
  E : Type u
  groupE : NormedAddCommGroup E
  spaceE : letI := field; letI := groupE; NormedSpace k E
  F : Type v
  groupF : NormedAddCommGroup F
  spaceF : letI := field; letI := groupF; NormedSpace k F

abbrev evaluationDomain.{u, v, a, b} (P : EvaluationInputs.{u, v, a, b}) :=
  letI := P.topK
  letI := P.field
  letI := P.groupE
  letI := P.spaceE
  letI := P.groupF
  letI := P.spaceF
  C(P.K, P.E →L[P.k] P.F) × C(P.K, P.E) × P.K

abbrev evaluationSignature.{u, v, a, b} : Signature where
  Params := EvaluationInputs.{u, v, a, b}
  State := evaluationDomain
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => P.F
  Anchor := Empty
  finiteAnchor := inferInstance

def evaluate.{u, v, a, b} (P : EvaluationInputs.{u, v, a, b})
    (q : evaluationDomain P) : P.F :=
  letI := P.topK
  letI := P.compactK
  letI := P.field
  letI := P.groupE
  letI := P.spaceE
  letI := P.groupF
  letI := P.spaceF
  ContinuousMap.applyContinuousLinearMap q.1 q.2.1 q.2.2

def evaluationActual.{u, v, a, b} : Realization evaluationSignature.{u, v, a, b} :=
  realize evaluationSignature (fun _ P q => evaluate P q) (fun e => nomatch e)

abbrev evaluationArena.{u, v, a, b} : Arena where
  signature := evaluationSignature.{u, v, a, b}
  Law R := ∀ (P : EvaluationInputs.{u, v, a, b}) (q : evaluationDomain P),
    R.readout () P q = q.1 q.2.2 (q.2.1 q.2.2)

theorem evaluation_source_bridge.{u, v, a, b} :
    evaluationScope.{u, v, a, b} ↔
      evaluationArena.{u, v, a, b}.Law evaluationActual.{u, v, a, b} := by
  constructor
  · intro h P q
    let := P.topK
    let := P.compactK
    let := P.field
    let := P.groupE
    let := P.spaceE
    let := P.groupF
    let := P.spaceF
    exact h q.1 q.2.1 q.2.2
  · intro h K tK cK k fK E gE sE F gF sF A g x
    exact h ⟨K, tK, cK, k, fK, E, gE, sE, F, gF, sF⟩ (A, g, x)

theorem evaluation_positive.{u, v, a, b} :
    evaluationArena.{u, v, a, b}.Law evaluationActual.{u, v, a, b} :=
  evaluation_source_bridge.mp evaluation_actual

end Reg.D5.S3.Topology.CompactSmoothPostcomposition

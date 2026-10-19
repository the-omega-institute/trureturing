import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
import Reg.Support.DependentFamily

/-! Full-source dependent-family audit of matrix readouts. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
open LeanInformationAudit Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
universe u

namespace General
@[reducible] def signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
end General

namespace Finite
@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
end Finite

private theorem reachable_zero {n : Type u} {α : Type} [Fintype n] [DecidableEq n]
    (K : α → Matrix n n ℂ) : reachableSpace K 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro l
  apply Submodule.span_le.mpr
  rintro y ⟨w, hw, v, hv, rfl⟩
  have hv0 : v = 0 := by simpa [matrixSupport] using hv
  simp [hv0]

private theorem support_le_reachable {n : Type u} {α : Type} [Fintype n] [DecidableEq n]
    (K : α → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    matrixSupport ρ ≤ reachableSpace K ρ := by
  apply le_iSup_of_le 0
  intro v hv
  exact Submodule.subset_span ⟨[], by simp, v, hv, by simp [krausWord]⟩

namespace Support
abbrev signature := General.signature.{u}
abbrev actual := General.actual.{u}
abbrev rejected := General.rejected.{u}

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {α : Type} [Fintype n] [DecidableEq n] [Fintype α] (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (l : ℕ),
    matrixSupport (orbitSum K c ρ l) = wordSpan K (R.readout () n ρ) l

private theorem actual_law : arena.{u}.Law actual := by
  exact @finite_orbit_support_eq_word_span.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let K : Unit → Matrix n n ℂ := fun _ => 0
  let c : Unit → ℝ := fun _ => 1
  have hc : ∀ a, 0 < c a := by intro a; norm_num [c]
  have hh := h K c hc (1 : Matrix n n ℂ) Matrix.PosSemidef.one 0
  change matrixSupport (orbitSum K c 1 0) = wordSpan K 0 0 at hh
  rw [← finite_orbit_support_eq_word_span K c hc 0 Matrix.PosSemidef.zero 0] at hh
  simpa [orbitSum, matrixSupport, Matrix.toEuclideanLin] using hh

def family : Registration arena.{u} (type_of% (@finite_orbit_support_eq_word_span.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature.{u} actual
    intro i
    refine ⟨ULift.{u} (Fin 1), 0, (fun _ _ => 1), ?_⟩
    intro he
    have hh := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
    exact zero_ne_one hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_orbit_support_eq_word_span.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Support.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Faithful
abbrev signature := General.signature.{u}
abbrev actual := General.actual.{u}
abbrev rejected := General.rejected.{u}

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {α : Type} [Fintype n] [DecidableEq n] [Fintype α] (K : α → Matrix n n ℂ) (c : α → ℝ)
    (hc : ∀ a, 0 < c a) (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef),
    ∃ L : ℕ, ∃ μ : ℝ, 0 < μ ∧
      matrixSupport (orbitSum K c ρ L) = reachableSpace K (R.readout () n ρ) ∧
      ∀ v ∈ reachableSpace K ρ,
        μ * ‖v‖ ^ 2 ≤ (inner ℂ v ((orbitSum K c ρ L).toEuclideanLin v)).re

private theorem actual_law : arena.{u}.Law actual := by
  exact @finite_reachable_faithful_sum.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let K : Unit → Matrix n n ℂ := fun _ => 0
  let c : Unit → ℝ := fun _ => 1
  have hc : ∀ a, 0 < c a := by intro a; norm_num [c]
  obtain ⟨L, μ, hμ, hs, _⟩ := h K c hc (1 : Matrix n n ℂ) Matrix.PosSemidef.one
  change matrixSupport (orbitSum K c 1 L) = reachableSpace K 0 at hs
  rw [reachable_zero] at hs
  have hle : matrixSupport (1 : Matrix n n ℂ) ≤ wordSpan K 1 L := by
    intro v hv
    exact Submodule.subset_span ⟨[], by simp, v, hv, by simp [krausWord]⟩
  rw [← finite_orbit_support_eq_word_span K c hc 1 Matrix.PosSemidef.one L, hs] at hle
  simpa [matrixSupport, Matrix.toEuclideanLin] using hle

def family : Registration arena.{u} (type_of% (@finite_reachable_faithful_sum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature.{u} actual
    intro i
    refine ⟨ULift.{u} (Fin 1), 0, (fun _ _ => 1), ?_⟩
    intro he
    have hh := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
    exact zero_ne_one hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_reachable_faithful_sum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Faithful.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Faithful.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Faithful

namespace Gap
abbrev signature := Finite.signature
abbrev actual := Finite.actual
abbrev rejected := Finite.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [Fintype α] {d : ℕ}
    (K : α → Matrix (Fin d) (Fin d) ℂ) (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hcomp : weightedDual K c 1 ≤ 1) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun N => ((weightedCP K c)^[N] ρ).trace) atTop (𝓝 0)),
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ v ∈ reachableSpace K (R.readout () d ρ),
        (inner ℂ v ((survivalEffect K c N).toEuclideanLin v)).re ≤ ‖v‖ ^ 2 / 2) ∧
      ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
        matrixSupport σ ≤ reachableSpace K ρ →
        ((weightedCP K c)^[N] σ).trace.re ≤ σ.trace.re / 2

private theorem actual_law : arena.Law actual := by
  exact @initial_termination_uniform_reachable_gap

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  let c : Unit → ℝ := fun _ => 1
  have hc : ∀ a, 0 < c a := by intro a; norm_num [c]
  have hT : weightedCP K c = LinearMap.id := by ext X i j; simp [weightedCP, K, c]
  have hD : weightedDual K c = LinearMap.id := by ext X i j; simp [weightedDual, weightedCP, K, c]
  have hcomp : weightedDual K c 1 ≤ 1 := by simp [hD]
  have hterm : Tendsto (fun N => ((weightedCP K c)^[N] 0).trace) atTop (𝓝 0) := by
    simpa [hT] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  obtain ⟨N, hN, hgap, _⟩ := h K c hc hcomp 0 Matrix.PosSemidef.zero hterm
  have hs : reachableSpace K (1 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤ := by
    apply top_le_iff.mp
    simpa [matrixSupport, Matrix.toEuclideanLin] using support_le_reachable K (1 : Matrix (Fin 1) (Fin 1) ℂ)
  let v : EuclideanSpace ℂ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hv : v ≠ 0 := by
    intro hz
    have he := congrArg (fun x : EuclideanSpace ℂ (Fin 1) => x 0) hz
    simpa [v] using he
  have hh := hgap v (by change v ∈ reachableSpace K (1 : Matrix (Fin 1) (Fin 1) ℂ); rw [hs]; trivial)
  have hS : survivalEffect K c N = 1 := by simp [survivalEffect, hD]
  rw [hS] at hh
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply,
    ] at hh
  change RCLike.re (inner ℂ v v) ≤ ‖v‖ ^ 2 / 2 at hh
  rw [inner_self_eq_norm_sq] at hh
  have hp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  change ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 / 2 at hh
  nlinarith

def family : Registration arena (type_of% (@initial_termination_uniform_reachable_gap)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨1, 0, 1, zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@initial_termination_uniform_reachable_gap) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Gap.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Gap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "domain", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Gap

namespace Absorption
abbrev signature := Finite.signature
abbrev actual := Finite.actual
abbrev rejected := Finite.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {α : Type} [Fintype α] {d : ℕ} {Θ : Type u} [TopologicalSpace Θ]
    (K : α → Matrix (Fin d) (Fin d) ℂ) (E : α → Matrix (Fin d) (Fin d) ℂ)
    (hE : ∀ a, (E a).PosSemidef) (c : Θ → α → ℝ) (U : Set Θ)
    (hpos : ∀ θ ∈ U, ∀ a, 0 < c θ a)
    (hcont : ∀ a, ContinuousOn (fun θ => c θ a) U)
    (hcomplete : ∀ θ ∈ U,
      weightedDual K (c θ) 1 + ∑ a, (c θ a : ℂ) • E a = 1)
    (θ₀ : Θ) (hθ₀ : θ₀ ∈ U) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef)
    (hterm : Tendsto (fun k => ((weightedCP K (c θ₀))^[k] ρ).trace) atTop (𝓝 0)),
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ θ ∈ U, ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
        matrixSupport σ ≤ reachableSpace K (R.readout () d ρ) →
        Tendsto (fun k => ((weightedCP K (c θ))^[k] σ).trace.re) atTop (𝓝 0) ∧
          Summable (fun k => (weightedCP K (c θ))^[k] σ) ∧
          (∑' k, (weightedCP K (c θ))^[k] σ) -
            weightedCP K (c θ) (∑' k, (weightedCP K (c θ))^[k] σ) = σ ∧
          ∀ F : Matrix (Fin d) (Fin d) ℂ, 0 ≤ F →
            F ≤ 1 - weightedDual K (c θ) 1 →
            Summable (fun k => (F * (weightedCP K (c θ))^[k] σ).trace) ∧
              (∑' k, (F * (weightedCP K (c θ))^[k] σ).trace) =
                (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace ∧
              0 ≤ (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace.re ∧
              (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace.re ≤ σ.trace.re ∧
              (F = 1 - weightedDual K (c θ) 1 →
                (F * ∑' k, (weightedCP K (c θ))^[k] σ).trace = σ.trace)) ∧
      (∀ θ ∈ U, ∀ X ∈ Submodule.span ℝ
        {σ : Matrix (Fin d) (Fin d) ℂ | σ.PosSemidef ∧
          matrixSupport σ ≤ reachableSpace K ρ},
        Summable (fun k => (weightedCP K (c θ))^[k] X) ∧
          (∑' k, (weightedCP K (c θ))^[k] X) -
            weightedCP K (c θ) (∑' k, (weightedCP K (c θ))^[k] X) = X) ∧
      ∀ C : Set Θ, IsCompact C → C.Nonempty → C ⊆ U →
        let g := compactBranchRatio c θ₀ C
        0 < g ∧ g ≤ 1 ∧
          (∀ θ ∈ C, ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
            matrixSupport σ ≤ reachableSpace K ρ → ∀ k,
            ((weightedCP K (c θ))^[k] σ).trace.re ≤
              (1 - g ^ N / 2) ^ (k / N) * σ.trace.re) ∧
          ∀ σ : Matrix (Fin d) (Fin d) ℂ, σ.PosSemidef →
            matrixSupport σ ≤ reachableSpace K ρ → σ.trace = 1 → ∀ k,
            sSup ((fun θ => ((weightedCP K (c θ))^[k] σ).trace.re) '' C) ≤
              (1 - g ^ N / 2) ^ (k / N)

private theorem actual_law : arena.{u}.Law actual := by
  exact @positive_branch_compact_absorption.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Θ := ULift.{u} Unit
  let K : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  let E : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  let c : Θ → Unit → ℝ := fun _ _ => 1
  let θ : Θ := ⟨()⟩
  have hT (t : Θ) : weightedCP K (c t) = LinearMap.id := by
    ext X i j; simp [weightedCP, K, c]
  have hD (t : Θ) : weightedDual K (c t) = LinearMap.id := by
    ext X i j; simp [weightedDual, weightedCP, K, c]
  have hterm : Tendsto (fun N => ((weightedCP K (c θ))^[N] 0).trace) atTop (𝓝 0) := by
    simpa [hT] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  obtain ⟨N, hN, hpoint, _⟩ := h K E (fun _ => Matrix.PosSemidef.zero) c Set.univ
    (by intro t ht a; norm_num [c]) (by intro a; exact continuous_const.continuousOn)
    (by intro t ht; rw [hD t]; simp [E]) θ (Set.mem_univ θ) 0 Matrix.PosSemidef.zero hterm
  have hs : reachableSpace K (1 : Matrix (Fin 1) (Fin 1) ℂ) = ⊤ := by
    apply top_le_iff.mp
    simpa [matrixSupport, Matrix.toEuclideanLin] using support_le_reachable K (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have ht := (hpoint θ (Set.mem_univ θ) 1 Matrix.PosSemidef.one (by
    change matrixSupport (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤ reachableSpace K 1
    rw [hs]; exact le_top)).1
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa [hT, Matrix.trace] using ht
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
  exact one_ne_zero he

def family : Registration arena.{u} (type_of% (@positive_branch_compact_absorption.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    change ObservationalDependence signature actual
    intro i
    exact ⟨1, 0, 1, zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_branch_compact_absorption.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Absorption.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse.Absorption.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "body", "body", "body", "domain", "arg", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Absorption

end Reg.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
import Reg.Support.DependentFamily
import Mathlib.Analysis.Quaternion

/-! Source-bound audits of the one-parameter generators of a locally compact group injecting
continuously into the units of a real Banach algebra: real multiples, the escape lemma,
closedness of the generator set, sums and commutators. -/

namespace Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators

open _root_.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u v

/-! ## Models -/

/-- The real line lifted to universe `u`, a complete commutative real normed algebra. -/
abbrev Line := ULift.{u} ℝ

/-- The one-point group in universe `v`. -/
abbrev Pt := PUnit.{v + 1}

/-- The trivial homomorphism from the one-point group into the units of `A`. -/
abbrev triv (A : Type u) [NormedRing A] : Pt.{v} →* Aˣ := 1

theorem triv_continuous (A : Type u) [NormedRing A] : Continuous (triv.{u, v} A) :=
  continuous_of_discreteTopology

theorem triv_injective (A : Type u) [NormedRing A] : Function.Injective (triv.{u, v} A) :=
  fun a b _ => Subsingleton.elim a b

/-- Through the trivial group every one-parameter generator vanishes: the curve
`t ↦ exp (t • X)` is constant, so its derivative `X` at `0` is zero. -/
theorem eq_zero_of_trivial {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {X : A} (h : IsOneParameterGenerator (triv.{u, v} A) X) : X = 0 := by
  obtain ⟨γ, -, hγ⟩ := h
  have hc : (fun t : ℝ => NormedSpace.exp (t • X)) = fun _ => (1 : A) := by
    funext t
    rw [← hγ t]
    simp
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [hc] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : A))
  simpa using this

/-- The element `0` is lifted by the constant curve at `1`. -/
theorem zero_generator {A : Type u} [NormedRing A] [NormedAlgebra ℝ A] {G : Type v}
    [TopologicalSpace G] [Group G] (ρ : G →* Aˣ) : IsOneParameterGenerator ρ (0 : A) :=
  ⟨fun _ => 1, continuous_const, fun t => by simp⟩

/-- In the trivial model the generators are exactly `0`. -/
theorem generator_iff (X : Line.{u}) : IsOneParameterGenerator (triv.{u, v} Line.{u}) X ↔ X = 0 :=
  ⟨eq_zero_of_trivial, fun h => h ▸ zero_generator _⟩

/-- In the trivial model the element `1` is not a generator. -/
theorem not_generator_one : ¬ IsOneParameterGenerator (triv.{u, v} Line.{u}) 1 := fun h =>
  one_ne_zero (eq_zero_of_trivial h)

/-- The quaternion `i`, lifted to universe `u`. -/
def qi : ULift.{u} ℍ := ⟨⟨0, 1, 0, 0⟩⟩

/-- The quaternion `j`, lifted to universe `u`. -/
def qj : ULift.{u} ℍ := ⟨⟨0, 0, 1, 0⟩⟩

/-- The commutator `i j - j i = 2 k` is not zero. -/
theorem commutator_qi_qj : qi.{u} * qj - qj * qi ≠ qi * 0 - 0 * qi := by
  intro h
  have := congrArg (fun z : ULift.{u} ℍ => z.down.imK) h
  norm_num [qi, qj] at this

/-! ## `IsOneParameterGenerator.smul`: the multiple `c • X` as a function of the scalar -/
namespace Smul

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _ : NormedRing A, Σ _ : NormedAlgebra ℝ A, A
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p c => letI := p.2.1; letI := p.2.2.1; c • p.2.2.2)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

/-- Retain the complete algebra, group, homomorphism, generator and scalar telescope of
`IsOneParameterGenerator.smul`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [iR : NormedRing A] [iA : NormedAlgebra ℝ A] {G : Type v}
    [TopologicalSpace G] [Group G] {ρ : G →* Aˣ} {X : A}, IsOneParameterGenerator ρ X →
    ∀ c : ℝ, IsOneParameterGenerator ρ (r.readout () ⟨A, iR, iA, X⟩ c)

/-- If every multiple were read as `1`, the multiples of the generator `0` of the trivial
group would make `1` a generator. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact not_generator_one.{u, v} (h (A := Line.{u}) (ρ := triv.{u, v} Line.{u})
    (zero_generator _) 0)

/-- At `X = 1` in the real line the scalars `0` and `1` give different multiples. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Line.{u}, inferInstance, inferInstance, 1⟩, 0, 1, ?_⟩
  change (0 : ℝ) • (1 : Line.{u}) ≠ (1 : ℝ) • (1 : Line.{u})
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @IsOneParameterGenerator.smul.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsOneParameterGenerator.smul.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Smul

def smul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@IsOneParameterGenerator.smul.{u, v}) (Realization Smul.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.smul_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.Smul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Smul.arena.{u, v}⟩
  objectArena := .source ⟨Smul.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Smul.arena.{u, v} ⟨Smul.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Smul.signature.{u}
    (fun _ p c => letI := p.2.1; letI := p.2.2.1; c • p.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `isOneParameterGenerator_of_mapClusterPt`: the normalized direction of the logarithms -/
namespace Escape

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _ : NormedRing A, Σ _ : NormedAlgebra ℝ A, ℕ → A
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p k => letI := p.2.1; letI := p.2.2.1; ‖p.2.2.2 k‖⁻¹ • p.2.2.2 k)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

/-- Retain the complete algebra, group, homomorphism, sequence, cluster-point and conclusion
telescope of `isOneParameterGenerator_of_mapClusterPt`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [iR : NormedRing A] [iA : NormedAlgebra ℝ A] {G : Type v}
    [TopologicalSpace G] [Group G] [CompleteSpace A] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (ρ : G →* Aˣ), Continuous ρ → Function.Injective ρ →
    ∀ {g : ℕ → G}, Tendsto g atTop (𝓝 1) → ∀ {Y : ℕ → A}, Tendsto Y atTop (𝓝 0) →
    (∀ k, ((ρ (g k) : Aˣ) : A) = NormedSpace.exp (Y k)) → ∀ {X : A},
    MapClusterPt X atTop (fun k => r.readout () ⟨A, iR, iA, Y⟩ k) →
    IsOneParameterGenerator ρ X

/-- If every direction were read as `1`, the constant sequences `g = 1`, `Y = 0` of the
trivial group would make `1` a generator. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  refine not_generator_one.{u, v} (h (A := Line.{u}) (triv.{u, v} Line.{u})
    (triv_continuous _) (triv_injective _) (g := fun _ => 1) tendsto_const_nhds
    (Y := fun _ => 0) tendsto_const_nhds (fun _ => by simp) (X := 1) ?_)
  exact (tendsto_const_nhds (x := (1 : Line.{u}))).mapClusterPt

/-- For the sequence `Y k = k` in the real line the directions at `0` and `1` differ. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Line.{u}, inferInstance, inferInstance, fun k => (k : Line.{u})⟩, 0, 1, ?_⟩
  change ‖((0 : ℕ) : Line.{u})‖⁻¹ • ((0 : ℕ) : Line.{u}) ≠
    ‖((1 : ℕ) : Line.{u})‖⁻¹ • ((1 : ℕ) : Line.{u})
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @isOneParameterGenerator_of_mapClusterPt.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isOneParameterGenerator_of_mapClusterPt.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Escape

def isOneParameterGenerator_of_mapClusterPt_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isOneParameterGenerator_of_mapClusterPt.{u, v}) (Realization Escape.signature.{u})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.isOneParameterGenerator_of_mapClusterPt_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.Escape.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Escape.arena.{u, v}⟩
  objectArena := .source ⟨Escape.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Escape.arena.{u, v} ⟨Escape.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Escape.signature.{u}
    (fun _ p k => letI := p.2.1; letI := p.2.2.1; ‖p.2.2.2 k‖⁻¹ • p.2.2.2 k)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
    definition := none
    coordinates := #[0, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "domain", "arg", "body"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `isClosed_setOf_isOneParameterGenerator`: the generator set read from its predicate -/
namespace Closed

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _ : NormedRing A, Σ _ : NormedAlgebra ℝ A, Σ G : Type v,
    Σ _ : TopologicalSpace G, Σ _ : Group G, G →* Aˣ
  State p := p.1 → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ s => Set.ofPred s) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ s => (Set.ofPred s)ᶜ) (fun e => nomatch e)

/-- Retain the complete algebra, group and homomorphism telescope of
`isClosed_setOf_isOneParameterGenerator`. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {A : Type u} [iR : NormedRing A] [iA : NormedAlgebra ℝ A] {G : Type v}
    [iT : TopologicalSpace G] [iG : Group G] [CompleteSpace A] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {ρ : G →* Aˣ}, Continuous ρ → Function.Injective ρ →
    IsClosed (r.readout () ⟨A, iR, iA, G, iT, iG, ρ⟩ (fun X => IsOneParameterGenerator ρ X))

/-- If the set were read as the complement of the generators, the trivial group would make
the complement of `{0}` closed in the real line, so `{0}` would be open. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hcl := h (A := Line.{u}) (ρ := triv.{u, v} Line.{u}) (triv_continuous _)
    (triv_injective _)
  have hset : (Set.ofPred fun X : Line.{u} =>
      IsOneParameterGenerator (triv.{u, v} Line.{u}) X)ᶜ = ({0}ᶜ : Set Line.{u}) := by
    ext X
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact not_congr (generator_iff.{u, v} X)
  change IsClosed (Set.ofPred fun X : Line.{u} =>
      IsOneParameterGenerator (triv.{u, v} Line.{u}) X)ᶜ at hcl
  rw [hset, isClosed_compl_iff] at hcl
  exact not_isOpen_singleton _ hcl

/-- The always-true and always-false predicates on the real line give different sets. -/
theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨Line.{u}, inferInstance, inferInstance, Pt.{v}, inferInstance, inferInstance,
    triv.{u, v} Line.{u}⟩, fun _ => True, fun _ => False, ?_⟩
  intro h
  have := congrArg (fun S : Set Line.{u} => (0 : Line.{u}) ∈ S) h
  simp [actual, realize] at this

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @isClosed_setOf_isOneParameterGenerator.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isClosed_setOf_isOneParameterGenerator.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Closed

def isClosed_setOf_isOneParameterGenerator_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isClosed_setOf_isOneParameterGenerator.{u, v}) (Realization Closed.signature.{u, v})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.isClosed_setOf_isOneParameterGenerator_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.Closed.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Closed.arena.{u, v}⟩
  objectArena := .source ⟨Closed.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Closed.arena.{u, v} ⟨Closed.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Closed.signature.{u, v} (fun _ _ s => Set.ofPred s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
    definition := none
    coordinates := #[0, 3, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `IsOneParameterGenerator.add`: the sum `X + Y` as a function of `Y` -/
namespace Add

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _ : NormedRing A, A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => letI := p.2.1; p.2.2 + s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

/-- Retain the complete algebra, group, homomorphism and generator telescope of
`IsOneParameterGenerator.add`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [iR : NormedRing A] [NormedAlgebra ℝ A] {G : Type v}
    [TopologicalSpace G] [Group G] [CompleteSpace A] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {ρ : G →* Aˣ}, Continuous ρ → Function.Injective ρ →
    ∀ {X Y : A}, IsOneParameterGenerator ρ X → IsOneParameterGenerator ρ Y →
    IsOneParameterGenerator ρ (r.readout () ⟨A, iR, X⟩ Y)

/-- If every sum were read as `1`, the generators `0` and `0` of the trivial group would make
`1` a generator. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact not_generator_one.{u, v} (h (A := Line.{u}) (ρ := triv.{u, v} Line.{u})
    (triv_continuous _) (triv_injective _) (zero_generator _) (zero_generator _))

/-- With `X = 0` in the real line the elements `0` and `1` give different sums. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨Line.{u}, inferInstance, 0⟩, (0 : Line.{u}), (1 : Line.{u}), ?_⟩
  change (0 : Line.{u}) + 0 ≠ 0 + 1
  simp

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @IsOneParameterGenerator.add.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsOneParameterGenerator.add.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Add

def add_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@IsOneParameterGenerator.add.{u, v}) (Realization Add.signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.add_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.Add.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Add.arena.{u, v}⟩
  objectArena := .source ⟨Add.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Add.arena.{u, v} ⟨Add.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Add.signature.{u} (fun _ p s => letI := p.2.1; p.2.2 + s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
    definition := none
    coordinates := #[0, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `IsOneParameterGenerator.commutator`: the commutator `X * Y - Y * X` as a function of `Y` -/
namespace Commutator

abbrev signature : Signature where
  Params := Σ A : Type u, Σ _ : NormedRing A, A
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => letI := p.2.1; p.2.2 * s - s * p.2.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.2.1; 1) (fun e => nomatch e)

/-- Retain the complete algebra, group, homomorphism and generator telescope of
`IsOneParameterGenerator.commutator`. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {A : Type u} [iR : NormedRing A] [NormedAlgebra ℝ A] {G : Type v}
    [TopologicalSpace G] [Group G] [CompleteSpace A] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {ρ : G →* Aˣ}, Continuous ρ → Function.Injective ρ →
    ∀ {X Y : A}, IsOneParameterGenerator ρ X → IsOneParameterGenerator ρ Y →
    IsOneParameterGenerator ρ (r.readout () ⟨A, iR, X⟩ Y)

/-- If every commutator were read as `1`, the generators `0` and `0` of the trivial group
would make `1` a generator. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact not_generator_one.{u, v} (h (A := Line.{u}) (ρ := triv.{u, v} Line.{u})
    (triv_continuous _) (triv_injective _) (zero_generator _) (zero_generator _))

/-- With `X = i` in the quaternions the elements `0` and `j` give the commutators `0` and
`2 k`. -/
theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨ULift.{u} ℍ, inferInstance, qi⟩, (0 : ULift.{u} ℍ), qj, ?_⟩
  change qi.{u} * 0 - 0 * qi ≠ qi * qj - qj * qi
  exact fun h => commutator_qi_qj h.symm

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @IsOneParameterGenerator.commutator.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsOneParameterGenerator.commutator.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Commutator

def commutator_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@IsOneParameterGenerator.commutator.{u, v}) (Realization Commutator.signature.{u})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.commutator_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators.Commutator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Commutator.arena.{u, v}⟩
  objectArena := .source ⟨Commutator.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Commutator.arena.{u, v} ⟨Commutator.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Commutator.signature.{u}
    (fun _ p s => letI := p.2.1; p.2.2 * s - s * p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
    definition := none
    coordinates := #[0, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators

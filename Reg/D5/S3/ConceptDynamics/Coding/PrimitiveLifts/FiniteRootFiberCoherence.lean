import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence
import Mathlib.Data.ZMod.Basic

open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence

universe u

structure Inputs where
  H : Type u
  group : Group H
  top : TopologicalSpace H
  topGroup : @IsTopologicalGroup H top group
  t2 : @T2Space H top
  h : H
  compactRoots : by
    letI := group
    letI := top
    exact ∀ n : ℕ, 0 < n → IsCompact {x : H | x ^ n = h}

private abbrev signature : Signature where
  Params := Inputs.{u} × ℕ
  State p := p.1.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1.H
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p x => by
    letI := p.1.group
    exact x ^ p.2) (fun e => nomatch e)

private def law (R : Realization signature.{u}) : Prop := ∀ P : Inputs.{u}, by
  letI := P.group
  exact (∀ n : ℕ, 0 < n → ∃ x : P.H, R.readout () (P, n) x = P.h) ↔
    ∃ φ : Multiplicative ℚ →* P.H, φ (Multiplicative.ofAdd (1 : ℚ)) = P.h

private abbrev arena : Arena where
  signature := signature.{u}
  Law := law

private abbrev sourceScope := type_of% (@compact_root_fibers_rational_coherence.{u})

private theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro source P
    exact @source P.H P.group P.top P.topGroup P.t2 P.h P.compactRoots
  · intro all H group top topGroup t2 h hcompact
    exact all ⟨H, group, top, topGroup, t2, h, hcompact⟩

private theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@compact_root_fibers_rational_coherence)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => p.1.h) (fun e => nomatch e)

private def sample : Inputs.{u} := by
  letI : TopologicalSpace (ULift.{u} (Multiplicative (ZMod 2))) := ⊥
  haveI : DiscreteTopology (ULift.{u} (Multiplicative (ZMod 2))) := discreteTopology_bot _
  exact {
    H := ULift.{u} (Multiplicative (ZMod 2))
    group := inferInstance
    top := inferInstance
    topGroup := inferInstance
    t2 := inferInstance
    h := ULift.up (Multiplicative.ofAdd 1)
    compactRoots := fun _ _ => (Set.toFinite _).isCompact }

private theorem sample_square (x : sample.H) :
    letI := sample.group
    x ^ 2 = 1 := by
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  change 2 • x.down.toAdd = (0 : ZMod 2)
  rw [nsmul_eq_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro all
  letI := sample.group
  have roots : ∀ n : ℕ, 0 < n → ∃ x : sample.H,
      rejected.readout () (sample, n) x = sample.h :=
    fun _ _ => ⟨sample.h, rfl⟩
  obtain ⟨φ, hφ⟩ := (all sample).mp roots
  obtain ⟨x, hx⟩ := (@compact_root_fibers_rational_coherence sample.H sample.group
    sample.top sample.topGroup sample.t2 sample.h sample.compactRoots).mpr ⟨φ, hφ⟩
      2 (by decide)
  have heq := hx.symm.trans (sample_square x)
  have hne : sample.h ≠ (1 : sample.H) := by decide
  exact hne heq

private def familyRegistration : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    letI := sample.group
    refine ⟨(sample, 1), 1, sample.h, ?_⟩
    change (1 : sample.H) ^ 1 ≠ sample.h ^ 1
    simpa only [pow_one] using (show (1 : sample.H) ≠ sample.h by decide)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@compact_root_fibers_rational_coherence)
      (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence.compact_root_fibers_rational_coherence.__information_unit
  realizationName := ``familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => by
    letI := p.1.group
    exact x ^ p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteRootFiberCoherence

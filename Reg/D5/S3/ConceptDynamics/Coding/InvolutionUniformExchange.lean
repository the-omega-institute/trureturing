import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
import Reg.Support.DependentFamily
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.Perm.Fin

open _root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
universe u

abbrev G3 := ULift.{u} (Equiv.Perm (Fin 3))
def g3s : G3.{u} := ⟨Equiv.swap 0 1⟩
def g3t : G3.{u} := ⟨Equiv.swap 1 2⟩
def g3t' : G3.{u} := ⟨Equiv.swap 0 2⟩

theorem g3_involution : g3s.{u} * g3s = 1 := by
  apply ULift.down_injective
  change Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 1 = 1
  simp

theorem g3_noncommuting : g3s.{u} * g3t ≠ g3t * g3s := by
  intro h
  have := congrArg (fun g : G3.{u} => g.down 0) h
  change (1 : Fin 3) = 2 at this
  exact (by decide : (1 : Fin 3) ≠ 2) this

theorem g3_noncommuting' : g3s.{u} * g3t' ≠ g3t' * g3s := by
  intro h
  have := congrArg (fun g : G3.{u} => g.down 1) h
  change (0 : Fin 3) = 2 at this
  exact (by decide : (0 : Fin 3) ≠ 2) this

theorem g3_states_distinct : g3t.{u} ≠ g3t' := by
  intro h
  have := congrArg (fun g : G3.{u} => g.down 0) h
  change (0 : Fin 3) = 2 at this
  exact (by decide : (0 : Fin 3) ≠ 2) this

theorem source_diagonal {H : Type u} [Group H] [Fintype H]
    (s : H) (hs : s * s = 1) : source s s = target H := by
  have hb : basis s * basis s = (1 : ZAlg H) := by
    simp [basis, hs, MonoidAlgebra.one_def]
  unfold source target
  rw [sub_mul, one_mul, mul_add, sub_mul, sub_mul, hb, one_mul, mul_one]
  simp only [one_mul]
  abel

theorem source_coefficient {H : Type u} [Group H] [Fintype H] [DecidableEq H]
    (s t g : H) : (source s t).coeff g =
    2 + (if t = g then 1 else 0) + (if t * s = g then 1 else 0) -
      (if s * t = g then 1 else 0) - (if (s * t) * s = g then 1 else 0) := by
  classical
  simp [source, uniform, basis, mul_add, sub_mul, one_mul, mul_one,
    MonoidAlgebra.single_mul_single, Finsupp.single_apply]
  <;> ring

theorem target_coefficient {H : Type u} [Group H] [Fintype H] (g : H) :
    (target H).coeff g = 2 := by
  classical
  simp [target, uniform, basis]

theorem g3_source_coefficient : (source g3s.{u} g3t).coeff g3t = 3 := by
  classical
  rw [source_coefficient]
  have hts : g3t.{u} * g3s ≠ g3t := by
    intro h
    have h0 := congrArg (fun g : G3.{u} => g.down 0) h
    exact (by decide : (2 : Fin 3) ≠ 0) h0
  have hst : g3s.{u} * g3t ≠ g3t := by
    intro h
    have h0 := congrArg (fun g : G3.{u} => g.down 0) h
    exact (by decide : (1 : Fin 3) ≠ 0) h0
  have hsts : (g3s.{u} * g3t) * g3s ≠ g3t := by
    intro h
    have h0 := congrArg (fun g : G3.{u} => g.down 0) h
    exact (by decide : (2 : Fin 3) ≠ 0) h0
  simp [hts, hst, hsts]

abbrev elementSignature : Signature where
  Params := Σ H : Type u, H
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def elementActual : Realization elementSignature.{u} :=
  realize elementSignature (fun _ _ t => t) (fun e => nomatch e)

def elementBad : Realization elementSignature.{u} :=
  realize elementSignature (fun _ p _ => p.2) (fun e => nomatch e)

theorem elementDependence : ObservationalDependence elementSignature.{u} elementActual := by
  intro i
  exact ⟨⟨G3.{u}, g3s⟩, g3t, g3t', g3_states_distinct⟩

theorem elementSensitivity (Law : Realization elementSignature.{u} → Prop)
    (hbad : ¬ Law elementBad) :
    Sensitivity ⟨elementSignature, Law⟩ elementActual := by
  constructor
  · intro i
    refine ⟨elementBad, ?_, rfl, hbad⟩
    intro j h
    exact (h (@Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

def distinctArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H)
    (hs : s * s = 1) (hst : s * t ≠ t * s),
    source s (R.readout () ⟨H, s⟩ t) ≠ target H

theorem distinct_actual_law : distinctArena.{u}.Law elementActual := by
  intro H instG instF s t hs hst
  exact source_ne_target s t hs hst

theorem distinct_rejected_law : ¬ distinctArena.{u}.Law elementBad := by
  intro h
  exact h g3s g3t g3_involution g3_noncommuting (source_diagonal g3s g3_involution)

def distinctRegistration : Registration distinctArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H)
      (hs : s * s = 1) (hst : s * t ≠ t * s), source s t ≠ target H) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨distinct_actual_law, elementBad, distinct_rejected_law⟩
  sensitivity := elementSensitivity distinctArena.Law distinct_rejected_law
  dependence := elementDependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "InvolutionUniformExchange") "source_ne_target") "Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange/Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(distinctArena.{u})⟩,
  objectArena := .source ⟨(distinctArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (distinctArena.{u}) ⟨(distinctRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.anchorEnumeration }


def forwardArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H),
    leftFactor s t * rightFactor s = source s (R.readout () ⟨H, s⟩ t)

theorem forward_actual_law : forwardArena.{u}.Law elementActual := by
  intro H instG instF s t
  exact factors_forward s t

theorem forward_rejected_law : ¬ forwardArena.{u}.Law elementBad := by
  intro h
  have heq : source g3s.{u} g3t = source g3s g3s :=
    (factors_forward g3s g3t).symm.trans (h g3s g3t)
  have hc := congrArg (fun p : ZAlg G3.{u} => p.coeff g3t) heq
  rw [g3_source_coefficient, source_diagonal g3s g3_involution,
    target_coefficient] at hc
  exact (by decide : (3 : ℤ) ≠ 2) hc

def forwardRegistration : Registration forwardArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H),
      leftFactor s t * rightFactor s = source s t) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨forward_actual_law, elementBad, forward_rejected_law⟩
  sensitivity := elementSensitivity forwardArena.Law forward_rejected_law
  dependence := elementDependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "InvolutionUniformExchange") "factors_forward") "Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange/Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(forwardArena.{u})⟩,
  objectArena := .source ⟨(forwardArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (forwardArena.{u}) ⟨(forwardRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.anchorEnumeration }


/-- A total carrier-only intervention, including singleton and empty fibers. -/
def other {α : Type u} (x : α) : α := by
  classical
  exact if h : ∃ y, y ≠ x then Classical.choose h else x

theorem other_ne {α : Type u} (x : α) (h : ∃ y, y ≠ x) : other x ≠ x := by
  rw [other, dif_pos h]
  exact Classical.choose_spec h

abbrev G2 := ULift.{u} (Equiv.Perm (Fin 2))
def g2s : G2.{u} := ⟨Equiv.swap 0 1⟩

theorem g2_involution : g2s.{u} * g2s = 1 := by
  apply ULift.down_injective
  change Equiv.swap (0 : Fin 2) 1 * Equiv.swap 0 1 = 1
  simp

theorem g2_not_one : g2s.{u} ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : G2.{u} => g.down 0) h
  exact (by decide : (1 : Fin 2) ≠ 0) h0

theorem g2_cases (g : G2.{u}) : g = 1 ∨ g = g2s := by
  have hd := Equiv.Perm.decomposeFin.symm_apply_apply g.down
  have hp : (Equiv.Perm.decomposeFin g.down).2 = 1 := Subsingleton.elim _ _
  have hd' : g.down = Equiv.swap 0 (Equiv.Perm.decomposeFin g.down).1 := by
    calc
      g.down = Equiv.Perm.decomposeFin.symm
          ((Equiv.Perm.decomposeFin g.down).1, (Equiv.Perm.decomposeFin g.down).2) := hd.symm
      _ = _ := by rw [hp, Equiv.Perm.decomposeFin_symm_of_one]
  have hfin := (Equiv.Perm.decomposeFin g.down).1.isLt
  have hz : (Equiv.Perm.decomposeFin g.down).1 = 0 ∨
      (Equiv.Perm.decomposeFin g.down).1 = 1 := by
    have hv : (Equiv.Perm.decomposeFin g.down).1.val = 0 ∨
        (Equiv.Perm.decomposeFin g.down).1.val = 1 := by omega
    exact hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
  rcases hz with hz | ho
  · left
    apply ULift.down_injective
    change g.down = Equiv.refl _
    simpa [hz] using hd'
  · right
    apply ULift.down_injective
    simpa [ho, g2s] using hd'

theorem g2_other : other g2s.{u} = 1 := by
  exact (g2_cases (other g2s)).resolve_right
    (other_ne g2s ⟨1, Ne.symm g2_not_one⟩)

theorem g2_uniform : uniform G2.{u} = basis 1 + basis g2s := by
  classical
  ext g
  rcases g2_cases g with rfl | rfl <;>
    simp [uniform, basis, g2_not_one, Ne.symm g2_not_one]

theorem g2_left : leftFactor g2s.{u} 1 = (1 + 1 : ZAlg G2.{u}) := by
  unfold leftFactor
  rw [g2_uniform]
  have hb : basis (1 : G2.{u}) = (1 : ZAlg G2.{u}) := by
    simp [basis, MonoidAlgebra.one_def]
  rw [hb, mul_one]
  abel

abbrev carrierSignature : Signature where
  Params := Type u
  State H := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ H := H
  Anchor := Empty
  finiteAnchor := inferInstance

def carrierActual : Realization carrierSignature.{u} :=
  realize carrierSignature (fun _ _ s => s) (fun e => nomatch e)

def carrierBad : Realization carrierSignature.{u} :=
  realize carrierSignature (fun _ _ s => other s) (fun e => nomatch e)

def reverseArena : Arena where
  signature := carrierSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
    rightFactor (R.readout () H s) * leftFactor s t = target H

theorem reverse_actual_law : reverseArena.{u}.Law carrierActual := by
  intro H instG instF s t hs
  exact factors_reverse s t hs

theorem reverse_rejected_law : ¬ reverseArena.{u}.Law carrierBad := by
  intro h
  have heq := h g2s.{u} 1 g2_involution
  change rightFactor (other g2s) * leftFactor g2s 1 = target G2 at heq
  rw [g2_other, g2_left] at heq
  have hr : rightFactor (1 : G2.{u}) = (1 + 1 : ZAlg G2.{u}) := by
    simp [rightFactor, basis, MonoidAlgebra.one_def]
  rw [hr] at heq
  have hc := congrArg (fun p : ZAlg G2.{u} => p.coeff 1) heq
  simp [add_mul, mul_add, target_coefficient, MonoidAlgebra.one_def] at hc

def reverseRegistration : Registration reverseArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
      rightFactor s * leftFactor s t = target H) where
  actual := carrierActual
  bridge := Iff.rfl
  variation := ⟨reverse_actual_law, carrierBad, reverse_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨carrierBad, ?_, rfl, reverse_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨G2.{u}, (1 : G2.{u}), g2s, Ne.symm g2_not_one⟩

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} carrierSignature.{u} (fun _ _ s => s) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "InvolutionUniformExchange") "factors_reverse") "Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange/Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(reverseArena.{u})⟩,
  objectArena := .source ⟨(reverseArena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (reverseArena.{u}) ⟨(reverseRegistration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} carrierSignature.{u} (fun _ _ s => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.anchorEnumeration }


#print axioms distinctRegistration
#print axioms forwardRegistration
#print axioms reverseRegistration
end Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardArena.{u}
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0} (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseArena.) (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.observation0.{u} : {H : Type u} →
  [inst : Group.{u} H] →
    [Fintype.{u} H] →
      (s t : H) →
        (hs :
            @Eq.{u + 1} H
              (@HMul.hMul.{u, u, u} H H H
                (@instHMul.{u} H
                  (@MulOne.toMul.{u} H
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                s s)
              (@OfNat.ofNat.{u} H (nat_lit 1)
                (@One.toOfNat1.{u} H
                  (@InvOneClass.toOne.{u} H
                    (@DivInvOneMonoid.toInvOneClass.{u} H
                      (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
            Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.carrierSignature.{u} PUnit.unit.{1} H :=
  fun {H : Type u} [Group.{u} H] [Fintype.{u} H] (s t : H)
    (hs :
      @Eq.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s s)
        (@OfNat.ofNat.{u} H (nat_lit 1)
          (@One.toOfNat1.{u} H
            (@InvOneClass.toOne.{u} H
              (@DivInvOneMonoid.toInvOneClass.{u} H
                (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.carrierSignature.{u}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.carrierActual.{u} PUnit.unit.{1} H s

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_reverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_reverse, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"reverseRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.reverseRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0} (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctArena.) (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"source_ne_target\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.observation0.{u} : {H : Type u} →
  [inst : Group.{u} H] →
    [Fintype.{u} H] →
      (s t : H) →
        (hs :
            @Eq.{u + 1} H
              (@HMul.hMul.{u, u, u} H H H
                (@instHMul.{u} H
                  (@MulOne.toMul.{u} H
                    (@MulOneClass.toMulOne.{u} H
                      (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                s s)
              (@OfNat.ofNat.{u} H (nat_lit 1)
                (@One.toOfNat1.{u} H
                  (@InvOneClass.toOne.{u} H
                    (@DivInvOneMonoid.toInvOneClass.{u} H
                      (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst))))))) →
          (hst :
              @Ne.{u + 1} H
                (@HMul.hMul.{u, u, u} H H H
                  (@instHMul.{u} H
                    (@MulOne.toMul.{u} H
                      (@MulOneClass.toMulOne.{u} H
                        (@Monoid.toMulOneClass.{u} H
                          (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                  s t)
                (@HMul.hMul.{u, u, u} H H H
                  (@instHMul.{u} H
                    (@MulOne.toMul.{u} H
                      (@MulOneClass.toMulOne.{u} H
                        (@Monoid.toMulOneClass.{u} H
                          (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
                  t s)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
              Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u} PUnit.unit.{1}
              (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) :=
  fun {H : Type u} [Group.{u} H] [Fintype.{u} H] (s t : H)
    (hs :
      @Eq.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s s)
        (@OfNat.ofNat.{u} H (nat_lit 1)
          (@One.toOfNat1.{u} H
            (@InvOneClass.toOne.{u} H
              (@DivInvOneMonoid.toInvOneClass.{u} H
                (@DivisionMonoid.toDivInvOneMonoid.{u} H (@Group.toDivisionMonoid.{u} H inst)))))))
    (hst :
      @Ne.{u + 1} H
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          s t)
        (@HMul.hMul.{u, u, u} H H H
          (@instHMul.{u} H
            (@MulOne.toMul.{u} H
              (@MulOneClass.toMulOne.{u} H
                (@Monoid.toMulOneClass.{u} H (@DivInvMonoid.toMonoid.{u} H (@Group.toDivInvMonoid.{u} H inst))))))
          t s)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementActual.{u} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) t

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"source_ne_target\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"source_ne_target\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.source_ne_target, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"distinctRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.distinctRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0} (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardArena.) (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).actual

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_forward\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).bridge

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.observation0.{u} : {H : Type u} →
  [Group.{u} H] →
    [Fintype.{u} H] →
      (s t : H) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
          Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u} PUnit.unit.{1}
          (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) :=
  fun {H : Type u} [Group.{u} H] [Fintype.{u} H] (s t : H) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementSignature.{u}
    Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.elementActual.{u} PUnit.unit.{1}
    (@Sigma.mk.{u + 1, u} (Type u) (fun (H : Type u) => H) H s) t

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_forward\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"factors_forward\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.factors_forward, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).actual (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"InvolutionUniformExchange\",\"forwardRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange, declaration := `Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange.forwardRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

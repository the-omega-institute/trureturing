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

register_information_theorem source_ne_target in distinctArena
  readout via (realize elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))
  realizes distinctRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "arg"], stateBinder := 4 }] })
  escape continues (open)

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

register_information_theorem factors_forward in forwardArena
  readout via (realize elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))
  realizes forwardRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

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

register_information_theorem factors_reverse in reverseArena
  readout via (realize carrierSignature.{u} (fun _ _ s => s) (fun e => nomatch e))
  realizes reverseRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms distinctRegistration
#print axioms forwardRegistration
#print axioms reverseRegistration
end Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange

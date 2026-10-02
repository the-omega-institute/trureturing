import D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
import Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange

open _root_.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open _root_.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
universe u

theorem sourceNat_diagonal {H : Type u} [Group H] [Fintype H]
    (s : H) (hs : s * s = 1) : sourceNat s s = targetNat H := by
  exact congrArg toNat (source_diagonal s hs)

def minimumArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H)
    (hs : s * s = 1) (hst : s * t ≠ t * s),
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
    ¬ExchangeChain (NAlg H) (sourceMatrix s (R.readout () ⟨H, s⟩ t)) (targetMatrix H) 0

theorem minimum_actual_law : minimumArena.{u}.Law elementActual := by
  intro H instG instF s t hs hst
  exact involution_minimum_one s t hs hst

theorem minimum_rejected_law : ¬ minimumArena.{u}.Law elementBad := by
  intro h
  have hn := (h g3s.{u} g3t g3_involution g3_noncommuting).2
  apply hn
  change ExchangeChain (NAlg G3.{u}) (scalar (sourceNat g3s g3s))
    (scalar (targetNat G3)) 0
  rw [sourceNat_diagonal g3s g3_involution]
  exact ExchangeChain.nil _

def minimumRegistration : Registration minimumArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H)
      (hs : s * s = 1) (hst : s * t ≠ t * s),
      ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
      ¬ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 0) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨minimum_actual_law, elementBad, minimum_rejected_law⟩
  sensitivity := elementSensitivity minimumArena.Law minimum_rejected_law
  dependence := elementDependence

register_information_theorem involution_minimum_one in minimumArena
  readout via (realize elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))
  realizes minimumRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "fn", "fn", "arg", "arg"], stateBinder := 4 }] })
  escape continues (open)

def productsArena : Arena where
  signature := elementSignature.{u}
  Law R := ∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
    toNat (leftFactor s t) * toNat (rightFactor s) =
      sourceNat s (R.readout () ⟨H, s⟩ t) ∧
    toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H

theorem products_actual_law : productsArena.{u}.Law elementActual := by
  intro H instG instF s t hs
  exact natural_factor_products s t hs

theorem products_rejected_law : ¬ productsArena.{u}.Law elementBad := by
  intro h
  have heq : sourceNat g3s.{u} g3t = sourceNat g3s g3s :=
    (natural_factor_products g3s g3t g3_involution).1.symm.trans
      (h g3s g3t g3_involution).1
  rw [sourceNat_diagonal g3s g3_involution] at heq
  have hc := congrArg (fun p : NAlg G3.{u} => p.coeff g3t) heq
  change (toNat (source g3s g3t)).coeff g3t = (toNat (target G3)).coeff g3t at hc
  simp only [toNat, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply,
    g3_source_coefficient, target_coefficient] at hc
  exact (by decide : (3 : ℕ) ≠ 2) hc

def productsRegistration : Registration productsArena.{u}
    (∀ {H : Type u} [Group H] [Fintype H] (s t : H) (hs : s * s = 1),
      toNat (leftFactor s t) * toNat (rightFactor s) = sourceNat s t ∧
      toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H) where
  actual := elementActual
  bridge := Iff.rfl
  variation := ⟨products_actual_law, elementBad, products_rejected_law⟩
  sensitivity := elementSensitivity productsArena.Law products_rejected_law
  dependence := elementDependence

register_information_theorem natural_factor_products in productsArena
  readout via (realize elementSignature.{u} (fun _ _ t => t) (fun e => nomatch e))
  realizes productsRegistration
  escape from source ({
    owner := `D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
      "fn", "arg", "arg", "arg"], stateBinder := 4 }] })
  escape continues (open)

#print axioms minimumRegistration
#print axioms productsRegistration
end Reg.D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy

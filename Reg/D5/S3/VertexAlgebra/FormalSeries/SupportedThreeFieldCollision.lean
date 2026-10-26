import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-! The source family and exact telescope bridge for signed collision are
specified below. A complete Contract.Registration additionally needs lawful
source selection, whole-family variation, sensitivity and observational
dependence. No validated four-slot registration is asserted. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision
open _root_.D5.S3.VertexAlgebra.SupportedThreeFieldCollision
open _root_.D5.S3.VertexAlgebra.SupportedChannelSeries
open _root_.D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
universe u
noncomputable section

structure Parameter where
  R : Type u
  ringR : CommRing R
  algebraR : @Algebra ℂ R _ ringR.toSemiring
  N : ℕ
  A : ℕ
  B : ℕ
  a : ℤ
  b : ℤ

def signature : Signature where
  Params := Parameter.{u}
  State p := (ℤ → ℤ → p.R) × MvPowerSeries (Fin 2) p.R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p source => by
    change p.R
    letI : CommRing p.R := p.ringR
    letI : Algebra ℂ p.R := p.algebraR
    exact ∑ᶠ i : ℕ,
      (((-1 : ℂ) ^ i) * integerBinomial ((p.N : ℤ) - p.a - 1) i) •
        source.1 (p.a - p.A - p.N + i) (p.b - p.B - i))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ {R : Type u} [instR : CommRing R] [instA : Algebra ℂ R]
    (F : ℤ → ℤ → R) (N A B : ℕ)
    (_lower : ∀ x y : ℤ, y < -(B : ℤ) → F x y = 0)
    (P : MvPowerSeries (Fin 2) R)
    (_common : ∀ x y : ℤ, clear N F (x - A) (y - B) = extend P x y)
    (a b : ℤ),
    Function.HasFiniteSupport (fun i : ℕ =>
      (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
        F (a - A - N + i) (b - B - i)) ∧
    r.readout () ⟨R, instR, instA, N, A, B, a, b⟩ (F, P) =
      extend (collision P) a b

theorem source_bridge :
    (type_of% (@signed_cleared_collision.{u})) ↔ arena.{u}.Law actual.{u} := Iff.rfl

abbrev RequiredEvidence := Registration arena.{u} (type_of% (@signed_cleared_collision.{u}))

end
end Reg.D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

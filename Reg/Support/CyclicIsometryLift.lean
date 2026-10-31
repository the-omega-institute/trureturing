import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeSugawaraConformal
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators VertexOperator
noncomputable section
namespace Reg.Support.CyclicIsometryLift

private def D0 : LatticeData :=
  ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩

namespace CanonicalPower
abbrev signature : Signature where
  Params := LatticeData
  State D := Carrier D ≃ₗ[ℂ] Carrier D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := (Carrier D ≃ₗ[ℂ] Carrier D) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature equality := by
  intro i
  refine ⟨D0, 1, LinearEquiv.neg ℂ, ?_⟩
  intro h
  have he : (LinearEquiv.neg ℂ : Carrier D0 ≃ₗ[ℂ] Carrier D0) = 1 :=
    Eq.mp (congrFun h 1) rfl
  have bad := congrArg (fun W : Carrier D0 ≃ₗ[ℂ] Carrier D0 =>
    MvPolynomial.constantCoeff (W (vacuum D0) 0)) he
  norm_num [vacuum, LinearEquiv.neg_apply] at bad

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (hgm : ∀ a, g^[m] a = a),
    R.readout () D
      ((D5.S3.VertexAlgebra.Lattice.IsometryLift.lift D g)^m)
      (diagonal D (orbitCharacter D g hg m hgm)) ∧
    (∀ a, orbitCharacter D g hg m hgm (g a) = orbitCharacter D g hg m hgm a) ∧
    (∀ a, complexSign (orbitCharacter D g hg m hgm a) =
      ∏ j ∈ Finset.range m,
        (D5.S3.VertexAlgebra.Lattice.IsometryLift.phase D g (g^[j] a) : ℂ)) ∧
    (∀ a, complexSign (orbitCharacter D g hg m hgm a) =
      (D5.S3.VertexAlgebra.Lattice.IsometryLift.phase D g (orbitNorm D g m a) : ℂ) *
        paritySign (bilinear D a (orbitNorm D g m a)))

private theorem bad : ¬ arena.Law rejected := by
  intro h
  exact (h D0 (AddEquiv.refl _) (by intros; rfl) 0 (by intros; rfl)).1

def family : Registration arena (type_of% (@canonical_power)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨canonical_power, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
end CanonicalPower

namespace CyclicLift
abbrev signature : Signature where
  Params := LatticeData
  State D := Carrier D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := Carrier D → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature equality := by
  intro i
  refine ⟨D0, 0, vacuum D0, ?_⟩
  intro h
  have bad : vacuum D0 = 0 := Eq.mp (congrFun h 0) rfl
  simpa [vacuum] using bad

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (g : Charge D ≃+ Charge D)
    (_hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
    (m : ℕ) (_hm : 0 < m) (_hgm : ∀ a, g^[m] a = a),
    ∃ chi : Charge D →+ F₂,
      R.readout () D (corrected D g chi (vacuum D)) (vacuum D) ∧
      (∀ (u : Carrier D) (n : ℤ) (v : Carrier D),
        corrected D g chi (((Y D u)[[n]]) v) =
          ((Y D (corrected D g chi u))[[n]]) (corrected D g chi v)) ∧
      (∀ v : Carrier D, corrected D g chi (translation D v) =
        translation D (corrected D g chi v)) ∧
      corrected D g chi ^ m = 1 ∧
      (orderOf g.toEquiv = m → ∀ k : ℕ, corrected D g chi ^ k = 1 ↔ m ∣ k)

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨chi, hc⟩ := h D0 (AddEquiv.refl _) (by intros; rfl) 1 (by decide)
    (by intros; rfl)
  exact hc.1

def family : Registration arena (type_of% (@cyclic_lift)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨cyclic_lift, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
end CyclicLift
end Reg.Support.CyclicIsometryLift

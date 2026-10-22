/- Source-family equality readouts for actual sector mathematics. -/
import D5.S3.VertexAlgebra.LatticeSectorRankZero
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open scoped VertexOperator BigOperators
noncomputable section
namespace Reg.Support.LatticeSectorIntertwiner

abbrev signature : Signature where
  Params := Type
  State X := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ X := X → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equality : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature equality := by
  intro i
  refine ⟨ℂ, 0, 1, ?_⟩
  intro h
  have bad : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero bad

private def D0 : LatticeData := ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩

namespace ChargeHomogeneity
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (α β : Charge D) (u v : Oscillator D) (n : ℤ),
    R.readout () (Carrier D) (((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v))
      (Finsupp.single (α + β) ((((Y D (Finsupp.single α u))[[n]]) (Finsupp.single β v)) (α + β)))

private theorem bad : ¬ arena.Law rejected := by
  intro h; exact h D0 0 0 0 0 0

def family : Registration arena (type_of% (@charge_homogeneity)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨charge_homogeneity, rejected, by intro h; exact h D0 0 0 0 0 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
end ChargeHomogeneity

namespace NormalizedGround
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β : Charge D) (I : IO D α β (α + β))
    (_ : MvPolynomial.constantCoeff (I.val 1 (-bilinear D α β - 1) 1) = 0),
    R.readout () (IO D α β (α + β)) I 0

private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hg : (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) * gramComplex D0 = 1 := by
    ext i; exact Fin.elim0 i
  have gh : gramComplex D0 * (0 : Matrix (Fin D0.rank) (Fin D0.rank) ℂ) = 1 := by
    ext i; exact Fin.elim0 i
  exact h D0 0 hg gh 0 0 0 (by simp)

def family : Registration arena (type_of% (@normalized_ground_detects_zero)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨normalized_ground_detects_zero, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
end NormalizedGround

namespace WrongCharge
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (α β γ : Charge D) (_ : γ ≠ α + β)
    (I : IO D α β γ), R.readout () (IO D α β γ) I 0

private def D1 : LatticeData :=
  ⟨1, fun _ _ => 2, by intros; rfl, by intro i; exact ⟨1, rfl⟩⟩

private theorem bad : ¬ arena.Law rejected := by
  intro h
  let H : Matrix (Fin D1.rank) (Fin D1.rank) ℂ := fun _ _ => 1 / 2
  have inv : H * gramComplex D1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    change (∑ _ : Fin 1, (1 / 2 : ℂ) * (2 : ℂ)) = 1
    norm_num
  let γ : Charge D1 := fun _ => 1
  have ne : γ ≠ (0 : Charge D1) + 0 := by
    intro he
    have e := congrFun he ⟨0, by decide⟩
    norm_num [γ] at e
  exact h D1 H inv 0 0 γ ne 0

def family : Registration arena (type_of% (@wrong_charge_vanishing)) where
  actual := equality
  bridge := Iff.rfl
  variation := ⟨wrong_charge_vanishing, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
end WrongCharge

end Reg.Support.LatticeSectorIntertwiner

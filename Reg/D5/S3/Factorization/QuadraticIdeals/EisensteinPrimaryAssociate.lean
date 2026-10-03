import D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => EisensteinOrder
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : EisensteinOrder)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (z : EisensteinOrder)
      (hz : ((QuadraticAlgebra.norm z : ℤ) : ZMod 3) = 1),
    ∃ u : EisensteinOrder, IsUnit u ∧ QuadraticAlgebra.norm u = 1 ∧
      (3 : EisensteinOrder) ∣ u * R.readout () () z - 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨u, _, _, hdiv⟩ := h 1 (by
    norm_num [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one])
  have hdiv' : (3 : EisensteinOrder) ∣ (-1 : EisensteinOrder) := by
    simpa [rejected, realize] using hdiv
  have hcoord : (3 : ℤ) ∣ (-1 : ℤ) :=
    (QuadraticAlgebra.algebraMap_dvd_iff.mp hdiv').1
  norm_num at hcoord

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro z hz
    exact exists_primary_associate z hz
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : EisensteinOrder), x ≠ y
    exact ⟨(), 0, 1, zero_ne_one⟩

register_information_theorem
  _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate
  in arena
  readout via (realize signature (fun _ _ z => z) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate

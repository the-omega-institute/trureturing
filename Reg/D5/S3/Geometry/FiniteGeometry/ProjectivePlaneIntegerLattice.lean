import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice

/-! Whole-source audit attempt. These exact source echoes and the actual
incidence family are NOT a completed Contract.Registration. SourceSelection,
exact law bridges and whole-family intervention/dependence evidence are not
supplied. No declared_validated claim is made. -/

namespace Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice
open _root_.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped BigOperators
universe u v

structure Inputs where
  P : Type u
  L : Type v
  membership : Membership P L
  points : Fintype P
  lines : Fintype L
  plane : @Configuration.ProjectivePlane P L membership

attribute [instance] Inputs.membership Inputs.points Inputs.lines Inputs.plane

/-- Preserve the original integer state and point-valued incidence readout. -/
def signature : DependentFamily.Signature where
  Params := Inputs.{u,v}
  State := fun I => I.L → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ I => I.P → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u,v} :=
  DependentFamily.realize signature.{u,v}
    (fun _ I a => incidence (P := I.P) a) (fun i => Empty.elim i)

section SourceEchoes
variable {P : Type u} {L : Type v} [Membership P L] [Fintype P] [Fintype L]
  [Configuration.ProjectivePlane P L]
local notation "Q" => (Configuration.ProjectivePlane.order P L : ℤ)

example (a : L → ℤ) : (∑ x : P, incidence a x) = (Q + 1) * ∑ l, a l :=
  total_incidence a
example (a : L → ℤ) (l : L) : lineSum (incidence a) l = Q * a l + ∑ k, a k :=
  lineSum_incidence a l
example : Function.Injective (incidence (P := P) (L := L)) := incidence_injective
example (z : P → ℤ) (s : ℤ) (ht : (∑ x, z x) = (Q + 1) * s)
    (hd : ∀ l : L, Q ∣ lineSum z l - s) :
    ∃! a : L → ℤ, incidence a = z ∧ (∑ l, a l) = s ∧
      ∀ l, a l = (lineSum z l - s) / Q := integer_reconstruction z s ht hd
example (z : P → ℤ) : z ∈ lattice (L := L) ↔
    ∃ s : ℤ, (∑ x, z x) = (Q + 1) * s ∧ ∀ l : L, Q ∣ lineSum z l - s :=
  mem_lattice_iff z
example (S : Finset P) (hne : S.Nonempty) (hp : S ≠ Finset.univ) :
    indicator S ∈ lattice (L := L) ↔ ∃ l : L, S = Finset.univ.filter (· ∈ l) :=
  boolean_mem_lattice_iff S hne hp
example (x : P) (k : ℤ) : (fun y => k * unit x y) ∈ lattice (L := L) ↔
    Q * (Q + 1) ∣ k := unit_mem_lattice_iff x k
example (x y : P) (hxy : x ≠ y) (k : ℤ) :
    (fun z => k * (unit x z - unit y z)) ∈ lattice (L := L) ↔ Q ∣ k :=
  difference_mem_lattice_iff x y hxy k
example (k : ℤ) : (fun _ : P => k) ∈ lattice (L := L) ↔ Q + 1 ∣ k :=
  constant_mem_lattice_iff k
end SourceEchoes

end Reg.D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice

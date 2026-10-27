import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open Lattice.NormFourVirasoroVector Lattice.NormFourVacuumIrreducible
open Lattice.NormFourVacuumVertexAlgebra
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators VertexOperator

/- The source bridge retains the actual state-field algebra and every natural
word grade throughout the entire lattice-parameter family. Whole-family
variation, sensitivity, observational dependence, lawful enrolled readout and
 source selection remain unproved. This bridge is not a Contract.Registration.
 Open audit: https://github.com/the-omega-institute/trureturing/issues/22336 -/
structure Params where
  D : LatticeData
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ
  hs : s ^ 2 = 1

abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := StateFieldVertexAlgebra (vacuumDescendants p.D p.a p.s) ×
    (ℕ → Submodule ℂ (vacuumDescendants p.D p.a p.s))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (vertexAlgebra p.D p.a p.ha p.s p.hs, grade p.D p.a p.s))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    let S := vacuumDescendants D a s
    let pair := r.readout () (⟨D, a, ha, s, hs⟩ : Params) ()
    let V := pair.1
    let G := pair.2
    (V.vacuum : Carrier D) = vacuum D ∧ V.vacuum ≠ 0 ∧
    (∀ v : S, (V.translation v : Carrier D) = translation D v.val ∧
      V.translation v = restrictedMode D a ha s hs (-1) v) ∧
    (∀ (u v : S) (k : ℤ), (((V.stateField u)[[k]]) v : Carrier D) =
      ((Y D u.val)[[k]]) v.val) ∧
    (∀ (u v : S) (k : ℤ), ((Y D u.val)[[k]]) v.val ∈ S) ∧
    (∃ e : S, e.val = vector D a s ∧ e ∈ G 2 ∧
      (∀ m : ℤ, ((V.stateField e)[[m+1]]) = restrictedMode D a ha s hs m) ∧
      (∀ m n : ℤ,
        restrictedMode D a ha s hs m * restrictedMode D a ha s hs n -
            restrictedMode D a ha s hs n * restrictedMode D a ha s hs m =
          ((m : ℂ) - (n : ℂ)) • restrictedMode D a ha s hs (m+n) +
            (if m+n = 0 then (((m : ℂ)^3 - (m : ℂ)) / 24) •
              (1 : Module.End ℂ S) else 0)) ∧
      ((V.stateField e)[[0]]) e = V.translation e ∧
      ((V.stateField e)[[1]]) e = (2 : ℂ) • e ∧
      ((V.stateField e)[[2]]) e = 0 ∧
      ((V.stateField e)[[3]]) e = (1 / 4 : ℂ) • V.vacuum ∧
      ∀ k : ℤ, 4 ≤ k → ((V.stateField e)[[k]]) e = 0) ∧
    G 0 = Submodule.span ℂ {V.vacuum} ∧
    (∀ n : ℕ, FiniteDimensional ℂ (G n)) ∧
    (∀ v : S, ∃ f : ℕ →₀ S,
      (∑ n ∈ f.support, f n) = v ∧ ∀ n, f n ∈ G n) ∧
    (∀ f : ℕ →₀ S, (∀ n, f n ∈ G n) →
      (∑ n ∈ f.support, f n) = 0 → f = 0) ∧
    (∀ (n : ℕ) (v : S), v ∈ G n →
      restrictedMode D a ha s hs 0 v = (n : ℂ) • v) ∧
    (∀ (n t : ℕ) (k : ℤ) (u v : S), u ∈ G n → v ∈ G t →
      let w : ℤ := (n : ℤ) + (t : ℤ) - k - 1
      (0 ≤ w → ((V.stateField u)[[k]]) v ∈ G w.toNat) ∧
      (w < 0 → ((V.stateField u)[[k]]) v = 0)) ∧
    (∀ U : Submodule ℂ S,
      (∀ (u v : S) (k : ℤ), v ∈ U → ((V.stateField u)[[k]]) v ∈ U) →
      U = ⊥ ∨ U = ⊤)

theorem source_bridge :
    (type_of% (@actual_simple_graded_vacuum_vertex_algebra)) ↔ law actual := Iff.rfl

theorem source_actual : law actual :=
  source_bridge.mp (@actual_simple_graded_vacuum_vertex_algebra)

end Reg.D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

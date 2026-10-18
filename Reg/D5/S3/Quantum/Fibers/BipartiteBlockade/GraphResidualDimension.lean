import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section
open scoped BigOperators Classical ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension

open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
open _root_.D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private residual_eq_ker from
  D5.S3.Quantum.Fibers.BipartiteBlockade.JointDiagonalCoordinates
open private family_independent family_large from
  D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

structure Parameters where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  color : V → Bool

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State p := p.V → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} :=
  realize signature (fun _ p Ω => by
    letI := p.finite
    letI := p.equality
    exact Module.finrank ℝ
      (attainableResidual p.graph (nonlinearNeighborhoods p.graph)
        (classWeight p.graph p.color Ω))) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (Ω : V → ℝ)
    (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty),
    r.readout () ⟨V, finite, equality, G, color⟩ Ω =
      (nonlinearNeighborhoods G).card - 1 ∧
    ∀ x : nonlinearNeighborhoods G → ℝ,
      compatibility (nonlinearNeighborhoods G) (classWeight G color Ω) x = 0 →
      ∃ δ : Configuration G → ℝ,
        (∑ S, δ S) = 0 ∧
        (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
        (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 ∧
        (∀ N : nonlinearNeighborhoods G, blockingMoment G N.val δ = x N) ∧
        (G.Connected → ∃ R : Matrix (Configuration G) (Configuration G) ℂ,
          R.IsHermitian ∧ Matrix.trace R = 0 ∧
          (∀ v, Matrix.trace (R * number G v) = 0) ∧
          (∀ v, Matrix.trace (R *
            ⁅hamiltonian G (fun u => (Ω u : ℂ)),
              ⁅hamiltonian G (fun u => (Ω u : ℂ)), number G v⁆⁆) = 0) ∧
          (∀ v, Matrix.trace (R * blockade G v) = (blockMoment G δ v : ℂ)) ∧
          ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, |t| < η →
            (maximallyMixed G + t • R).PosDef ∧
            Matrix.trace (maximallyMixed G + t • R) = 1 ∧
            (∀ v, occupationMean G (maximallyMixed G + t • R) v =
              occupationMean G (maximallyMixed G) v) ∧
            (∀ v, acceleration G Ω (maximallyMixed G + t • R) v =
              acceleration G Ω (maximallyMixed G) v) ∧
            ∀ v, blockadeMean G (maximallyMixed G + t • R) v =
              blockadeMean G (maximallyMixed G) v + t * blockMoment G δ v)

/-- The source is reconstructed exactly. A valid observation-dependence proof
for the invariant dimension readout is not supplied. -/
theorem source_equivalence :
    (type_of% (@graph_residual_dimension_and_realization.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h V finite equality G color proper Ω nonzero nonempty
    exact ⟨(h G color proper Ω nonzero nonempty).1,
      (h G color proper Ω nonzero nonempty).2⟩
  · intro h V finite equality G color proper Ω nonzero nonempty
    exact h G color proper Ω nonzero nonempty

namespace Local

structure Parameters where
  V : Type u
  finite : Fintype V
  equality : DecidableEq V
  graph : SimpleGraph V
  drive : V → ℝ

@[reducible] def signature : Signature where
  Params := Parameters.{u}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

@[reducible] def actual : Realization signature.{u} :=
  realize signature (fun _ p radius => by
    letI := p.finite
    letI := p.equality
    exact Module.finrank ℝ
      (affineSpan ℝ (physicalBlockingResiduals p.graph p.drive radius)).direction)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty) (radius : ℝ) (positive : 0 < radius),
    Submodule.span ℝ (physicalBlockingResiduals G Ω radius) =
      LinearMap.ker (compatibility (nonlinearNeighborhoods G) (classWeight G color Ω)) ∧
    Module.finrank ℝ (Submodule.span ℝ (physicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 ∧
    r.readout () ⟨V, finite, equality, G, Ω⟩ radius =
      (nonlinearNeighborhoods G).card - 1

/-- The affine-dimension source is exact; its readout is constant over all
strictly positive radii under the source assumptions. -/
theorem source_equivalence :
    (type_of% (@local_density_residual_dimension.{u})) ↔ arena.{u}.Law actual := Iff.rfl

end Local

namespace Full

open Local

@[reducible] def actual : Realization Local.signature.{u} :=
  realize Local.signature (fun _ p radius => by
    letI := p.finite
    letI := p.equality
    exact Module.finrank ℝ
      (affineSpan ℝ (fullPhysicalBlockingResiduals p.graph p.drive radius)).direction)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := Local.signature.{u}
  Law r := ∀ {V : Type u} [finite : Fintype V] [equality : DecidableEq V]
    (G : SimpleGraph V) (connected : G.Connected)
    (color : V → Bool) (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0)
    (nonempty : (nonlinearNeighborhoods G).Nonempty) (radius : ℝ) (positive : 0 < radius),
    fullPhysicalBlockingResiduals G Ω radius =
      classExpansion G '' physicalBlockingResiduals G Ω radius ∧
    Function.Injective (classExpansion G) ∧
    Module.finrank ℝ (Submodule.span ℝ (fullPhysicalBlockingResiduals G Ω radius)) =
      (nonlinearNeighborhoods G).card - 1 ∧
    r.readout () ⟨V, finite, equality, G, Ω⟩ radius =
      (nonlinearNeighborhoods G).card - 1

/-- The full-vector source is exact; valid-radius observation dependence
for its affine-dimension readout remains unavailable. -/
theorem source_equivalence :
    (type_of% (@full_blocking_residual_dimension.{u})) ↔ arena.{u}.Law actual := Iff.rfl

end Full

#print axioms source_equivalence
#print axioms Local.source_equivalence
#print axioms Full.source_equivalence

end Reg.D5.S3.Quantum.Fibers.BipartiteBlockade.GraphResidualDimension

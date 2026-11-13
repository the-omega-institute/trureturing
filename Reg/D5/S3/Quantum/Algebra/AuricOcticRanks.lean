import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.AuricOcticRanks

/-! Source-bound readouts and exact telescope bridges for the consumed rank declarations. -/

set_option autoImplicit false
noncomputable section
open Module LinearMap
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.AuricActualOcticWindow

namespace Reg.D5.S3.Quantum.Algebra.AuricOcticRanks
universe u v w

structure Coordinates where
  K : Type u
  Ω : Type v
  [fieldK : Field K]
  [finiteLabels : Fintype Ω]
  [decideLabels : DecidableEq Ω]
attribute [instance] Coordinates.fieldK Coordinates.finiteLabels Coordinates.decideLabels

structure ActionParameters where
  K : Type u
  Ω : Type v
  G : Type w
  [fieldK : Field K]
  [finiteLabels : Fintype Ω]
  [decideLabels : DecidableEq Ω]
  [groupG : Group G]
  [finiteG : Fintype G]
  [actionG : MulAction G Ω]
attribute [instance] ActionParameters.fieldK ActionParameters.finiteLabels
  ActionParameters.decideLabels ActionParameters.groupG ActionParameters.finiteG ActionParameters.actionG

abbrev projectionSignature : Signature where
  Params := Coordinates.{u, v}
  State p := Finset p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (p.Ω → p.K) →ₗ[p.K] (p.Ω → p.K)
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature.{u, v} := realize projectionSignature
  (fun _ _ S => coordinateProject S) (fun e => nomatch e)

abbrev rankSignature : Signature where
  Params := ActionParameters.{u, v, w}
  State p := Submodule p.K (p.Ω → p.K) × Finset p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature.{u, v, w} := realize rankSignature
  (fun _ _ x => rowRank x.1 x.2) (fun e => nomatch e)

abbrev crossSignature : Signature where
  Params := Coordinates.{u, v}
  State p := ((p.Ω → p.K) →ₗ[p.K] (p.Ω → p.K)) × Finset p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def crossActual : Realization crossSignature.{u, v} := realize crossSignature
  (fun _ _ x => crossRank x.1 x.2) (fun e => nomatch e)

abbrev actionCrossSignature : Signature where
  Params := ActionParameters.{u, v, w}
  State p := ((p.Ω → p.K) →ₗ[p.K] (p.Ω → p.K)) × Finset p.Ω
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actionCrossActual : Realization actionCrossSignature.{u, v, w} := realize actionCrossSignature
  (fun _ _ x => crossRank x.1 x.2) (fun e => nomatch e)

structure OrbitParameters where
  Ω : Type v
  G : Type w
  [finiteLabels : Fintype Ω]
  [decideLabels : DecidableEq Ω]
  [groupG : Group G]
  [finiteG : Fintype G]
  [actionG : MulAction G Ω]
attribute [instance] OrbitParameters.finiteLabels OrbitParameters.decideLabels
  OrbitParameters.groupG OrbitParameters.finiteG OrbitParameters.actionG
abbrev membershipSignature : Signature where
  Params := OrbitParameters.{v, w}
  State p := Finset p.Ω × p.G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.Ω
  Anchor := Empty
  finiteAnchor := inferInstance
def membershipActual : Realization membershipSignature.{v, w} := realize membershipSignature
  (fun _ _ x => orbitSet x.1 x.2) (fun e => nomatch e)

namespace Disjointness
abbrev arena : Arena where
  signature := projectionSignature.{u, v}
  Law R := ∀ (p : Coordinates.{u, v}) (U : Submodule p.K (p.Ω → p.K)) (S : Finset p.Ω),
    Disjoint (U.map (R.readout () p S)) (U.map (R.readout () p Sᶜ))

theorem source_bridge : (type_of% (@projected_disjoint.{u, v})) ↔ arena.{u, v}.Law projectionActual.{u, v} := by
  constructor
  · intro h p U S; exact h U S
  · intro h K Ω _ _ _ U S; exact h { K := K, Ω := Ω } U S

end Disjointness

namespace Containment
abbrev arena : Arena where
  signature := projectionSignature.{u, v}
  Law R := ∀ (p : Coordinates.{u, v}) (U : Submodule p.K (p.Ω → p.K)) (S : Finset p.Ω),
    U ≤ U.map (R.readout () p S) ⊔ U.map (R.readout () p Sᶜ)

theorem source_bridge : (type_of% (@window_le_projected_sup.{u, v})) ↔ arena.{u, v}.Law projectionActual.{u, v} := by
  constructor
  · intro h p U S; exact h U S
  · intro h K Ω _ _ _ U S; exact h { K := K, Ω := Ω } U S

end Containment

namespace Equality
abbrev arena : Arena where
  signature := projectionSignature.{u, v}
  Law R := ∀ (p : Coordinates.{u, v}) (U : Submodule p.K (p.Ω → p.K)) (S : Finset p.Ω),
    rowRank U S + rowRank U Sᶜ = finrank p.K U →
      ∀ x ∈ U, R.readout () p S x ∈ U

theorem source_bridge : (type_of% (@projection_stable_of_rank_equality.{u, v})) ↔ arena.{u, v}.Law projectionActual.{u, v} := by
  constructor
  · intro h p U S he; exact h U S he
  · intro h K Ω _ _ _ U S he; exact h { K := K, Ω := Ω } U S he

end Equality

namespace Membership
abbrev arena : Arena where
  signature := membershipSignature.{v, w}
  Law R := ∀ (p : OrbitParameters.{v, w}) (S : Finset p.Ω) (g : p.G) (i : p.Ω),
    i ∈ R.readout () p (S, g) ↔ g⁻¹ • i ∈ S

theorem source_bridge : (type_of% (@mem_orbitSet.{v, w})) ↔ arena.{v, w}.Law membershipActual.{v, w} := by
  constructor
  · intro h p S g i; exact h S g i
  · intro h Ω G _ _ _ _ _ S g i; exact h { Ω := Ω, G := G } S g i

end Membership

namespace StrictRank
abbrev arena : Arena where
  signature := rankSignature.{u, v, w}
  Law R := ∀ (p : ActionParameters.{u, v, w}) (U : Submodule p.K (p.Ω → p.K)),
    Fintype.card p.Ω = 8 → finrank p.K U = 4 →
    (∀ x y : p.Ω, ∃ g : p.G, g • x = y) →
    (∀ (g : p.G) S, R.readout () p (U, orbitSet S g) = R.readout () p (U, S)) →
    (∀ S : Finset p.Ω, S.Nonempty → Sᶜ.Nonempty →
      4 < R.readout () p (U, S) + R.readout () p (U, Sᶜ)) →
    ∀ S : Finset p.Ω, S.Nonempty → Sᶜ.Nonempty → S.card + 1 ≤ 2 * R.readout () p (U, S)

theorem source_bridge : (type_of% (@invariant_half_rank_strict.{v, w, u})) ↔ arena.{u, v, w}.Law rankActual.{u, v, w} := by
  constructor
  · intro h p U hΩ hU ht hi hc S hs hsc; exact h U hΩ hU ht hi hc S hs hsc
  · intro h Ω G _ _ _ _ _ K _ U hΩ hU ht hi hc S hs hsc; exact h { K := K, Ω := Ω, G := G } U hΩ hU ht hi hc S hs hsc

end StrictRank

namespace Matrix
abbrev arena : Arena where
  signature := crossSignature.{u, v}
  Law R := ∀ (p : Coordinates.{u, v}) (n : (p.Ω → p.K) →ₗ[p.K] (p.Ω → p.K)) (S : Finset p.Ω),
    ((LinearMap.toMatrix' n).submatrix (fun i : S => (i : p.Ω))
      (fun j : ↥(Sᶜ) => (j : p.Ω))).rank = R.readout () p (n, S)

theorem source_bridge : (type_of% (@crossRank_matrix.{v, u})) ↔ arena.{u, v}.Law crossActual.{u, v} := by
  constructor
  · intro h p n S; exact h n S
  · intro h Ω K _ _ _ n S; exact h { K := K, Ω := Ω } n S

end Matrix

namespace CutFree
abbrev arena : Arena where
  signature := actionCrossSignature.{u, v, w}
  Law R := ∀ (p : ActionParameters.{u, v, w}) (U : Submodule p.K (p.Ω → p.K))
    (n : (p.Ω → p.K) →ₗ[p.K] (p.Ω → p.K)), n.ker = U → n.range = U →
    Fintype.card p.Ω = 8 → finrank p.K U = 4 →
    (∀ x y : p.Ω, ∃ g : p.G, g • x = y) →
    (∀ (g : p.G) S, rowRank U (orbitSet S g) = rowRank U S) →
    (∀ S : Finset p.Ω, 0 < S.card → S.card < 8 → S.card + 1 ≤ 2 * rowRank U S) →
    ∀ S : Finset p.Ω, 2 ≤ S.card → S.card ≤ 6 →
      2 ≤ R.readout () p (n, S) ∨ 2 ≤ R.readout () p (n, Sᶜ)

theorem source_bridge : (type_of% (@cut_free_of_actual_ranks.{v, u, w})) ↔ arena.{u, v, w}.Law actionCrossActual.{u, v, w} := by
  constructor
  · intro h p U n hk hr hΩ hU ht hi hs S h2 h6; exact h U n hk hr hΩ hU ht hi hs S h2 h6
  · intro h Ω K _ _ _ G _ _ _ U n hk hr hΩ hU ht hi hs S h2 h6; exact h { K := K, Ω := Ω, G := G } U n hk hr hΩ hU ht hi hs S h2 h6

end CutFree

end Reg.D5.S3.Quantum.Algebra.AuricOcticRanks

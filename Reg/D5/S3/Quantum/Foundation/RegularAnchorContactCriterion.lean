import D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The source theorem is reconstructed from the original gap observation on V.
The four-slot audit additionally needs whole-family variation, role sensitivity,
observational dependence and exact enrolled source selection. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorNormalChart

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  p : pure cone unit
  effect : V →ₗ[ℝ] ℝ
  chart : FullBall3Chart cone unit p

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P x => (P.unit - P.effect) x) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → EB3 P.cone P.unit →
    Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p) →
    common P.cone P.unit P.p P.effect → Regular P.cone P.unit P.p →
    ∃ k : P.V →ₗ[ℝ] ℝ,
      (∀ x, k x = P.unit x - O.readout () P x) ∧
      Nonempty (NativeChart P.cone P.unit P.p k P.chart)

abbrev sourceScope : Prop := type_of% (@regular_anchor_native.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg h3 hinj he hreg
    refine ⟨P.effect, ?_, ?_⟩
    · intro x
      change P.effect x = P.unit x - (P.unit x - P.effect x)
      ring
    · exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg h3 hinj
        P.p P.effect he hreg P.chart
  · intro h V add space finite C u hc hs hg h3 hinj p e he hreg a
    obtain ⟨k, hk, hd⟩ := h (@Inputs.mk V add space finite C u p e a)
      hc hs hg h3 hinj he hreg
    have hke : k = e := by
      ext x
      have hx := hk x
      change k x = u x - (u x - e x) at hx
      linarith
    simpa only [hke] using hd

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@regular_anchor_native.{v})

end Reg.D5.S3.Quantum.Foundation.RegularAnchorNormalChart

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ
  p : pure cone unit
  effect : V →ₗ[ℝ] ℝ
  chart : FullBall3Chart cone unit p
  native : NativeChart cone unit p effect chart

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := ThreeSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ThreeSpace × ℝ × ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P w => (actualImage P.native, rho P.native w, width P.chart)) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    Convex ℝ (O.readout () P 0).1 ∧ (IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → EB3 P.cone P.unit →
    (∀ w : ThreeSpace, ‖w‖ = 1 →
      ((O.readout () P w).2.1 = 1 ↔ ∃ f : P.V →ₗ[ℝ] ℝ,
        proper P.cone P.unit f ∧ f (P.chart.param w) = 1 ∧
          f (P.chart.param (-w)) = 0)) ∧
    ((O.readout () P 0).2.2 = 1 ↔ ∃ w : ThreeSpace,
      ‖w‖ = 1 ∧ (O.readout () P w).2.1 = 1))

abbrev sourceScope : Prop :=
  type_of% (@actual_image_convex.{v}) ∧
  type_of% (@rho_one_iff_antipodal.{v}) ∧ type_of% (@width_one_iff_rho_one.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · rintro ⟨hC,hR,hW⟩ P
    refine ⟨@hC P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native, ?_⟩
    intro hc hs hg h3
    constructor
    · intro w hw
      exact @hR P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart
        hc hs hg h3 P.native w hw
    · exact @hW P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart
        hc hs hg h3 P.native
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro V add space finite C u p e a n
      exact (h (@Inputs.mk V add space finite C u p e a n)).1
    · intro V add space finite C u p e a hc hs hg h3 n w hw
      exact (h (@Inputs.mk V add space finite C u p e a n)).2 hc hs hg h3 |>.1 w hw
    · intro V add space finite C u p e a hc hs hg h3 n
      exact (h (@Inputs.mk V add space finite C u p e a n)).2 hc hs hg h3 |>.2

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp ⟨@actual_image_convex.{v}, @rho_one_iff_antipodal.{v}, @width_one_iff_rho_one.{v}⟩

end Reg.D5.S3.Quantum.Foundation.RegularAnchorWidthAntipode

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorShell

open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Inputs := RegularAnchorWidthAntipode.Inputs.{v}

structure Reading where
  image : Set ThreeSpace
  body : Set ThreeSpace
  support : ℝ
  radius : ℝ
  distance : ℝ

abbrev signature : Signature where
  Params := Inputs.{v}
  State _ := ThreeSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reading
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P w => ⟨actualImage P.native,shell P.native,
    rho P.native w,minimum P.native,boundaryDistance P.native⟩) (fun a => nomatch a)

structure Laws (P : Inputs.{v}) (o : ThreeSpace → Reading) : Prop where
  image_convex : Convex ℝ (o 0).image
  support : ∀ w r, (∀ z ∈ (o 0).body, -⟪w,z⟫ ≤ r) ↔ (o w).support ≤ r
  lipschitz : ∃ M : ℝ, 0 < M ∧ ∀ w z : ThreeSpace,
    |(o w).support - (o z).support| ≤ M * ‖w-z‖
  attained : ∃ w : ThreeSpace, ‖w‖ = 1 ∧ (o w).support = (o 0).radius ∧
    1 ≤ (o 0).radius ∧ ∀ z : ThreeSpace, ‖z‖ = 1 → (o 0).radius ≤ (o z).support
  contact_direction : ∀ z : ThreeSpace, z ∈ Metric.closedBall 0 1 →
    z ∈ frontier (o 0).body → ‖z‖ = 1 ∧ (o (-z)).support = 1
  unit_support : ∀ w : ThreeSpace, ‖w‖ = 1 → (o w).support = 1 →
    -w ∈ frontier (o 0).body
  minimum_contact : (o 0).radius = 1 ↔
    (Metric.closedBall (0 : ThreeSpace) 1 ∩ frontier (o 0).body).Nonempty
  halfspaces : ∀ z : ThreeSpace, z ∈ (o 0).body ↔
    ∀ w : ThreeSpace, ‖w‖ = 1 → -⟪w,z⟫ ≤ (o w).support
  scaled_ball : Metric.closedBall (0 : ThreeSpace) (o 0).radius ⊆ (o 0).body
  strict_margin : 1 < (o 0).radius →
    Metric.closedBall (0 : ThreeSpace) 1 ⊆ interior (o 0).body ∧
      ∀ x ∈ Metric.closedBall (0 : ThreeSpace) 1,
        ∀ y ∈ frontier (o 0).body, (o 0).radius - 1 ≤ dist x y
  strict_distance : 1 < (o 0).radius →
    (o 0).radius - 1 ≤ (o 0).distance ∧ 0 < (o 0).radius - 1

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P, Laws P (O.readout () P)

abbrev sourceScope : Prop :=
  type_of% (@actual_image_convex.{v}) ∧
  type_of% (@shell_support_le_iff.{v}) ∧
  type_of% (@rho_lipschitz.{v}) ∧
  type_of% (@minimum_attained.{v}) ∧
  type_of% (@ball_frontier_direction.{v}) ∧
  type_of% (@rho_one_frontier.{v}) ∧
  type_of% (@minimum_one_iff_contact.{v}) ∧
  type_of% (@mem_shell_iff.{v}) ∧
  type_of% (@minimum_ball_subset.{v}) ∧
  type_of% (@strict_margin.{v}) ∧
  type_of% (@strict_boundary_distance.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ P
    exact {
      image_convex := @h1 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      support := @h2 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      lipschitz := @h3 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      attained := @h4 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      contact_direction := fun z hz hb =>
        @h5 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native z hz hb
      unit_support := fun w hw hr =>
        @h6 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native w hw hr
      minimum_contact := @h7 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      halfspaces := @h8 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      scaled_ball := @h9 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      strict_margin := @h10 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native
      strict_distance := @h11 P.V P.add P.space P.finite P.cone P.unit P.p P.effect P.chart P.native }
  · intro h
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).image_convex
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).support
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).lipschitz
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).attained
    · intro V add space finite C u p e a n z hz hb
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).contact_direction z hz hb
    · intro V add space finite C u p e a n w hw hr
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).unit_support w hw hr
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).minimum_contact
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).halfspaces
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).scaled_ball
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).strict_margin
    · intro V add space finite C u p e a n
      exact (h (@RegularAnchorWidthAntipode.Inputs.mk V add space finite C u p e a n)).strict_distance

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp ⟨@actual_image_convex.{v},@shell_support_le_iff.{v},@rho_lipschitz.{v},
    @minimum_attained.{v},@ball_frontier_direction.{v},@rho_one_frontier.{v},
    @minimum_one_iff_contact.{v},@mem_shell_iff.{v},@minimum_ball_subset.{v},
    @strict_margin.{v},@strict_boundary_distance.{v}⟩

end Reg.D5.S3.Quantum.Foundation.RegularAnchorShell

namespace Reg.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.FacetZeroGluing
open _root_.D5.S3.Quantum.Foundation.OrthogonalJointCompletion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Inputs := RegularAnchorNormalChart.Inputs.{v}
abbrev signature := RegularAnchorNormalChart.signature.{v}
abbrev actual := RegularAnchorNormalChart.actual.{v}

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ → EB3 P.cone P.unit →
    Function.Injective (fun p : pure P.cone P.unit => exclusion P.cone P.unit p) →
    common P.cone P.unit P.p P.effect → Regular P.cone P.unit P.p →
    ∃ k : P.V →ₗ[ℝ] ℝ,
      (∀ x, k x = P.unit x - O.readout () P x) ∧
      ∃ n : NativeChart P.cone P.unit P.p k P.chart, ContactCriterion n

abbrev sourceScope : Prop := type_of% (@regular_anchor_contact_criterion.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hs hg h3 hinj he hreg
    refine ⟨P.effect,?_,?_⟩
    · intro x
      change P.effect x = P.unit x - (P.unit x - P.effect x)
      ring
    · exact @h P.V P.add P.space P.finite P.cone P.unit hc hs hg h3 hinj
        P.p P.effect he hreg P.chart
  · intro h V add space finite C u hc hs hg h3 hinj p e he hreg a
    obtain ⟨k,hk,hn⟩ := h (@RegularAnchorNormalChart.Inputs.mk V add space finite C u p e a)
      hc hs hg h3 hinj he hreg
    have hke : k = e := by
      ext x
      have hx := hk x
      change k x = u x - (u x - e x) at hx
      linarith
    subst k
    exact hn

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@regular_anchor_contact_criterion.{v})

end Reg.D5.S3.Quantum.Foundation.RegularAnchorContactCriterion

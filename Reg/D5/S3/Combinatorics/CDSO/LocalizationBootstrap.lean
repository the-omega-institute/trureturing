import Reg.Support.DependentFamily
import D5.S3.Combinatorics.CDSO.LocalizationBootstrap

/-! Complete source reconstruction with the actual common-event probability readout.
The family intervention and observational-dependence certificates are not supplied. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.CDSO.LocalizationBootstrap

open _root_.D5.S3.Combinatorics.CDSO.LocalizationBootstrap
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Filter Topology

noncomputable section

abbrev sourceScope := type_of% (@lemma135)

abbrev signature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State p := Σ x : JointArray p.1 p.2, x.TailChoice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature
    (fun _ _ s => JointArray.tailEventMass s.1 s.2) (fun e => nomatch e)

def observedEstimate (R : DependentFamily.Realization signature) (Cp Cu CH C : ℝ)
    {a h : ℕ} (x : JointArray a h) (D : x.TailChoice) : Prop :=
  let p := R.readout () (a, h) ⟨x, D⟩
  0 < p ∧
  p ≤ Cp * (a : ℝ)^(-3 / 2 : ℝ) ∧
  JointArray.tailSum x D.D ≤ Cu * (a : ℝ)^(-3 / 2 : ℝ) ∧
  JointArray.tailEnergy x D ≤ CH * (a : ℝ)^(3 / 2 : ℝ) ∧
  (JointArray.tailEnergy x D + (2 * (a : ℝ)^3 - C * (a : ℝ)^2) * p ≤ JointArray.d x ∧
    (h : ℝ)^2 / p + (2 * (a : ℝ)^3 - C * (a : ℝ)^2) * p ≤
      JointArray.tailEnergy x D + (2 * (a : ℝ)^3 - C * (a : ℝ)^2) * p)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (h : ℕ) (M : ℝ), 2 ≤ h ∧ 0 < M →
    ∃ Cp Cu CH C : ℝ, 0 < Cp ∧ 0 < Cu ∧ 0 < CH ∧ 0 < C ∧ ∃ N : ℕ,
      (∀ a : ℕ, 4 ≤ a → N ≤ a → ∀ (x : JointArray a h) (D : x.TailChoice),
        JointArray.d x ≤ M * (a : ℝ)^(3 / 2 : ℝ) →
          observedEstimate R Cp Cu CH C x D) ∧
      UniformLocalization h M ∧
      (∀ (x : ∀ a : IndexAtLeast4, JointArray a h)
        (D : ∀ a : IndexAtLeast4, (x a).TailChoice),
        EventuallyAtLeast (fun a => JointArray.d (x a) ≤ M * scale a (3 / 2 : ℝ)) →
        Tendsto (fun a => JointArray.delta (x a) (D a)) atTop (𝓝 0) ∧
          EventuallyAtLeast (fun a => observedEstimate R Cp Cu CH C (x a) (D a)))

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp (@lemma135)

/-- The full family certificate requires actual-law variation, sensitivity and
observational dependence on the whole admissible source domain. -/
def familyCertificate : Option (DependentFamily.Registration arena sourceScope) := none

#print axioms source_bridge
#print axioms actual_positive

end

end Reg.D5.S3.Combinatorics.CDSO.LocalizationBootstrap

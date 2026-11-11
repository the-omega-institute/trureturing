import D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- RegUNVALIDATED / UNCOMPILED_UNACCEPTED. Full-telescope typed ATTEMPTS only.
For EVERY target below:
 escapeFrom: named literal source readout; compiled occurrence binding is pending.
 readout: typed actual realization; lawful enrollment and sourceSelection are pending.
 realization: ENTIRE original telescope, actual_law, definitional source_bridge;
 rejected lawful families, whole-family intervention, other-readout/anchor-fixed
 sensitivity, actual observational dependence and axiom closure remain missing.
 continuation: unknown. No registration, binding or validation is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup
open Set Finset Filter Real
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace stable_positive_mesh
/- Source readout: first moving generator including its convergence premise. RegUNVALIDATED. -/
abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {α γ : ℝ → ℝ} {α₀ γ₀ : ℝ}
    (hα₀ : 0 < α₀) (hγ₀ : 0 < γ₀)
    (hirr : Irrational (γ₀ / α₀))
    (hα : Tendsto (fun x => V.readout () α x) atTop (𝓝 α₀)) (hγ : Tendsto γ atTop (𝓝 γ₀)),
    ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ D T : ℝ,
      ∀ X : ℝ, T ≤ X → ∀ Δ : ℝ, D ≤ Δ →
        ∃ a b : ℕ, b ≤ B ∧ (a : ℝ) ≤ 2 * Δ / α₀ ∧
          Δ - ε / 2 ≤ (a : ℝ) * V.readout () α X + (b : ℝ) * γ X ∧
          (a : ℝ) * V.readout () α X + (b : ℝ) * γ X ≤ Δ - ε / 4

private theorem actual_law : arena.Law actual := by
  exact @_root_.D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup.stable_positive_mesh

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup.stable_positive_mesh)) ↔ arena.Law actual := Iff.rfl

#print axioms actual_law
#print axioms source_bridge
end stable_positive_mesh

end Reg.D5.S3.Arith.DiophantineApproximation.StablePositiveSemigroup

import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.AuricActualOcticWindow

set_option autoImplicit false
noncomputable section

open Module LinearMap
open scoped TensorProduct Classical
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.AuricActualOcticWindow

namespace Reg.D5.S3.Quantum.Algebra.AuricActualOcticWindow
universe u v w

/-- Original fields and window, with the complete source hypotheses. -/
structure Parameters where
  F : Type u
  D : Type v
  K : Type w
  [fieldF : Field F]
  [fieldD : Field D]
  [fieldK : Field K]
  [algebraFD : Algebra F D]
  [algebraFK : Algebra F K]
  [algebraDK : Algebra D K]
  [tower : IsScalarTower F D K]
  [finiteD : FiniteDimensional F D]
  [zeroCharacteristic : CharZero F]
  [finiteK : FiniteDimensional F K]
  [normalK : Normal F K]
  W : Submodule F D
  hD : finrank F D = 8
  hW : finrank F W = 4
  hE : {c : D | ∀ z ∈ W, c * z ∈ W} = Set.range (algebraMap F D)

attribute [instance] Parameters.fieldF Parameters.fieldD Parameters.fieldK
  Parameters.algebraFD Parameters.algebraFK Parameters.algebraDK Parameters.tower
  Parameters.finiteD Parameters.zeroCharacteristic Parameters.finiteK Parameters.normalK

abbrev signature : Signature where
  Params := Parameters.{u, v, w}
  State p := {a : p.D // a ∉ quotientSet p.W}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.D →ₗ[p.F] p.D
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The readout is the original inverse-obstruction operator, not a truth value. -/
def actual : Realization signature.{u, v, w} := realize signature
  (fun _ p a => actualOperator p.W p.hD p.hW a.val a.property)
  (fun e => nomatch e)

/-- Exact source postcondition, with only the original operator occurrence abstracted. -/
def conclusion (p : Parameters.{u, v, w}) (a : p.D)
    (op : p.D →ₗ[p.F] p.D) : Prop :=
    Function.Bijective (obstruction p.W a) ∧
    ∃ e : p.K ⊗[p.F] p.D ≃ₐ[p.K] ((p.D →ₐ[p.F] p.K) → p.K),
      (∀ (c : p.K) (d : p.D) (σ : p.D →ₐ[p.F] p.K), e (c ⊗ₜ[p.F] d) σ = c * σ d) ∧
      let U := (p.W.baseChange p.K).map e.toLinearMap
      let n := e.toLinearMap ∘ₗ op.baseChange p.K ∘ₗ e.symm.toLinearMap
      let N := LinearMap.toMatrix' n
      n.comp n = 0 ∧ n.range = U ∧ n.ker = U ∧ N * N = 0 ∧ N.rank = 4 ∧
      (∀ (g : p.K ≃ₐ[p.F] p.K) (σ τ : p.D →ₐ[p.F] p.K),
        N (g.toAlgHom.comp σ) (g.toAlgHom.comp τ) = g (N σ τ)) ∧
      (∀ S : Finset (p.D →ₐ[p.F] p.K), S.Nonempty → Sᶜ.Nonempty →
        S.card + 1 ≤ 2 * finrank p.K (U.map (coordinateProject S))) ∧
      (∀ S : Finset (p.D →ₐ[p.F] p.K), 2 ≤ S.card → S.card ≤ 6 →
        2 ≤ (N.submatrix (fun i : S => (i : p.D →ₐ[p.F] p.K))
          (fun j : ↥(Sᶜ) => (j : p.D →ₐ[p.F] p.K))).rank ∨
        2 ≤ (N.submatrix (fun i : ↥(Sᶜ) => (i : p.D →ₐ[p.F] p.K))
          (fun j : S => (j : p.D →ₐ[p.F] p.K))).rank)

abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law R := ∀ (p : Parameters.{u, v, w}) (a : signature.State p),
    conclusion p a.val (R.readout () p a)

/-- The complete telescope is reconstructed without a conditional matrix replacement. -/
theorem full_telescope_bridge :
    (type_of% (@general43_2_cut_free.{u, v, w})) ↔ arena.{u, v, w}.Law actual := by
  constructor
  · intro h p a
    exact @h p.F p.D p.fieldF p.fieldD p.algebraFD p.K p.fieldK p.algebraFK
      p.finiteD p.zeroCharacteristic p.finiteK p.normalK p.algebraDK p.tower
      p.W p.hD p.hW p.hE a.val a.property
  · intro h F D _ _ _ K _ _ _ _ _ _ _ _ W hD hW hE a ha
    exact h { F := F, D := D, K := K, W := W, hD := hD, hW := hW, hE := hE } ⟨a, ha⟩

end Reg.D5.S3.Quantum.Algebra.AuricActualOcticWindow

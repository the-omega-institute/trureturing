import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.AuricActualOcticSupport

/-! Source-bound operator readout and complete support-connectivity telescope. -/

set_option autoImplicit false
noncomputable section

open Module LinearMap
open scoped TensorProduct Classical
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.AuricActualOcticWindow

namespace Reg.D5.S3.Quantum.Algebra.AuricActualOcticSupport
universe u v w z

/-- Original fields and window, with the complete source hypotheses. -/
structure Parameters where
  F : Type u
  D : Type v
  K : Type w
  L : Type z
  [fieldF : Field F]
  [fieldD : Field D]
  [fieldK : Field K]
  [fieldL : Field L]
  [algebraKL : Algebra K L]
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
  Parameters.fieldL Parameters.algebraKL
  Parameters.algebraFD Parameters.algebraFK Parameters.algebraDK Parameters.tower
  Parameters.finiteD Parameters.zeroCharacteristic Parameters.finiteK Parameters.normalK

abbrev signature : Signature where
  Params := Parameters.{u, v, w, z}
  State p := {a : p.D // a ∉ quotientSet p.W}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.D →ₗ[p.F] p.D
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The readout is the original inverse-obstruction operator, not a truth value. -/
def actual : Realization signature.{u, v, w, z} := realize signature
  (fun _ p a => actualOperator p.W p.hD p.hW a.val a.property)
  (fun e => nomatch e)

/-- Exact source postcondition, with only the original operator occurrence abstracted. -/
def conclusion (p : Parameters.{u, v, w, z})
    (op : p.D →ₗ[p.F] p.D) : Prop :=
    ∃ e : p.K ⊗[p.F] p.D ≃ₐ[p.K] ((p.D →ₐ[p.F] p.K) → p.K),
      (∀ (c : p.K) (d : p.D) (σ : p.D →ₐ[p.F] p.K), e (c ⊗ₜ[p.F] d) σ = c * σ d) ∧
      let n := e.toLinearMap ∘ₗ op.baseChange p.K ∘ₗ e.symm.toLinearMap
      let N := LinearMap.toMatrix' n
      (∀ σ τ, Relation.ReflTransGen (fun i j => N i j ≠ 0) σ τ) ∧
      (∀ σ τ, Relation.ReflTransGen (fun i j => algebraMap p.K p.L (N i j) ≠ 0) σ τ) ∧
      Irreducible (_root_.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant.rowMatrix
        (N.map (algebraMap p.K p.L))).det ∧
      Irreducible (_root_.D5.S3.Quantum.Algebra.FixedDiagonalDeterminant.diagonalMatrix
        (N.map (algebraMap p.K p.L))).det

abbrev arena : Arena where
  signature := signature.{u, v, w, z}
  Law R := ∀ (p : Parameters.{u, v, w, z}) (a : signature.State p),
    conclusion p (R.readout () p a)

/-- The complete telescope is reconstructed without a conditional matrix replacement. -/
theorem full_telescope_bridge :
    (type_of% (@general43_2_support.{u, v, w, z})) ↔ arena.{u, v, w, z}.Law actual := by
  constructor
  · intro h p a
    exact @h p.F p.D p.fieldF p.fieldD p.algebraFD p.K p.fieldK p.algebraFK
      p.finiteD p.zeroCharacteristic p.finiteK p.normalK p.algebraDK p.tower
      p.L p.fieldL p.algebraKL p.W p.hD p.hW p.hE a.val a.property
  · intro h F D _ _ _ K _ _ _ _ _ _ _ _ L _ _ W hD hW hE a ha
    exact h { F := F, D := D, K := K, L := L, W := W, hD := hD, hW := hW, hE := hE } ⟨a, ha⟩

namespace OriginalPolynomial

structure State (p : Parameters.{u, v, w, z}) where
  bD : Basis (Fin 8) p.F p.D
  bW : Basis (Fin 4) p.F p.W
  bQ : Basis (Fin 4) p.F (p.D ⧸ p.W)
  a : p.D
  ha : a ∉ quotientSet p.W

abbrev signature : Signature where
  Params := Parameters.{u, v, w, z}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MvPolynomial (Fin 8) p.F
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Readout of the polynomial in its original coefficient field and original bases. -/
def actual : Realization signature.{u, v, w, z} := realize signature
  (fun _ p s => obstructionPolynomial p.W s.bD s.bW s.bQ)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v, w, z}
  Law R := ∀ (p : Parameters.{u, v, w, z}) (s : State p),
    Irreducible (MvPolynomial.map ((algebraMap p.K p.L).comp (algebraMap p.F p.K))
      (R.readout () p s))

/-- The source theorem retains every original basis and all coefficient extensions. -/
theorem full_telescope_bridge :
    (type_of% (@general43_2_original_polynomial.{u, v, w, z})) ↔
      arena.{u, v, w, z}.Law actual := by
  constructor
  · intro h p s
    exact @h p.F p.D p.fieldF p.fieldD p.algebraFD p.K p.fieldK p.algebraFK
      p.finiteD p.zeroCharacteristic p.finiteK p.normalK p.algebraDK p.tower
      p.L p.fieldL p.algebraKL p.W p.hD p.hW p.hE s.bD s.bW s.bQ s.a s.ha
  · intro h F D _ _ _ K _ _ _ _ _ _ _ _ L _ _ W hD hW hE bD bW bQ a ha
    exact h { F := F, D := D, K := K, L := L, W := W, hD := hD, hW := hW, hE := hE }
      { bD := bD, bW := bW, bQ := bQ, a := a, ha := ha }

end OriginalPolynomial

end Reg.D5.S3.Quantum.Algebra.AuricActualOcticSupport

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the rational current readouts in the two mode-one laws. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate (nebeLatticeData)
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity (nebeGram_posDef)
open _root_.D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport (current)
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction LatticePositiveEnergy
open LeanInformationAudit

open private rationalCurrent_ne_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics

noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature LatticeData RationalCartan Carrier

def actual : Realization signature := realize signature (fun _ D => rationalCurrent D)
  (fun e => nomatch e)

private def direction (D : LatticeData) : RationalCartan D := fun _ => 1

private theorem nebe_current_ne_zero : rationalCurrent nebeLatticeData (direction nebeLatticeData) ≠ 0 := by
  apply rationalCurrent_ne_zero
  intro h
  have he := congrFun h (0 : Fin nebeLatticeData.rank)
  exact one_ne_zero he

private theorem current_zero (D : LatticeData) : rationalCurrent D 0 = 0 := by
  simp [rationalCurrent, current]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨nebeLatticeData, direction nebeLatticeData, 0, ?_⟩
  intro h
  exact nebe_current_ne_zero (h.trans (current_zero _))

namespace InBlock

private def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) (x : W),
    mu D (blockQuadratic D hPos W) 1 (rationalCurrent D x) = R.readout () D x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x : (⊤ : Submodule ℚ (RationalCartan nebeLatticeData)) := ⟨direction _, Submodule.mem_top⟩
  exact nebe_current_ne_zero
    ((blockQuadratic_mode_one_of_mem nebeLatticeData nebeGram_posDef ⊤ x).symm.trans
      (h nebeLatticeData nebeGram_posDef ⊤ x))

def family : Registration arena (type_of% blockQuadratic_mode_one_of_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨blockQuadratic_mode_one_of_mem, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    blockQuadratic_mode_one_of_mem (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.blockQuadratic_mode_one_of_mem.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.InBlock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ D => rationalCurrent D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateOperand := some #["arg"]
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end InBlock

namespace Perpendicular

private def rejected : Realization signature := realize signature
  (fun _ D _ => rationalCurrent D (direction D)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (W : Submodule ℚ (RationalCartan D)) {x : RationalCartan D},
    x ∈ (rationalGram D).orthogonal W →
      mu D (blockQuadratic D hPos W) 1 (R.readout () D x) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let W : Submodule ℚ (RationalCartan nebeLatticeData) := ⊤
  let x : W := ⟨direction _, Submodule.mem_top⟩
  have hz := h nebeLatticeData nebeGram_posDef W (x := 0) (Submodule.zero_mem _)
  exact nebe_current_ne_zero
    ((blockQuadratic_mode_one_of_mem nebeLatticeData nebeGram_posDef W x).symm.trans hz)

def family : Registration arena (type_of% @blockQuadratic_mode_one_of_orthogonal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@blockQuadratic_mode_one_of_orthogonal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@blockQuadratic_mode_one_of_orthogonal) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.blockQuadratic_mode_one_of_orthogonal.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.Perpendicular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ D => rationalCurrent D) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateOperand := some #["arg"]
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Perpendicular

namespace FixedStates

private abbrev AmbientGroup := Matrix.SpecialLinearGroup (Fin 2) (ZMod 47)
private abbrev States := Carrier nebeLatticeData
private abbrev Params := Σ H : Subgroup AmbientGroup, Representation ℂ H States × H

abbrev signature := Reg.Support.SingleDependentReadout.signature Params (fun _ => States)
  (fun _ => States)

def actual : Realization signature := realize signature (fun _ p v => p.2.1 p.2.2 v)
  (fun e => nomatch e)

private def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Subgroup AmbientGroup), ¬ 3 ∣ Nat.card H →
    ∀ (ρ : Representation ℚ H (RationalCartan nebeLatticeData)), Function.Injective ρ →
    ∀ (A : Representation ℂ H States),
      (∀ g x y, rationalGram nebeLatticeData (ρ g x) (ρ g y) = rationalGram nebeLatticeData x y) →
      (∀ g x, A g (rationalCurrent nebeLatticeData x) = rationalCurrent nebeLatticeData (ρ g x)) →
      (∀ g u n v, A g (mu nebeLatticeData u n v) = mu nebeLatticeData (A g u) n (A g v)) →
      ∃ q : Fin 2 → States, (∀ i, q i ∈ grade nebeLatticeData 2) ∧
        (∀ g i, R.readout () ⟨H, A, g⟩ (q i) = q i) ∧ LinearIndependent ℂ q

private abbrev H₀ : Subgroup AmbientGroup := ⊥

private def action : Representation ℂ H₀ States := Representation.trivial _ _ _

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let ρ : Representation ℚ H₀ (RationalCartan nebeLatticeData) := Representation.trivial _ _ _
  have hcard : ¬ 3 ∣ Nat.card H₀ := by
    rw [Nat.card_unique]
    decide
  have hρ : Function.Injective ρ := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨q, _, hfixed, hind⟩ := h H₀ hcard ρ hρ action
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  exact (hind.ne_zero 0) (hfixed 1 0).symm

def family : Registration arena (type_of% p48q_prime_to_three_fixed_weight_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨p48q_prime_to_three_fixed_weight_two, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨H₀, action, 1⟩, rationalCurrent nebeLatticeData (direction nebeLatticeData), 0, ?_⟩
    exact nebe_current_ne_zero

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    p48q_prime_to_three_fixed_weight_two (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.p48q_prime_to_three_fixed_weight_two.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics.FixedStates.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => p.2.1 p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics
    coordinates := #[0, 4, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn"]
      functionOperand := true
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedStates

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qInvariantQuadratics

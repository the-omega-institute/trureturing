import Mathlib.Algebra.Field.ULift
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the concrete order-three matrix. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix (Fin 48) (Fin 48) ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 48) (Fin 48) ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M ^ 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () nebeOrderThree = 1

private theorem rejected_law : ¬ arena.Law rejected := zero_ne_one

def family : Registration arena (type_of% nebeOrderThree_cube) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_cube, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Matrix (Fin 48) (Fin 48) ℤ) ^ 3 ≠ 1 ^ 3
    simp

noncomputable def cubeRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_cube (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.nebeOrderThree_cube.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M ^ 3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev traceSignature : Signature where
  Params := Unit
  State _ := Matrix (Fin 48) (Fin 48) ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejectedTrace : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => 1) (fun e => nomatch e)

namespace Trace

def actual : Realization traceSignature :=
  realize traceSignature (fun _ _ M => M.trace) (fun e => nomatch e)

abbrev arena : Arena where
  signature := traceSignature
  Law R := R.readout () () nebeOrderThree = 0

private theorem rejected_law : ¬ arena.Law rejectedTrace := one_ne_zero

def family : Registration arena (type_of% nebeOrderThree_trace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_trace, rejectedTrace, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejectedTrace,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Matrix (Fin 48) (Fin 48) ℤ).trace ≠ (1 : Matrix (Fin 48) (Fin 48) ℤ).trace
    norm_num [Matrix.trace_one]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_trace (Realization traceSignature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.nebeOrderThree_trace.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.Trace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ M => M.trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Trace

namespace SquareTrace

def actual : Realization traceSignature :=
  realize traceSignature (fun _ _ M => (M ^ 2).trace) (fun e => nomatch e)

abbrev arena : Arena where
  signature := traceSignature
  Law R := R.readout () () nebeOrderThree = 0

private theorem rejected_law : ¬ arena.Law rejectedTrace := one_ne_zero

def family : Registration arena (type_of% nebeOrderThree_trace_square) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_trace_square, rejectedTrace, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejectedTrace,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change ((0 : Matrix (Fin 48) (Fin 48) ℤ) ^ 2).trace ≠ ((1 : Matrix (Fin 48) (Fin 48) ℤ) ^ 2).trace
    norm_num [Matrix.trace_one]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_trace_square (Realization traceSignature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.nebeOrderThree_trace_square.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.SquareTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature (fun _ _ M => (M ^ 2).trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SquareTrace

namespace FixedRank

universe u

abbrev Parameters := Σ K : Type u, Field K

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Matrix (Fin 48) (Fin 48) ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI := p.2
    exact Module.End p.1 (Fin 48 → p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p => @rowAction p.1 p.2) (fun e => nomatch e)

noncomputable def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => by
    letI := p.2
    exact 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [CharZero K],
    Module.finrank K (LinearMap.ker (R.readout () ⟨K, f⟩ nebeOrderThree - 1)) = 16

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  let _ : CharZero (ULift.{u} ℚ) :=
    ⟨fun m n h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩
  intro h
  have hRank := h (ULift.{u} ℚ)
  let K := ULift.{u} ℚ
  let dimension (T : Module.End K (Fin 48 → K)) := Module.finrank K (LinearMap.ker T)
  have hFull : dimension (1 - 1) = 48 := by
    calc
      dimension (1 - 1) = dimension 0 := congrArg dimension (sub_self _)
      _ = 48 := by
        change Module.finrank K (LinearMap.ker (0 : Module.End K (Fin 48 → K))) = 48
        rw [LinearMap.ker_zero, finrank_top, Module.finrank_pi, Fintype.card_fin]
  exact (by decide : (48 : ℕ) ≠ 16) (hFull.symm.trans hRank)

noncomputable def family : Registration arena.{u} (type_of% nebeOrderThree_fixedRank16.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeOrderThree_fixedRank16, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} ℚ, inferInstance⟩, 0, 1, ?_⟩
    change rowAction (ULift.{u} ℚ) 0 ≠ rowAction (ULift.{u} ℚ) 1
    have h0 : rowAction (ULift.{u} ℚ) 0 = 0 := by
      simp [rowAction]
    have h1 : rowAction (ULift.{u} ℚ) 1 = 1 := by
      unfold rowAction
      rw [Matrix.transpose_one]
      change ((Int.castRingHom (ULift.{u} ℚ)).mapMatrix (1 : Matrix (Fin 48) (Fin 48) ℤ)).toLin' = 1
      rw [map_one, Matrix.toLin'_one, ← Module.End.one_eq_id]
    rw [h0, h1]
    exact zero_ne_one

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeOrderThree_fixedRank16.{u} (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.nebeOrderThree_fixedRank16.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate.FixedRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => @rowAction p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "fn",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedRank

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate

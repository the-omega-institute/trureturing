import D5.S3.VertexAlgebra.TwistedGround.BinarySchur
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Exact quadratic readout and variation for binary Schur elimination. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.BinarySchur

open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
open _root_.D5.S3.VertexAlgebra.TwistedGround.BinarySchur
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

structure Parameters where
  Index : Type u
  finite : Fintype Index
  decidable : DecidableEq Index
  a : ZMod 8
  b : ZMod 8
  c : ZMod 8
  odd : residue b = 1
  B : Matrix (Fin 2) Index (ZMod 8)
  L : Matrix Index Index (ZMod 8)
  unit : letI := finite
    letI := decidable
    IsUnit (fromBlocks (gram a b c) B Bᵀ (L + Lᵀ)).det

abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := Parameters.{u}
  State p := Fin 2 ⊕ p.Index → ZMod 8
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 8
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p x =>
    letI := p.finite
    letI := p.decidable
    (fromBlocks (halfGram p.a p.b p.c) p.B 0 p.L).toBilin' x x)
    (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun empty => nomatch empty)

def arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law observation := ∀ p : Parameters.{u},
    letI := p.finite
    letI := p.decidable
    let P := shear p.a p.b p.c p.B
    let R := residual p.a p.b p.c p.B p.L
    P.det = 1 ∧
      Pᵀ * fromBlocks (gram p.a p.b p.c) p.B p.Bᵀ (p.L + p.Lᵀ) * P =
        fromBlocks (gram p.a p.b p.c) 0 0 (R + Rᵀ) ∧
      IsUnit (R + Rᵀ).det ∧
      ∀ w : Fin 2 ⊕ p.Index → ZMod 8,
        observation.readout () p (P *ᵥ w) =
          (halfGram p.a p.b p.c).toBilin' (w ∘ Sum.inl) (w ∘ Sum.inl) +
            R.toBilin' (w ∘ Sum.inr) (w ∘ Sum.inr)

theorem exact_source_bridge :
    (type_of% (@even_binary_elimination.{u})) ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro source p
    letI := p.finite
    letI := p.decidable
    exact source p.a p.b p.c p.odd p.B p.L p.unit
  · intro law I finite decidable a b c hb B L hu
    exact law ⟨I, finite, decidable, a, b, c, hb, B, L, hu⟩

private def hyperbolic : Parameters.{u} where
  Index := ULift.{u} Empty
  finite := inferInstance
  decidable := inferInstance
  a := 0
  b := 1
  c := 0
  odd := by rfl
  B := 0
  L := 0
  unit := by simp [gram, Matrix.det_fin_two]

private theorem rejected_law : ¬ arena.{u}.Law (rejected : Realization signature.{u}) := by
  intro law
  have h := (law hyperbolic).2.2.2 (fun _ => 1)
  change (0 : ZMod 8) =
      (halfGram 0 1 0).toBilin' (fun _ => 1) (fun _ => 1) +
      (_root_.D5.S3.VertexAlgebra.TwistedGround.BinarySchur.residual 0 1 0
        (0 : Matrix (Fin 2) (ULift.{u} Empty) (ZMod 8)) 0).toBilin'
        (fun _ => 1) (fun _ => 1) at h
  norm_num [halfGram, Matrix.toBilin'_apply, Fin.sum_univ_two] at h
  exact (by decide : (0 : ZMod 8) ≠ 1) h

private theorem sensitivity : Sensitivity arena.{u} (actual : Realization signature.{u}) := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other h
      exact (h (Subsingleton.elim (α := Unit) _ _)).elim
    · funext empty
      exact nomatch empty
  · intro empty
    exact nomatch empty

private theorem dependence : ObservationalDependence signature.{u} (actual : Realization signature.{u}) := by
  intro role
  refine ⟨hyperbolic, (fun _ => 0), (fun _ => 1), ?_⟩
  change (fromBlocks (halfGram 0 1 0) (0 : Matrix (Fin 2) (ULift.{u} Empty) (ZMod 8)) 0 0).toBilin'
      (fun _ => 0) (fun _ => 0) ≠
    (fromBlocks (halfGram 0 1 0) (0 : Matrix (Fin 2) (ULift.{u} Empty) (ZMod 8)) 0 0).toBilin'
      (fun _ => 1) (fun _ => 1)
  norm_num [halfGram, Matrix.toBilin'_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  exact (by decide : (0 : ZMod 8) ≠ 1)

def familyRegistration : Registration arena.{u} (type_of% (@even_binary_elimination.{u})) where
  actual := actual
  bridge := exact_source_bridge
  variation := ⟨exact_source_bridge.{u}.mp (@even_binary_elimination.{u}), rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_binary_elimination.{u})
    (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor)) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.BinarySchur.even_binary_elimination "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.BinarySchur.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms exact_source_bridge
#print axioms familyRegistration

end

end Reg.D5.S3.VertexAlgebra.TwistedGround.BinarySchur

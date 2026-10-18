import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.UniformValues
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Subentropy.Basic

open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

universe u v

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t f => f t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ t f => f t + 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, subentropyKernel (0 : Matrix Unit Unit ℂ),
    subentropyKernel (1 : Matrix Unit Unit ℂ), ?_⟩
  norm_num [actual, realize, subentropyKernel, Matrix.det_unique, Matrix.ofNat_apply]

namespace RectangularGram

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {κ : Type v}
    [fi : Fintype ι] [di : DecidableEq ι] [fk : Fintype κ] [dk : DecidableEq κ]
    (V : Matrix ι κ ℂ) (t : ℝ),
    R.readout () t (subentropyKernel (V.conjTranspose * V)) =
      subentropyKernel (V * V.conjTranspose) t

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance 0 1
  norm_num [rejected, realize, subentropyKernel] at he

def source_registration : Registration arena.{u,v}
    (type_of% @kernel_rectangular_gram.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_rectangular_gram, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kernel_rectangular_gram.{u,v}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.Basic.kernel_rectangular_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.Basic.RectangularGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t f => f t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.Basic
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RectangularGram

namespace Diagonal

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [di : DecidableEq ι]
    (p : ι → ℝ) (t : ℝ) (ht : t ≠ 0),
    R.readout () t (subentropyKernel (Matrix.diagonal (fun i => (p i : ℂ)))) =
      t / (1 + t) - ∏ i, t / (t + p i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 0) 1 (by norm_num)
  norm_num [rejected, realize, subentropyKernel, Matrix.det_unique] at he

def source_registration : Registration arena.{u}
    (type_of% @kernel_diagonal.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_diagonal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kernel_diagonal.{u}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Subentropy.Basic.kernel_diagonal.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.Basic.Diagonal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t f => f t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.Basic
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Diagonal

namespace AdjointReadout
open _root_.D5.S3.Quantum.Subentropy.UniformValues
open scoped BigOperators

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.2 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : ∀ (e : signature.{u,v}.Anchor) (p : signature.{u,v}.Params),
    signature.{u,v}.State p :=
  fun e => nomatch e

def observation : ∀ (i : signature.{u,v}.Role) (p : signature.{u,v}.Params),
    signature.{u,v}.State p → signature.{u,v}.Output i p :=
  fun _ _ V => V.conjTranspose

def actual : Realization signature.{u,v} :=
  realize signature observation emptyAnchor

def badAdjoint {ι : Type u} {κ : Type v} (V : Matrix ι κ ℂ) : Matrix κ ι ℂ := by
  classical
  exact fun j i =>
    if j = Classical.choice (show Nonempty κ from ⟨j⟩) then 2 * star (V i j) else 0

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ V => badAdjoint V) emptyAnchor

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro h
  have hc := congrArg (fun M => M ⟨()⟩ ⟨()⟩) h
  change star (0 : ℂ) = star (1 : ℂ) at hc
  norm_num at hc

private theorem uniformTwo_pos {ι : Type u} [Fintype ι] [DecidableEq ι]
    (hc : Fintype.card ι = 2) :
    0 < matrixSubentropy (diagonal (fun _ : ι => ((1 / 2 : ℝ) : ℂ))) := by
  rw [subentropy_uniformTwo hc]
  have hlog := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
  norm_num at hlog
  linarith

private def gate (κ : Type v) [DecidableEq κ] [Nonempty κ] : Matrix κ κ ℂ :=
  diagonal (fun j => if j = Classical.choice (inferInstance : Nonempty κ) then 2 else 0)

private theorem badAdjoint_eq {ι : Type u} {κ : Type v}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (V : Matrix ι κ ℂ) :
    badAdjoint V = gate κ * V.conjTranspose := by
  classical
  ext j i
  simp only [badAdjoint, gate, diagonal_mul, conjTranspose_apply]
  split_ifs <;> simp_all

private theorem gate_uniform_zero {κ : Type v}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] :
    matrixSubentropy (gate κ * diagonal (fun _ : κ => ((1 / 2 : ℝ) : ℂ))) = 0 := by
  classical
  let c : κ := Classical.choice (inferInstance : Nonempty κ)
  let w : κ → ℂ := Pi.single c 1
  have hw : ∑ j, star (w j) * w j = 1 := by simp [w, Pi.single_apply]
  have hp : gate κ * diagonal (fun _ : κ => ((1 / 2 : ℝ) : ℂ)) =
      vecMulVec w (star w) := by
    unfold gate
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases hi : i = c <;> by_cases hj : j = c <;>
      simp_all [c, w, diagonal_apply, vecMulVec, Pi.single_apply, eq_comm]
  rw [hp]
  exact matrixSubentropy_pure w hw

private theorem bad_gram_zero {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (V : Matrix ι κ ℂ)
    (hgram : V.conjTranspose * V = diagonal (fun _ => ((1 / 2 : ℝ) : ℂ))) :
    matrixSubentropy (badAdjoint V * V) = 0 := by
  rw [badAdjoint_eq, Matrix.mul_assoc, hgram]
  exact gate_uniform_zero

private theorem q_mul_comm {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    matrixSubentropy (A * B) = matrixSubentropy (B * A) := by
  unfold matrixSubentropy subentropyKernel
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have h := Matrix.det_one_add_mul_comm ((t⁻¹ : ℝ) • A) B
  simp only [Matrix.smul_mul, Matrix.mul_smul] at h
  exact congrArg (fun z : ℂ => t / (1 + t) - z.re⁻¹) h

private theorem bad_embedding_zero {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (J : Matrix ι κ ℂ) (hJ : J.conjTranspose * J = 1) :
    matrixSubentropy (J * diagonal (fun _ : κ => ((1 / 2 : ℝ) : ℂ)) * badAdjoint J) = 0 := by
  rw [q_mul_comm, badAdjoint_eq, Matrix.mul_assoc, ← Matrix.mul_assoc J.conjTranspose J,
    hJ, Matrix.one_mul]
  exact gate_uniform_zero

def hadamard : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ :=
  fun i j => if i.down = 1 ∧ j.down = 1 then -(1 / 2) else 1 / 2

private theorem hadamard_left :
    (hadamard : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ).conjTranspose *
      (hadamard : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ) =
      diagonal (fun _ : ULift.{v} (Fin 2) => ((1 / 2 : ℝ) : ℂ)) := by
  ext ⟨i⟩ ⟨j⟩
  simp only [Matrix.mul_apply]
  rw [← Equiv.ulift.symm.sum_comp]
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Fin.sum_univ_succ, map_ofNat,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]

private theorem hadamard_right :
    (hadamard : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ) *
      (hadamard : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ).conjTranspose =
      diagonal (fun _ : ULift.{u} (Fin 2) => ((1 / 2 : ℝ) : ℂ)) := by
  ext ⟨i⟩ ⟨j⟩
  simp only [Matrix.mul_apply]
  rw [← Equiv.ulift.symm.sum_comp]
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Fin.sum_univ_succ, map_ofNat,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]

namespace Gram
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V : Matrix ι κ ℂ),
    matrixSubentropy (R.readout () ⟨ι, κ⟩ V * V) =
      matrixSubentropy (V * V.conjTranspose)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2))
    inferInstance inferInstance inferInstance inferInstance hadamard
  change matrixSubentropy (badAdjoint hadamard * hadamard) = _ at hb
  rw [bad_gram_zero hadamard hadamard_left, hadamard_right] at hb
  have hp := uniformTwo_pos (ι := ULift.{u} (Fin 2)) (by simp)
  linarith

def family : Registration arena.{u,v} (type_of% @matrixSubentropy_rectangular_gram.{u,v}) where
  actual := realize signature.{u,v} (fun _ _ V => V.conjTranspose) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@matrixSubentropy_rectangular_gram, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrixSubentropy_rectangular_gram.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.Basic.matrixSubentropy_rectangular_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.Basic.AdjointReadout.Gram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ V => V.conjTranspose) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.Basic
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Gram

namespace Isometry
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (J : Matrix ι κ ℂ), J.conjTranspose * J = 1 →
    matrixSubentropy (J * A * R.readout () ⟨ι, κ⟩ J) = matrixSubentropy A

def identityLift : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ :=
  fun i j => if i.down = j.down then 1 else 0
private theorem identityLift_isometry :
    (identityLift : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ).conjTranspose *
      (identityLift : Matrix (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2)) ℂ) = 1 := by
  ext ⟨i⟩ ⟨j⟩
  simp only [Matrix.mul_apply]
  rw [← Equiv.ulift.symm.sum_comp]
  fin_cases i <;> fin_cases j <;>
    norm_num [identityLift, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.one_apply]
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hb := @h (ULift.{u} (Fin 2)) (ULift.{v} (Fin 2))
    inferInstance inferInstance inferInstance inferInstance
    (diagonal (fun _ => ((1 / 2 : ℝ) : ℂ))) identityLift identityLift_isometry
  change matrixSubentropy (_ * _ * badAdjoint identityLift) = _ at hb
  rw [bad_embedding_zero identityLift identityLift_isometry] at hb
  have hp := uniformTwo_pos (ι := ULift.{v} (Fin 2)) (by simp)
  linarith

def family : Registration arena.{u,v} (type_of% @matrixSubentropy_isometric_embedding.{u,v}) where
  actual := realize signature.{u,v} (fun _ _ V => V.conjTranspose) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@matrixSubentropy_isometric_embedding, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrixSubentropy_isometric_embedding.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.Basic.matrixSubentropy_isometric_embedding.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.Basic.AdjointReadout.Isometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ V => V.conjTranspose) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.Basic
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Isometry
end AdjointReadout

namespace Pure
open scoped BigOperators

abbrev signature : Signature where
  Params := Σ ι : Type u, ι → ℂ
  State p := Matrix p.1 p.1 ℂ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def emptyAnchor : ∀ (e : signature.{u}.Anchor) (p : signature.{u}.Params),
    signature.{u}.State p :=
  fun e => nomatch e

def observation : ∀ (i : signature.{u}.Role) (p : signature.{u}.Params),
    signature.{u}.State p → signature.{u}.Output i p :=
  fun _ p f => f (vecMulVec p.2 (star p.2))

def actual : Realization signature.{u} :=
  realize signature observation emptyAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ p f => f (vecMulVec p.2 (star p.2)) + 1)
    emptyAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (hv : ∑ i, star (v i) * v i = 1),
    R.readout () ⟨ι, v⟩ matrixSubentropy = 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} Unit) inferInstance inferInstance (fun _ => 1) (by simp)
  change matrixSubentropy (vecMulVec (fun _ : ULift.{u} Unit => (1 : ℂ))
    (star (fun _ : ULift.{u} Unit => (1 : ℂ)))) + 1 = 0 at he
  rw [matrixSubentropy_pure _ (by simp)] at he
  norm_num at he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, fun _ => 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize, observation]

def family : Registration arena.{u} (type_of% @matrixSubentropy_pure.{u}) where
  actual := realize signature.{u} (fun _ p f => f (vecMulVec p.2 (star p.2))) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@matrixSubentropy_pure, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matrixSubentropy_pure.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Subentropy.Basic.matrixSubentropy_pure.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Subentropy.Basic.Pure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p f => f (vecMulVec p.2 (star p.2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Subentropy.Basic
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pure
end Reg.D5.S3.Quantum.Subentropy.Basic

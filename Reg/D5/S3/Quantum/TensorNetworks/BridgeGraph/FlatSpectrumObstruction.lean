import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the native scalar-Gram dimension obstruction. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

noncomputable section

def nativeM (r : Fin 3) : Matrix (Fin 1) (Fin 3) ℂ :=
  fun _ j => if r = j then 1 else 0

def nativeN (r : Fin 3) : Matrix (Fin 3) (Fin 1) ℂ :=
  fun i _ => if i = r then 1 else 0

theorem native_gram :
    (QuantumMaxFlowBound.flow nativeM nativeN)ᴴ *
      QuantumMaxFlowBound.flow nativeM nativeN = (1 : ℂ) • 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [QuantumMaxFlowBound.flow, nativeM, nativeN, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ), 0 < c → 5 * a < 2 * b →
    ∀ (lam : ℝ), 0 < lam →
      (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
        (lam : ℂ) • 1 → r.readout () () (3 * c) d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN (by norm_num) (by norm_num) 1 (by norm_num) (by simpa using native_gram)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have : ¬ ((1 : ℕ) ≤ 0) := by omega
  exact this (Eq.mp he (Nat.zero_le 0))

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.obstruction) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


namespace CommonKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => EuclideanSpace ℂ (Fin n)) (fun n => EuclideanSpace ℂ (Fin n) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ), 0 < c →
    ∀ {lam : ℂ}, lam ≠ 0 →
      (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1 →
      ∀ x : EuclideanSpace ℂ (Fin b),
        (∀ r, (M r).toEuclideanLin x = 0) → R.readout () b x 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN (by norm_num) (by norm_num) native_gram 0 (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, WithLp.toLp 2 (fun _ => (1 : ℂ)), ?_⟩
  intro h
  have he := Eq.mp (congrFun h 0) rfl
  have hn := congrArg (fun x : EuclideanSpace ℂ (Fin 1) => x 0) he
  norm_num [actual, realize, Matrix.one_apply] at hn

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.flow_common_kernel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.flow_common_kernel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.flow_common_kernel) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.flow_common_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.CommonKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CommonKernel

namespace KroneckerRank

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Matrix (Fin 3) (Fin 3) ℂ) (n : ℕ),
    R.readout () () (Matrix.kronecker H (1 : Matrix (Fin n) (Fin n) ℂ)).rank
      (n * H.rank)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  omega

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.rank_kronecker_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.rank_kronecker_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.rank_kronecker_one) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.rank_kronecker_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.KroneckerRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end KroneckerRank

namespace ConcatGram

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) (fun n => Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c d : ℕ} (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (H : Matrix (Fin 3) (Fin 3) ℂ),
    (∀ r s, (N r)ᴴ * N s = H r s • 1) →
      R.readout () c ((FlatSpectrumObstruction.concat N)ᴴ * FlatSpectrumObstruction.concat N)
        (Matrix.kronecker H (1 : Matrix (Fin c) (Fin c) ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 0) (d := 0) 0 0 (by intros; ext i; exact Fin.elim0 i)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := Eq.mp (congrFun h 0) rfl
  have hn := congrArg (fun X => X (0, 0) (0, 0)) he
  change (1 : ℂ) = 0 at hn
  exact one_ne_zero hn

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.concat_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.concat_gram, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.concat_gram) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.concat_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.ConcatGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ConcatGram

namespace StackGram

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (k : Fin c) {lam : ℂ},
    (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1 →
      R.readout () b ((FlatSpectrumObstruction.stack M)ᴴ *
        Matrix.kronecker (fun r s => ((N r)ᴴ * N s) k k)
          (1 : Matrix (Fin a) (Fin a) ℂ) * FlatSpectrumObstruction.stack M) (lam • 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 0) (b := 0) (c := 1) (d := 0) 0 0 0 (lam := 0)
    (by ext ⟨i, _⟩; exact Fin.elim0 i)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := Eq.mp (congrFun h 0) rfl
  have hn := congrArg (fun X => X 0 0) he
  change (1 : ℂ) = 0 at hn
  exact one_ne_zero hn

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.stack_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.stack_gram, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.stack_gram) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.stack_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.StackGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end StackGram

private theorem native_independent :
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (nativeM p.1)ᴴ * nativeM p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro t ht p
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A p.1 p.2) ht
  simpa [nativeM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, eq_comm] using he

namespace CrossGram

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Matrix (Fin n) (Fin n) ℂ) (fun n => Matrix (Fin n) (Fin n) ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (k : Fin c),
    LinearIndependent ℂ (fun p : Fin 3 × Fin 3 => (M p.1)ᴴ * M p.2) →
    ∀ {lam : ℂ},
      (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N = lam • 1 →
      ∀ r s, R.readout () c ((N r)ᴴ * N s) ((((N r)ᴴ * N s) k k) • 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h nativeM nativeN 0 native_independent native_gram 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro h
  have he := Eq.mp (congrFun h 0) rfl
  have hn := congrArg (fun X => X 0 0) he
  change (1 : ℂ) = 0 at hn
  exact one_ne_zero hn

def source_registration : Registration arena (type_of% @FlatSpectrumObstruction.scalar_cross_grams) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@FlatSpectrumObstruction.scalar_cross_grams, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@FlatSpectrumObstruction.scalar_cross_grams) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.scalar_cross_grams.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction.CrossGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CrossGram
end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

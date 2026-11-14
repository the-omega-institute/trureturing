import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix

noncomputable section
universe u_a u_b u_m u_n

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

namespace TwoIsometries

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u_a} {b : Type u_b} {m : Type u_m} {n : Type u_n} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ)
    (V : Matrix a m ℂ) (W : Matrix b n ℂ)
    (_hV : Vᴴ * V = 1) (_hW : Wᴴ * W = 1),
    R.readout () () (traceNorm (V * A * Wᴴ)) (traceNorm A)

private theorem rejected_law : ¬ arena.{u_a, u_b, u_m, u_n}.Law rejected := by
  intro h
  let e : ULift.{u_m} Unit ↪ ULift.{u_a} Unit :=
    ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  let f : ULift.{u_n} Unit ↪ ULift.{u_b} Unit :=
    ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩
  exact h (a := ULift.{u_a} Unit) (b := ULift.{u_b} Unit)
    (m := ULift.{u_m} Unit) (n := ULift.{u_n} Unit) 0
    (coordinateEmbedding e) (coordinateEmbedding f)
    (coordinateEmbedding_isometry e) (coordinateEmbedding_isometry f)

def source_registration : Registration arena.{u_a, u_b, u_m, u_n} (type_of% @traceNorm_two_isometries.{u_a, u_b, u_m, u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_two_isometries, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_a, u_b, u_m, u_n}.Law actual rejected rejected_law
  dependence := dependence



end TwoIsometries

namespace Reindex

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u_a} {b : Type u_b} {m : Type u_m} {n : Type u_n} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) (e : a ≃ m) (f : b ≃ n),
    R.readout () () (traceNorm (A.submatrix e f)) (traceNorm A)

private theorem rejected_law : ¬ arena.{u_a, u_b, u_m, u_n}.Law rejected := by
  intro h
  exact h (a := ULift.{u_a} Unit) (b := ULift.{u_b} Unit)
    (m := ULift.{u_m} Unit) (n := ULift.{u_n} Unit) 0
    ((Equiv.ulift : ULift.{u_a} Unit ≃ Unit).trans
      (Equiv.ulift : ULift.{u_m} Unit ≃ Unit).symm)
    ((Equiv.ulift : ULift.{u_b} Unit ≃ Unit).trans
      (Equiv.ulift : ULift.{u_n} Unit ≃ Unit).symm)

def source_registration : Registration arena.{u_a, u_b, u_m, u_n} (type_of% @traceNorm_submatrix_equiv.{u_a, u_b, u_m, u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_submatrix_equiv, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_a, u_b, u_m, u_n}.Law actual rejected rejected_law
  dependence := dependence



end Reindex

namespace Transpose

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u_n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ),
    R.readout () () (traceNorm Aᵀ) (traceNorm A)

private theorem rejected_law : ¬ arena.{u_n}.Law rejected := by
  intro h
  exact h (n := ULift.{u_n} Unit) 0

def source_registration : Registration arena.{u_n} (type_of% @traceNorm_transpose.{u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_transpose, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_n}.Law actual rejected rejected_law
  dependence := dependence



end Transpose

namespace Adjoint

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u_n} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ),
    R.readout () () (traceNorm Aᴴ) (traceNorm A)

private theorem rejected_law : ¬ arena.{u_n}.Law rejected := by
  intro h
  exact h (n := ULift.{u_n} Unit) 0

def source_registration : Registration arena.{u_n} (type_of% @traceNorm_conjTranspose.{u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_conjTranspose, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_n}.Law actual rejected rejected_law
  dependence := dependence



end Adjoint

namespace CoordinateEmbedding

abbrev matrixSignature : Signature where
  Params := Type u_m
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := matrixSignature
  Law R := ∀ {a : Type u_a} {m : Type u_m} [Fintype a] [DecidableEq a]
    [Fintype m] [DecidableEq m] (e : m ↪ a),
    R.readout () m ((coordinateEmbedding e)ᴴ * coordinateEmbedding e) 1

private theorem rejected_law : ¬ arena.{u_a, u_m}.Law rejected := by
  intro h
  exact h (a := ULift.{u_a} Unit) (m := ULift.{u_m} Unit)
    ⟨fun _ => ⟨()⟩, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem dependence : ObservationalDependence matrixSignature.{u_m} actual := by
  intro i
  refine ⟨ULift.{u_m} Unit, (0 : Matrix (ULift.{u_m} Unit) (ULift.{u_m} Unit) ℂ), 1, ?_⟩
  intro he
  have hbad : (1 : Matrix (ULift.{u_m} Unit) (ULift.{u_m} Unit) ℂ) = 0 :=
    Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena.{u_a, u_m} (type_of% @coordinateEmbedding_isometry.{u_a, u_m}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coordinateEmbedding_isometry, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence



end CoordinateEmbedding

namespace RectAdjoint

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u_m} {n : Type u_n} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ),
    R.readout () () (traceNorm Aᴴ) (traceNorm A)

private theorem rejected_law : ¬ arena.{u_m, u_n}.Law rejected := by
  intro h
  exact h (m := ULift.{u_m} Unit) (n := ULift.{u_n} Unit) 0

def source_registration : Registration arena.{u_m, u_n} (type_of% @traceNorm_conjTranspose_rect.{u_m, u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_conjTranspose_rect, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_m, u_n}.Law actual rejected rejected_law
  dependence := dependence



end RectAdjoint

end

end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance


namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
universe u_m u_n

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

namespace ScalarGram

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (c : ℝ) (_hc : 0 ≤ c)
    (_hA : Aᴴ * A = (c : ℂ) • ((c : ℂ) • (1 : Matrix n n ℂ))),
    R.readout () () (traceNorm A) (c * Fintype.card n)

private theorem rejected_law : ¬ arena.{u_m, u_n}.Law rejected := by
  intro h
  exact h (m := ULift.{u_m} Unit) (n := ULift.{u_n} Unit)
    0 0 (by norm_num) (by simp)

def source_registration : Registration arena.{u_m, u_n} (type_of% @traceNorm_of_scalar_gram.{u_m, u_n}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_of_scalar_gram, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.{u_m, u_n}.Law actual rejected rejected_law
  dependence := dependence



end ScalarGram

namespace MixedColumn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (traceNorm mixedColumn) (Real.sqrt (1 / 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def source_registration : Registration arena (type_of% @traceNorm_mixedColumn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_mixedColumn, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



end MixedColumn

namespace HalfIdentity

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (traceNorm (halfIdentity n)) (n / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def source_registration : Registration arena (type_of% @traceNorm_halfIdentity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_halfIdentity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



end HalfIdentity

namespace BellColumn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (traceNorm bellColumn) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def source_registration : Registration arena (type_of% @traceNorm_bellColumn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_bellColumn, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



end BellColumn

namespace BellOneCross

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (traceNorm bellOneCross) (2 * Real.sqrt (1 / 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def source_registration : Registration arena (type_of% @traceNorm_bellOneCross) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_bellOneCross, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



end BellOneCross

namespace BellSquare

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (traceNorm bellSquare) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

def source_registration : Registration arena (type_of% @traceNorm_bellSquare) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_bellSquare, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



end BellSquare

end

end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms


namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (R : Fin 2 × Fin 2 → m) (C : Fin 2 × Fin 2 → n)
    (rk rb ck cb : Bool), (rk = true ∨ ck = true) → (rb = true ∨ cb = true) →
    (∀ x y, R x = R y ↔ (rk = true → x.1 = y.1) ∧ (rb = true → x.2 = y.2)) →
    (∀ x y, C x = C y ↔ (ck = true → x.1 = y.1) ∧ (cb = true → x.2 = y.2)) →
    O.readout () () (traceNorm (fourEntries R C))
      (bellValue ((if rk && ck then 1 else 0) + (if rb && cb then 1 else 0)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h (Fin 2 × Fin 2) (Fin 2 × Fin 2) _ _ _ _ id id
    true true true true (Or.inl rfl) (Or.inl rfl)
    (fun x y => by simp [Prod.ext_iff]) (fun x y => by simp [Prod.ext_iff])

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @traceNorm_fourEntries) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_fourEntries, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence



abbrev countSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law O := ∀ {a b : ℕ}, a ≤ 2 → b ≤ 2 → bellValue a = bellValue b → O.readout () () a b

private theorem count_rejected_law : ¬ countArena.Law countRejected := by
  intro h
  exact @h 0 0 (by omega) (by omega) rfl

private theorem count_dependence : ObservationalDependence countSignature countActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

def count_source_registration : Registration countArena (type_of% @bellValue_injective) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@bellValue_injective, countRejected, count_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity countArena.Law countActual countRejected
    count_rejected_law
  dependence := count_dependence



#print axioms source_registration
#print axioms count_source_registration

namespace EmbeddedSingle

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Type × Type)
    (fun p => Matrix p.1 p.2 ℂ) (fun p => Matrix p.1 p.2 ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {a b m n : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ↪ a) (f : n ↪ b) (i : m) (j : n) (c : ℂ),
    O.readout () (a, b)
      (coordinateEmbedding e * Matrix.single i j c *
        (coordinateEmbedding f)ᴴ)
      (Matrix.single (e i) (f j) c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h Unit Unit Unit Unit _ _ _ _ _ _ _ _
    (Equiv.refl Unit).toEmbedding (Equiv.refl Unit).toEmbedding () () 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(Unit, Unit), (0 : Matrix Unit Unit ℂ), 1, ?_⟩
  intro he
  have hbad : (1 : Matrix Unit Unit ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  have hc := congrArg (fun M : Matrix Unit Unit ℂ => M () ()) hbad
  norm_num at hc

def source_registration : Registration arena (type_of% @embedded_single) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@embedded_single, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence



#print axioms source_registration

end EmbeddedSingle

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

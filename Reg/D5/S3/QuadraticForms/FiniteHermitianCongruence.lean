import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuadraticForms.FiniteHermitianCongruence
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ULift

namespace Reg.D5.S3.QuadraticForms.FiniteHermitianCongruence

open _root_.D5.S3.QuadraticForms.FiniteHermitianCongruence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

structure Parameter where
  K : Type u
  field : Field K
  finite : Finite K
  sigma : K ≃+* K
  N : ℕ
  B : Matrix (Fin N) (Fin N) K

attribute [instance] Parameter.field Parameter.finite

def signature : Signature where
  Params := Parameter.{u}
  State p := Matrix (Fin p.N) (Fin p.N) p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.N) (Fin p.N) p.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (p : Parameter.{u}) (T : Matrix (Fin p.N) (Fin p.N) p.K) =>
      T.transpose * p.B * T.map p.sigma)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (p : Parameter.{u}) _ =>
    (0 : Matrix (Fin p.N) (Fin p.N) p.K)) (fun e => nomatch e)

/-- The original telescope with only its congruence readout replaced. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [f : Field K] [q : Finite K]
    (sigma : K ≃+* K) (_hinv : Function.Involutive sigma)
    (_hne : sigma ≠ RingEquiv.refl K) (N : ℕ)
    (B : Matrix (Fin N) (Fin N) K)
    (_hB : (B.map sigma).transpose = B),
    ∃ T : Matrix (Fin N) (Fin N) K, IsUnit T ∧
      R.readout () ⟨K, f, q, sigma, N, B⟩ T =
        Matrix.diagonal (fun i : Fin N => if i.val < B.rank then 1 else 0)

def registration : Registration arena
    (∀ {K : Type u} [Field K] [Finite K]
      (sigma : K ≃+* K) (hinv : Function.Involutive sigma)
      (hne : sigma ≠ RingEquiv.refl K) (N : ℕ)
      (B : Matrix (Fin N) (Fin N) K)
      (hB : (B.map sigma).transpose = B),
      ∃ T : Matrix (Fin N) (Fin N) K, IsUnit T ∧
        T.transpose * B * T.map sigma =
          Matrix.diagonal (fun i : Fin N => if i.val < B.rank then 1 else 0)) := by
  classical
  have hbad : ¬ arena.Law (rejected : Realization signature.{u}) := by
    intro h
    let F := ULift.{u} (GaloisField 2 2)
    let g := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F
    have hord : orderOf g = 2 := by
      change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) = 2
      rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
        finrank_ulift, GaloisField.finrank 2 (by decide)]
    have hg : g ^ 2 = 1 := by simpa only [hord] using pow_orderOf_eq_one g
    have hi : Function.Involutive g.toRingEquiv := by
      intro x
      have hx := DFunLike.congr_fun hg x
      simpa [AlgEquiv.coe_pow, Function.iterate_succ_apply'] using hx
    have hn : g.toRingEquiv ≠ RingEquiv.refl F := by
      intro he
      have he' : g = 1 := by
        apply AlgEquiv.ext
        intro x
        exact DFunLike.congr_fun he x
      rw [he', orderOf_one] at hord
      omega
    obtain ⟨T, _, ht⟩ := h g.toRingEquiv hi hn 1 1 (by simp)
    have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) F => M 0 0) ht
    simpa [rejected, realize, Matrix.diagonal_apply, Matrix.rank_one] using hh
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨finite_hermitian_congruence, rejected, hbad⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hbad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  · intro i
    let p : Parameter.{u} := ⟨ULift.{u} (ZMod 2), inferInstance, inferInstance,
      RingEquiv.refl _, 1, 1⟩
    refine ⟨p, (0 : Matrix (Fin 1) (Fin 1) p.K),
      (1 : Matrix (Fin 1) (Fin 1) p.K), ?_⟩
    change (0 : Matrix (Fin 1) (Fin 1) p.K).transpose * p.B *
      (0 : Matrix (Fin 1) (Fin 1) p.K).map p.sigma ≠
      (1 : Matrix (Fin 1) (Fin 1) p.K).transpose * p.B *
        (1 : Matrix (Fin 1) (Fin 1) p.K).map p.sigma
    simp [p]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.QuadraticForms.FiniteHermitianCongruence.finite_hermitian_congruence.{u})
    (type_of% (realize signature.{u}
      (fun (_ : Unit) (p : Parameter.{u}) (T : Matrix (Fin p.N) (Fin p.N) p.K) =>
      T.transpose * p.B * T.map p.sigma) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.QuadraticForms.FiniteHermitianCongruence.finite_hermitian_congruence.__information_unit,
  realizationName := `Reg.D5.S3.QuadraticForms.FiniteHermitianCongruence.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u}
    (fun (_ : Unit) (p : Parameter.{u}) (T : Matrix (Fin p.N) (Fin p.N) p.K) =>
      T.transpose * p.B * T.map p.sigma) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.QuadraticForms.FiniteHermitianCongruence
    definition := none
    coordinates := #[0, 1, 2, 3, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.QuadraticForms.FiniteHermitianCongruence

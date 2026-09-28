import D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open _root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
universe u v w

@[reducible] def matrixSignature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ d := Matrix d d ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence matrixSignature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (ULift.up 0)) (ULift.up 0)
  exact zero_ne_one hentry



-- Entry calculations for the independently lifted singleton countermodels.
private theorem const_mul {a b c : Type*} [Fintype b] [Unique b] (x y : ℂ) :
    Matrix.of (fun (_ : a) (_ : b) => x) * Matrix.of (fun (_ : b) (_ : c) => y) =
      ((fun _ _ => x * y) : Matrix a c ℂ) := by
  ext i j
  change (∑ _ : b, x * y) = x * y
  simp

private theorem const_star {a b : Type*} (x : ℂ) :
    (fun (_ : a) (_ : b) => x)ᴴ = fun _ _ => star x := rfl

private theorem const_smul {a b : Type*} (x y : ℂ) :
    x • ((fun _ _ => y) : Matrix a b ℂ) = fun _ _ => x * y := rfl

private theorem zero_entries {a b : Type*} :
    (0 : Matrix a b ℂ) = fun _ _ => 0 := rfl

private theorem one_entries {a : Type*} [DecidableEq a] [Subsingleton a] :
    (1 : Matrix a a ℂ) = fun _ _ => 1 := by
  ext i j
  change (if i = j then (1 : ℂ) else 0) = 1
  simp [Subsingleton.elim i j]

private theorem const_sub {a b : Type*} (x y : ℂ) :
    ((fun _ _ => x) : Matrix a b ℂ) - (fun _ _ => y) = fun _ _ => x - y := rfl

private theorem const_add {a b : Type*} (x y : ℂ) :
    ((fun _ _ => x) : Matrix a b ℂ) + (fun _ _ => y) = fun _ _ => x + y := rfl

@[reducible] def familySignature : Signature where
  Params := (s : Type u) × Type w
  State p := p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def familyActual : Realization familySignature.{u,w} :=
  realize familySignature (fun _ _ x => x) (fun e => nomatch e)

def familyRejected : Realization familySignature.{u,w} :=
  realize familySignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem familyDependence : ObservationalDependence familySignature.{u,w} familyActual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 1), ULift.{w} (Fin 1)⟩,
    (fun _ _ _ => 0), (fun _ _ _ => 1), ?_⟩
  intro h
  have hentry := congrFun (congrFun (congrFun h (ULift.up 0)) (ULift.up 0)) (ULift.up 0)
  exact zero_ne_one hentry

run_cmd do
  let root := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
  let rows ← (#[(`DecodingSyndromeBlock.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.decoding_syndrome_block), (`OrthogonalSyndromeRecovery.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.orthogonal_syndrome_recovery), (`SyndromeTransportOrthogonal.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.syndrome_transport_orthogonal) ]).mapM fun (arena, target) => do
    pure {
      objectArenaName := root ++ arena
      theoremName := target
      statementIdentity := LeanInformationAudit.theoremStatementIdentity (← Lean.getEnv) target
      registrationModuleName := root : LeanInformationAudit.SnapshotOccurrence }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := rows, source := rows, companionPrefix := some root }

namespace DecodingSyndromeBlock

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (rho : Matrix d d ℂ) (j k : s),
    syndromeDecoding S (S j * rho * (S k)ᴴ) =
      if j = k then r.readout () d rho else 0

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ S hS rho j k
  exact decoding_syndrome_block.{u,v,w} S hS rho j k

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1) (ULift.up 0) (ULift.up 0)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, syndromeEncoding,
    syndromeDecoding, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem decoding_syndrome_block in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

#print axioms registration
end DecodingSyndromeBlock

namespace OrthogonalSyndromeRecovery

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S)
    (sigma : Matrix s s ℂ) (rho : Matrix d d ℂ),
    syndromeDecoding S (syndromeEncoding S sigma rho) =
      Matrix.trace sigma • r.readout () d rho

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ S hS sigma rho
  exact orthogonal_syndrome_recovery.{u,v,w} S hS sigma rho

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1) (fun _ _ => 1)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, syndromeEncoding,
    syndromeDecoding, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem orthogonal_syndrome_recovery in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration
end OrthogonalSyndromeRecovery

namespace SyndromeTransportOrthogonal

def arena : Arena where
  signature := familySignature.{u,w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (V : s → Matrix d d ℂ)
    (hV : ∀ i, (V i)ᴴ * V i = 1),
    OrthogonalSyndromes (fun i => S i * r.readout () ⟨s, d⟩ V i)

theorem actual_law : arena.{u,v,w}.Law familyActual := by
  intro s n d _ _ _ _ _ S hS V hV
  exact syndrome_transport_orthogonal.{u,v,w} S hS V hV

theorem rejected_law : ¬ arena.{u,v,w}.Law familyRejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  let V : ULift.{u} (Fin 1) → Matrix (ULift.{w} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ => 1
  have hV : ∀ i, (V i)ᴴ * V i = 1 := by intro i; simp [V]
  have he := h S hS V hV (ULift.up 0) (ULift.up 0)
  change ((S (ULift.up 0) * (0 : Matrix (ULift.{w} (Fin 1)) (ULift.{w} (Fin 1)) ℂ))ᴴ *
    (S (ULift.up 0) * 0)) = (if (ULift.up 0 : ULift.{u} (Fin 1)) = ULift.up 0 then 1 else 0) at he
  rw [Matrix.mul_zero, Matrix.conjTranspose_zero, Matrix.zero_mul, if_pos rfl] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  change (0 : ℂ) = (if (ULift.up 0 : ULift.{w} (Fin 1)) = ULift.up 0 then 1 else 0) at hentry
  rw [if_pos rfl] at hentry
  exact zero_ne_one hentry

def registration : Registration arena.{u,v,w} (arena.Law familyActual) where
  actual := familyActual
  bridge := Iff.rfl
  variation := ⟨actual_law, familyRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨familyRejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := familyDependence

set_option trace.InformationRegistration.check true in
register_information_theorem syndrome_transport_orthogonal in arena
  readout via (realize familySignature.{u,w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn"]
      stateBinder := 10 }] })
  escape continues (open)

#print axioms registration
end SyndromeTransportOrthogonal

run_cmd LeanInformationAudit.validateRegistrySnapshot (← Lean.getEnv)

end Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding

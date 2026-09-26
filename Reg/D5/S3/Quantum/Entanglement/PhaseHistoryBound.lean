import D5.S3.Quantum.Entanglement.PhaseHistoryBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound
open _root_.D5.S3.Quantum.Entanglement.PhaseHistoryBound
open _root_.D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder
noncomputable section
universe u

namespace Moments
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (n t : ℕ) → Matrix (Path n) Bit ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ), 0 < p → p < 1 → ∀ (φ : ℕ → ℝ),
    ∃ U : ℕ → Unitary (Bit × Bit),
      (∀ t i j k, U t (basis (false, i)) (j,k) = step p (φ t) (j,k) i) ∧
      (∀ n t i x, circuit U n t (blankState false n i) (register n x) =
        R.readout () p φ n t x i) ∧
      (∀ n t i x, ‖R.readout () p φ n t x i‖^2 =
        if head n x = i then pathMass p n x else 0) ∧
      (∀ n i, expectation p n i (fun _ => 1) = 1) ∧
      (∀ n i s, s ≤ n → expectation p n i (fun x => observed n x s) = mean p i s) ∧
      (∀ n i s t, s ≤ t → t ≤ n →
        expectation p n i (fun x => observed n x s * observed n x t) -
          mean p i s * mean p i t =
          (-p)^(t-s) * mean p i s * (1-mean p i s))

def actual : Realization signature :=
  realize signature (fun _ p φ => source p φ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, _, _, hb, _⟩ := h (1/2) (by norm_num) (by norm_num) (fun _ => 0)
  have hf := hb 0 0 false false
  norm_num [rejected, realize, head, pathMass] at hf

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_source_moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1/2 : ℝ), (fun _ => 0), (fun _ => Real.pi), ?_⟩
    intro h
    have he := congrArg (fun f => f 1 0 (true, false) true) h
    norm_num [actual, realize, source, head, pathAmplitude, bit, memory,
      mul_comm Complex.I, Complex.exp_pi_mul_I] at he
end Moments

namespace Bound
abbrev signature : Signature where
  Params := (_ : ℝ) × ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ), 0 < p → p < 1 → ∀ (n : ℕ) (θ : ℝ) (φ δ : ℕ → ℝ),
    (∀ t < n, ∃ k : ℤ, θ - φ t = δ t + k * (2 * Real.pi)) →
    ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix Bit Bit ℂ) -
      (error p θ φ n (R.readout () ⟨p,n⟩ δ)).conjTranspose *
        error p θ φ n (R.readout () ⟨p,n⟩ δ)).PosSemidef ∧
    ∀ (J : Type u) [Fintype J] [DecidableEq J],
      ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix (J × Bit) (J × Bit) ℂ) -
        (Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (R.readout () ⟨p,n⟩ δ))).conjTranspose *
        Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (R.readout () ⟨p,n⟩ δ))).PosSemidef

def actual : Realization signature :=
  realize signature (fun _ p δ => center p.1 δ p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Real.pi) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (1/2) (by norm_num) (by norm_num) 0 0 (fun _ => 0) (fun _ => 0)
    (by intro t ht; omega)).1
  have hd := hh.diag_nonneg (i := false)
  norm_num [rejected, realize, error, source, head, pathAmplitude, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_bool, mul_comm Complex.I,
    Complex.exp_pi_mul_I] at hd

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phase_history_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(1/2 : ℝ), 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change center (1/2) (fun _ => 0) 1 ≠ center (1/2) (fun _ => 1) 1
    norm_num [center]
end Bound

register_information_theorem actual_source_moments in Moments.arena
  readout via (realize Moments.signature (fun _ p φ => source p φ) (fun e => nomatch e))
  realizes Moments.registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg",
        "fn", "arg", "body", "body", "body", "body", "arg",
        "fn", "fn", "fn", "fn"], stateBinder := 3 }] })
  escape continues (open)

#print axioms Moments.registration

register_information_theorem phase_history_bound in Bound.arena
  readout via (realize Bound.signature (fun _ p δ => center p.1 δ p.2) (fun e => nomatch e))
  realizes Bound.registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound
    coordinates := #[0, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "arg", "fn", "arg",
        "arg", "arg"], stateBinder := 6 }] })
  escape continues (open)

#print axioms Bound.registration

end
end Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound

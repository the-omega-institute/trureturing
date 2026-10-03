import D5.S3.Quantum.Transport.FibonacciPrefix
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Transport.FibonacciPrefix
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix Kronecker
noncomputable section
namespace Reg.D5.S3.Quantum.Transport.FibonacciPrefix

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := (ZMod d × ZMod d) ≃ (ZMod d × ZMod d)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d t => lowTrajectory d t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Equiv.refl _) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (d e : ℕ) [NeZero d] [NeZero e] (_ : 2 ≤ d) (_ : 2 ≤ e),
    (∀ N (a b : ZMod d × ZMod d), carryPrefix d N a = carryPrefix d N b →
      ∀ j ≤ N, integerTrajectory d j a - integerTrajectory d j b =
        phi ^ j * (integerTrajectory d 0 a - integerTrajectory d 0 b)) ∧
    (∀ N (a b : ZMod d × ZMod d), 1 ≤ N → a ≠ b →
      carryPrefix d N a = carryPrefix d N b →
      Real.goldenRatio ^ N ≤ Real.goldenRatio ^ 3 * ((d : ℝ) - 1) ^ 2) ∧
    (∀ P, 1 ≤ P → (∀ a, r.readout () d P a = a) →
      Function.Injective (carryPrefix d P)) ∧
    (∀ N : ℕ, 3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1) < (N : ℝ) →
      Function.Injective (carryPrefix d N)) ∧
    (∀ a b : ZMod d × ZMod d,
      (∀ j, carryHistory d a j = carryHistory d b j) → a = b) ∧
    (prefixThreshold d : ℤ) = ⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋ + 1 ∧
    (∀ N, prefixThreshold d ≤ N → Function.Injective (carryPrefix d N)) ∧
    prefixThreshold 2 = 4 ∧
    (∀ t (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      movingPullback d e t B =
        (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t)ᴴ *
          (((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t * B *
            ((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t)ᴴ) ⊗ₖ
              (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
          D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N ↔
        ∀ a b, carryPrefix d N a ≠ carryPrefix d N b → B a b = 0) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N → ∀ t, 1 ≤ t → t ≤ N →
        movingPullback d e t B = D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B) ∧
    Antitone (prefixAlgebra d e) ∧
    (⨅ N : ℕ, ⨅ (_ : 1 ≤ N), prefixAlgebra d e N) = diagonalAlgebra d ∧
    (∀ P, 1 ≤ P → (∀ a, lowTrajectory d P a = a) →
      prefixAlgebra d e P = diagonalAlgebra d) ∧
    (∀ N, prefixThreshold d ≤ N → prefixAlgebra d e N = diagonalAlgebra d)

theorem actual_law : arena.Law actual := by
  intro d e _ _ hd he
  exact fibonacci_prefix_transport d e hd he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h 2 2 (by norm_num) (by norm_num)).2.2.1
    1 (by norm_num) (by intro a; rfl)
  have heq : carryPrefix 2 1 ((0,0) : ZMod 2 × ZMod 2) =
      carryPrefix 2 1 ((1,0) : ZMod 2 × ZMod 2) := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    norm_num [carryPrefix, carryHistory, lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci,
      ZMod.val_one_eq_one_mod]
  have hx := congrArg Prod.fst (hi heq)
  exact zero_ne_one hx

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    change lowTrajectory 2 0 = lowTrajectory 2 1 at h
    have hx := congrArg (fun q : (ZMod 2 × ZMod 2) ≃ (ZMod 2 × ZMod 2) =>
      (q ((1,0) : ZMod 2 × ZMod 2)).1) h
    norm_num [lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci] at hx

register_information_theorem fibonacci_prefix_transport in arena
  readout via (realize signature (fun _ d t => lowTrajectory d t) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Transport.FibonacciPrefix
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "body", "body", "domain", "body", "fn", "arg", "fn"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Quantum.Transport.FibonacciPrefix

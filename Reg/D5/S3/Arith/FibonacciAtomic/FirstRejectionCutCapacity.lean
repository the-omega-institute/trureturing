import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

open _root_.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity

abbrev signature : Signature where
  Params := Σ k : ℕ, Finset (Fin (k+1))
  State p := Word p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Label p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => task w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (A : Finset (Fin (k+1))),
    (∀ P : Profile k A, code A (representative P) = encode P) ∧
    (∀ a : Side k A, ∃ P : Profile k A, code A a = encode P) ∧
    (∀ a a' : Side k A,
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k+1) => Window)
        (R.readout () ⟨k,A⟩) (fun r => r ∈ A) a =
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k+1) => Window)
        (R.readout () ⟨k,A⟩) (fun r => r ∈ A) a' ↔ code A a = code A a') ∧
    delta A ≤ d A ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k+1) => Window)
      (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2 ^ d A + (∑ j ∈ internals A, 2 ^ c A j) +
        (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) ∧
    (∀ w : Word k, boolean w = decide ((R.readout () ⟨k,A⟩) w = ⊤)) ∧
    (∀ a : Side k A,
      (∀ b, boolean (merge A a b) = false) ↔ closed A a ≠ ⊤) ∧
    (∀ a a' : Side k A,
      (∀ b, boolean (merge A a b) = boolean (merge A a' b)) ↔
        (closed A a ≠ ⊤ ∧ closed A a' ≠ ⊤) ∨
        (closed A a = ⊤ ∧ closed A a' = ⊤ ∧ ∀ i, Cross A i → port A a i = port A a' i)) ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k+1) => Window)
      boolean (fun r => r ∈ A) = 2 ^ d A + epsilon A ∧
    (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 1) ∧
    (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = k+2) ∧
    (∀ m : ℕ, 1 ≤ m → m < k+1 → A = interval k 0 m →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = m+1) ∧
    (1 ≤ k → A = {Fin.last k} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 3) ∧
    (∀ l : ℕ, 0 < l → l < k → A = interval k l (k+1) →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(k+1-l)+2) ∧
    (∀ l r : ℕ, 0 < l → l < r → r < k+1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (A = {(0 : Fin (k+1))} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2) ∧
    (∀ i : Fin (k+1), 0 < i.val → i.val < k → A = {i} →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 4) ∧
    (∀ l r : ℕ, 0 < l → l+1 < r → r ≤ k+1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (k = 0 → (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 1) ∧
      (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2)) ∧
    (1 ≤ k →
      List.ofFn (x k) = .high :: .low :: List.replicate (k-1) .middle ∧
      List.ofFn (y k) = List.replicate k .middle ++ [.zero] ∧
      boolean (x k) = false ∧ boolean (y k) = false ∧
      (R.readout () ⟨k,A⟩) (x k) = ((0 : Fin (k+1)) : Label k) ∧
      (R.readout () ⟨k,A⟩) (y k) = (Fin.last k : Label k) ∧
      ¬ ∃ post : Bool → Label k, ∀ w : Word k, post (boolean w) = (R.readout () ⟨k,A⟩) w)

theorem actual_law : arena.Law actual := by
  intro k A
  exact result k A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0 ∅).2.2.2.2.2.1 (fun _ => Window.zero)
  change false = decide ((⊤ : Label 0) = ⊤) at bad
  simp at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,∅⟩, (fun _ => Window.zero), (fun _ => Window.middle), ?_⟩
    change task (fun _ : Fin 1 => Window.zero) ≠ task (fun _ : Fin 1 => Window.middle)
    simp [task,bad]

register_information_theorem result in arena
  readout via (realize signature (fun _ _ w => task w) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","arg","arg","fn","arg","body","body","fn","arg","fn","arg","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity

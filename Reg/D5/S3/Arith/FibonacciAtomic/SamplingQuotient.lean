import D5.S3.Arith.FibonacciAtomic.SamplingQuotient
import Reg.Support.DependentFamily

open Matrix
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.Arith.FibonacciAtomic.SamplingQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient

@[reducible] def signature : Signature where
  Params := Σ _n : ℕ, Σ m : ℕ, Fin m → ℕ
  State p := ZMod p.1 × ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2.1 → ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x i => readout p.1 (p.2.2 i) x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (t : Fin m → ℕ) (ht : StrictMono t),
    let M (N : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod N) := !![0, 1; 1, 1]
    let S (N : ℕ) : ZMod N × ZMod N → ZMod N × ZMod N :=
      fun x => (x.2, x.1 + x.2)
    let i0 : Fin m := ⟨0, by omega⟩
    let s := t i0
    let g := (Finset.univ.erase i0).gcd (fun i => t i - s)
    let O := R.readout () ⟨n, m, t⟩
    (∀ x j, readout n (s + (j + 2) * g) x =
      (M n ^ g).trace * readout n (s + (j + 1) * g) x -
        (-1 : ZMod n) ^ g * readout n (s + j * g) x) ∧
    (∀ z, (O z = 0 ↔ readout n s z = 0 ∧ readout n (s + g) z = 0) ∧
      (O z = 0 ↔ ((S n)^[s] z).2 = 0 ∧
        (Nat.fib g : ZMod n) * ((S n)^[s] z).1 = 0)) ∧
    (∀ x y, O x = O y ↔
      ∀ j : ℕ, readout n (s + j * g) x = readout n (s + j * g) y) ∧
    (∀ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
      (∀ x, O (S n x) = Φ (O x)) → ∀ z, O z = 0 → O (S n z) = 0) ∧
    Function.Injective (fun x => (readout n s x, readout n (s + 1) x)) ∧
    (!![(Nat.fib s : ZMod n), Nat.fib (s + 1);
      Nat.fib (s + 1), Nat.fib (s + 2)] : Matrix (Fin 2) (Fin 2) (ZMod n)).det =
        (-1 : ZMod n) ^ (s + 1) ∧
    ((∃ z, z ≠ 0 ∧ O z = 0) →
      ¬ ∃ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
        ∀ x, O (S n x) = Φ (O x)) ∧
    (M 3 ^ 4 = (2 : ZMod 3) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3), readout 3 (4 * j) x = 2 ^ j * x.2) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3),
      readout 3 (8 * j) x = x.2 ∧ readout 3 (8 * j + 4) x = 2 * x.2) ∧
    (∀ j : ℕ, readout 3 (4 * j) (0, 0) = readout 3 (4 * j) (1, 0)) ∧
    readout 3 1 (0, 0) = 0 ∧ readout 3 1 (1, 0) = 1 ∧
    (0 : ZMod 3) ≠ 1 ∧
    (let O4 := fun x : ZMod 3 × ZMod 3 => ![readout 3 0 x, readout 3 4 x]
     (∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) ∧
     (¬ ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 (S 3 x) = Φ (O4 x)) ∧
     ¬ ((∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) →
        ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 (S 3 x) = Φ (O4 x)))

theorem actual_law : arena.Law actual := sampling_quotient

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : StrictMono (fun i : Fin 2 => i.val) := fun _ _ h => h
  have bad := ((h 2 2 (by omega) (by omega) (fun i => i.val) ht).2.1
    (1, 0)).1.mp rfl
  have hb := bad.2
  have he : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  norm_num [readout, he] at hb

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 2, fun j => j.val⟩, (0, 0), (1, 0), ?_⟩
    cases i
    decide

register_information_theorem sampling_quotient in arena
  readout via (realize signature
    (fun _ p x i => readout p.1 (p.2.2 i) x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "value"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient

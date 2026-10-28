/- GID: D5/S0/Computability/BinaryMachine/StackPower
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite stack multiplication produces exact polynomial unary witness budgets. -/

import Mathlib.Tactic.Ring
import D5.S0.Computability.BinaryMachine.StackControl
import D5.S0.Computability.BinaryMachine.PolynomialBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.StackPower
open StackMachine (Registers)
open StackProgram

/-- Registers 2 and 3 hold unary base and accumulator. The three work registers
4, 5 and 6 are empty at each interface. Registers 0 and 1 form a preserved frame. -/
def addBase := seq (StackWords.copy (k := 6) 2 4 6) (StackWords.transfer (k := 6) 4 5)
def addEncoding := StackWords.copyMapEncoding.sum (Encoding.fin 3)
def multiply := seq (whileCounter (k := 6) 3 addBase) (StackControl.moveWord (k := 6) 5 3 6)
def multiplyEncoding := (Encoding.bool.sum addEncoding).sum StackControl.moveEncoding

private theorem exec_addBase (r : Registers 6) (n : Nat)
    (hb : r 2 = List.replicate n true) (h₄ : r 4 = []) (h₆ : r 6 = []) :
    Exec addBase addBase.start r (7 * n + 8)
      (true, StackMachine.set r 5 (List.replicate n true ++ r 5)) := by
  let r₁ := StackMachine.set r 4 (r 2)
  have hc := StackWords.exec_copy (k := 6) 2 4 6 (by decide) (by decide) (by decide) r h₆
  have ht := StackWords.exec_transfer (k := 6) 4 5 (by decide) r₁
  have hh := exec_seq _ _ hc ht
  have ho : StackMachine.set (StackMachine.set r₁ 4 []) 5 ((r₁ 4).reverse ++ r₁ 5) =
      StackMachine.set r 5 (List.replicate n true ++ r 5) := by
    funext a
    by_cases h₅ : a = 5
    · subst a; simp [r₁, hb]
    · by_cases h : a = 4
      · subst a; simp [h₄]
      · simp [r₁, StackMachine.set, h₅, h]
  rw [ho] at hh
  have htme : (r 4).length + 5 * (r 2).length + 6 + (2 * (r₁ 4).length + 2) = 7 * n + 8 := by
    simp [r₁, hb, h₄]; omega
  rw [htme] at hh
  exact hh

private theorem exec_loop (count n : Nat) (r : Registers 6)
    (hc : r 3 = List.replicate count true) (hb : r 2 = List.replicate n true)
    (h₄ : r 4 = []) (h₆ : r 6 = []) :
    Exec (whileCounter (k := 6) 3 addBase) (whileCounter (k := 6) 3 addBase).start r
      (count * (7 * n + 9) + 2)
      (true, StackMachine.set (StackMachine.set r 3 []) 5
        (List.replicate (count * n) true ++ r 5)) := by
  induction count generalizing r with
  | zero =>
    have he := exec_whileCounter_done (k := 6) 3 addBase r (by simpa using hc)
    have ho : StackMachine.set (StackMachine.set r 3 []) 5 (r 5) = r := by
      funext a
      by_cases h₅ : a = 5
      · subst a; simp
      · by_cases h₃ : a = 3
        · subst a; simp [h₅, hc]
        · simp [StackMachine.set, h₅, h₃]
    simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append]
    rw [ho]
    exact he
  | succ count ih =>
    let r₀ := StackMachine.set r 3 (List.replicate count true)
    let r₁ := StackMachine.set r₀ 5 (List.replicate n true ++ r₀ 5)
    have he := exec_addBase r₀ n (by simpa [r₀] using hb)
      (by simpa [r₀] using h₄) (by simpa [r₀] using h₆)
    have hr := ih r₁ (by simp [r₁, r₀]) (by simpa [r₁, r₀] using hb)
      (by simpa [r₁, r₀] using h₄) (by simpa [r₁, r₀] using h₆)
    have hh := exec_whileCounter_next (k := 6) 3 addBase
      (by simpa [List.replicate_succ] using hc) he hr
    have ho : StackMachine.set (StackMachine.set r₁ 3 []) 5 (List.replicate (count * n) true ++ r₁ 5) =
        StackMachine.set (StackMachine.set r 3 []) 5 (List.replicate ((count + 1) * n) true ++ r 5) := by
      funext a
      by_cases h₅ : a = 5
      · subst a
        simp [r₁, r₀, Nat.add_mul, ← List.append_assoc, List.replicate_append_replicate]
      · by_cases h₃ : a = 3
        · subst a; simp
        · simp [r₁, r₀, StackMachine.set, h₅, h₃]
    rw [ho] at hh
    have htme : 7 * n + 8 + (count * (7 * n + 9) + 2) + 1 = (count + 1) * (7 * n + 9) + 2 := by
      simp only [Nat.add_mul, Nat.one_mul]; omega
    rw [htme] at hh
    exact hh

/-- Actual multiplication of two unary counts preserves all frame words and
empties its work registers, including when either count is zero. -/
theorem exec_multiply (r : Registers 6) (count n : Nat)
    (hc : r 3 = List.replicate count true) (hb : r 2 = List.replicate n true)
    (h₄ : r 4 = []) (h₅ : r 5 = []) (h₆ : r 6 = []) :
    Exec multiply multiply.start r (count * (11 * n + 9) + 8)
      (true, StackMachine.set r 3 (List.replicate (count * n) true)) := by
  let r₁ := StackMachine.set (StackMachine.set r 3 []) 5 (List.replicate (count * n) true ++ r 5)
  have hl := exec_loop count n r hc hb h₄ h₆
  have hm := StackControl.exec_moveWord (k := 6) 5 3 6 (by decide) (by decide) (by decide) r₁
    (by simp [r₁, h₆])
  have hh := exec_seq _ _ hl hm
  have ho : StackMachine.set (StackMachine.set r₁ 5 []) 3 (r₁ 5) =
      StackMachine.set r 3 (List.replicate (count * n) true) := by
    funext a
    by_cases h₃ : a = 3
    · subst a; simp [r₁, h₅]
    · by_cases h : a = 5
      · subst a; simp [h₅]
      · simp [r₁, StackMachine.set, h₃, h]
  rw [ho] at hh
  have htme : count * (7 * n + 9) + 2 + ((r₁ 3).length + 4 * (r₁ 5).length + 6) =
      count * (11 * n + 9) + 8 := by
    simp [r₁, h₅]
    ring
  rw [htme] at hh
  exact hh

def Label (c : Nat) : Nat → Type
  | 0 => StackControl.WriteLabel (List.replicate c true)
  | e + 1 => Sum (Label c e) (Sum (Sum Bool (Sum (Sum Bool (Sum (Fin 4) (Fin 6))) (Fin 4)))
      (Sum Bool (Sum (Fin 4) (Fin 4))))

def power (c : Nat) : (e : Nat) → Program 6 (Label c e)
  | 0 => StackControl.write 3 (List.replicate c true)
  | e + 1 => seq (power c e) multiply

def encoding (c : Nat) : (e : Nat) → Encoding (Label c e)
  | 0 => StackControl.writeEncoding (List.replicate c true)
  | e + 1 => (encoding c e).sum multiplyEncoding

def time (c : Nat) : Nat → Nat → Nat
  | 0, _ => 2 * c + 1
  | e + 1, n => time c e n + c * n ^ e * (11 * n + 9) + 8

/-- A fixed coefficient and exponent compute their exact unary polynomial
budget through counted instructions, with all temporary registers restored. -/
theorem exec_power (c e n : Nat) (r : Registers 6)
    (hb : r 2 = List.replicate n true) (h₃ : r 3 = [])
    (h₄ : r 4 = []) (h₅ : r 5 = []) (h₆ : r 6 = []) :
    Exec (power c e) (power c e).start r (time c e n)
      (true, StackMachine.set r 3 (List.replicate (c * n ^ e) true)) := by
  induction e with
  | zero => simpa [power, time, h₃] using StackControl.exec_write (k := 6) 3 (List.replicate c true) r
  | succ e ih =>
    let r₁ := StackMachine.set r 3 (List.replicate (c * n ^ e) true)
    have hm := exec_multiply r₁ (c * n ^ e) n (by simp [r₁])
      (by simpa [r₁] using hb) (by simpa [r₁] using h₄)
      (by simpa [r₁] using h₅) (by simpa [r₁] using h₆)
    have hh := exec_seq _ _ ih hm
    have ho : StackMachine.set r₁ 3 (List.replicate (c * n ^ e * n) true) =
        StackMachine.set r 3 (List.replicate (c * n ^ (e + 1)) true) := by
      funext a
      by_cases h : a = 3 <;> simp [r₁, StackMachine.set, h, Nat.pow_succ, Nat.mul_assoc]
    rw [ho] at hh
    exact hh

/-- The actual unary-budget runtime has a numerical polynomial upper bound. -/
theorem polynomialBound_time (c e : Nat) : PolynomialBound (time c e) := by
  induction e with
  | zero => exact PolynomialBound.constant (2 * c + 1)
  | succ e ih =>
    exact (ih.add (((PolynomialBound.constant c).mul (PolynomialBound.identity.pow e)).mul
      (((PolynomialBound.constant 11).mul PolynomialBound.identity).add (PolynomialBound.constant 9)))).add
        (PolynomialBound.constant 8)

end Complexity.StackPower

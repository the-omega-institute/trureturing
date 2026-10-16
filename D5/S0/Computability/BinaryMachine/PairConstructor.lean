/- GID: D5/S0/Computability/BinaryMachine/PairConstructor
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/PairConstructor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact outer pair words are constructed by counted finite stack instructions. -/

import D5.S0.Computability.BinaryMachine.StackPair
import D5.S0.Computability.BinaryMachine.StackControl

set_option autoImplicit false
namespace Complexity.PairConstructor
open StackMachine (Registers)
open StackProgram

def build : Program 6
    (Sum (Fin 4) (Sum (Fin 4) (Sum (Fin 4) (Sum (Fin 6) (Sum Bool (Fin 4)))))) :=
  seq (StackWords.transfer 1 2) (seq (StackWords.transfer 0 3)
    (seq (StackWords.transfer 2 0) (seq (StackWords.scatter 3 0 2 true true)
      (seq (push 0 false) (StackWords.transfer 2 0)))))

def buildEncoding := (Encoding.fin 3).sum ((Encoding.fin 3).sum ((Encoding.fin 3).sum
  ((Encoding.fin 5).sum (Encoding.bool.sum (Encoding.fin 3)))))

/-- The unchanged outer format is built with an exact linear budget. Empty
components and every raw payload are included. Other frame registers are intact. -/
theorem exec_build (r : Registers 6) (h₂ : r 2 = []) (h₃ : r 3 = []) :
    Exec build build.start r (7 * (r 0).length + 4 * (r 1).length + 12)
      (true, StackMachine.set (StackMachine.set r 0 (pairWords (r 0) (r 1))) 1 []) := by
  let r₁ := StackMachine.set (StackMachine.set r 1 []) 2 ((r 1).reverse ++ r 2)
  let r₂ := StackMachine.set (StackMachine.set r₁ 0 []) 3 ((r₁ 0).reverse ++ r₁ 3)
  let r₃ := StackMachine.set (StackMachine.set r₂ 2 []) 0 ((r₂ 2).reverse ++ r₂ 0)
  let r₄ := StackMachine.set (StackMachine.set (StackMachine.set r₃ 3 []) 0
    ((r₃ 3).reverse ++ r₃ 0)) 2 ((r₃ 3).reverse.map (StackWords.mapBit true true) ++ r₃ 2)
  let r₅ := StackMachine.set r₄ 0 (false :: r₄ 0)
  have h₁ := StackWords.exec_transfer (k := 6) 1 2 (by decide) r
  have h₂' := StackWords.exec_transfer (k := 6) 0 3 (by decide) r₁
  have h₃' := StackWords.exec_transfer (k := 6) 2 0 (by decide) r₂
  have h₄ := StackWords.exec_scatter (k := 6) 3 0 2 (by decide) (by decide) (by decide) true true r₃
  have h₅ := exec_push (k := 6) 0 false r₄
  have h₆ := StackWords.exec_transfer (k := 6) 2 0 (by decide) r₅
  have hh := exec_seq _ _ h₁ (exec_seq _ _ h₂' (exec_seq _ _ h₃'
    (exec_seq _ _ h₄ (exec_seq _ _ h₅ h₆))))
  have hout : StackMachine.set (StackMachine.set r₅ 2 []) 0 ((r₅ 2).reverse ++ r₅ 0) =
      StackMachine.set (StackMachine.set r 0 (pairWords (r 0) (r 1))) 1 [] := by
    funext a
    by_cases ha₀ : a = 0
    · subst a
      simp [r₅, r₄, r₃, r₂, r₁, h₂, h₃, StackWords.map_ones, pairWords, List.reverse_append,
        List.append_assoc]
    · by_cases ha₁ : a = 1
      · subst a; simp [r₅, r₄, r₃, r₂, r₁]
      · by_cases ha₂ : a = 2
        · subst a; simp [ha₀, ha₁, h₂]
        · by_cases ha₃ : a = 3
          · subst a; simp [r₅, r₄, ha₀, ha₁, ha₂, h₃]
          · simp [r₅, r₄, r₃, r₂, r₁, StackMachine.set, ha₀, ha₁, ha₂, ha₃]
  change Exec _ _ _ _ (true, _) at hh
  rw [hout] at hh
  have hcost : 2 * (r 1).length + 2 + (2 * (r₁ 0).length + 2 +
      (2 * (r₂ 2).length + 2 + (3 * (r₃ 3).length + 2 + (2 + (2 * (r₅ 2).length + 2))))) =
      7 * (r 0).length + 4 * (r 1).length + 12 := by
    simp [r₅, r₄, r₃, r₂, r₁, h₂, h₃, StackWords.map_ones]
    omega
  rw [hcost] at hh
  exact hh

end Complexity.PairConstructor

/- GID: D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteMiniCut01137Root
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteMiniCut01137Root
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteMiniCut01137Root.actual_prefix_score_lower_bound
   digest: The complete finite elimination program consumes all original factor bounds, each scoped bucket inequality, every literal factor partition and the terminal minimum. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S0.Certificates.FiniteMinPlusElimination
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket00
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket01
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket02
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket03
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket04
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket05
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket06
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket07
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket08
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket09
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket10
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket11
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket12
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket13
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket14
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group00
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group01
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group02
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group03
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group04
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group05
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group06
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group07
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group08
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group09
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group10
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group11
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group12
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group13
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group14
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group15
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group16
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group17
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Root
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open D5.S0.Certificates.FiniteMinPlusElimination
open D5.S0.Certificates
def Context := {e : Assignment // Compatible (prefixPartial 13 17589) e}
def lift (f : Assignment → ℤ) : Factor Context := fun e => (6987435 : ℤ) * f e.val
def factor : Nat → Factor Context
  | 0 => lift PreparedEJMCompleteMiniCut01137Group00.normalizedAt
  | 1 => lift PreparedEJMCompleteMiniCut01137Group01.normalizedAt
  | 2 => lift PreparedEJMCompleteMiniCut01137Group02.normalizedAt
  | 3 => lift PreparedEJMCompleteMiniCut01137Group03.normalizedAt
  | 4 => lift PreparedEJMCompleteMiniCut01137Group04.normalizedAt
  | 5 => lift PreparedEJMCompleteMiniCut01137Group05.normalizedAt
  | 6 => lift PreparedEJMCompleteMiniCut01137Group06.normalizedAt
  | 7 => lift PreparedEJMCompleteMiniCut01137Group07.normalizedAt
  | 8 => lift PreparedEJMCompleteMiniCut01137Group08.normalizedAt
  | 9 => lift PreparedEJMCompleteMiniCut01137Group09.normalizedAt
  | 10 => lift PreparedEJMCompleteMiniCut01137Group10.normalizedAt
  | 11 => lift PreparedEJMCompleteMiniCut01137Group11.normalizedAt
  | 12 => lift PreparedEJMCompleteMiniCut01137Group12.normalizedAt
  | 13 => lift PreparedEJMCompleteMiniCut01137Group13.normalizedAt
  | 14 => lift PreparedEJMCompleteMiniCut01137Group14.normalizedAt
  | 15 => lift PreparedEJMCompleteMiniCut01137Group15.normalizedAt
  | 16 => lift PreparedEJMCompleteMiniCut01137Group16.normalizedAt
  | 17 => lift PreparedEJMCompleteMiniCut01137Group17.normalizedAt
  | 18 => lift PreparedEJMCompleteMiniCut01137Bucket00.lowerAt
  | 19 => lift PreparedEJMCompleteMiniCut01137Bucket01.lowerAt
  | 20 => lift PreparedEJMCompleteMiniCut01137Bucket02.lowerAt
  | 21 => lift PreparedEJMCompleteMiniCut01137Bucket03.lowerAt
  | 22 => lift PreparedEJMCompleteMiniCut01137Bucket04.lowerAt
  | 23 => lift PreparedEJMCompleteMiniCut01137Bucket05.lowerAt
  | 24 => lift PreparedEJMCompleteMiniCut01137Bucket06.lowerAt
  | 25 => lift PreparedEJMCompleteMiniCut01137Bucket07.lowerAt
  | 26 => lift PreparedEJMCompleteMiniCut01137Bucket08.lowerAt
  | 27 => lift PreparedEJMCompleteMiniCut01137Bucket09.lowerAt
  | 28 => lift PreparedEJMCompleteMiniCut01137Bucket10.lowerAt
  | 29 => lift PreparedEJMCompleteMiniCut01137Bucket11.lowerAt
  | 30 => lift PreparedEJMCompleteMiniCut01137Bucket12.lowerAt
  | 31 => lift PreparedEJMCompleteMiniCut01137Bucket13.lowerAt
  | 32 => lift PreparedEJMCompleteMiniCut01137Bucket14.lowerAt
  | _ => fun _ => 0

def initial : State Context :=
  ⟨(6987435 : ℤ) * 6431200094, [factor 0, factor 1, factor 2, factor 3, factor 4, factor 5, factor 6, factor 7, factor 8, factor 9, factor 10, factor 11, factor 12, factor 13, factor 14, factor 15, factor 16, factor 17]⟩

def operation0 : Elimination Context :=
  ⟨[factor 1, factor 13, factor 14], [factor 0, factor 2, factor 3, factor 4, factor 5, factor 6, factor 7, factor 8, factor 9, factor 10, factor 11, factor 12, factor 15, factor 16, factor 17], (6987435 : ℤ) * (-122250419), factor 18⟩

def state1 : State Context := next initial operation0

def operation1 : Elimination Context :=
  ⟨[factor 2], [factor 18, factor 0, factor 3, factor 4, factor 5, factor 6, factor 7, factor 8, factor 9, factor 10, factor 11, factor 12, factor 15, factor 16, factor 17], (6987435 : ℤ) * (-870932444), factor 19⟩

def state2 : State Context := next state1 operation1

def operation2 : Elimination Context :=
  ⟨[factor 3], [factor 19, factor 18, factor 0, factor 4, factor 5, factor 6, factor 7, factor 8, factor 9, factor 10, factor 11, factor 12, factor 15, factor 16, factor 17], (6987435 : ℤ) * (0), factor 20⟩

def state3 : State Context := next state2 operation2

def operation3 : Elimination Context :=
  ⟨[factor 8], [factor 20, factor 19, factor 18, factor 0, factor 4, factor 5, factor 6, factor 7, factor 9, factor 10, factor 11, factor 12, factor 15, factor 16, factor 17], (6987435 : ℤ) * (-403379955), factor 21⟩

def state4 : State Context := next state3 operation3

def operation4 : Elimination Context :=
  ⟨[factor 9], [factor 21, factor 20, factor 19, factor 18, factor 0, factor 4, factor 5, factor 6, factor 7, factor 10, factor 11, factor 12, factor 15, factor 16, factor 17], (6987435 : ℤ) * (0), factor 22⟩

def state5 : State Context := next state4 operation4

def operation5 : Elimination Context :=
  ⟨[factor 15], [factor 22, factor 21, factor 20, factor 19, factor 18, factor 0, factor 4, factor 5, factor 6, factor 7, factor 10, factor 11, factor 12, factor 16, factor 17], (6987435 : ℤ) * (-1227987909), factor 23⟩

def state6 : State Context := next state5 operation5

def operation6 : Elimination Context :=
  ⟨[factor 6, factor 20], [factor 23, factor 22, factor 21, factor 19, factor 18, factor 0, factor 4, factor 5, factor 7, factor 10, factor 11, factor 12, factor 16, factor 17], (6987435 : ℤ) * (0), factor 24⟩

def state7 : State Context := next state6 operation6

def operation7 : Elimination Context :=
  ⟨[factor 10, factor 11, factor 18], [factor 24, factor 23, factor 22, factor 21, factor 19, factor 0, factor 4, factor 5, factor 7, factor 12, factor 16, factor 17], (6987435 : ℤ) * (0), factor 25⟩

def state8 : State Context := next state7 operation7

def operation8 : Elimination Context :=
  ⟨[factor 17], [factor 25, factor 24, factor 23, factor 22, factor 21, factor 19, factor 0, factor 4, factor 5, factor 7, factor 12, factor 16], (6987435 : ℤ) * (-312383211), factor 26⟩

def state9 : State Context := next state8 operation8

def operation9 : Elimination Context :=
  ⟨[factor 21], [factor 26, factor 25, factor 24, factor 23, factor 22, factor 19, factor 0, factor 4, factor 5, factor 7, factor 12, factor 16], (6987435 : ℤ) * (-139648167), factor 27⟩

def state10 : State Context := next state9 operation9

def operation10 : Elimination Context :=
  ⟨[factor 12, factor 23, factor 25], [factor 27, factor 26, factor 24, factor 22, factor 19, factor 0, factor 4, factor 5, factor 7, factor 16], (6987435 : ℤ) * (0), factor 28⟩

def state11 : State Context := next state10 operation10

def operation11 : Elimination Context :=
  ⟨[factor 16, factor 26], [factor 28, factor 27, factor 24, factor 22, factor 19, factor 0, factor 4, factor 5, factor 7], (6987435 : ℤ) * (-732920220), factor 29⟩

def state12 : State Context := next state11 operation11

def operation12 : Elimination Context :=
  ⟨[factor 0, factor 5, factor 7, factor 19, factor 24, factor 28], [factor 29, factor 27, factor 22, factor 4], (6987435 : ℤ) * (-359666261), factor 30⟩

def state13 : State Context := next state12 operation12

def operation13 : Elimination Context :=
  ⟨[factor 4, factor 27, factor 29, factor 30], [factor 22], (6987435 : ℤ) * (-1006414852), factor 31⟩

def state14 : State Context := next state13 operation13

def operation14 : Elimination Context :=
  ⟨[factor 22, factor 31], [], (6987435 : ℤ) * (-848005158), factor 32⟩

def state15 : State Context := next state14 operation14

def operations : List (Elimination Context) :=
  [operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, operation11, operation12, operation13, operation14]

private theorem step0_valid : ValidStep initial operation0 := by
  constructor
  · have literal : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] : List Nat).Perm
        ([1, 13, 14] ++ [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket00.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation0, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step1_valid : ValidStep state1 operation1 := by
  constructor
  · have literal : ([18, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17] : List Nat).Perm
        ([2] ++ [18, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, state1, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket01.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation1, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step2_valid : ValidStep state2 operation2 := by
  constructor
  · have literal : ([19, 18, 0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17] : List Nat).Perm
        ([3] ++ [19, 18, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, state1, state2, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket02.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation2, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_zero, mul_add, add_assoc] using receipt

private theorem step3_valid : ValidStep state3 operation3 := by
  constructor
  · have literal : ([20, 19, 18, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17] : List Nat).Perm
        ([8] ++ [20, 19, 18, 0, 4, 5, 6, 7, 9, 10, 11, 12, 15, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, state1, state2, state3, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket03.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation3, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step4_valid : ValidStep state4 operation4 := by
  constructor
  · have literal : ([21, 20, 19, 18, 0, 4, 5, 6, 7, 9, 10, 11, 12, 15, 16, 17] : List Nat).Perm
        ([9] ++ [21, 20, 19, 18, 0, 4, 5, 6, 7, 10, 11, 12, 15, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, state1, state2, state3, state4, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket04.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation4, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_zero, mul_add, add_assoc] using receipt

private theorem step5_valid : ValidStep state5 operation5 := by
  constructor
  · have literal : ([22, 21, 20, 19, 18, 0, 4, 5, 6, 7, 10, 11, 12, 15, 16, 17] : List Nat).Perm
        ([15] ++ [22, 21, 20, 19, 18, 0, 4, 5, 6, 7, 10, 11, 12, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, state1, state2, state3, state4, state5, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket05.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation5, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step6_valid : ValidStep state6 operation6 := by
  constructor
  · have literal : ([23, 22, 21, 20, 19, 18, 0, 4, 5, 6, 7, 10, 11, 12, 16, 17] : List Nat).Perm
        ([6, 20] ++ [23, 22, 21, 19, 18, 0, 4, 5, 7, 10, 11, 12, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, state1, state2, state3, state4, state5, state6, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket06.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation6, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_zero, mul_add, add_assoc] using receipt

private theorem step7_valid : ValidStep state7 operation7 := by
  constructor
  · have literal : ([24, 23, 22, 21, 19, 18, 0, 4, 5, 7, 10, 11, 12, 16, 17] : List Nat).Perm
        ([10, 11, 18] ++ [24, 23, 22, 21, 19, 0, 4, 5, 7, 12, 16, 17]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, state1, state2, state3, state4, state5, state6, state7, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket07.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation7, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_zero, mul_add, add_assoc] using receipt

private theorem step8_valid : ValidStep state8 operation8 := by
  constructor
  · have literal : ([25, 24, 23, 22, 21, 19, 0, 4, 5, 7, 12, 16, 17] : List Nat).Perm
        ([17] ++ [25, 24, 23, 22, 21, 19, 0, 4, 5, 7, 12, 16]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, state1, state2, state3, state4, state5, state6, state7, state8, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket08.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation8, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step9_valid : ValidStep state9 operation9 := by
  constructor
  · have literal : ([26, 25, 24, 23, 22, 21, 19, 0, 4, 5, 7, 12, 16] : List Nat).Perm
        ([21] ++ [26, 25, 24, 23, 22, 19, 0, 4, 5, 7, 12, 16]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, state1, state2, state3, state4, state5, state6, state7, state8, state9, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket09.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation9, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step10_valid : ValidStep state10 operation10 := by
  constructor
  · have literal : ([27, 26, 25, 24, 23, 22, 19, 0, 4, 5, 7, 12, 16] : List Nat).Perm
        ([12, 23, 25] ++ [27, 26, 24, 22, 19, 0, 4, 5, 7, 16]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket10.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation10, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_zero, mul_add, add_assoc] using receipt

private theorem step11_valid : ValidStep state11 operation11 := by
  constructor
  · have literal : ([28, 27, 26, 24, 22, 19, 0, 4, 5, 7, 16] : List Nat).Perm
        ([16, 26] ++ [28, 27, 24, 22, 19, 0, 4, 5, 7]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, operation11, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket11.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation11, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step12_valid : ValidStep state12 operation12 := by
  constructor
  · have literal : ([29, 28, 27, 24, 22, 19, 0, 4, 5, 7] : List Nat).Perm
        ([0, 5, 7, 19, 24, 28] ++ [29, 27, 22, 4]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, operation11, operation12, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket12.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation12, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step13_valid : ValidStep state13 operation13 := by
  constructor
  · have literal : ([30, 29, 27, 22, 4] : List Nat).Perm
        ([4, 27, 29, 30] ++ [22]) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, operation11, operation12, operation13, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, state13, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket13.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation13, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem step14_valid : ValidStep state14 operation14 := by
  constructor
  · have literal : ([31, 22] : List Nat).Perm
        ([22, 31] ++ []) := by
      decide +kernel
    simpa only [initial, operation0, operation1, operation2, operation3, operation4, operation5, operation6, operation7, operation8, operation9, operation10, operation11, operation12, operation13, operation14, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10, state11, state12, state13, state14, next, List.map_append, List.map_cons, List.map_nil]
      using literal.map factor
  · intro e
    have receipt := mul_le_mul_of_nonneg_left
      (PreparedEJMCompleteMiniCut01137Bucket14.inequality_at e.val)
      (by decide : (0 : ℤ) ≤ 6987435)
    simpa only [operation14, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, zero_add, add_zero, mul_add, add_assoc] using receipt

private theorem valid_program : ValidProgram initial operations := by
  change ValidStep initial operation0 ∧ ValidStep state1 operation1 ∧ ValidStep state2 operation2 ∧ ValidStep state3 operation3 ∧ ValidStep state4 operation4 ∧ ValidStep state5 operation5 ∧ ValidStep state6 operation6 ∧ ValidStep state7 operation7 ∧ ValidStep state8 operation8 ∧ ValidStep state9 operation9 ∧ ValidStep state10 operation10 ∧ ValidStep state11 operation11 ∧ ValidStep state12 operation12 ∧ ValidStep state13 operation13 ∧ ValidStep state14 operation14 ∧ True
  exact ⟨step0_valid, step1_valid, step2_valid, step3_valid, step4_valid, step5_valid, step6_valid, step7_valid, step8_valid, step9_valid, step10_valid, step11_valid, step12_valid, step13_valid, step14_valid, trivial⟩

private theorem component_sum (e : Assignment) :
    PreparedEJMCompleteMiniCut01137Group00.score e + PreparedEJMCompleteMiniCut01137Group01.score e + PreparedEJMCompleteMiniCut01137Group02.score e + PreparedEJMCompleteMiniCut01137Group03.score e + PreparedEJMCompleteMiniCut01137Group04.score e + PreparedEJMCompleteMiniCut01137Group05.score e + PreparedEJMCompleteMiniCut01137Group06.score e + PreparedEJMCompleteMiniCut01137Group07.score e + PreparedEJMCompleteMiniCut01137Group08.score e + PreparedEJMCompleteMiniCut01137Group09.score e + PreparedEJMCompleteMiniCut01137Group10.score e + PreparedEJMCompleteMiniCut01137Group11.score e + PreparedEJMCompleteMiniCut01137Group12.score e + PreparedEJMCompleteMiniCut01137Group13.score e + PreparedEJMCompleteMiniCut01137Group14.score e + PreparedEJMCompleteMiniCut01137Group15.score e + PreparedEJMCompleteMiniCut01137Group16.score e + PreparedEJMCompleteMiniCut01137Group17.score e = score F1 F2 e := by
  simp only [PreparedEJMCompleteMiniCut01137Group00.score, PreparedEJMCompleteMiniCut01137Group01.score, PreparedEJMCompleteMiniCut01137Group02.score, PreparedEJMCompleteMiniCut01137Group03.score, PreparedEJMCompleteMiniCut01137Group04.score, PreparedEJMCompleteMiniCut01137Group05.score, PreparedEJMCompleteMiniCut01137Group06.score, PreparedEJMCompleteMiniCut01137Group07.score, PreparedEJMCompleteMiniCut01137Group08.score, PreparedEJMCompleteMiniCut01137Group09.score, PreparedEJMCompleteMiniCut01137Group10.score, PreparedEJMCompleteMiniCut01137Group11.score, PreparedEJMCompleteMiniCut01137Group12.score, PreparedEJMCompleteMiniCut01137Group13.score, PreparedEJMCompleteMiniCut01137Group14.score, PreparedEJMCompleteMiniCut01137Group15.score, PreparedEJMCompleteMiniCut01137Group16.score, PreparedEJMCompleteMiniCut01137Group17.score, PreparedEJMCompleteMiniCut01137Factor00.score, PreparedEJMCompleteMiniCut01137Factor01.score, PreparedEJMCompleteMiniCut01137Factor02.score, PreparedEJMCompleteMiniCut01137Factor03.score, PreparedEJMCompleteMiniCut01137Factor04.score, PreparedEJMCompleteMiniCut01137Factor05.score, PreparedEJMCompleteMiniCut01137Factor06.score, PreparedEJMCompleteMiniCut01137Factor07.score, PreparedEJMCompleteMiniCut01137Factor08.score, PreparedEJMCompleteMiniCut01137Factor09.score, PreparedEJMCompleteMiniCut01137Factor10.score, PreparedEJMCompleteMiniCut01137Factor11.score, PreparedEJMCompleteMiniCut01137Factor12.score, PreparedEJMCompleteMiniCut01137Factor13.score, PreparedEJMCompleteMiniCut01137Factor14.score, PreparedEJMCompleteMiniCut01137Factor15.score, PreparedEJMCompleteMiniCut01137Factor16.score, PreparedEJMCompleteMiniCut01137Factor17.score, PreparedEJMCompleteMiniCut01137Factor18.score, PreparedEJMCompleteMiniCut01137Factor19.score, PreparedEJMCompleteMiniCut01137Factor20.score, PreparedEJMCompleteMiniCut01137Factor21.score, PreparedEJMCompleteMiniCut01137Factor22.score, PreparedEJMCompleteMiniCut01137Factor23.score, PreparedEJMCompleteMiniCut01137Factor24.score, PreparedEJMCompleteMiniCut01137Factor25.score, PreparedEJMCompleteMiniCut01137Factor26.score, PreparedEJMCompleteMiniCut01137Factor27.score, PreparedEJMCompleteMiniCut01137Factor28.score, PreparedEJMCompleteMiniCut01137Factor29.score, PreparedEJMCompleteMiniCut01137Factor30.score, PreparedEJMCompleteMiniCut01137Factor31.score,
    EJMInflationScore.score, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.reduceSucc, add_zero]
  ring

private theorem initial_lower : ∀ e : Context, initial.value e ≤ score F1 F2 e.val := by
  intro e
  have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (PreparedEJMCompleteMiniCut01137Group00.bound e.val e.property) (PreparedEJMCompleteMiniCut01137Group01.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group02.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group03.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group04.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group05.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group06.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group07.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group08.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group09.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group10.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group11.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group12.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group13.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group14.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group15.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group16.bound e.val e.property)) (PreparedEJMCompleteMiniCut01137Group17.bound e.val e.property)
  rw [component_sum e.val] at combined
  have represented : initial.value e = PreparedEJMCompleteMiniCut01137Group00.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group01.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group02.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group03.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group04.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group05.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group06.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group07.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group08.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group09.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group10.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group11.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group12.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group13.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group14.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group15.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group16.lowerAt e.val + PreparedEJMCompleteMiniCut01137Group17.lowerAt e.val := by
    simp only [initial, State.value, factor, lift, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, PreparedEJMCompleteMiniCut01137Group00.lowerAt, PreparedEJMCompleteMiniCut01137Group00.table, PreparedEJMCompleteMiniCut01137Group00.normalizedAt, PreparedEJMCompleteMiniCut01137Group01.lowerAt, PreparedEJMCompleteMiniCut01137Group01.table, PreparedEJMCompleteMiniCut01137Group01.normalizedAt, PreparedEJMCompleteMiniCut01137Group02.lowerAt, PreparedEJMCompleteMiniCut01137Group02.table, PreparedEJMCompleteMiniCut01137Group02.normalizedAt, PreparedEJMCompleteMiniCut01137Group03.lowerAt, PreparedEJMCompleteMiniCut01137Group03.table, PreparedEJMCompleteMiniCut01137Group03.normalizedAt, PreparedEJMCompleteMiniCut01137Group04.lowerAt, PreparedEJMCompleteMiniCut01137Group04.table, PreparedEJMCompleteMiniCut01137Group04.normalizedAt, PreparedEJMCompleteMiniCut01137Group05.lowerAt, PreparedEJMCompleteMiniCut01137Group05.table, PreparedEJMCompleteMiniCut01137Group05.normalizedAt, PreparedEJMCompleteMiniCut01137Group06.lowerAt, PreparedEJMCompleteMiniCut01137Group06.table, PreparedEJMCompleteMiniCut01137Group06.normalizedAt, PreparedEJMCompleteMiniCut01137Group07.lowerAt, PreparedEJMCompleteMiniCut01137Group07.table, PreparedEJMCompleteMiniCut01137Group07.normalizedAt, PreparedEJMCompleteMiniCut01137Group08.lowerAt, PreparedEJMCompleteMiniCut01137Group08.table, PreparedEJMCompleteMiniCut01137Group08.normalizedAt, PreparedEJMCompleteMiniCut01137Group09.lowerAt, PreparedEJMCompleteMiniCut01137Group09.table, PreparedEJMCompleteMiniCut01137Group09.normalizedAt, PreparedEJMCompleteMiniCut01137Group10.lowerAt, PreparedEJMCompleteMiniCut01137Group10.table, PreparedEJMCompleteMiniCut01137Group10.normalizedAt, PreparedEJMCompleteMiniCut01137Group11.lowerAt, PreparedEJMCompleteMiniCut01137Group11.table, PreparedEJMCompleteMiniCut01137Group11.normalizedAt, PreparedEJMCompleteMiniCut01137Group12.lowerAt, PreparedEJMCompleteMiniCut01137Group12.table, PreparedEJMCompleteMiniCut01137Group12.normalizedAt, PreparedEJMCompleteMiniCut01137Group13.lowerAt, PreparedEJMCompleteMiniCut01137Group13.table, PreparedEJMCompleteMiniCut01137Group13.normalizedAt, PreparedEJMCompleteMiniCut01137Group14.lowerAt, PreparedEJMCompleteMiniCut01137Group14.table, PreparedEJMCompleteMiniCut01137Group14.normalizedAt, PreparedEJMCompleteMiniCut01137Group15.lowerAt, PreparedEJMCompleteMiniCut01137Group15.table, PreparedEJMCompleteMiniCut01137Group15.normalizedAt, PreparedEJMCompleteMiniCut01137Group16.lowerAt, PreparedEJMCompleteMiniCut01137Group16.table, PreparedEJMCompleteMiniCut01137Group16.normalizedAt, PreparedEJMCompleteMiniCut01137Group17.lowerAt, PreparedEJMCompleteMiniCut01137Group17.table, PreparedEJMCompleteMiniCut01137Group17.normalizedAt]
    ring
  rw [represented]
  exact combined

private theorem terminal_minimum_32 : ∀ (x18 : Fin 4),
    (-280636802 : ℤ) ≤ PreparedEJMCompleteMiniCut01137Tables.normal16305 x18 := by
  decide +kernel

private theorem terminal : Terminal state15 (6987435 : ℤ) := by
  refine ⟨[(6987435 : ℤ) * (-280636802)], ?_, ?_⟩
  · change List.Forall₂ (fun (m : ℤ) (f : Factor Context) => ∀ e, m ≤ f e)
      [(6987435 : ℤ) * (-280636802)] [factor 32]
    refine List.Forall₂.cons ?_ (List.Forall₂.nil)
    · intro e
      exact mul_le_mul_of_nonneg_left (terminal_minimum_32 (e.val 18))
        (by decide : (0 : ℤ) ≤ 6987435)
  · change (6987435 : ℤ) ≤ (6987435 : ℤ) * 407611498 + ((6987435 : ℤ) * (-280636802))
    decide +kernel

theorem actual_prefix_score_lower_bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : scale ≤ score F1 F2 e := by
  exact program_lower_bound (fun e : Context => score F1 F2 e.val)
    initial operations (6987435 : ℤ) initial_lower valid_program terminal ⟨e, hp⟩

#print axioms actual_prefix_score_lower_bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Root

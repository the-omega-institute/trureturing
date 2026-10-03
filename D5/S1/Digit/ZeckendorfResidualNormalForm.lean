/- GID: D5/S1/Digit/ZeckendorfResidualNormalForm
   generality: I
   mirror-B: none(waiver:source-arithmetic-bridge)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.List.Infix]
   utility: none
   digest: Complete residuals admit bounded legal representatives avoiding the replacement block. -/

import D5.S1.Digit.ZeckendorfResidualCover
import D5.S1.Digit.ZeckendorfContextualReplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfResidualNormalForm

open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.ZeckendorfResidualCover
open D5.S1.Digit.ZeckendorfContextualReplacement

/-- Fixed-length MSD binary rank; replacement strictly decreases this natural rank. -/
def rank : List (Fin 2) → ℕ
  | [] => 0
  | a :: w => a.val * 2 ^ w.length + rank w

/-- Every complete residual has a legal length-H+7 representative whose final
H digits avoid B1. Replacements preserve the full partial residual. -/
theorem normalized_state_cover (H : ℕ) (hH : 14 ≤ H)
    (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
    ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
      ZeckendorfRawWindow.residual (Nat.fib H) w = ZeckendorfRawWindow.residual (Nat.fib H) v ∧
      ¬ B1 <:+: v.drop 7 := by
  classical
  have append_rank (p t : List (Fin 2)) : rank (p ++ t) = rank p * 2 ^ t.length + rank t := by
    induction p with
    | nil => simp [rank]
    | cons a p ih =>
      simp only [List.cons_append,rank,List.length_append,ih,List.length_cons,pow_add]
      ring
  have decrease (p u : List (Fin 2)) : rank (p ++ B0 ++ u) < rank (p ++ B1 ++ u) := by
    rw [append_rank,append_rank,append_rank,append_rank]
    have hb : rank B0 < rank B1 := by norm_num [B0,B1,rank]
    have hp : 0 < 2 ^ u.length := by positivity
    have := Nat.mul_lt_mul_of_pos_right hb hp
    have hl : B0.length = B1.length := by decide
    rw [hl,Nat.add_mul,Nat.add_mul]
    omega
  obtain ⟨v,hv,hl,he⟩ := all_state_cover H (Nat.fib H) hH le_rfl w hw
  let P : ℕ → Prop := fun k => ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
    ZeckendorfRawWindow.residual (Nat.fib H) w = ZeckendorfRawWindow.residual (Nat.fib H) v ∧ rank v = k
  have hp : ∃ k, P k := ⟨rank v,v,hv,hl,he,rfl⟩
  obtain ⟨v,hv,hl,he,hmin⟩ := Nat.find_spec hp
  refine ⟨v,hv,hl,he,?_⟩
  intro hinfix
  obtain ⟨p,u,hpu⟩ := hinfix
  let p' := v.take 7 ++ p
  have heq : v = p' ++ B1 ++ u := by
    have split := List.take_append_drop 7 v
    rw [← hpu] at split
    simpa [p',List.append_assoc] using split.symm
  have hv' : NoAdjacentOnes (p' ++ B1 ++ u) := by rw [← heq]; exact hv
  have hu : 14 + u.length ≤ H := by
    have ht : (v.drop 7).length = H := by simp [hl]
    have hh := congrArg List.length hpu
    simp only [List.length_append, B1, List.length_cons, List.length_nil] at hh
    omega
  have legal : NoAdjacentOnes (p' ++ B0 ++ u) := by
    have hch : (p' ++ B1 ++ u).IsChain (fun a b => a = 0 ∨ b = 0) := hv'
    simpa [NoAdjacentOnes,List.isChain_append,B0,B1] using hch
  have length : (p' ++ B0 ++ u).length = H + 7 := by
    rw [heq] at hl
    simpa [B0,B1] using hl
  have eq_res := contextual_replacement H p' u hH hu hv'
  have candidate : P (rank (p' ++ B0 ++ u)) := by
    refine ⟨p' ++ B0 ++ u,legal,length,?_,rfl⟩
    rw [heq] at he
    exact he.trans eq_res
  have lt : rank (p' ++ B0 ++ u) < Nat.find hp := by
    rw [← hmin,heq]
    exact decrease p' u
  exact Nat.find_min hp lt candidate

#print axioms normalized_state_cover

end D5.S1.Digit.ZeckendorfResidualNormalForm

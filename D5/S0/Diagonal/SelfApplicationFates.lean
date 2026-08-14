/- GID: D5/S0/Diagonal/SelfApplicationFates
   generality: G
   mirror-B: D5/B/S0/Diagonal/SelfApplicationFates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: On the binary alphabet every non-degenerate fractional self-map has exactly one of four self-application fates, and the live fate holds precisely for the golden φ-family, whose discriminant is 5. -/

import Mathlib

namespace D5.S0.Diagonal.SelfApplicationFates

structure BinaryFractionalMap where
  a : Fin 2
  b : Fin 2
  c : Fin 2
  d : Fin 2
deriving DecidableEq, Fintype

def determinant (m : BinaryFractionalMap) : Int :=
  (m.a : Int) * m.d - (m.b : Int) * m.c

def Nondegenerate (m : BinaryFractionalMap) : Prop := determinant m ≠ 0

def fixedPolynomial (m : BinaryFractionalMap) (x : Rat) : Rat :=
  (m.c : Rat) * x ^ 2 + ((m.d : Rat) - m.a) * x - m.b

def fixedCoefficients (m : BinaryFractionalMap) : Int × Int × Int :=
  ((m.c : Int), (m.d : Int) - m.a, -(m.b : Int))

def discriminant (m : BinaryFractionalMap) : Int :=
  ((m.d : Int) - m.a) ^ 2 + 4 * (m.b : Int) * m.c

set_option backward.isDefEq.respectTransparency false in
inductive SelfApplicationFate
  | empty
  | dead
  | collapse
  | live
deriving DecidableEq, Fintype

def HasFate (m : BinaryFractionalMap) : SelfApplicationFate → Prop
  | .empty => fixedCoefficients m = (0, 0, 0)
  | .dead => fixedCoefficients m = (0, 0, -1)
  | .collapse =>
      (discriminant m = 0 ∨ discriminant m = 4) ∧
        fixedCoefficients m ≠ (0, 0, 0) ∧ fixedCoefficients m ≠ (0, 0, -1)
  | .live => discriminant m = 5

instance (m : BinaryFractionalMap) (fate : SelfApplicationFate) :
    Decidable (HasFate m fate) := by
  cases fate <;> simp only [HasFate] <;> infer_instance

def IsPhiFamily (m : BinaryFractionalMap) : Prop :=
  (m.a = 1 ∧ m.b = 1 ∧ m.c = 1 ∧ m.d = 0) ∨
    (m.a = 0 ∧ m.b = 1 ∧ m.c = 1 ∧ m.d = 1)

instance (m : BinaryFractionalMap) : Decidable (IsPhiFamily m) := by
  unfold IsPhiFamily
  infer_instance

theorem self_application_four_fates (m : BinaryFractionalMap) (hm : Nondegenerate m) :
    (∃! fate, HasFate m fate) ∧
      (HasFate m .live ↔ IsPhiFamily m) ∧
      (HasFate m .live →
        fixedCoefficients m = (1, -1, -1) ∨ fixedCoefficients m = (1, 1, -1)) ∧
      (HasFate m .live → discriminant m = 1 ^ 2 + 4) := by
  rcases m with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Nondegenerate, determinant] at hm
  all_goals
    constructor
    · first
      | refine ⟨.empty, by decide, ?_⟩
      | refine ⟨.dead, by decide, ?_⟩
      | refine ⟨.collapse, by decide, ?_⟩
      | refine ⟨.live, by decide, ?_⟩
      all_goals
        intro fate hfate
        fin_cases fate <;> simp_all [HasFate, fixedCoefficients, discriminant]
    · decide

end D5.S0.Diagonal.SelfApplicationFates

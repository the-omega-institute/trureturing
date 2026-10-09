/- GID: D5/S3/Arith/PrimeTripletWheel
   generality: G
   mirror-B: none
   mirror-E: none(waiver:general-reflection-theorem)
   anchors: [docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md#十六-轮筛三点相关绝对原点与-fibonacci-窗口]
   utility: none
   digest: Reflection identifies the two diameter-six wheel candidate spaces at every nonzero modulus.

   The arithmetic statement is about wheel-admissible residues in ZMod W.
   It does not assert infinitude or asymptotics for actual prime triplets.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimeTripletWheel

/-- The two diameter-six offset templates. -/
def tripletPlus : Finset ℕ := {0, 2, 6}

def tripletMinus : Finset ℕ := {0, 4, 6}

/-- Ordered gap difference for a three-point template. -/
def gapDifference (g₁ g₂ : ℤ) : ℤ := g₂ - g₁

/-- Reversing the ordered gaps negates the three-point direction. -/
theorem reflected_gapDifference (g₁ g₂ : ℤ) :
    gapDifference g₂ g₁ = -gapDifference g₁ g₂ := by
  dsimp [gapDifference]
  ring

/-- Wheel admissibility for the three-point orientation H-plus. -/
def plusAdmissible (W : ℕ) [NeZero W] (a : ZMod W) : Prop :=
  IsUnit a ∧ IsUnit (a + 2) ∧ IsUnit (a + 6)

/-- Wheel admissibility for the reflected orientation H-minus. -/
def minusAdmissible (W : ℕ) [NeZero W] (a : ZMod W) : Prop :=
  IsUnit a ∧ IsUnit (a + 4) ∧ IsUnit (a + 6)

/-- The affine reflection sending H-plus to H-minus. -/
def reflect (W : ℕ) [NeZero W] (a : ZMod W) : ZMod W :=
  -a - 6

theorem reflect_involutive (W : ℕ) [NeZero W] (a : ZMod W) :
    reflect W (reflect W a) = a := by
  dsimp [reflect]
  ring

/-- Reflection exchanges the two orientation predicates at every nonzero modulus. -/
theorem plus_reflect_iff (W : ℕ) [NeZero W] (a : ZMod W) :
    plusAdmissible W a ↔ minusAdmissible W (reflect W a) := by
  constructor
  · rintro ⟨h0, h2, h6⟩
    refine ⟨?_, ?_, ?_⟩
    · convert h6.neg using 1 <;> dsimp [reflect] <;> ring
    · convert h2.neg using 1 <;> dsimp [reflect] <;> ring
    · convert h0.neg using 1 <;> dsimp [reflect] <;> ring
  · rintro ⟨h0, h4, h6⟩
    refine ⟨?_, ?_, ?_⟩
    · convert h6.neg using 1 <;> dsimp [reflect] <;> ring
    · convert h4.neg using 1 <;> dsimp [reflect] <;> ring
    · convert h0.neg using 1 <;> dsimp [reflect] <;> ring

/-- The plus and minus candidate residues as finite subtypes. -/
def PlusResidue (W : ℕ) [NeZero W] :=
  {a : ZMod W // plusAdmissible W a}

def MinusResidue (W : ℕ) [NeZero W] :=
  {a : ZMod W // minusAdmissible W a}

/-- The reflection is an equivalence between the two candidate spaces. -/
noncomputable def reflectEquiv (W : ℕ) [NeZero W] :
    PlusResidue W ≃ MinusResidue W where
  toFun := fun a =>
    ⟨reflect W a.1, (plus_reflect_iff W a.1).mp a.2⟩
  invFun := fun b =>
    ⟨reflect W b.1, by
      apply (plus_reflect_iff W (reflect W b.1)).mpr
      rw [reflect_involutive W b.1]
      exact b.2⟩
  left_inv := by
    intro a
    apply Subtype.ext
    exact reflect_involutive W a.1
  right_inv := by
    intro b
    apply Subtype.ext
    exact reflect_involutive W b.1

/-- The two oriented wheel candidate spaces have equal cardinality for every nonzero modulus. -/
theorem candidate_space_card_eq (W : ℕ) [NeZero W] :
    Fintype.card (PlusResidue W) = Fintype.card (MinusResidue W) := by
  classical
  exact Fintype.card_congr (reflectEquiv W)

end D5.S3.Arith.PrimeTripletWheel

/- GID: D5/S3/Arith/PrimeTripletWheel
   generality: G
   mirror-B: none(waiver:general-reflection-theorem)
   mirror-E: none(waiver:general-reflection-theorem)
   anchors: [docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md#十六轮筛三点相关绝对原点与-fibonacci-窗口]
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
    letI : Fintype (PlusResidue W) :=
      Fintype.ofFinite {a : ZMod W // plusAdmissible W a}
    letI : Fintype (MinusResidue W) :=
      Fintype.ofFinite {a : ZMod W // minusAdmissible W a}
    Fintype.card (PlusResidue W) = Fintype.card (MinusResidue W) := by
  classical
  exact @Fintype.card_congr _ _
    (Fintype.ofFinite {a : ZMod W // plusAdmissible W a})
    (Fintype.ofFinite {a : ZMod W // minusAdmissible W a})
    (reflectEquiv W)

/-! ### Finite audit interfaces

The theory dossier records two finite readouts: the origin-fixed prefix at
`W = 30`, and the ordered three-point witness after the `W = 210` layer.  The
definitions below keep those readouts in the finite residue type, so that the
numerical certificates are kernel-checked and remain separate from any claim
about actual prime triples.
-/

def plusCandidate (W : ℕ) [NeZero W] (r : Fin W) : Prop :=
  Nat.Coprime r.1 W ∧ Nat.Coprime (r.1 + 2) W ∧ Nat.Coprime (r.1 + 6) W

def minusCandidate (W : ℕ) [NeZero W] (r : Fin W) : Prop :=
  Nat.Coprime r.1 W ∧ Nat.Coprime (r.1 + 4) W ∧ Nat.Coprime (r.1 + 6) W

instance plusCandidateDecidable (W : ℕ) [NeZero W] :
    DecidablePred (plusCandidate W) := by
  intro r
  unfold plusCandidate
  infer_instance

instance minusCandidateDecidable (W : ℕ) [NeZero W] :
    DecidablePred (minusCandidate W) := by
  intro r
  unfold minusCandidate
  infer_instance

def plusResidues (W : ℕ) [NeZero W] : Finset (Fin W) := by
  exact Finset.univ.filter (plusCandidate W)

def minusResidues (W : ℕ) [NeZero W] : Finset (Fin W) := by
  exact Finset.univ.filter (minusCandidate W)

def originPrefix (W b : ℕ) [NeZero W] (candidate : Fin W → Prop)
    [DecidablePred candidate] : ℕ := by
  exact ((Finset.univ : Finset (Fin W)).filter fun r =>
    candidate r ∧ 1 ≤ r.1 ∧ r.1 ≤ b).card

def tripleReadout (W s t : ℕ) [NeZero W]
    (candidate : Fin W → Prop) [DecidablePred candidate] : ℕ := by
  exact ((Finset.univ : Finset (Fin W)).filter fun r =>
    candidate r ∧ candidate ⟨(r.1 + s) % W,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne W))⟩ ∧
      candidate ⟨(r.1 + t) % W,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne W))⟩).card

theorem plus_residues_30 :
    plusResidues 30 = ({⟨11, by decide⟩, ⟨17, by decide⟩} : Finset (Fin 30)) := by
  decide

theorem minus_residues_30 :
    minusResidues 30 = ({⟨7, by decide⟩, ⟨13, by decide⟩} : Finset (Fin 30)) := by
  decide

theorem plus_origin_prefix_30 :
    originPrefix 30 10 (plusCandidate 30) = 0 := by
  decide

theorem minus_origin_prefix_30 :
    originPrefix 30 10 (minusCandidate 30) = 1 := by
  decide

theorem plus_triple_readout_210 :
    tripleReadout 210 6 30 (plusCandidate 210) = 1 := by
  decide

theorem minus_triple_readout_210 :
    tripleReadout 210 6 30 (minusCandidate 210) = 0 := by
  decide

end D5.S3.Arith.PrimeTripletWheel

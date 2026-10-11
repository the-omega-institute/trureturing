/- GID: D5/S3/ConceptDynamics/Coding/ResetNumberedHistories
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNumberedHistories
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Equivariant numbered homeomorphism for every positive reset carrier. -/

import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
import D5.S3.TotalVariation.ParryBilateralLaw
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryBilateralLaw (ResetPath)
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization (History)
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph groupHistory)
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)
open Multiplicative

/-- The native XOR group retains the absolute Boolean sign. -/
abbrev Sign := Multiplicative Bool

/-- Reset flips the sign; increment has the identity label. -/
def resetMatrix (q : ℕ) : GroupMat Sign q q := fun i j =>
  (if j.val = 0 then MonoidAlgebra.single (ofAdd true) 1 else 0) +
  (if j.val = i.val + 1 then MonoidAlgebra.single 1 1 else 0)

private theorem parameter_positive (q : ℕ) (hq : 0 < q) :
    0 < parryParameter q ∧ ∀ j, 0 < suffixWeight q (parryParameter q) j := by
  by_cases h : 2 ≤ q
  · have law := parry_stationary_law q h
    have hp : 0 < parryParameter q := by linarith [law.1.1]
    exact ⟨hp, fun j => lt_of_lt_of_le hp (law.2.1 j).1⟩
  · have he : q = 1 := by omega
    subst q
    constructor
    · norm_num [parryParameter]
    · intro j
      have hj : j.val = 0 := by omega
      norm_num [suffixWeight, parryParameter, hj]

private theorem kernel_support (q : ℕ) (hq : 0 < q) (s t : State q) :
    0 < kernel q (parryParameter q) s t ↔
      (t.1 = !s.1 ∧ t.2.val = 0) ∨
      (t.1 = s.1 ∧ t.2.val = s.2.val + 1) := by
  have hp := parameter_positive q hq
  unfold kernel
  split_ifs with h₀ h₁
  · exact iff_of_true (div_pos hp.1 (hp.2 s.2)) (Or.inl h₀)
  · exact iff_of_true (div_pos (mul_pos hp.1 (hp.2 t.2)) (hp.2 s.2)) (Or.inr h₁)
  · simp [h₀, h₁]

private theorem matrix_coefficient (q : ℕ) (i j : Fin q) (g : Sign) :
    ((resetMatrix q) i j).coeff g =
      if (j.val = 0 ∧ g = ofAdd true) ∨ (j.val = i.val + 1 ∧ g = 1)
        then 1 else 0 := by
  have hdis : j.val = 0 → j.val ≠ i.val + 1 := by omega
  by_cases h₀ : j.val = 0 <;> by_cases h₁ : j.val = i.val + 1 <;>
    by_cases hg₀ : g = ofAdd true <;> by_cases hg₁ : g = 1 <;>
    simp_all [resetMatrix, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, eq_comm]

private theorem step_coefficient (q : ℕ) (hq : 0 < q) (s t : State q)
    (h : 0 < kernel q (parryParameter q) s t) :
    ((resetMatrix q) s.2 t.2).coeff (ofAdd (xor s.1 t.1)) = 1 := by
  rw [matrix_coefficient]
  obtain h | h := (kernel_support q hq s t).mp h
  · have hx : xor s.1 t.1 = true := by rw [h.1]; cases s.1 <;> rfl
    simp [h.2, hx]
  · have hx : xor s.1 t.1 = false := by rw [h.1]; cases s.1 <;> rfl
    simp [h.2, hx, show ofAdd false = (1 : Sign) from rfl]

/-- A local positive step becomes its actual edge, with the unique number zero. -/
def numberedStep (q : ℕ) (hq : 0 < q)
    (p : {st : State q × State q //
      0 < kernel q (parryParameter q) st.1 st.2}) : Edge (resetMatrix q) × Sign :=
  (⟨p.val.1.2, p.val.2.2, ofAdd (xor p.val.1.1 p.val.2.1),
    ⟨0, by rw [step_coefficient q hq _ _ p.property]; decide⟩⟩,
    ofAdd p.val.1.1)

/-- Encode adjacent source coordinates, retaining the absolute group anchor. -/
def encode (q : ℕ) (hq : 0 < q) (x : ResetPath q) :
    History (expandedGraph (resetMatrix q)) where
  val t := numberedStep q hq ⟨(x.val t, x.val (t + 1)), x.property t⟩
  property t := by
    apply Prod.ext
    · rfl
    · change ofAdd (x.val t).1 * ofAdd (xor (x.val t).1 (x.val (t + 1)).1) =
        ofAdd (x.val (t + 1)).1
      cases (x.val t).1 <;> cases (x.val (t + 1)).1 <;> rfl

private theorem edge_support (q : ℕ) (e : Edge (resetMatrix q)) :
    (e.target.val = 0 ∧ e.label = ofAdd true) ∨
      (e.target.val = e.source.val + 1 ∧ e.label = 1) := by
  have hn : 0 < ((resetMatrix q) e.source e.target).coeff e.label :=
    lt_of_le_of_lt (Nat.zero_le e.number.val) e.number.isLt
  rw [matrix_coefficient] at hn
  split_ifs at hn with h
  · exact h
  · omega

/-- Decode the source suffix and the same edge's absolute group coordinate. -/
def decode (q : ℕ) (hq : 0 < q) (y : History (expandedGraph (resetMatrix q))) :
    ResetPath q where
  val t := (toAdd (y.val t).2, (y.val t).1.source)
  property t := by
    have hi : (y.val t).1.target = (y.val (t + 1)).1.source :=
      congrArg Prod.fst (y.property t)
    have hg : (y.val t).2 * (y.val t).1.label = (y.val (t + 1)).2 :=
      congrArg Prod.snd (y.property t)
    apply (kernel_support q hq _ _).mpr
    dsimp only
    obtain h | h := edge_support q (y.val t).1
    · left
      refine ⟨?_, by rw [← hi]; exact h.1⟩
      rw [← hg, h.2]
      change xor (toAdd (y.val t).2) true = !(toAdd (y.val t).2)
      cases toAdd (y.val t).2 <;> rfl
    · right
      refine ⟨?_, by rw [← hi]; exact h.1⟩
      rw [← hg, h.2, mul_one]

private theorem decode_encode (q : ℕ) (hq : 0 < q) (x : ResetPath q) :
    decode q hq (encode q hq x) = x := by
  apply Subtype.ext
  rfl

private theorem edge_ext (q : ℕ) (e f : Edge (resetMatrix q))
    (hs : e.source = f.source) (ht : e.target = f.target) (hl : e.label = f.label)
    (hn : e.number.val = f.number.val) : e = f := by
  rcases e with ⟨i, j, g, n⟩
  rcases f with ⟨i', j', g', n'⟩
  dsimp only at hs ht hl hn
  subst i'
  subst j'
  subst g'
  have h : n = n' := Fin.ext hn
  cases h
  rfl

private theorem encode_decode (q : ℕ) (hq : 0 < q)
    (y : History (expandedGraph (resetMatrix q))) : encode q hq (decode q hq y) = y := by
  apply Subtype.ext
  funext t
  apply Prod.ext
  · have hi : (y.val t).1.target = (y.val (t + 1)).1.source :=
      congrArg Prod.fst (y.property t)
    have hg : (y.val t).2 * (y.val t).1.label = (y.val (t + 1)).2 :=
      congrArg Prod.snd (y.property t)
    have hl : ofAdd (xor (toAdd (y.val t).2) (toAdd (y.val (t + 1)).2)) =
        (y.val t).1.label := by
      rw [← hg]
      change ofAdd (xor (toAdd (y.val t).2)
        (xor (toAdd (y.val t).2) (toAdd (y.val t).1.label))) =
          ofAdd (toAdd (y.val t).1.label)
      rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    have hc : ((resetMatrix q) (y.val t).1.source (y.val t).1.target).coeff
        (y.val t).1.label = 1 := by
      rw [matrix_coefficient]
      simp [edge_support q (y.val t).1]
    have hn : (y.val t).1.number.val = 0 := by have := (y.val t).1.number.isLt; omega
    apply edge_ext
    · rfl
    · exact hi.symm
    · exact hl
    · exact hn.symm
  · rfl

/-- Native product and subtype topologies give a finite-window homeomorphism. -/
def resetHomeomorph (q : ℕ) (hq : 0 < q) :
    ResetPath q ≃ₜ History (expandedGraph (resetMatrix q)) where
  toFun := encode q hq
  invFun := decode q hq
  left_inv := decode_encode q hq
  right_inv := encode_decode q hq
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    apply (continuous_of_discreteTopology : Continuous (numberedStep q hq)).comp
    apply Continuous.subtype_mk
    exact ((continuous_apply t).comp continuous_subtype_val).prodMk
      ((continuous_apply (t + 1)).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    let f : Edge (resetMatrix q) × Sign → State q := fun p => (toAdd p.2, p.1.source)
    exact (continuous_of_discreteTopology : Continuous f).comp
      ((continuous_apply t).comp continuous_subtype_val)

/-- Unit left shift on the actual positive-kernel paths. -/
def resetShift (q : ℕ) (x : ResetPath q) : ResetPath q :=
  ⟨fun t => x.val (t + 1), fun t => by simpa [add_assoc] using x.property (t + 1)⟩

/-- Complement the absolute source sign without changing its suffix. -/
def resetComplement (q : ℕ) (x : ResetPath q) : ResetPath q :=
  ⟨fun t => flip (x.val t), fun t => by
    have h : kernel q (parryParameter q) (flip (x.val t)) (flip (x.val (t + 1))) =
        kernel q (parryParameter q) (x.val t) (x.val (t + 1)) := by
      rcases x.val t with ⟨b, i⟩
      rcases x.val (t + 1) with ⟨d, j⟩
      cases b <;> cases d <;> simp [kernel, D5.S3.TotalVariation.TwistedResetPaths.flip]
    rw [h]
    exact x.property t⟩

/-- This same constructed homeomorphism preserves all numbered coordinates and
intertwines unit time and Boolean complement with the existing left group action. -/
theorem reset_numbered_coding (q : ℕ) (hq : 0 < q) :
    ∃ e : ResetPath q ≃ₜ History (expandedGraph (resetMatrix q)),
      (∀ x t, (e x).val t = numberedStep q hq ⟨(x.val t, x.val (t + 1)), x.property t⟩) ∧
      (∀ y t, (e.symm y).val t = (toAdd (y.val t).2, (y.val t).1.source)) ∧
      (∀ x, e (resetShift q x) =
        D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion.shift (expandedGraph (resetMatrix q)) (e x)) ∧
      (∀ x, e (resetComplement q x) = groupHistory (resetMatrix q) (ofAdd true) (e x)) := by
  refine ⟨resetHomeomorph q hq, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rfl
  · intro x
    apply Subtype.ext
    funext t
    apply Prod.ext
    · apply edge_ext
      · rfl
      · rfl
      · change ofAdd (xor (!(x.val t).1) (!(x.val (t + 1)).1)) =
          ofAdd (xor (x.val t).1 (x.val (t + 1)).1)
        cases (x.val t).1 <;> cases (x.val (t + 1)).1 <;> rfl
      · rfl
    · change ofAdd (!(x.val t).1) = (ofAdd true : Sign) * ofAdd (x.val t).1
      cases (x.val t).1 <;> rfl

#print axioms resetHomeomorph
#print axioms reset_numbered_coding

end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories

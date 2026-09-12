/- GID: D5/S3/Analytic/Convexity/ExtendedFarkas
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/ExtendedFarkas
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Farkas alternative extends to coefficients with two infinities under the four validity constraints. -/

/-
Source: madvorak/duality, revision 7e6502ab40b9ea7d42bd2eadc115b6a8b653392f.
https://github.com/madvorak/duality/tree/7e6502ab40b9ea7d42bd2eadc115b6a8b653392f
Original files: ExtendedFields.lean and FarkasSpecial.lean.
The mathematical source accompanies the work of Martin Dvorak and Vladimir Kolmogorov.
Modified for Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
namespaces and theorem names, unbundled ordered algebra, current notation and APIs,
local use of native normalization facts instead of authored binding declarations,
and removal of unused declarations and the diagnostic Linters import.
The mathematical constructions and quantified contracts are retained.
Retirement: replace with a native declaration at the Mathlib revision actually
adopted by this repository only after that declaration's exact type and direct
instantiation preserve these ordered-scalar and extended-coefficient contracts,
including finite primal/dual attainment and the standard axiom closure.
An upstream acceptance or a declaration on an unadopted revision is insufficient.
The complete upstream and historical Mathlib Apache-2.0 licenses are bundled in
D5/S3/Analytic/Convexity/FarkasAlternative.lean.
-/

/-
Historical EReal provenance: Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the bundled license above.
Authors: Kevin Buzzard.
Mathlib4: 333e2d79fdaee86489af73dee919bc4b66957a52, Mathlib/Data/Real/EReal.lean.
Its Lean3 origin: 2196ab363eb097c008d4497125e0dde23fb36db2, src/data/real/ereal.lean.
Henrik Böving supplied the original instances and extended-field notation.
Richard Copley identified the additive homomorphism needed for finite sums.
-/

import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.Order.Field.Basic
import D5.S3.Analytic.Convexity.FarkasAlternative

open D5.S3.Analytic.Convexity.FarkasAlternative

namespace D5.S3.Analytic.Convexity.ExtendedFarkas

noncomputable section

/-
This entire file is inspired by:
https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean
-/

/-- `Extend F` is the type of values in `F ∪ {⊥, ⊤}` where, informally speaking,
    `⊥` (negative infinity) is stronger than `⊤` (positive infinity). -/
abbrev Extend (F : Type*) := WithBot (WithTop F)

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

-- Henrik Böving helped me with this instance:
instance : AddCommMonoid (Extend F) :=
  inferInstanceAs (AddCommMonoid (WithBot (WithTop F)))

instance : LinearOrder (Extend F) :=
  inferInstanceAs (LinearOrder (WithBot (WithTop F)))

-- Henrik Böving helped me with this instance:
instance : AddCommMonoidWithOne (Extend F) :=
  inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop F)))

instance : BoundedOrder (Extend F) := inferInstanceAs (BoundedOrder (WithBot (WithTop F)))

instance : DecidableRel ((· < ·) : Extend F → Extend F → Prop) := WithBot.decidableLT

/-- The canonical inclusion from `F` to `Extend F` is registered as a coercion. -/
@[coe] def toE : F → Extend F := some ∘ some

instance : Coe F (Extend F) := ⟨toE⟩

namespace EF

/-! ### Coercion -/

/-! ### Addition -/

/-! ### Negation -/

/-- Negation on `Extend F`. -/
def neg : Extend F → Extend F
| ⊥ => ⊤
| ⊤ => ⊥
| (x : F) => toE (-x)

instance : Neg (Extend F) := ⟨EF.neg⟩

instance : SubNegZeroMonoid (Extend F) where
  neg_zero := congr_arg toE neg_zero
  zsmul := zsmulRec

instance : InvolutiveNeg (Extend F) where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : F) => congr_arg toE (neg_neg a)

end EF

-- Henrik Böving authored the original extended-field notation section.
-- Explicit type applications here replace that notation without changing its type.
abbrev NNeg (F : Type*) [AddCommMonoid F] [PartialOrder F] [IsOrderedAddMonoid F] := { a : F // 0 ≤ a }

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

section extras_EF

def EF.smulNN (c : (NNeg F)) : (Extend F) → (Extend F)
| ⊥ => ⊥
| ⊤ => if c = 0 then 0 else ⊤
| (f : F) => toE (c.val * f)

instance : SMulZeroClass (NNeg F) (Extend F) where
  smul := EF.smulNN
  smul_zero (c : (NNeg F)) := congr_arg toE (mul_zero c.val)

-- Richard Copley pointed out that we need this homomorphism:
def RatAddHom : F →+ (Extend F) := ⟨⟨toE, rfl⟩, fun _ _ => rfl⟩

end extras_EF

open scoped Matrix
variable {I J : Type*} [Fintype I] [Fintype J]

section hetero_matrix_products_defs
variable {α γ : Type*} [AddCommMonoid α] [SMul γ α] -- elements come from `α` but weights (coefficients) from `γ`

/-- `dotWeig v w` is the sum of the element-wise products `w i • v i` akin the dot product but heterogeneous
    (mnemonic: "vector times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def dotWeig (v : I → α) (w : I → γ) : α := ∑ i : I, w i • v i

infixl:72 " ᵥ⬝ " => dotWeig

/-- `Matrix.mulWeig M w` is the heterogeneous analogue of the matrix-vector product `Matrix.mulVec M w`
    (mnemonic: "matrix times weights").
    Note that the order of arguments (also with the infix notation) is opposite than in the `SMul` it builds upon. -/
def Matrix.mulWeig (M : Matrix I J α) (w : J → γ) (i : I) : α :=
  M i ᵥ⬝ w

infixr:73 " ₘ* " => Matrix.mulWeig

end hetero_matrix_products_defs

section extended_Farkas

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 666666 in
/-- Just like `inequality_farkas_neg` but for `A` and `b` over `(Extend F)`. -/
theorem extended_farkas [DecidableEq I]
    -- The matrix (LHS)
    (A : Matrix I J (Extend F))
    -- The upper-bounding vector (RHS)
    (b : I → (Extend F))
    -- `A` must not have both `⊥` and `⊤` in the same row
    (hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤))
    -- `A` must not have both `⊥` and `⊤` in the same column
    (hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤))
    -- `A` must not have `⊤` on any row where `b` has `⊤`
    (hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤)
    -- `A` must not have `⊥` on any row where `b` has `⊥`
    (hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥) :
    --
    (∃ x : J → (NNeg F), A ₘ* x ≤ b) ≠ (∃ y : I → (NNeg F), -Aᵀ ₘ* y ≤ 0 ∧ b ᵥ⬝ y < 0) := by
  classical
  have Finset_subtype_univ_sum_eq_subtype_univ_sum_I {β : Type _} {p q : I → Prop} (hpq : p = q)
      [Fintype { a : I // p a }] [Fintype { a : I // q a }] [AddCommMonoid β]
      {f : { a : I // p a } → β} {g : { a : I // q a } → β}
      (hfg : ∀ a : I, ∀ hpa : p a, ∀ hqa : q a, f ⟨a, hpa⟩ = g ⟨a, hqa⟩) :
      Finset.univ.sum f = Finset.univ.sum g := by
    classical
    subst hpq
    congr 1
    · ext a
      simp [toE, EF.neg]
    · funext a
      exact hfg a a.property a.property
  -- Andrew Yang authored this restriction-of-sum argument.
  have Finset_univ_sum_of_zero_when_not_I {β : Type _} [Fintype I] [AddCommMonoid β]
      {f : I → β} (p : I → Prop) [DecidablePred p] (hpf : ∀ a : I, ¬(p a) → f a = 0) :
      Finset.univ.sum f = Finset.univ.sum (fun a : { a : I // p a } => f a.val) := by
    classical
    classical
    trans (Finset.univ.filter p).sum f
    · symm
      apply Finset.sum_subset_zero_on_sdiff
      · apply Finset.subset_univ
      · simpa [toE, EF.neg]
      · intros
        rfl
    · apply Finset.sum_subtype
      simp [toE, EF.neg]
  have Finset_subtype_univ_sum_eq_subtype_univ_sum_J {β : Type _} {p q : J → Prop} (hpq : p = q)
      [Fintype { a : J // p a }] [Fintype { a : J // q a }] [AddCommMonoid β]
      {f : { a : J // p a } → β} {g : { a : J // q a } → β}
      (hfg : ∀ a : J, ∀ hpa : p a, ∀ hqa : q a, f ⟨a, hpa⟩ = g ⟨a, hqa⟩) :
      Finset.univ.sum f = Finset.univ.sum g := by
    classical
    subst hpq
    congr 1
    · ext a
      simp [toE, EF.neg]
    · funext a
      exact hfg a a.property a.property
  have Finset_univ_sum_of_zero_when_not_J {β : Type _} [Fintype J] [AddCommMonoid β]
      {f : J → β} (p : J → Prop) [DecidablePred p] (hpf : ∀ a : J, ¬(p a) → f a = 0) :
      Finset.univ.sum f = Finset.univ.sum (fun a : { a : J // p a } => f a.val) := by
    classical
    classical
    trans (Finset.univ.filter p).sum f
    · symm
      apply Finset.sum_subset_zero_on_sdiff
      · apply Finset.subset_univ
      · simpa [toE, EF.neg]
      · intros
        rfl
    · apply Finset.sum_subtype
      simp [toE, EF.neg]
  have ef_coe_strict_mono : StrictMono (toE (F := F)) :=
    WithBot.coe_strictMono.comp WithTop.coe_strictMono
  have ef_coe_injective : Function.Injective (toE (F := F)) :=
    ef_coe_strict_mono.injective
  have ef_coe_le_coe_iff {x y : F} : (x : Extend F) ≤ (y : Extend F) ↔ x ≤ y :=
    ef_coe_strict_mono.le_iff_le
  have ef_coe_lt_coe_iff {x y : F} : (x : Extend F) < (y : Extend F) ↔ x < y :=
    ef_coe_strict_mono.lt_iff_lt
  have ef_coe_eq_coe_iff {x y : F} : (x : Extend F) = (y : Extend F) ↔ x = y :=
    ef_coe_injective.eq_iff
  have ef_coe_zero : ((0 : F) : Extend F) = 0 := rfl
  have ef_bot_lt_coe (x : F) : (⊥ : Extend F) < x :=
    WithBot.bot_lt_coe _
  have ef_coe_neq_bot (x : F) : (x : Extend F) ≠ ⊥ :=
    (ef_bot_lt_coe x).ne'
  have ef_coe_lt_top (x : F) : (x : Extend F) < ⊤ :=
    WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _
  have ef_coe_neq_top (x : F) : (x : Extend F) ≠ ⊤ :=
    (ef_coe_lt_top x).ne
  have ef_bot_lt_zero : (⊥ : Extend F) < 0 :=
    ef_bot_lt_coe 0
  have ef_zero_neq_bot : (0 : Extend F) ≠ ⊥ :=
    ef_coe_neq_bot 0
  have ef_zero_lt_top : (0 : Extend F) < ⊤ :=
    ef_coe_lt_top 0
  have ef_zero_neq_top : (0 : Extend F) ≠ ⊤ :=
    ef_coe_neq_top 0
  have ef_coe_add (x y : F) : toE (x + y) = toE x + toE y :=
    rfl
  have ef_coe_nonpos {x : F} : x ≤ (0 : Extend F) ↔ x ≤ 0 :=
    ef_coe_le_coe_iff
  have ef_coe_neg' {x : F} : x < (0 : Extend F) ↔ x < 0 :=
    ef_coe_lt_coe_iff
  have ef_add_bot (x : Extend F) : x + ⊥ = ⊥ :=
    WithBot.add_bot x
  have ef_bot_add (x : Extend F) : ⊥ + x = ⊥ :=
    WithBot.bot_add x
  have ef_top_add_top : (⊤ : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_top_add_coe (x : F) : (⊤ : Extend F) + x = ⊤ :=
    rfl
  have ef_coe_add_top (x : F) : (x : Extend F) + ⊤ = ⊤ :=
    rfl
  have ef_coe_neg (x : F) : toE (-x) = -(toE x) := rfl
  have ef_neg_eq_top_iff {x : Extend F} : -x = ⊤ ↔ x = ⊥ :=
    neg_injective.eq_iff' rfl
  have ef_neg_eq_bot_iff {x : Extend F} : -x = ⊥ ↔ x = ⊤ :=
    neg_injective.eq_iff' rfl
  have ef_pos_smul_top {c : (NNeg F)} (hc : 0 < c) : c • (⊤ : (Extend F)) = ⊤ := by
    classical
    change (if c = 0 then 0 else (⊤ : Extend F)) = ⊤
    simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff, hc.ne.symm]
  have ef_smul_top_neq_bot (c : (NNeg F)) : c • (⊤ : (Extend F)) ≠ ⊥ := by
    classical
    change (if c = 0 then 0 else (⊤ : Extend F)) ≠ ⊥
    by_cases hc0 : c = 0 <;> simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff, hc0]
  have ef_smul_coe_neq_bot (c : (NNeg F)) (f : F) : c • toE f ≠ (⊥ : (Extend F)) :=
    ef_coe_neq_bot (c * f)
  have ef_smul_bot (c : (NNeg F)) : c • (⊥ : (Extend F)) = ⊥ :=
    rfl
  have ef_smul_nonbot_neq_bot (c : (NNeg F)) {r : (Extend F)} (hr : r ≠ ⊥) : c • r ≠ ⊥ := by
    classical
    match r with
    | ⊥ => simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hr
    | ⊤ => apply ef_smul_top_neq_bot
    | (f : F) => apply ef_smul_coe_neq_bot
  have ef_zero_smul_nonbot {r : (Extend F)} (hr : r ≠ ⊥) : (0 : (NNeg F)) • r = 0 := by
    classical
    show EF.smulNN 0 r = 0
    simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff, EF.smulNN]
    match r with
    | ⊥ => simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] at hr
    | ⊤ => rfl
    | (f : F) => rfl
  have ef_zero_smul_coe (f : F) : (0 : (NNeg F)) • toE f = 0 :=
    ef_zero_smul_nonbot (ef_coe_neq_bot f)
  have no_bot_dot_weig_zero_I  {v : I → (Extend F)} (hv : ∀ i, v i ≠ ⊥) :
      v ᵥ⬝ (0 : I → (NNeg F)) = (0 : (Extend F)) :=
    Finset.sum_eq_zero (fun (i : I) _ =>
      match hvi : v i with
      | ⊤ => show EF.smulNN 0 ⊤ = 0 by
          change (if (0 : NNeg F) = 0 then (0 : Extend F) else ⊤) = 0
          simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff]
      | ⊥ => False.elim (hv i hvi)
      | (f : F) => ef_zero_smul_coe f)
  have has_bot_dot_weig_nneg_I  {v : I → Extend F} {i : I} (hvi : v i = ⊥) (w : I → NNeg F) :
      v ᵥ⬝ w = (⊥ : Extend F) := by
    apply WithBot.sum_eq_bot_iff.mpr
    exact ⟨i, Finset.mem_univ i, by rw [hvi]; rfl⟩
  have no_bot_dot_weig_nneg_I  {v : I → Extend F} (hv : ∀ i, v i ≠ ⊥) (w : I → NNeg F) :
      v ᵥ⬝ w ≠ (⊥ : Extend F) := by
    intro h
    obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp h
    exact ef_smul_nonbot_neq_bot (w i) (hv i) hi
  have no_bot_has_top_dot_weig_pos_I  {v : I → Extend F} (hv : ∀ a, v a ≠ ⊥) {i : I}
      (hvi : v i = ⊤) (w : I → NNeg F) (hwi : 0 < w i) : v ᵥ⬝ w = ⊤ := by
    let f : I → WithTop F := fun j =>
      (w j • v j : WithBot (WithTop F)).unbot (ef_smul_nonbot_neq_bot (w j) (hv j))
    have hf (j : I) : (f j : WithBot (WithTop F)) = w j • v j :=
      WithBot.coe_unbot _ _
    have hsum : v ᵥ⬝ w = ((∑ j, f j : WithTop F) : WithBot (WithTop F)) := by
      rw [WithBot.coe_sum]
      exact Finset.sum_congr rfl (fun j _ => (hf j).symm)
    rw [hsum]
    apply congr_arg (fun x : WithTop F => (x : WithBot (WithTop F)))
    apply WithTop.sum_eq_top.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply WithBot.coe_injective
    rw [hf, hvi]
    exact ef_pos_smul_top hwi
  have no_bot_has_top_dot_weig_le_I  {v : I → (Extend F)} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
      (w : I → (NNeg F)) {f : F} (hq : v ᵥ⬝ w ≤ f) :
      w i ≤ 0 := by
    classical
    by_contra! contr
    rw [no_bot_has_top_dot_weig_pos_I hv hvi w contr, top_le_iff] at hq
    exact ef_coe_neq_top f hq
  have no_bot_has_top_dot_weig_nneg_le_I  {v : I → (Extend F)} (hv : ∀ a, v a ≠ ⊥) {i : I} (hvi : v i = ⊤)
      (w : I → (NNeg F)) {f : F} (hq : v ᵥ⬝ w ≤ f) :
      w i = 0 :=
    le_antisymm (no_bot_has_top_dot_weig_le_I hv hvi w hq) (w i).property
  have dot_weig_zero_le_zero_I  (v : I → (Extend F)) :
      v ᵥ⬝ (0 : I → (NNeg F)) ≤ (0 : (Extend F)) := by
    classical
    if hv : ∀ i, v i ≠ ⊥ then
      rw [no_bot_dot_weig_zero_I hv]
    else
      push Not at hv
      rw [has_bot_dot_weig_nneg_I]
      · apply bot_le
      · exact hv.choose_spec
  have no_bot_dot_weig_zero_J  {v : J → (Extend F)} (hv : ∀ i, v i ≠ ⊥) :
      v ᵥ⬝ (0 : J → (NNeg F)) = (0 : (Extend F)) :=
    Finset.sum_eq_zero (fun (i : J) _ =>
      match hvi : v i with
      | ⊤ => show EF.smulNN 0 ⊤ = 0 by
          change (if (0 : NNeg F) = 0 then (0 : Extend F) else ⊤) = 0
          simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff]
      | ⊥ => False.elim (hv i hvi)
      | (f : F) => ef_zero_smul_coe f)
  have has_bot_dot_weig_nneg_J  {v : J → Extend F} {i : J} (hvi : v i = ⊥) (w : J → NNeg F) :
      v ᵥ⬝ w = (⊥ : Extend F) := by
    apply WithBot.sum_eq_bot_iff.mpr
    exact ⟨i, Finset.mem_univ i, by rw [hvi]; rfl⟩
  have no_bot_dot_weig_nneg_J  {v : J → Extend F} (hv : ∀ i, v i ≠ ⊥) (w : J → NNeg F) :
      v ᵥ⬝ w ≠ (⊥ : Extend F) := by
    intro h
    obtain ⟨i, _, hi⟩ := WithBot.sum_eq_bot_iff.mp h
    exact ef_smul_nonbot_neq_bot (w i) (hv i) hi
  have no_bot_has_top_dot_weig_pos_J  {v : J → Extend F} (hv : ∀ a, v a ≠ ⊥) {i : J}
      (hvi : v i = ⊤) (w : J → NNeg F) (hwi : 0 < w i) : v ᵥ⬝ w = ⊤ := by
    let f : J → WithTop F := fun j =>
      (w j • v j : WithBot (WithTop F)).unbot (ef_smul_nonbot_neq_bot (w j) (hv j))
    have hf (j : J) : (f j : WithBot (WithTop F)) = w j • v j :=
      WithBot.coe_unbot _ _
    have hsum : v ᵥ⬝ w = ((∑ j, f j : WithTop F) : WithBot (WithTop F)) := by
      rw [WithBot.coe_sum]
      exact Finset.sum_congr rfl (fun j _ => (hf j).symm)
    rw [hsum]
    apply congr_arg (fun x : WithTop F => (x : WithBot (WithTop F)))
    apply WithTop.sum_eq_top.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply WithBot.coe_injective
    rw [hf, hvi]
    exact ef_pos_smul_top hwi
  have no_bot_has_top_dot_weig_le_J  {v : J → (Extend F)} (hv : ∀ a, v a ≠ ⊥) {i : J} (hvi : v i = ⊤)
      (w : J → (NNeg F)) {f : F} (hq : v ᵥ⬝ w ≤ f) :
      w i ≤ 0 := by
    classical
    by_contra! contr
    rw [no_bot_has_top_dot_weig_pos_J hv hvi w contr, top_le_iff] at hq
    exact ef_coe_neq_top f hq
  have no_bot_has_top_dot_weig_nneg_le_J  {v : J → (Extend F)} (hv : ∀ a, v a ≠ ⊥) {i : J} (hvi : v i = ⊤)
      (w : J → (NNeg F)) {f : F} (hq : v ᵥ⬝ w ≤ f) :
      w i = 0 :=
    le_antisymm (no_bot_has_top_dot_weig_le_J hv hvi w hq) (w i).property
  have dot_weig_zero_le_zero_J  (v : J → (Extend F)) :
      v ᵥ⬝ (0 : J → (NNeg F)) ≤ (0 : (Extend F)) := by
    classical
    if hv : ∀ i, v i ≠ ⊥ then
      rw [no_bot_dot_weig_zero_J hv]
    else
      push Not at hv
      rw [has_bot_dot_weig_nneg_J]
      · apply bot_le
      · exact hv.choose_spec
  have Matrix_mul_weig_zero_le_zero  (M : Matrix J I (Extend F)) :
      M ₘ* (0 : I → (NNeg F)) ≤ (0 : J → (Extend F)) := by
    classical
    intro i
    apply dot_weig_zero_le_zero_I
    --
  if hbot : ∃ i : I, b i = ⊥ then
    obtain ⟨i, hi⟩ := hbot
    if hi' : (∀ j : J, A i j ≠ ⊥) then
      convert false_ne_true
      · rw [iff_false, not_exists]
        intro x hAxb
        specialize hAxb i
        rw [hi, le_bot_iff] at hAxb
        exact no_bot_dot_weig_nneg_J hi' x hAxb
      · rw [iff_true]
        use 0
        constructor
        · apply Matrix_mul_weig_zero_le_zero
        · rw [has_bot_dot_weig_nneg_I hi]
          exact ef_bot_lt_zero
    else
      push Not at hi'
      exfalso
      apply hbA
      exact ⟨i, hi', hi⟩
  else
    let I' : Type _ := { i : I // b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥ } -- non-tautological rows
    let J' : Type _ := { j : J // ∀ i' : I', A i'.val j ≠ ⊤ } -- columns that allow non-zero values
    let A' : Matrix I' J' F := -- the new matrix
      Matrix.of (fun i' : I' => fun j' : J' =>
        match matcha : A i'.val j'.val with
        | (f : F) => f
        | ⊥ => False.elim (i'.property.right j' matcha)
        | ⊤ => False.elim (j'.property i' matcha)
      )
    let b' : I' → F := -- the new RHS
      fun i' : I' =>
        match hbi : b i'.val with
        | (f : F) => f
        | ⊥ => False.elim (hbot ⟨i', hbi⟩)
        | ⊤ => False.elim (i'.property.left hbi)
    have sum_to_e_I (f : I' → F) : toE (∑ i, f i) = ∑ i, toE (f i) :=
      map_sum (RatAddHom (F := F)) f Finset.univ
    have sum_to_e_J (f : J' → F) : toE (∑ j, f j) = ∑ j, toE (f j) :=
      map_sum (RatAddHom (F := F)) f Finset.univ
    convert inequality_farkas_neg A' b'
    · constructor
      · intro ⟨x, ineqalities⟩
        use (fun j' : J' => x j'.val)
        constructor
        · intro j'
          exact (x j'.val).property
        intro i'
        rw [←ef_coe_le_coe_iff]
        convert ineqalities i'.val; swap
        · simp only [b']
          split <;> rename_i hbi <;> simp only [hbi]
          · rfl
          · exfalso
            apply hbot
            use i'
            exact hbi
          · exfalso
            apply i'.property.left
            exact hbi
        simp only [Matrix.mulVec, dotProduct, Matrix.mulWeig, dotWeig]
        erw [sum_to_e_J, Finset_univ_sum_of_zero_when_not_J (fun j : J => ∀ i' : I', A i'.val j ≠ ⊤)]
        · congr
          ext j'
          rw [mul_comm]
          simp only [A', Matrix.of_apply]
          split <;> rename_i hAij <;> simp only [hAij]
          · rfl
          · exfalso
            apply i'.property.right
            exact hAij
          · exfalso
            apply j'.property
            exact hAij
        · intro j where_top
          push Not at where_top
          obtain ⟨t, ht⟩ := where_top
          have hxj : x j = 0
          · obtain ⟨e, he⟩ : ∃ e : F, b t = e
            · match hbt : b t.val with
              | (f : F) =>
                exact ⟨_, rfl⟩
              | ⊥ =>
                exfalso
                apply hbot
                use t
                exact hbt
              | ⊤ =>
                exfalso
                apply t.property.left
                exact hbt
            exact no_bot_has_top_dot_weig_nneg_le_J (t.property.right) ht x (he ▸ ineqalities t.val)
          rw [hxj]
          apply ef_zero_smul_nonbot
          apply i'.property.right
      · intro ⟨x, hx, ineqalities⟩
        use (fun j : J => if hj : (∀ i' : I', A i'.val j ≠ ⊤) then ⟨x ⟨j, hj⟩, hx ⟨j, hj⟩⟩ else 0)
        intro i
        if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then
          convert ef_coe_le_coe_iff.mpr (ineqalities ⟨i, hi⟩)
          · unfold Matrix.mulVec dotProduct Matrix.mulWeig dotWeig
            simp_rw [dite_smul]
            erw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro j _
              apply ef_zero_smul_nonbot
              exact hi.right j.val
            · erw [←Finset.sum_coe_sort_eq_attach]
              erw [sum_to_e_J]
              apply Finset_subtype_univ_sum_eq_subtype_univ_sum_J
              · ext
                simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff]
              · intro j hj _
                rw [mul_comm]
                simp only [A', Matrix.of_apply]
                split <;> rename_i hAij <;> simp only [hAij]
                · rfl
                · exfalso
                  apply hi.right
                  exact hAij
                · exfalso
                  exact hj ⟨i, hi⟩ hAij
          · simp only [b']
            split <;> rename_i hbi <;> simp only [hbi]
            · rfl
            · exfalso
              apply hbot
              use i
              exact hbi
            · exfalso
              apply hi.left
              exact hbi
        else
          push Not at hi
          if hbi : b i = ⊤ then
            rw [hbi]
            apply le_top
          else
            obtain ⟨j, hAij⟩ := hi hbi
            convert_to ⊥ ≤ b i
            · apply has_bot_dot_weig_nneg_J hAij
            apply bot_le
    · constructor
      · intro ⟨y, ineqalities, sharpine⟩
        use (fun i' : I' => y i'.val)
        constructor
        · intro i'
          exact (y i'.val).property
        have h0 (i : I) (i_not_I' : ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥)) : y i = 0
        · by_contra contr
          have hyi : 0 < y i
          · cases lt_or_eq_of_le (y i).property with
            | inl hpos =>
              exact hpos
            | inr h0 =>
              exfalso
              apply contr
              ext
              exact h0.symm
          if bi_top : b i = ⊤ then
            have impos : b ᵥ⬝ y = ⊤
            · push Not at hbot
              exact no_bot_has_top_dot_weig_pos_I hbot bi_top y hyi
            rw [impos] at sharpine
            exact not_top_lt sharpine
          else
            push Not at i_not_I'
            obtain ⟨j, Aij_eq_bot⟩ := i_not_I' bi_top
            have htop : ((-Aᵀ) j) ᵥ⬝ y = ⊤
            · refine no_bot_has_top_dot_weig_pos_I ?_ (by simpa [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using Aij_eq_bot) y hyi
              intro k hk
              exact hAj ⟨j, ⟨i, Aij_eq_bot⟩, ⟨k, by simpa [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using hk⟩⟩
            have ineqality : ((-Aᵀ) j) ᵥ⬝ y ≤ 0 := ineqalities j
            rw [htop, top_le_iff] at ineqality
            exact ef_zero_neq_top ineqality
        constructor
        · have hnb (i : I) (i_not_I' : ¬ (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥)) (j : J) : (-Aᵀ) j i ≠ ⊥
          · intro contr
            have btop : ∃ j : J, A i j = ⊤
            · use j
              simpa [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff] using contr
            refine hAi ⟨i, ?_, btop⟩
            push Not at i_not_I'
            apply i_not_I'
            intro bi_eq_top
            apply hAb
            use i
          intro j'
          have inequality : ∑ i : I, y i • (-Aᵀ) j'.val i ≤ 0 := ineqalities j'
          rw [Finset_univ_sum_of_zero_when_not_I (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at inequality
          · rw [←ef_coe_le_coe_iff]
            convert inequality <;> try rfl
            simp only [Matrix.mulVec, dotProduct]
            erw [sum_to_e_I]
            congr
            ext i'
            simp only [A', Matrix.neg_apply, Matrix.transpose_apply, Matrix.of_apply]
            split <;> rename_i hAij <;> simp only [hAij]
            · rewrite [mul_comm]
              rfl
            · exfalso
              apply i'.property.right
              exact hAij
            · exfalso
              apply j'.property
              exact hAij
          · intro i hi
            rw [h0 i hi]
            apply ef_zero_smul_nonbot
            apply hnb
            exact hi
        · unfold dotWeig at sharpine
          rw [Finset_univ_sum_of_zero_when_not_I (fun i : I => b i ≠ ⊤ ∧ ∀ (j : J), A i j ≠ ⊥)] at sharpine
          · unfold dotProduct
            erw [←ef_coe_lt_coe_iff, sum_to_e_I]
            convert sharpine with i' <;> try rfl
            simp only [b']
            split <;> rename_i hbi <;> simp only [hbi]
            · rewrite [mul_comm]
              rfl
            · exfalso
              apply hbot
              use i'
              exact hbi
            · exfalso
              apply i'.property.left
              exact hbi
          · intro i hi
            rw [h0 i hi]
            apply ef_zero_smul_nonbot
            intro contr
            exact hbot ⟨i, contr⟩
      · intro ⟨y, hy, ineqalities, sharpine⟩
        use (fun i : I => if hi : (b i ≠ ⊤ ∧ ∀ j : J, A i j ≠ ⊥) then ⟨y ⟨i, hi⟩, hy ⟨i, hi⟩⟩ else 0)
        constructor
        · intro j
          if hj : (∀ i : I, A i j ≠ ⊤) then
            convert ef_coe_le_coe_iff.mpr (ineqalities ⟨j, fun i' => hj i'.val⟩) <;> try rfl
            simp only [Matrix.mulWeig, Matrix.neg_apply, Matrix.transpose_apply, Pi.zero_apply]
            simp only [dotWeig, dite_smul]
            erw [Finset.sum_dite]
            convert add_zero _
            · apply Finset.sum_eq_zero
              intro i _
              apply ef_zero_smul_nonbot
              intro contr
              rw [Matrix.neg_apply, ef_neg_eq_bot_iff] at contr
              exact hj i contr
            · simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.transpose_apply, ef_coe_neg]
              erw [sum_to_e_I]
              apply Finset_subtype_univ_sum_eq_subtype_univ_sum_I
              · ext
                simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff]
              · intro i hi hif
                rw [mul_comm]
                simp only [A', Matrix.neg_apply, Matrix.of_apply]
                split <;> rename_i hAij <;> simp only [hAij]
                · rfl
                · exfalso
                  apply hi.right
                  exact hAij
                · exfalso
                  apply hj
                  exact hAij
          else
            push Not at hj
            obtain ⟨i, Aij_eq_top⟩ := hj
            unfold Matrix.mulWeig
            rw [has_bot_dot_weig_nneg_I]
            · apply bot_le
            · rwa [Matrix.neg_apply, Matrix.transpose_apply, ef_neg_eq_bot_iff]
        · convert ef_coe_lt_coe_iff.mpr sharpine <;> try rfl
          unfold dotProduct dotWeig
          simp_rw [dite_smul]
          erw [Finset.sum_dite]
          convert add_zero _
          · apply Finset.sum_eq_zero
            intro j _
            apply ef_zero_smul_nonbot
            exact (hbot ⟨j.val, ·⟩)
          · erw [←Finset.sum_coe_sort_eq_attach]
            erw [sum_to_e_I]
            apply Finset_subtype_univ_sum_eq_subtype_univ_sum_I
            · ext
              simp [toE, EF.neg, ef_neg_eq_top_iff, ef_neg_eq_bot_iff]
            · intro i hi _
              rw [mul_comm]
              simp only [b', Matrix.of_apply]
              split <;> rename_i hbi <;> simp only [hbi]
              · rfl
              · exfalso
                exact hbot ⟨i, hbi⟩
              · exfalso
                exact hi.left hbi

end extended_Farkas

end

end D5.S3.Analytic.Convexity.ExtendedFarkas

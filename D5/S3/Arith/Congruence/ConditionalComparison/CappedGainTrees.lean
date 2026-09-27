/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTrees
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: CappedGainTrees. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainTrees.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainGeometric
import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainProbability
import D5.S3.Arith.Congruence.ConditionalComparison.TreeSelection
import Mathlib.Data.Fin.Tuple.Take

/-! Actual finite residual trees, with proved probability caps. -/

namespace Erdos7
namespace FiniteLaw

theorem prob_add_not {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (A : Ω → Prop) [DecidablePred A] : μ.prob A + μ.prob (fun x ↦ ¬ A x) = 1 := by
  rw [prob, prob, ← expect_add]
  convert μ.expect_const 1 using 1
  apply μ.expect_congr
  intro x
  by_cases h : A x <;> simp [h]

theorem sum_subtype_weight {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (A : Ω → Prop) [DecidablePred A] : (∑ x : {x // A x}, μ.weight x) = μ.prob A := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter A) (by simp) μ.weight]
  simp [prob, expect, mul_ite, Finset.sum_filter]

noncomputable def restrict {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (A : Ω → Prop) [DecidablePred A] (hA : 0 < μ.prob A) : FiniteLaw {x // A x} where
  weight x := μ.weight x / μ.prob A
  weight_nonneg x := div_nonneg (μ.weight_nonneg x) hA.le
  weight_sum := by rw [← Finset.sum_div, sum_subtype_weight]; exact div_self hA.ne'

theorem restrict_prob_le {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B] (hA : 0 < μ.prob A) :
    (μ.restrict A hA).prob (fun x ↦ B x) ≤ μ.prob B / μ.prob A := by
  classical
  change (∑ x : {x // A x}, (μ.weight x / μ.prob A) * (if B x then 1 else 0)) ≤ _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hA.le
  rw [← Finset.sum_subtype (Finset.univ.filter A) (by simp)
    (fun x ↦ μ.weight x * (if B x then 1 else 0)), Finset.sum_filter]
  unfold prob expect
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, μ.weight_nonneg]

end FiniteLaw

namespace CappedGain

theorem uniform_prefix_prob {p a d : ℕ} (hp : 0 < p) (u : Prefix p d) (hd : d ≤ a) :
    letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    (FiniteLaw.uniform (Word p a)).prob (fun w ↦ HasPrefix w u hd) = 1 / (p : ℚ)^d := by
  classical
  rw [FiniteLaw.uniform_prob_eq_card]
  rw [← Nat.card_eq_fintype_card, card_prefix_extensions]
  simp only [Word, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : (p : ℚ)^a = (p : ℚ)^(a-d) * (p : ℚ)^d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  rw [he]
  field_simp

def Good {p a : ℕ} (f : ForbiddenPrefixesOf p a) (w : Word p a) : Prop :=
  ∀ i : Fin a, ¬ HasPrefix w (f i.succ) (indexedDepthLe i.succ)

instance {p a : ℕ} (f : ForbiddenPrefixesOf p a) : DecidablePred (Good f) := by
  unfold Good
  infer_instance

theorem good_mass_lower {p a : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a) :
    letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    (p : ℚ) - 2 ≤ ((p : ℚ) - 1) * (FiniteLaw.uniform (Word p a)).prob (Good f) := by
  classical
  letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  let μ := FiniteLaw.uniform (Word p a)
  have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hu := μ.prob_exists_finset_le_sum (Finset.univ : Finset (Fin a))
    (fun i w ↦ HasPrefix w (f i.succ) (indexedDepthLe i.succ))
  have hbad : μ.prob (fun w ↦ ¬ Good f w) ≤
      ∑ i : Fin a, 1 / (p : ℚ)^(i.val+1) := by
    convert hu using 1
    · unfold FiniteLaw.prob FiniteLaw.expect
      apply Finset.sum_congr rfl
      intro w _
      have he : (¬ Good f w) ↔ (∃ i ∈ (Finset.univ : Finset (Fin a)),
          HasPrefix w (f i.succ) (indexedDepthLe i.succ)) := by simp [Good]
      simp only [← he]
    · apply Finset.sum_congr rfl
      intro i _
      exact (uniform_prefix_prob (by omega) (f i.succ) (indexedDepthLe i.succ)).symm
  have hsum : ((p : ℚ)-1) * (∑ i : Fin a, 1 / (p : ℚ)^(i.val+1)) ≤ 1 := by
    rw [Finset.mul_sum]
    have h := beta_sum_le_one (p := (p : ℚ)) (by linarith) a
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa only [beta, mul_one_div] using h
  have h := μ.prob_add_not (Good f)
  have hh := mul_le_mul_of_nonneg_left hbad (show 0 ≤ (p : ℚ)-1 by linarith)
  dsimp only [μ] at *
  nlinarith

theorem good_mass_pos {p a : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a) :
    letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
    0 < (FiniteLaw.uniform (Word p a)).prob (Good f) := by
  letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have h := good_mass_lower hp f
  have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hn := (FiniteLaw.uniform (Word p a)).prob_nonneg (Good f)
  nlinarith

/-- A residual coordinate includes its actual embedding and its avoidance proof. -/
structure Tree (p a : ℕ) (f : ForbiddenPrefixesOf p a) where
  space : Type
  finite : Fintype space
  law : @FiniteLaw space finite
  word : space → Word p a
  avoids : ∀ y d, 0 < d.val → ¬ HasPrefix (word y) (f d) (indexedDepthLe d)

attribute [instance] Tree.finite

noncomputable def fullTree {p a : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a) :
    Tree p a f := by
  classical
  letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  exact {
    space := {w // Good f w}
    finite := inferInstance
    law := (FiniteLaw.uniform (Word p a)).restrict (Good f) (good_mass_pos hp f)
    word := Subtype.val
    avoids := by
      intro y d hd
      let i : Fin a := ⟨d.val-1, by omega⟩
      have he : i.succ = d := Fin.ext (by dsimp [i]; omega)
      intro hprefix
      exact y.property i (forbiddenPrefixOf_congr f y.val he hprefix) }

noncomputable def fullTheta {p a : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a) : ℚ := by
  letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  exact ((p : ℚ)-1) * (FiniteLaw.uniform (Word p a)).prob (Good f)

theorem fullTheta_lower {p a : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a) :
    (p : ℚ)-2 ≤ fullTheta hp f := good_mass_lower hp f

theorem fullTree_prefix_cap {p a d : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p a)
    (u : Prefix p d) (hd : d ≤ a) :
    (fullTree hp f).law.prob (fun y ↦ HasPrefix ((fullTree hp f).word y) u hd) ≤
      beta (p : ℚ) d / fullTheta hp f := by
  classical
  letI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  have h := (FiniteLaw.uniform (Word p a)).restrict_prob_le (Good f)
    (fun w ↦ HasPrefix w u hd) (good_mass_pos hp f)
  rw [uniform_prefix_prob (by omega)] at h
  change ((FiniteLaw.uniform (Word p a)).restrict (Good f) (good_mass_pos hp f)).prob
    (fun w ↦ HasPrefix w.val u hd) ≤ _
  refine h.trans_eq ?_
  unfold beta fullTheta
  have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hne : (p : ℚ)-1 ≠ 0 := by linarith
  field_simp

noncomputable def regularTree {p a : ℕ} (hp : 19 ≤ p) (f : ForbiddenPrefixesOf p a) :
    Tree p a f := by
  classical
  cases p with
  | zero => omega
  | succ q =>
    letI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
    exact {
      space := Word q a
      finite := inferInstance
      law := FiniteLaw.uniform _
      word := regularAvoidMap f
      avoids := regularAvoidMap_avoids f }

theorem regularTree_prefix_cap {p a d : ℕ} (hp : 19 ≤ p) (f : ForbiddenPrefixesOf p a)
    (u : Prefix p d) (hd : d ≤ a) :
    (regularTree hp f).law.prob (fun y ↦ HasPrefix ((regularTree hp f).word y) u hd) ≤
      beta 18 d / 17 := by
  classical
  cases p with
  | zero => omega
  | succ q =>
    letI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
    let μ := FiniteLaw.uniform (Word q a)
    change μ.prob (fun w ↦ HasPrefix (regularAvoidMap f w) u hd) ≤ _
    have hcap : μ.prob (fun w ↦ HasPrefix (regularAvoidMap f w) u hd) ≤ 1 / (q : ℚ)^d := by
      by_cases hex : ∃ w, HasPrefix (regularAvoidMap f w) u hd
      · obtain ⟨v, hv⟩ := hex
        have h := μ.prob_mono (fun w ↦ HasPrefix (regularAvoidMap f w) u hd)
          (fun w ↦ HasPrefix w (Fin.take d hd v) hd) (by
          intro w hw i
          apply Fin.succAbove_right_injective
          exact (hw i).trans (hv i).symm)
        exact h.trans_eq (uniform_prefix_prob (by omega) (Fin.take d hd v) hd)
      · have hz : μ.prob (fun w ↦ HasPrefix (regularAvoidMap f w) u hd) = 0 := by
          convert μ.prob_false using 1
          apply μ.prob_congr
          intro w
          exact iff_false_intro (fun h ↦ hex ⟨w, h⟩)
        rw [hz]
        positivity
    have hq : (18 : ℚ) ≤ q := by exact_mod_cast (show 18 ≤ q by omega)
    have hpow : (18 : ℚ)^d ≤ (q : ℚ)^d := pow_le_pow_left₀ (by norm_num) hq d
    have hdiv := one_div_le_one_div_of_le (show (0 : ℚ) < 18^d by positivity) hpow
    have he : (1 : ℚ)/18^d = beta 18 d / 17 := by unfold beta; ring
    exact hcap.trans (hdiv.trans_eq he)

end CappedGain
end Erdos7

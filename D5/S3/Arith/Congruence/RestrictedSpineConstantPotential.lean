/- GID: D5/S3/Arith/Congruence/RestrictedSpineConstantPotential
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/RestrictedSpineConstantPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct a normalized finite-word law with constant weighted prefix potential. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048

namespace D5.S3.Arith.Congruence.RestrictedSpineConstantPotential

universe u

open scoped BigOperators

/-- Words as iterated products, exposing the next symbol without casts. -/
@[reducible] def Word (A : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => A × Word A n

instance wordFintype {A : Type u} [Fintype A] : (n : ℕ) → Fintype (Word A n)
  | 0 => inferInstanceAs (Fintype PUnit.{u + 1})
  | n + 1 => @instFintypeProd A (Word A n) _ (wordFintype n)

/-- Uniform word weights, expressed recursively. -/
noncomputable def uniformWeight {A : Type u} [Fintype A] :
    (n : ℕ) → Word A n → ℝ
  | 0, _ => 1
  | n + 1, t => uniformWeight n t.2 / Fintype.card A

/-- The potential of the uniform suffix under a matching-prefix kernel. -/
noncomputable def uniformValue (q : ℝ) : List ℝ → ℝ
  | [] => 0
  | w :: ws => (w + uniformValue q ws) / q

/-- The harmonic recursion for a restricted spine. -/
noncomputable def spineValue (q k : ℝ) : List ℝ → ℝ
  | [] => 0
  | w :: ws =>
      (k / (w + uniformValue q ws) + 1 / (w + spineValue q k ws))⁻¹

/-- A side branch releases the remaining suffix; the spine continues. -/
def Admissible {A : Type u} (side : Finset A) (spine : A) :
    (n : ℕ) → Word A n → Prop
  | 0, _ => True
  | n + 1, t => t.1 ∈ side ∨ (t.1 = spine ∧ Admissible side spine n t.2)

/-- Sum of layer weights until the first mismatch of two words. -/
noncomputable def tailKernel {A : Type u} [DecidableEq A] :
    (ws : List ℝ) → Word A ws.length → Word A ws.length → ℝ
  | [], _, _ => 0
  | w :: ws, x, t => if x.1 = t.1 then w + tailKernel ws x.2 t.2 else 0

/-- Explicit recursive test weights; the theorem below proves they form a law. -/
noncomputable def spineWeight {A : Type u} [Fintype A] [DecidableEq A]
    (side : Finset A) (spine : A) :
    (ws : List ℝ) → Word A ws.length → ℝ
  | [], _ => 1
  | w :: ws, t =>
      (if t.1 ∈ side then
        spineValue (Fintype.card A) side.card (w :: ws) /
          (w + uniformValue (Fintype.card A) ws) * uniformWeight ws.length t.2
       else 0) +
      (if t.1 = spine then
        spineValue (Fintype.card A) side.card (w :: ws) /
          (w + spineValue (Fintype.card A) side.card ws) * spineWeight side spine ws t.2
       else 0)

set_option maxHeartbeats 800000 in
/-- Every finite restricted spine has an explicit normalized test law whose
weighted matching-prefix potential is constant at every admissible word. -/
theorem restricted_spine_constant_potential
    {A : Type u} [Fintype A] [DecidableEq A]
    (side : Finset A) (spine : A) (hspine : spine ∉ side)
    (ws : List ℝ) (hw : ∀ w ∈ ws, 0 < w) :
    (∀ t, 0 ≤ spineWeight side spine ws t) ∧
    (∑ t, spineWeight side spine ws t) = 1 ∧
    (∀ t, ¬Admissible side spine ws.length t → spineWeight side spine ws t = 0) ∧
    (∀ x, Admissible side spine ws.length x →
      (∑ t, spineWeight side spine ws t * (1 + tailKernel ws x t)) =
        1 + spineValue (Fintype.card A) side.card ws) := by
  classical
  have : Nonempty A := ⟨spine⟩
  have hq : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hk : 0 ≤ (side.card : ℝ) := Nat.cast_nonneg _
  have aux : ∀ (vs : List ℝ), (∀ w ∈ vs, 0 < w) →
      0 ≤ uniformValue (Fintype.card A) vs ∧
      0 ≤ spineValue (Fintype.card A) side.card vs ∧
      (∀ t, 0 ≤ uniformWeight (A := A) vs.length t) ∧
      (∑ t : Word A vs.length, uniformWeight vs.length t) = 1 ∧
      (∀ x : Word A vs.length,
        (∑ t, uniformWeight vs.length t * tailKernel vs x t) =
          uniformValue (Fintype.card A) vs) ∧
      (∀ t, 0 ≤ spineWeight side spine vs t) ∧
      (∑ t, spineWeight side spine vs t) = 1 ∧
      (∀ t, ¬Admissible side spine vs.length t → spineWeight side spine vs t = 0) ∧
      (∀ x, Admissible side spine vs.length x →
        (∑ t, spineWeight side spine vs t * tailKernel vs x t) =
          spineValue (Fintype.card A) side.card vs) := by
    intro vs
    induction vs with
    | nil =>
        intro _
        simp [uniformValue, spineValue, uniformWeight, spineWeight, tailKernel, Admissible,
          Word]
    | cons w vs ih =>
        intro hpos
        have hw0 : 0 < w := hpos w (by simp)
        have hrest : ∀ z ∈ vs, 0 < z := fun z hz => hpos z (by simp [hz])
        rcases ih hrest with ⟨hu, hv, hun, hum, hup, hsn, hsm, hss, hsp⟩
        have hu0 : 0 < w + uniformValue (Fintype.card A) vs := by linarith
        have hv0 : 0 < w + spineValue (Fintype.card A) side.card vs := by linarith
        have hd : 0 < (side.card : ℝ) / (w + uniformValue (Fintype.card A) vs) +
            1 / (w + spineValue (Fintype.card A) side.card vs) :=
          add_pos_of_nonneg_of_pos (div_nonneg hk hu0.le) (one_div_pos.mpr hv0)
        have hV : 0 < spineValue (Fintype.card A) side.card (w :: vs) :=
          inv_pos.mpr hd
        have match_sum (f : Word A (w :: vs).length → ℝ)
            (x : Word A (w :: vs).length) :
            (∑ t, f t * tailKernel (w :: vs) x t) =
              ∑ t : Word A vs.length, f (x.1, t) * (w + tailKernel vs x.2 t) := by
          change (∑ t : A × Word A vs.length, _) = _
          simp only [Fintype.sum_prod_type, tailKernel, mul_ite, mul_zero]
          rw [Finset.sum_comm]
          simp
        have uniform_mass :
            (∑ t : Word A (w :: vs).length, uniformWeight (w :: vs).length t) = 1 := by
          change (∑ t : A × Word A vs.length, uniformWeight vs.length t.2 /
            (Fintype.card A : ℝ)) = 1
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.sum_div, hum]
          simp [hq.ne']
        have uniform_potential (x : Word A (w :: vs).length) :
            (∑ t, uniformWeight (w :: vs).length t * tailKernel (w :: vs) x t) =
              uniformValue (Fintype.card A) (w :: vs) := by
          rw [match_sum]
          change (∑ t : Word A vs.length,
            (uniformWeight vs.length t / (Fintype.card A : ℝ)) *
              (w + tailKernel vs x.2 t)) =
            (w + uniformValue (Fintype.card A) vs) / (Fintype.card A : ℝ)
          simp_rw [div_mul_eq_mul_div, mul_add]
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hum, hup]
          simp
        have branch_balance :
            (side.card : ℝ) *
                (spineValue (Fintype.card A) side.card (w :: vs) /
                  (w + uniformValue (Fintype.card A) vs)) +
              spineValue (Fintype.card A) side.card (w :: vs) /
                (w + spineValue (Fintype.card A) side.card vs) = 1 := by
          rw [spineValue]
          field_simp [hu0.ne', hv0.ne', hd.ne']
        have spine_mass : (∑ t, spineWeight side spine (w :: vs) t) = 1 := by
          change (∑ t : A × Word A vs.length, _) = 1
          simp only [Fintype.sum_prod_type, spineWeight, Finset.sum_add_distrib,
            Finset.sum_ite_irrel, ← Finset.mul_sum, hum, hsm, mul_one]
          simpa using branch_balance
        refine ⟨(div_nonneg hu0.le hq.le), hV.le, ?_, uniform_mass,
          uniform_potential, ?_, spine_mass, ?_, ?_⟩
        · intro t
          exact div_nonneg (hun t.2) hq.le
        · intro t
          have htu := hun t.2
          have hts := hsn t.2
          simp only [spineWeight]
          split_ifs <;> positivity
        · intro t ht
          have hnside : t.1 ∉ side := fun h => ht (Or.inl h)
          by_cases heq : t.1 = spine
          · have hntail : ¬Admissible side spine vs.length t.2 :=
              fun h => ht (Or.inr ⟨heq, h⟩)
            simp [spineWeight, hspine, heq, hss t.2 hntail]
          · simp [spineWeight, hnside, heq]
        · intro x hx
          rw [match_sum]
          rcases hx with hside | ⟨heq, htail⟩
          · have hne : x.1 ≠ spine := by
              intro heq
              exact hspine (heq ▸ hside)
            simp only [spineWeight, hside, hne, ite_true, ite_false, add_zero]
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
            have inside : (∑ t : Word A vs.length,
                uniformWeight vs.length t * (w + tailKernel vs x.2 t)) =
                w + uniformValue (Fintype.card A) vs := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, hum, hup]
              simp
            rw [inside]
            exact div_mul_cancel₀ _ hu0.ne'
          · have hnside : x.1 ∉ side := heq ▸ hspine
            simp only [spineWeight, heq, hspine, ite_true, ite_false, zero_add]
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
            have inside : (∑ t : Word A vs.length,
                spineWeight side spine vs t * (w + tailKernel vs x.2 t)) =
                w + spineValue (Fintype.card A) side.card vs := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsm, hsp x.2 htail]
              simp
            rw [inside]
            exact div_mul_cancel₀ _ hv0.ne'
  rcases aux ws hw with ⟨_, _, _, _, _, hn, hm, hs, hp⟩
  refine ⟨hn, hm, hs, ?_⟩
  intro x hx
  simp_rw [mul_add, mul_one]
  rw [Finset.sum_add_distrib, hm, hp x hx]

#print axioms restricted_spine_constant_potential

end D5.S3.Arith.Congruence.RestrictedSpineConstantPotential

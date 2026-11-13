/- GID: D5/S3/Quantum/Completion/RawRightGroupPropagation
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawRightGroupPropagation
   mirror-E: none(waiver:raw-unital-magma)
   anchors: []
   utility: none
   digest: Actual group tails preserve all original directed comparisons. -/

import D5.S3.Quantum.Completion.RawUnanchoredReplication
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Common group tails and independent bidirectional-zero tails on a unital magma. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.RawRightGroupPropagation
open D5.S3.Quantum.Completion.RawUnanchoredReplication
universe u v

/-- An actual group of original labels, with the original mixed right associativity.
The embedding preserves the actual unit, product and marker; its image is U-stable. -/
structure LabelGroup {M : Type u} [MulOneClass M] (U : M → M)
    (G : Type v) [Group G] where
  label : G ↪ M
  map_one : label 1 = 1
  map_mul : ∀ g k, label (g*k) = label g * label k
  marker : G → G
  map_marker : ∀ g, label (marker g) = U (label g)
  assoc : ∀ a g k, (a * label g) * label k = a * label (g*k)

variable {M : Type u} [MulOneClass M] {G : Type v} [Group G]
    {U : M → M} {c : M → M → ℝ}

/-- Common actual group tails preserve comparisons on the whole original magma. -/
theorem right_invariant (h : RawCost U c) (L : LabelGroup U G) (a b : M) (g : G) :
    c (a * L.label g) (b * L.label g) = c a b := by
  let F : G → ℝ := fun t => c (a * L.label t) (b * L.label t)
  let R : Set ℝ := Set.range F
  have hne : R.Nonempty := ⟨F 1, ⟨1, rfl⟩⟩
  have hbd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact h.nonneg _ _
  have hm (t : G) : sInf R ≤ F t := csInf_le hbd ⟨t, rfl⟩
  have hstep (t w : G) : F (t*w) ≤ 3*F t - 2*sInf R := by
    have hb := h.balance (a * L.label t) (b * L.label t) (L.label w) (L.label w)
    rw [h.diagonal] at hb
    simp only [← L.map_marker, L.assoc] at hb
    change F (t*w) + F (t*L.marker w) + F (t*L.marker (L.marker w)) =
      3*F t + 3*0 at hb
    linarith [hm (t*L.marker w), hm (t*L.marker (L.marker w))]
  have heq (s : G) : F s = sInf R := by
    have hlow : (F s + 2*sInf R)/3 ≤ sInf R := by
      apply le_csInf hne
      rintro _ ⟨t, rfl⟩
      have ht := hstep t (t⁻¹*s)
      rw [mul_inv_cancel_left] at ht
      linarith
    exact le_antisymm (by linarith) (hm s)
  have hg := (heq g).trans (heq 1).symm
  simpa only [F, L.map_one, mul_one] using hg

/-- The entire bidirectional-zero set, with its inherited group operations.
Neither symmetry of c nor marker stability of this subgroup is asserted. -/
def zeroSubgroup (h : RawCost U c) (L : LabelGroup U G) : Subgroup G where
  carrier := {z | c (L.label z) 1 = 0 ∧ c 1 (L.label z) = 0}
  one_mem' := by simp only [Set.mem_ofPred_eq, L.map_one, h.diagonal, and_self]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    have hf := single h (L.label x) 1 (L.label y) 1
    have hr := single h 1 (L.label x) 1 (L.label y)
    simp only [one_mul, mul_one, hx, hy, hx', hy', ← L.map_mul] at hf hr
    exact ⟨le_antisymm (by linarith) (h.nonneg _ _),
      le_antisymm (by linarith) (h.nonneg _ _)⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    have hf := right_invariant h L (L.label x⁻¹) 1 x
    have hr := right_invariant h L 1 (L.label x⁻¹) x
    simp only [one_mul, ← L.map_mul, inv_mul_cancel, L.map_one] at hf hr
    exact ⟨hf.symm.trans hx', hr.symm.trans hx⟩

/-- Two independent bidirectional-zero tails preserve all original backgrounds. -/
theorem independent_zero_tails (h : RawCost U c) (L : LabelGroup U G)
    (a b : M) (z w : zeroSubgroup h L) :
    c (a * L.label (z : G)) (b * L.label (w : G)) = c a b := by
  let Z := zeroSubgroup h L
  have hiter (n : ℕ) (g : G) : L.label (L.marker^[n] g) = U^[n] (L.label g) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', L.map_marker, ih]
  let T (n : ℕ) (g : Z) : Z :=
    ⟨L.marker^[n] (g : G) * (L.marker^[n] 1)⁻¹, by
      have hf := right_invariant h L (L.label (L.marker^[n] (g : G)))
        (L.label (L.marker^[n] 1)) ((L.marker^[n] 1)⁻¹)
      have hr := right_invariant h L (L.label (L.marker^[n] 1))
        (L.label (L.marker^[n] (g : G))) ((L.marker^[n] 1)⁻¹)
      simp only [← L.map_mul, mul_inv_cancel, L.map_one] at hf hr
      simp only [hiter, L.map_one, sync_iter h] at hf hr
      exact ⟨hf.trans g.property.1, hr.trans g.property.2⟩⟩
  let F : Z × Z → ℝ := fun p => c (a * L.label (p.1 : G)) (b * L.label (p.2 : G))
  let R : Set ℝ := Set.range F
  have hne : R.Nonempty := ⟨F (1,1), ⟨(1,1), rfl⟩⟩
  have hbd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact h.nonneg _ _
  have hm (s t : Z) : sInf R ≤ F (s,t) := csInf_le hbd ⟨(s,t), rfl⟩
  have hzero (s t : Z) : c (L.label (s : G)) (L.label (t : G)) = 0 := by
    have hb := unit_compare h (L.label (s : G)) (L.label (t : G))
    rw [s.property.1, t.property.2] at hb
    exact le_antisymm (by linarith) (h.nonneg _ _)
  have hmark (s t x y : Z) (n : ℕ) :
      c ((a * L.label (s : G)) * U^[n] (L.label (x : G)))
        ((b * L.label (t : G)) * U^[n] (L.label (y : G))) =
        F (s*T n x,t*T n y) := by
    rw [← hiter, ← hiter]
    rw [← right_invariant h L _ _ ((L.marker^[n] 1)⁻¹)]
    simp only [L.assoc, F, T, Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc]
  have hstep (s t x y : Z) : F (s*x,t*y) ≤ 3*F (s,t) - 2*sInf R := by
    have hb := h.balance (a * L.label (s : G)) (b * L.label (t : G))
      (L.label (x : G)) (L.label (y : G))
    rw [hzero] at hb
    have hfirst : c ((a * L.label (s : G)) * L.label (x : G))
        ((b * L.label (t : G)) * L.label (y : G)) = F (s*x,t*y) := by
      simp only [F, Subgroup.coe_mul, L.assoc]
    rw [hfirst, show c ((a * L.label (s : G)) * U (L.label (x : G)))
        ((b * L.label (t : G)) * U (L.label (y : G))) = F (s*T 1 x,t*T 1 y) from hmark s t x y 1,
      show c ((a * L.label (s : G)) * U (U (L.label (x : G))))
        ((b * L.label (t : G)) * U (U (L.label (y : G)))) = F (s*T 2 x,t*T 2 y) from hmark s t x y 2] at hb
    change F (s*x,t*y) + F (s*T 1 x,t*T 1 y) + F (s*T 2 x,t*T 2 y) =
      3*F (s,t) + 3*0 at hb
    linarith [hm (s*T 1 x) (t*T 1 y), hm (s*T 2 x) (t*T 2 y)]
  have heq (p : Z × Z) : F p = sInf R := by
    have hlow : (F p + 2*sInf R)/3 ≤ sInf R := by
      apply le_csInf hne
      rintro _ ⟨⟨s,t⟩, rfl⟩
      have ht := hstep s t (s⁻¹*p.1) (t⁻¹*p.2)
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at ht
      linarith
    exact le_antisymm (by linarith) (hm p.1 p.2)
  have hz := (heq (z,w)).trans (heq (1,1)).symm
  simpa only [F, Subgroup.coe_one, L.map_one, mul_one] using hz

end D5.S3.Quantum.Completion.RawRightGroupPropagation

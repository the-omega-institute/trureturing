/- GID: D5/S3/ConceptDynamics/Attribution/FiniteTableCalibration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FiniteTableCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Table laws transport finite calibrations and preserve fixed mass on support. -/

import D5.S3.ConceptDynamics.Attribution.FixedKernelMass

/-! Transport between finite calibrations and probability laws on their deterministic tables. -/

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass (seedFixedMass)

namespace D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration

universe u v w s

variable {G : Type u} {X : Type v} {Y : Type w}
variable [Group G] [MulAction G X] [MulAction G Y]

local instance (priority := 2000) tableSMul : SMul G (X → Y) where
  smul g t x := g • t (g⁻¹ • x)

local instance (priority := 2000) tableAction : MulAction G (X → Y) where
  toSMul := tableSMul
  one_smul t := funext fun x => by
    change (1 : G) • t ((1 : G)⁻¹ • x) = t x
    rw [inv_one, one_smul, one_smul]
  mul_smul g h t := funext fun x => by
    change (g * h) • t ((g * h)⁻¹ • x) = g • (h • t (h⁻¹ • (g⁻¹ • x)))
    rw [mul_inv_rev, mul_smul h⁻¹, mul_smul g]

private theorem readout_smul (g : G) (t : X → Y) (x : X) :
    (g • t) (g • x) = g • t x := by
  change g • t (g⁻¹ • (g • x)) = _
  rw [inv_smul_smul]

local instance (priority := 2100) tableSubgroupAction (H : Subgroup G) : MulAction H (X → Y) :=
  MulAction.compHom (X → Y) H.subtype

variable [Fintype (X → Y)]

section Pushforward

variable {S : Type s} [Fintype S]

noncomputable def tableLaw (weights : S → ℝ) (f : X → S → Y) (t : X → Y) : ℝ := by
  classical
  exact ∑ s, if (fun x => f x s) = t then weights s else 0

variable [MulAction G S]

/-- Pushing a calibration to its tables preserves the marginal probabilities. It sends
fixed seeds to fixed tables, and invariant weights give an invariant table law. -/
theorem calibration_table_law
    (weights : S → ℝ) (nn : ∀ s, 0 ≤ weights s)
    (total : ∑ s, weights s = 1)
    (f : X → S → Y) (cov : ∀ (g : G) x s, f (g • x) (g • s) = g • f x s)
    [DecidableEq Y] (P : X → Y → ℝ)
    (marginal : ∀ x y, (∑ s, if f x s = y then weights s else 0) = P x y) :
    let p := tableLaw weights f
    (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      ((∀ (g : G) s, weights (g • s) = weights s) →
        ∀ (g : G) t, p (g • t) = p t) ∧
      (∀ x y, (∑ t, if t x = y then p t else 0) = P x y) ∧
      seedFixedMass (G := G) weights ≤ seedFixedMass (G := G) p := by
  classical
  let table (s : S) (x : X) := f x s
  let p := tableLaw weights f
  have equivariant (g : G) (s : S) : table (g • s) = g • table s := by
    apply funext
    intro x
    have eq := (cov g (g⁻¹ • x) s).trans
      (readout_smul g (table s) (g⁻¹ • x)).symm
    simpa only [smul_inv_smul, table] using eq
  have push (A : Finset (X → Y)) :
      (∑ t ∈ A, p t) = ∑ s ∈ univ.filter (fun s => table s ∈ A), weights s := by
    simpa only [p, tableLaw, table, sum_filter] using
      sum_fiberwise_eq_sum_filter univ A table weights
  refine ⟨fun t => by
    unfold tableLaw
    exact sum_nonneg (fun s _ => by split <;> [exact nn s; rfl]),
    (push univ).trans (by simpa using total), ?_, ?_, ?_⟩
  · intro invariant g t
    let moveTable : Equiv.Perm (X → Y) := MulAction.toPerm g
    let moveSeed : Equiv.Perm S := MulAction.toPerm g
    have hit (s : S) : table (g • s) = g • t ↔ table s = t := by
      rw [equivariant]
      exact moveTable.injective.eq_iff
    unfold tableLaw
    rw [← Equiv.sum_comp moveSeed]
    exact sum_congr rfl fun s _ => by
      change (if table (g • s) = g • t then weights (g • s) else 0) =
        (if table s = t then weights s else 0)
      rw [hit, invariant]
  · intro x y
    rw [← sum_filter, push]
    simpa only [sum_filter, mem_filter, mem_univ, true_and, table] using marginal x y
  · unfold seedFixedMass
    rw [push]
    apply sum_le_sum_of_subset_of_nonneg
    · intro s hs
      refine mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      intro h
      exact (equivariant h s).symm.trans (congrArg table ((mem_filter.mp hs).2 h))
    · exact fun s _ _ => nn s

end Pushforward

/-- Restrict an invariant table law to its positive support. Evaluation on that support
realizes its marginals and preserves the mass fixed by a subgroup. -/
theorem positive_table_calibration [DecidableEq Y]
    (H : Subgroup G) (P : X → Y → ℝ) (p : (X → Y) → ℝ)
    (pn : ∀ t, 0 ≤ p t) (pt : ∑ t, p t = 1) (pi : ∀ (g : G) t, p (g • t) = p t)
    (pr : ∀ x y, (∑ t, if t x = y then p t else 0) = P x y) :
    ∃ (U : Type (max v w)) (_ : Fintype U) (_ : MulAction G U)
      (q : U → ℝ) (f : X → U → Y),
      (∀ t, 0 < q t) ∧ (∑ t, q t = 1) ∧ (∀ (g : G) t, q (g • t) = q t) ∧
      (∀ x y, (∑ t, if f x t = y then q t else 0) = P x y) ∧
      (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
      seedFixedMass (G := H) q = seedFixedMass (G := H) p := by
  classical
  let U := {t : X → Y // 0 < p t}
  let action : MulAction G U := {
    smul := fun g t => ⟨g • t.val, pi g t.val ▸ t.property⟩
    one_smul := fun t => Subtype.ext (one_smul G t.val)
    mul_smul := fun g h t => Subtype.ext (mul_smul g h t.val) }
  let _ := action
  let weights (t : U) := p t.val
  let readout (x : X) (t : U) := t.val x
  have supportSum (a : (X → Y) → ℝ) (zero : ∀ t, p t = 0 → a t = 0) :
      (∑ t : U, a t.val) = ∑ t, a t :=
    FiniteKernelStabilizers.row_sum (fun (_ : Unit) => p) (fun _ => pn) () a zero
  refine ⟨U, inferInstance, action, weights, readout, fun t => t.property,
    (supportSum p (fun _ h => h)).trans pt, fun g t => pi g t.val, ?_, ?_, ?_⟩
  · intro x y
    refine (supportSum (fun t => if t x = y then p t else 0) (fun t h => by simp [h])).trans ?_
    exact pr x y
  · exact fun g x t => readout_smul g t.val x
  · unfold seedFixedMass
    simp only [sum_filter]
    have same (t : U) : (∀ h : H, h • t = t) ↔ ∀ h : H, h • t.val = t.val :=
      ⟨fun fixed h => congrArg Subtype.val (fixed h), fun fixed h => Subtype.ext (fixed h)⟩
    trans ∑ t : X → Y, if ∀ h : H, h • t = t then p t else 0
    · simpa only [same, weights] using supportSum
        (fun t => if ∀ h : H, h • t = t then p t else 0) (fun t h => by simp [h])
    · apply sum_congr rfl
      intro t _
      apply ite_congr
      · exact propext ⟨fun fixed h => by
          change (h : G) • t = t
          exact fixed h, fun fixed h => by
          change (h : G) • t = t
          exact fixed h⟩
      · intro _
        rfl
      · intro _
        rfl

end D5.S3.ConceptDynamics.Attribution.FiniteTableCalibration

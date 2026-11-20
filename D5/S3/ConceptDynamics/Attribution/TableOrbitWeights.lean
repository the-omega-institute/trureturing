/- GID: D5/S3/ConceptDynamics/Attribution/TableOrbitWeights
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/TableOrbitWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Event masses of invariant laws are linear combinations of within-orbit frequencies. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Instances.Real.Lemmas
import D5.S3.ConceptDynamics.Attribution.NormalSubgroupFixedMass

/-! Orbit variables for probability laws of finite deterministic readouts. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

universe u v w s

variable {G : Type u} {T I : Type*} [Group G] [MulAction G T] [Fintype T]

private abbrev Orbit := MulAction.orbitRel.Quotient G T

private noncomputable instance : Fintype (Orbit (G := G) (T := T)) := Fintype.ofFinite _

private def orbitOf (t : T) : Orbit (G := G) (T := T) := Quotient.mk'' t

noncomputable def orbitFrequency (A : Finset T) (o : MulAction.orbitRel.Quotient G T) : ℝ := by
  classical
  exact ((A.filter fun t => orbitOf t = o).card : ℝ) /
    ((univ.filter fun t : T => orbitOf t = o).card : ℝ)

open Classical in
private theorem weighted_event_by_orbit (A : Finset T) (p : T → ℝ)
    (invariant : ∀ (g : G) t, p (g • t) = p t) :
    (∑ t ∈ A, p t) =
      ∑ o : Orbit (G := G) (T := T),
        (∑ t ∈ univ.filter (fun t : T => orbitOf t = o), p t) * orbitFrequency A o := by
  classical
  let representative (o : Orbit (G := G) (T := T)) : T := Quotient.out o
  have orbitRep (o : Orbit (G := G) (T := T)) : orbitOf (representative o) = o :=
    Quotient.out_eq o
  have constant (t : T) (o : Orbit (G := G) (T := T)) (h : orbitOf t = o) :
      p t = p (representative o) := by
    obtain ⟨g, hg⟩ := Quotient.exact (h.trans (orbitRep o).symm)
    rw [← hg, invariant]
  have count (B : Finset T) (o : Orbit (G := G) (T := T)) :
      (∑ t ∈ B.filter (fun t : T => orbitOf t = o), p t) =
        ((B.filter fun t : T => orbitOf t = o).card : ℝ) * p (representative o) := by
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro t ht
    exact constant t o (mem_filter.mp ht).2
  rw [← sum_fiberwise_of_maps_to (g := orbitOf (G := G)) (t := univ)
    (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro o _
  rw [count A o, count univ o]
  unfold orbitFrequency
  let n : ℝ := ((univ.filter fun t : T => orbitOf t = o).card : ℝ)
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr <| card_ne_zero.mpr
    ⟨representative o, mem_filter.mpr ⟨mem_univ _, orbitRep o⟩⟩
  change _ = n * p (representative o) * (_ / n)
  rw [mul_comm n, mul_assoc, mul_div, mul_comm n, mul_div_cancel_right₀ _ hn, mul_comm]

/-- Mass constraints on any finite events are equivalent to linear constraints on the
orbit masses. The event indices can include both the row cells and the fixed-table event. -/
theorem invariant_event_masses_iff (event : I → Finset T) (mass : I → ℝ) :
    (∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      (∀ (g : G) t, p (g • t) = p t) ∧ ∀ i, (∑ t ∈ event i, p t) = mass i) ↔
    (∃ z : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
      ∀ i, (∑ o, z o * orbitFrequency (event i) o) = mass i) := by
  classical
  constructor
  · rintro ⟨p, nn, total, invariant, prescribed⟩
    let z (o : Orbit (G := G) (T := T)) := ∑ t ∈ univ.filter (fun t => orbitOf t = o), p t
    refine ⟨z, fun o => sum_nonneg (fun t _ => nn t), ?_, ?_⟩
    · exact (sum_fiberwise_of_maps_to (g := orbitOf (G := G)) (t := univ)
        (fun _ _ => mem_univ _) p).trans total
    · intro i
      exact (weighted_event_by_orbit (event i) p invariant).symm.trans (prescribed i)
  · rintro ⟨z, nn, total, prescribed⟩
    let n (o : Orbit (G := G) (T := T)) : ℝ :=
      ((univ.filter fun t : T => orbitOf t = o).card : ℝ)
    let p (t : T) := z (orbitOf t) / n (orbitOf t)
    have invariant (g : G) (t : T) : p (g • t) = p t := by
      have eq : orbitOf (g • t) = orbitOf t := MulAction.orbitRel.Quotient.quotient_smul_eq
      simp only [p, eq]
    have orbitTotal (o : Orbit (G := G) (T := T)) :
        (∑ t ∈ univ.filter (fun t : T => orbitOf t = o), p t) = z o := by
      calc
        _ = ∑ _t ∈ univ.filter (fun t : T => orbitOf t = o), z o / n o := by
          apply sum_congr rfl
          intro t ht
          simp only [p, (mem_filter.mp ht).2]
        _ = z o := by
          have hn : n o ≠ 0 := Nat.cast_ne_zero.mpr <| card_ne_zero.mpr
            ⟨Quotient.out o, mem_filter.mpr ⟨mem_univ _, Quotient.out_eq o⟩⟩
          rw [sum_const, nsmul_eq_mul]
          change n o * (z o / n o) = _
          rw [mul_comm, div_mul_cancel₀ _ hn]
    refine ⟨p, fun t => div_nonneg (nn _) (Nat.cast_nonneg _), ?_, invariant, ?_⟩
    · rw [← sum_fiberwise_of_maps_to (g := orbitOf (G := G)) (t := univ)
        (fun _ _ => mem_univ _)]
      exact (sum_congr rfl (fun o _ => orbitTotal o)).trans total
    · intro i
      rw [weighted_event_by_orbit (event i) p invariant]
      simp_rw [orbitTotal]
      exact prescribed i

private theorem max_linear_event_mass {O : Type*} [Fintype O] (coefficient : I → O → ℝ)
    (mass : I → ℝ) (score : O → ℝ)
    (feasible : ∃ z : O → ℝ, (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
      ∀ i, (∑ o, z o * coefficient i o) = mass i) :
    ∃ z : O → ℝ, (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
      (∀ i, (∑ o, z o * coefficient i o) = mass i) ∧
      ∀ w : O → ℝ, (∀ o, 0 ≤ w o) → (∑ o, w o) = 1 →
        (∀ i, (∑ o, w o * coefficient i o) = mass i) →
        (∑ o, w o * score o) ≤ ∑ o, z o * score o := by
  let constraints : Set (O → ℝ) :=
    {z | (∑ o, z o) = 1} ∩ ⋂ i, {z | (∑ o, z o * coefficient i o) = mass i}
  let box : Set (O → ℝ) := Set.Icc 0 1
  have closed : IsClosed constraints := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_finsetSum univ fun o _ => continuous_apply o) continuous_const
    · exact isClosed_iInter fun i =>
        isClosed_eq
          (continuous_finsetSum univ fun o _ => (continuous_apply o).mul continuous_const)
          continuous_const
  have compact : IsCompact (box ∩ constraints) := isCompact_Icc.inter_right closed
  have in_constraints (z : O → ℝ) (nn : ∀ o, 0 ≤ z o) (total : (∑ o, z o) = 1)
      (satisfies : ∀ i, (∑ o, z o * coefficient i o) = mass i) : z ∈ box ∩ constraints := by
    refine ⟨⟨nn, fun o => ?_⟩, total, Set.mem_iInter.mpr satisfies⟩
    change z o ≤ (1 : ℝ)
    rw [← total]
    exact single_le_sum (fun j _ => nn j) (mem_univ o)
  obtain ⟨initial, nn, total, satisfies⟩ := feasible
  let objective (z : O → ℝ) : ℝ := ∑ o, z o * score o
  have continuous : Continuous objective :=
    continuous_finsetSum univ fun o _ => (continuous_apply o).mul continuous_const
  obtain ⟨z, ⟨inBox, htotal, matched⟩, optimal⟩ :=
    compact.exists_isMaxOn ⟨initial, in_constraints initial nn total satisfies⟩
      continuous.continuousOn
  refine ⟨z, inBox.1, htotal, Set.mem_iInter.mp matched, ?_⟩
  intro w wn wt wm
  exact optimal (in_constraints w wn wt wm)

/-- The maximum invariant mass of a distinguished event is attained whenever the
prescribed event masses are feasible. The same value is the optimum of the
linear program with variables given by masses of whole orbits. -/
theorem maximal_invariant_event_mass (event : I → Finset T) (mass : I → ℝ) (target : Finset T)
    (feasible : ∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      (∀ (g : G) t, p (g • t) = p t) ∧ ∀ i, (∑ t ∈ event i, p t) = mass i) :
    ∃ z : MulAction.orbitRel.Quotient G T → ℝ,
      (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
      (∀ i, (∑ o, z o * orbitFrequency (event i) o) = mass i) ∧
      (∀ w : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ w o) → (∑ o, w o) = 1 →
        (∀ i, (∑ o, w o * orbitFrequency (event i) o) = mass i) →
        (∑ o, w o * orbitFrequency target o) ≤ ∑ o, z o * orbitFrequency target o) ∧
      (∀ a : ℝ,
        (∃ p : T → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
          (∀ (g : G) t, p (g • t) = p t) ∧ (∀ i, (∑ t ∈ event i, p t) = mass i) ∧
          (∑ t ∈ target, p t) = a) ↔
        (∃ w : MulAction.orbitRel.Quotient G T → ℝ, (∀ o, 0 ≤ w o) ∧ (∑ o, w o) = 1 ∧
          (∀ i, (∑ o, w o * orbitFrequency (event i) o) = mass i) ∧
          (∑ o, w o * orbitFrequency target o) = a)) := by
  obtain ⟨z, nn, total, satisfies, optimal⟩ := max_linear_event_mass
    (fun i => orbitFrequency (G := G) (event i)) mass (orbitFrequency target)
    ((invariant_event_masses_iff event mass).mp feasible)
  refine ⟨z, nn, total, satisfies, optimal, fun a => ?_⟩
  let events : Option I → Finset T := fun i => i.elim target event
  let values : Option I → ℝ := fun i => i.elim a mass
  constructor
  · rintro ⟨p, hp, htotal, invariant, coupling, goalMass⟩
    obtain ⟨w, hw, wtotal, constraints⟩ := (invariant_event_masses_iff events values).mp
      ⟨p, hp, htotal, invariant, fun i => by cases i with
        | none => exact goalMass
        | some i => exact coupling i⟩
    exact ⟨w, hw, wtotal, fun i => constraints (some i), constraints none⟩
  · rintro ⟨w, hw, wtotal, coupling, goalMass⟩
    obtain ⟨p, hp, htotal, invariant, constraints⟩ := (invariant_event_masses_iff events values).mpr
      ⟨w, hw, wtotal, fun i => by cases i with
        | none => exact goalMass
        | some i => exact coupling i⟩
    exact ⟨p, hp, htotal, invariant, fun i => constraints (some i), constraints none⟩

section Calibration

open D5.S3.ConceptDynamics.Attribution.FixedKernelMass (seedFixedMass)

variable {X : Type v} {Y : Type w} {S : Type s}
variable [Fintype (X → Y)] [MulAction G X] [MulAction G Y]
variable [Fintype S] [MulAction G S]

attribute [local instance 2000] NormalSubgroupFixedMass.tableSMul NormalSubgroupFixedMass.tableAction

local instance (priority := 2100) tableSubgroupAction (H : Subgroup G) : MulAction H (X → Y) :=
  MulAction.compHom (X → Y) H.subtype

private theorem calibration_table_law
    (H : Subgroup G) (weights : S → ℝ) (nn : ∀ s, 0 ≤ weights s)
    (total : ∑ s, weights s = 1) (invariant : ∀ (g : G) s, weights (g • s) = weights s)
    (f : X → S → Y) (cov : ∀ (g : G) x s, f (g • x) (g • s) = g • f x s)
    [DecidableEq Y] (P : X → Y → ℝ)
    (marginal : ∀ x y, (∑ s, if f x s = y then weights s else 0) = P x y) :
    ∃ p : (X → Y) → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t) = 1 ∧
      (∀ (g : G) t, p (g • t) = p t) ∧
      (∀ x y, (∑ t ∈ univ.filter (fun t : X → Y => t x = y), p t) = P x y) ∧
      seedFixedMass (G := H) weights ≤ seedFixedMass (G := H) p := by
  classical
  let table (s : S) (x : X) := f x s
  let p (t : X → Y) := ∑ s, if table s = t then weights s else 0
  have equivariant (g : G) (s : S) : table (g • s) = g • table s := by
    apply funext
    intro x
    have eq := (cov g (g⁻¹ • x) s).trans (NormalSubgroupFixedMass.readout_smul g (table s) (g⁻¹ • x)).symm
    simpa only [smul_inv_smul, table] using eq
  have push (A : Finset (X → Y)) :
      (∑ t ∈ A, p t) = ∑ s ∈ univ.filter (fun s => table s ∈ A), weights s := by
    simpa only [p, Finset.sum_filter] using sum_fiberwise_eq_sum_filter univ A table weights
  refine ⟨p, fun t => sum_nonneg (fun s _ => by split <;> [exact nn s; rfl]),
    (push univ).trans (by simpa using total), ?_, ?_, ?_⟩
  · intro g t
    let moveTable : Equiv.Perm (X → Y) := MulAction.toPerm g
    let moveSeed : Equiv.Perm S := MulAction.toPerm g
    have hit (s : S) : table (g • s) = g • t ↔ table s = t := by
      rw [equivariant]
      exact moveTable.injective.eq_iff
    unfold p
    rw [← Equiv.sum_comp moveSeed]
    exact sum_congr rfl (fun s _ => by simp only [moveSeed, MulAction.toPerm_apply, hit, invariant])
  · intro x y
    rw [push]
    simpa only [sum_filter, mem_filter, mem_univ, true_and, table] using marginal x y
  · unfold seedFixedMass
    rw [push]
    apply sum_le_sum_of_subset_of_nonneg
    · intro s hs
      refine mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      intro h
      change (h : G) • table s = table s
      exact (equivariant h.val s).symm.trans (congrArg table ((mem_filter.mp hs).2 h))
    · exact fun s _ _ => nn s

open Classical in
/-- The orbit program bounds every finite calibration. An optimal invariant table law
realizes the kernel and has fixed mass equal to the value of the program. -/
theorem maximal_table_fixed_mass
    [Fintype X] [Fintype Y] [Nonempty X] [DecidableEq Y]
    (H : Subgroup G) (P : X → Y → ℝ) (nn : ∀ x y, 0 ≤ P x y)
    (normalized : ∀ x, ∑ y, P x y = 1)
    (cov : ∀ (g : G) x y, P (g • x) (g • y) = P x y) :
    let cell (xy : X × Y) := univ.filter (fun t : X → Y => t xy.1 = xy.2)
    let fixed := univ.filter (fun t : X → Y => ∀ h : H, h • t = t)
    ∃ z : MulAction.orbitRel.Quotient G (X → Y) → ℝ,
      (∀ o, 0 ≤ z o) ∧ (∑ o, z o) = 1 ∧
      (∀ x y, (∑ o, z o * orbitFrequency (cell (x, y)) o) = P x y) ∧
      (∀ w : MulAction.orbitRel.Quotient G (X → Y) → ℝ,
        (∀ o, 0 ≤ w o) → (∑ o, w o) = 1 →
        (∀ x y, (∑ o, w o * orbitFrequency (cell (x, y)) o) = P x y) →
        (∑ o, w o * orbitFrequency fixed o) ≤ ∑ o, z o * orbitFrequency fixed o) ∧
      (∀ (U : Type s) [Fintype U] [MulAction G U]
        (w : U → ℝ) (f : X → U → Y),
        (∀ s, 0 ≤ w s) → (∑ s, w s = 1) → (∀ (g : G) s, w (g • s) = w s) →
        (∀ x y, (∑ s, if f x s = y then w s else 0) = P x y) →
        (∀ (g : G) x s, f (g • x) (g • s) = g • f x s) →
        seedFixedMass (G := H) w ≤ ∑ o, z o * orbitFrequency fixed o) ∧
      ∃ (U : Type (max v w)) (_ : Fintype U) (_ : MulAction G U)
        (q : U → ℝ) (f : X → U → Y),
        (∀ t, 0 < q t) ∧ (∑ t, q t) = 1 ∧ (∀ (g : G) t, q (g • t) = q t) ∧
        (∀ x y, (∑ t, if f x t = y then q t else 0) = P x y) ∧
        (∀ (g : G) x t, f (g • x) (g • t) = g • f x t) ∧
        seedFixedMass (G := H) q = ∑ o, z o * orbitFrequency fixed o := by
  classical
  let cell (xy : X × Y) : Finset (X → Y) := univ.filter (fun t => t xy.1 = xy.2)
  let fixed : Finset (X → Y) := univ.filter (fun t => ∀ h : H, h • t = t)
  let row (xy : X × Y) := P xy.1 xy.2
  obtain ⟨_, _, _, U, _, _, w, f, positive, total, invariant, marginal, fcov, _⟩ :=
    FixedKernelMass.maximal_fixed_seed_mass.{u,v,w,s} (G := G) P nn normalized cov
  obtain ⟨q, qn, qt, qi, qr, _⟩ :=
    calibration_table_law H w (fun s => (positive s).le) total invariant f fcov P marginal
  obtain ⟨z, zn, zt, zr, maximal, value⟩ := maximal_invariant_event_mass (G := G)
    cell row fixed ⟨q, qn, qt, qi, fun xy => qr xy.1 xy.2⟩
  refine ⟨z, zn, zt, fun x y => zr (x, y), ?_, ?_, ?_⟩
  · intro weights hn ht hr
    exact maximal weights hn ht (fun xy => hr xy.1 xy.2)
  · intro S _ _ mass readout hn ht hi hp hc
    obtain ⟨p, pn, pt, pi, pr, bound⟩ :=
      calibration_table_law H mass hn ht hi readout hc P hp
    obtain ⟨weights, wn, wt, wr, same⟩ :=
      (value (seedFixedMass (G := H) p)).mp ⟨p, pn, pt, pi, fun xy => pr xy.1 xy.2, rfl⟩
    exact bound.trans (same ▸ maximal weights wn wt wr)
  · obtain ⟨p, pn, pt, pi, pr, score⟩ :=
      (value (∑ o, z o * orbitFrequency fixed o)).mpr ⟨z, zn, zt, zr, rfl⟩
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
      simpa only [cell, row, sum_filter] using pr (x, y)
    · exact fun g x t => NormalSubgroupFixedMass.readout_smul g t.val x
    · unfold seedFixedMass
      simp only [sum_filter]
      have same (t : U) : (∀ h : H, h • t = t) ↔ ∀ h : H, h • t.val = t.val :=
        ⟨fun fixed h => congrArg Subtype.val (fixed h), fun fixed h => Subtype.ext (fixed h)⟩
      trans ∑ t : X → Y, if ∀ h : H, h • t = t then p t else 0
      · simpa only [same, weights] using supportSum
          (fun t => if ∀ h : H, h • t = t then p t else 0) (fun t h => by simp [h])
      · simpa only [fixed, sum_filter] using score

end Calibration

end D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

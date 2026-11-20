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

/-! Orbit variables for probability laws of finite deterministic readouts. -/

set_option autoImplicit false

open Finset
open scoped Classical

namespace D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

variable {G T I : Type*} [Group G] [MulAction G T] [Fintype T]

private abbrev Orbit := MulAction.orbitRel.Quotient G T

private noncomputable instance : Fintype (Orbit (G := G) (T := T)) := Fintype.ofFinite _

private def orbitOf (t : T) : Orbit (G := G) (T := T) := Quotient.mk'' t

noncomputable def orbitFrequency (A : Finset T) (o : MulAction.orbitRel.Quotient G T) : ℝ := by
  classical
  exact ((A.filter fun t => orbitOf t = o).card : ℝ) /
    ((univ.filter fun t : T => orbitOf t = o).card : ℝ)

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

end D5.S3.ConceptDynamics.Attribution.TableOrbitWeights

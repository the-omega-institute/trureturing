/- GID: D5/S3/ConceptDynamics/Attribution/UniformOrbitCounts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/UniformOrbitCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integer event counts of equivariant finite seed laws factor through orbit multiplicities. -/

import D5.S3.ConceptDynamics.Attribution.UniformTableCalibration
import D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees

/-! Orbit counts and equivariant seed replication with prescribed integral multiplicities. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts

open D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees (countedDegrees)
open UniformTableCalibration (Orbit orbit orbitCount)

universe u v w

set_option maxHeartbeats 900000 in
open Classical in
theorem realize_orbit_copy_counts {G : Type u} {T : Type v}
    [Group G] [Fintype T] [MulAction G T]
    [Fintype (Orbit G T)] (n : Orbit G T → ℕ) :
    ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
      (∀ (g : G) s, f (g • s) = g • f s) ∧
      (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
        ∀ h : H, (h : G) • f s = f s) ∧
      ∀ A : Finset T, (∑ s : S, if f s ∈ A then (1 : ℕ) else 0) =
        ∑ o : Orbit G T, orbitCount A o * n o := by
  classical
  let m (t : T) : ℕ := n (orbit t)
  have inv (g : G) (t : T) : m (g • t) = m t := by
    exact congrArg n MulAction.orbitRel.Quotient.quotient_smul_eq
  obtain ⟨S, _, _, f, equiv, fixed, counts⟩ := UniformTableCalibration.SeedCopies.exact_card_count m inv
  refine ⟨S, inferInstance, inferInstance, f, equiv, fixed, fun A => ?_⟩
  calc
    _ = ∑ t : T, if t ∈ A then m t else 0 := by
      have hc := counts (fun t => t ∈ A)
      convert hc using 2 <;> congr 1
    _ = _ := ?_
  rw [← Finset.sum_filter]
  have hA : (univ.filter fun t => t ∈ A) = A := by ext t; simp
  rw [hA]
  rw [← Finset.sum_fiberwise_of_maps_to (g := orbit (G := G)) (t := univ)
    (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro o _
  unfold orbitCount
  calc
    _ = ∑ _t ∈ A.filter (fun t => orbit t = o), n o := by
      exact Finset.sum_congr rfl fun t ht => congrArg n (mem_filter.mp ht).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]


set_option maxHeartbeats 900000 in
open Classical in
theorem count_seed_fibers_by_orbit {G : Type u} {T : Type v} {S : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    [Fintype S] [MulAction G S] (f : S → T)
    (equiv : ∀ (g : G) s, f (g • s) = g • f s) :
    ∃ n : Orbit G T → ℕ, ∀ A : Finset T,
      (∑ s : S, if f s ∈ A then (1 : ℕ) else 0) = ∑ o, orbitCount A o * n o := by
  classical
  let m (t : T) : ℕ := ∑ s : S, if f s = t then 1 else 0
  have invariant (g : G) (t : T) : m (g • t) = m t := by
    unfold m
    let move : Equiv.Perm S := MulAction.toPerm g
    rw [← Equiv.sum_comp move]
    apply Finset.sum_congr rfl
    intro s _
    change (if f (g • s) = g • t then 1 else 0) = (if f s = t then 1 else 0)
    have hit : g • f s = g • t ↔ f s = t :=
      (MulAction.toPerm g : Equiv.Perm T).injective.eq_iff
    rw [equiv, hit]
  let n : Orbit G T → ℕ := fun o => m (Quotient.out o)
  have lifted (t : T) : m t = n (orbit t) := by
    obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (orbit (G := G) t))
    change g • t = Quotient.out (orbit t) at hg
    exact (invariant g t).symm.trans (congrArg m hg)
  refine ⟨n, fun A => ?_⟩
  calc
    (∑ s : S, if f s ∈ A then (1 : ℕ) else 0) = ∑ t ∈ A, m t := by
      simpa only [m, ← Finset.sum_filter] using
        (sum_fiberwise_eq_sum_filter univ A f (fun _ => (1 : ℕ))).symm
    _ = ∑ o, orbitCount A o * n o := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := orbit (G := G)) (t := univ)
        (fun _ _ => mem_univ _)]
      apply Finset.sum_congr rfl
      intro o _
      unfold orbitCount
      calc
        _ = ∑ _t ∈ A.filter (fun t => orbit t = o), n o := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [lifted, (mem_filter.mp ht).2]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

open Classical in
/-- Rows count how many members of each orbit lie in the corresponding event. -/
noncomputable def orbitEventMatrix {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    (E : I → Finset T) : (Orbit G T → ℤ) →+ (I → ℤ) where
  toFun n i := ∑ o, (orbitCount (E i) o : ℤ) * n o
  map_zero' := by ext i; simp
  map_add' n k := by ext i; simp [mul_add, sum_add_distrib]


set_option maxHeartbeats 900000 in
open Classical in
/-- A feasible integer degree realizes all event counts on one equivariant seed set,
with subgroup fixedness reflected by the seed map. -/
theorem orbit_event_counts_match_fiber {G : Type u} {T : Type v} {I : Type w}
    [Group G] [Fintype T] [MulAction G T] [Fintype (Orbit G T)]
    (E : I → Finset T) (w : I → ℤ) (k : ℕ) :
    k ∈ countedDegrees (orbitEventMatrix (G := G) E) w ↔
      ∃ (S : Type v) (_ : Fintype S) (_ : MulAction G S) (f : S → T),
        (∀ (g : G) s, f (g • s) = g • f s) ∧
        (∀ (H : Subgroup G) s, (∀ h : H, (h : G) • s = s) ↔
          ∀ h : H, (h : G) • f s = f s) ∧
        ∀ i, ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℤ) =
          (k : ℤ) * w i := by
  classical
  constructor
  · rintro ⟨n, hn, eq⟩
    let m : Orbit G T → ℕ := fun o => (n o).toNat
    obtain ⟨S, _, _, f, equiv, fixed, counts⟩ := realize_orbit_copy_counts m
    refine ⟨S, inferInstance, inferInstance, f, equiv, fixed, fun i => ?_⟩
    have countEq := congrArg (fun n : ℕ => (n : ℤ)) (counts (E i))
    have equation := congrFun eq i
    change (∑ o, (orbitCount (E i) o : ℤ) * n o) = (k : ℤ) * w i at equation
    have cast_m (o : Orbit G T) : (m o : ℤ) = n o := Int.toNat_of_nonneg (hn o)
    have equation' : ((∑ o, orbitCount (E i) o * m o : ℕ) : ℤ) = (k : ℤ) * w i := by
      simp only [Nat.cast_sum, Nat.cast_mul, cast_m]
      exact equation
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
      countEq.trans equation'
  · rintro ⟨S, _, _, f, equiv, _, cards⟩
    obtain ⟨n, counts⟩ := count_seed_fibers_by_orbit f equiv
    refine ⟨fun o => (n o : ℤ), fun _ => Int.natCast_nonneg _, ?_⟩
    funext i
    have countEq := congrArg (fun n : ℕ => (n : ℤ)) (counts (E i))
    change (∑ o, (orbitCount (E i) o : ℤ) * (n o : ℤ)) = (k : ℤ) * w i
    have useEq : (∑ o, (orbitCount (E i) o : ℤ) * (n o : ℤ)) =
        ((∑ s : S, if f s ∈ E i then (1 : ℕ) else 0) : ℤ) := by
      simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        using countEq.symm
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      using useEq.trans (cards i)


end D5.S3.ConceptDynamics.Attribution.UniformOrbitCounts

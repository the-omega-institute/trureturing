/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyCharge
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyRow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: The native charge scan selects the orbit colour anchored at the component maximum. -/

import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk

attribute [local instance] Classical.propDecidable

private def scanStep {k : ℕ} (p : P k) (x : Fin (2 * k))
    (best : ℕ × Bool) (n : ℕ) : ℕ × Bool :=
  let u := (walk p x n).val
  if best.1 < u then (u, n % 2 == 0) else best

private theorem scan_spec {k : ℕ} (p : P k) (x : Fin (2 * k))
    (l : List ℕ) (best : ℕ × Bool)
    (hl : ∀ n ∈ l, n < 2 * k)
    (hbest : ∃ v : Fin (2 * k), best.1 = v.val ∧
      best.2 = decide ((matchingPerm p * matchingPerm (e k)).SameCycle x v) ∧
      Component p x v) :
    ∃ v : Fin (2 * k),
      (l.foldl (scanStep p x) best).1 = v.val ∧
      (l.foldl (scanStep p x) best).2 =
        decide ((matchingPerm p * matchingPerm (e k)).SameCycle x v) ∧
      Component p x v ∧ best.1 ≤ v.val ∧
      ∀ n ∈ l, (walk p x n).val ≤ v.val := by
  classical
  induction l generalizing best with
  | nil =>
    obtain ⟨v, hv, hb, hc⟩ := hbest
    exact ⟨v, hv, hb, hc, by omega, by simp⟩
  | cons n ns ih =>
    let next := scanStep p x best n
    have hn : n < 2 * k := hl n (by simp)
    have hnext : ∃ v : Fin (2 * k), next.1 = v.val ∧
        next.2 = decide ((matchingPerm p * matchingPerm (e k)).SameCycle x v) ∧
        Component p x v := by
      dsimp [next, scanStep]
      split
      · exact ⟨walk p x n, rfl, (walk_colour p x n).symm,
          (walk_covers_component p x _).mpr ⟨n, hn, rfl⟩⟩
      · exact hbest
    obtain ⟨v, hv, hb, hc, hbound, hall⟩ :=
      ih next (fun m hm => hl m (by simp [hm])) hnext
    have hmono : best.1 ≤ next.1 := by
      dsimp [next, scanStep]
      split <;> omega
    have hnew : (walk p x n).val ≤ next.1 := by
      dsimp [next, scanStep]
      split <;> omega
    refine ⟨v, hv, hb, hc, hmono.trans hbound, ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hnew.trans hbound
    · exact hall m hm

private theorem charge_with_max {k : ℕ} (p : P k) (x c : Fin (2 * k))
    (hc : Component p x c)
    (hmax : ∀ y, Component p x y → y.val ≤ c.val) :
    charge p x = decide ((matchingPerm p * matchingPerm (e k)).SameCycle x c) := by
  classical
  have hstart : ∃ v : Fin (2 * k), (x.val, true).1 = v.val ∧
      (x.val, true).2 =
        decide ((matchingPerm p * matchingPerm (e k)).SameCycle x v) ∧
      Component p x v := by
    refine ⟨x, rfl, ?_, Relation.ReflTransGen.refl⟩
    have hs : (matchingPerm p * matchingPerm (e k)).SameCycle x x :=
      Perm.SameCycle.refl _ _
    simp [hs]
  obtain ⟨v, _, hbit, hv, _, hall⟩ :=
    scan_spec p x (List.range (2 * k)) (x.val, true)
      (fun n hn => List.mem_range.mp hn) hstart
  obtain ⟨n, hn, hnc⟩ := (walk_covers_component p x c).mp hc
  have hcv : c.val ≤ v.val := by
    rw [← hnc]
    exact hall n (List.mem_range.mpr hn)
  have heq : v = c := Fin.ext (Nat.le_antisymm (hmax v hv) hcv)
  subst v
  exact hbit

private theorem component_symm {k : ℕ} (p : P k) {x y : Fin (2 * k)}
    (h : Component p x y) : Component p y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v h huv ih =>
    apply ih.head
    rcases huv with hp | he
    · left
      change p.val v = u
      rw [← hp]
      exact p.property.1 u
    · right
      change (e k).val v = u
      rw [← he]
      exact (e k).property.1 u

/-- The native bounded fold computes the orbit bipartition with the actual
maximum of each component positive. All product orbits include fixed points. -/
theorem charge_maximum_characterization {k : ℕ} (p : P k) (x : Fin (2 * k)) :
    ∃ c : Fin (2 * k), Component p x c ∧
      (∀ y, Component p x y → y.val ≤ c.val) ∧
      ∀ y, Component p x y → charge p y =
        decide ((matchingPerm p * matchingPerm (e k)).SameCycle y c) := by
  classical
  let C : Finset (Fin (2 * k)) := Finset.univ.filter (Component p x)
  have hne : C.Nonempty := ⟨x,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
  let c := C.max' hne
  have hc : Component p x c := (Finset.mem_filter.mp (C.max'_mem hne)).2
  have hmax : ∀ y, Component p x y → y.val ≤ c.val := by
    intro y hy
    exact C.le_max' y (by simp [C, hy])
  refine ⟨c, hc, hmax, ?_⟩
  intro y hy
  apply charge_with_max p y c ((component_symm p hy).trans hc)
  intro z hz
  exact hmax z (hy.trans hz)

#print axioms charge_maximum_characterization

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge

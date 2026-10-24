/- GID: D5/S1/Words/Sequenceability/UniformRelativePath
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/UniformRelativePath
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A whole-carrier cycle with exact coordinate and label inventories yields the actual relative path, all prefixes, intervals, and total. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.UniformRelativePath

open Equiv
open scoped BigOperators

/-! The composition below is the exact finite-path part of the universal
relative-path construction.  The affine column lift and its endpoint surgery
provide the hypotheses in the characteristic-specific modules. -/

theorem compose_full_path {X G : Type*} [Fintype X] [AddCommGroup G]
    (Q : Perm X) (coord : X → G) (s t : X) (u : G) (M : ℕ)
    (B L : Set G)
    (hcard : Fintype.card X = M + 1)
    (hcycle : Q.IsCycleOn (Finset.univ : Finset X))
    (hqt : Q t = s)
    (hcoord : Function.Injective coord)
    (hs : coord s = 0)
    (ht : coord t = u)
    (hvertices : Set.BijOn coord {x | x ≠ s ∧ x ≠ t} B)
    (hlabels : Set.BijOn (fun x => coord (Q x) - coord x) {x | x ≠ t} L) :
    ∃ v : ℕ → G,
      v 0 = 0 ∧ v M = u ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) B ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M) L ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = u := by
  let orbit : ℕ → X := fun n => (Q ^ n) s
  let v : ℕ → G := fun n => coord (orbit n)
  have hcard' : Fintype.card X = (M + 1) := hcard
  have hbound : Set.InjOn orbit (Set.Iio (M + 1)) := by
    simpa only [hcard'] using hcycle.injOn_pow_apply (Finset.mem_univ s)
  have horbit (z : X) : ∃ n < M + 1, orbit n = z := by
    simpa only [hcard'] using
      hcycle.exists_pow_eq (Finset.mem_univ s) (Finset.mem_univ z)
  have hzero : orbit 0 = s := by rfl
  have hlast : orbit M = t := by
    apply Q.injective
    rw [hqt]
    have hclose := hcycle.pow_card_apply (Finset.mem_univ s)
    simpa only [hcard', pow_succ', Perm.mul_apply] using hclose
  have hvinj : Function.Injective (fun n : Fin (M + 1) => v n.val) := by
    intro i j hij
    exact Fin.ext (hbound i.isLt j.isLt (hcoord hij))
  have hv0 : v 0 = 0 := by simp [v, orbit, hs]
  have hvM : v M = u := by simp [v, orbit, hlast, ht]
  have hinside : Set.BijOn orbit (Set.Ioo 0 M)
      {x | x ≠ s ∧ x ≠ t} := by
    constructor
    · intro n hn
      constructor
      · intro he
        have hn := hbound (x₁ := n) (x₂ := 0)
          (by change n < M + 1; omega) (by change 0 < M + 1; omega)
          (he.trans hzero.symm)
        omega
      · intro he
        have hn := hbound (x₁ := n) (x₂ := M)
          (by change n < M + 1; omega) (by change M < M + 1; omega)
          (he.trans hlast.symm)
        omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi.2)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj.2) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hn0 : n ≠ 0 := by
        intro h
        subst n
        exact hz.1 (heq.symm.trans hzero)
      have hnM : n ≠ M := by
        intro h
        subst n
        exact hz.2 (heq.symm.trans hlast)
      exact ⟨n, ⟨by omega, by omega⟩, heq⟩
  have hpunctured : Set.BijOn orbit (Set.Iio M) {x | x ≠ t} := by
    constructor
    · intro n hn heq
      have hh := hbound (x₁ := n) (x₂ := M)
        (by change n < M + 1; omega) (by change M < M + 1; omega)
        (heq.trans hlast.symm)
      omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hnM : n ≠ M := by
        intro h
        subst n
        exact hz (heq.symm.trans hlast)
      exact ⟨n, (show n < M from by omega), heq⟩
  have hlabels' := hlabels.comp hpunctured
  have hstep (n : ℕ) : orbit (n + 1) = Q (orbit n) := by
    simp only [orbit, pow_succ', Perm.mul_apply]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, (v (i + 1) - v i)) = v n - v 0 :=
    Finset.sum_range_sub v n
  refine ⟨v, hv0, hvM, hvinj, ?_, ?_, ?_, ?_, ?_⟩
  · exact hvertices.comp hinside
  · exact hlabels'.congr (fun n _ => by
      change coord (orbit (n + 1)) - coord (orbit n) =
        coord (Q (orbit n)) - coord (orbit n)
      rw [hstep])
  · intro i j heq
    apply hvinj
    simpa only [hsum, sub_left_inj] using heq
  · intro a b hab hb hzero'
    have hinterval :
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) = v b - v a := by
      rw [Finset.sum_Ico_eq_sub _ hab.le, hsum, hsum]
      abel
    have heq : v b = v a := sub_eq_zero.mp (hinterval.symm.trans hzero')
    have hij := hvinj (a₁ := ⟨b, by omega⟩) (a₂ := ⟨a, by omega⟩) heq
    have heqb : b = a := congrArg Fin.val hij
    omega
  · rw [hsum, hv0, hvM]
    simp

#print axioms compose_full_path

end D5.S1.Words.Sequenceability.UniformRelativePath

/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathFullGeneration
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/WeightedPathFullGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-depth generation of endpoint-rooted A-path block algebras by local kernels. -/

import D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
import D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option autoImplicit false

noncomputable section
open scoped Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open D5.S3.Quantum.Algebra.Knot.WeightedPathReturningBlocks
open D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality

namespace D5.S3.Quantum.Algebra.Knot.WeightedPathFullGeneration

attribute [local instance] Classical.propDecidable
local instance {L : Type*} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

private theorem prefix_bound_and_parity {N n : ℕ} (hN : 2 ≤ N) (v : Fin N)
    (p : LegalPath (SimpleGraph.pathGraph N).Adj n ⟨0, by omega⟩ v) :
    ∀ (j : ℕ) (hj : j ≤ n),
      (p.val ⟨j, by omega⟩).val ≤ j ∧
      (p.val ⟨j, by omega⟩).val % 2 = j % 2 := by
  intro j
  induction j with
  | zero =>
      intro hj
      change (p.val 0).val ≤ 0 ∧ (p.val 0).val % 2 = 0 % 2
      have hs := congrArg Fin.val p.property.1
      change (p.val 0).val = 0 at hs
      rw [hs]
      exact ⟨Nat.le_refl 0, rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨hbound, hparity⟩ := ih (by omega)
      have hadj := p.property.2.2 (⟨j, by omega⟩ : Fin n)
      rw [SimpleGraph.pathGraph_adj] at hadj
      change (p.val ⟨j, by omega⟩).val + 1 = (p.val ⟨j + 1, by omega⟩).val ∨
        (p.val ⟨j + 1, by omega⟩).val + 1 = (p.val ⟨j, by omega⟩).val at hadj
      omega

/-- Exact reachability at every depth in the endpoint-rooted path graph. -/
theorem path_reachable_iff {N n : ℕ} (hN : 2 ≤ N) (v : Fin N) :
    Nonempty (LegalPath (SimpleGraph.pathGraph N).Adj n ⟨0, by omega⟩ v) ↔
      v.val ≤ n ∧ v.val % 2 = n % 2 := by
  constructor
  · rintro ⟨p⟩
    have h := prefix_bound_and_parity hN v p n (by omega)
    have he := congrArg Fin.val p.property.2.1
    change (p.val (Fin.last n)).val ≤ n ∧ (p.val (Fin.last n)).val % 2 = n % 2 at h
    rw [he] at h
    exact h
  · rintro ⟨hbound, hparity⟩
    let a := n - v.val
    have ha : a % 2 = 0 := by dsimp only [a]; omega
    let qval : ℕ → ℕ := fun i => if i ≤ a then i % 2 else i - a
    have qbound (i : ℕ) (hi : i ≤ n) : qval i < N := by
      dsimp only [qval]
      split_ifs with hp
      · omega
      · have hv := v.isLt
        dsimp only [a] at hp ⊢
        omega
    let q : Fin (n + 1) → Fin N := fun i => ⟨qval i.val, qbound i.val (by omega)⟩
    refine ⟨⟨q, ?_, ?_, ?_⟩⟩
    · apply Fin.ext
      simp [q, qval]
    · apply Fin.ext
      dsimp only [q, qval]
      simp only [Fin.val_last]
      split_ifs with hp
      · dsimp only [a] at hp
        omega
      · dsimp only [a]
        omega
    · intro i
      rw [SimpleGraph.pathGraph_adj]
      dsimp only [q, qval]
      simp only [Fin.val_castSucc, Fin.val_succ]
      split_ifs <;> omega

/-- A nonreturning nonempty endpoint at depth m+2 is precisely m+2. -/
theorem path_fresh_endpoint {N m : ℕ} (hN : 2 ≤ N) (v : Fin N)
    (hold : ¬ Nonempty (LegalPath (SimpleGraph.pathGraph N).Adj m ⟨0, by omega⟩ v))
    (hnew : Nonempty (LegalPath (SimpleGraph.pathGraph N).Adj
      (m + 1 + 1) ⟨0, by omega⟩ v)) : v.val = m + 1 + 1 := by
  have hb := (path_reachable_iff hN v).mp hnew
  have hn : ¬ (v.val ≤ m ∧ v.val % 2 = m % 2) := by
    intro h
    exact hold ((path_reachable_iff hN v).mpr h)
  omega

private theorem ascending_coordinates {N n : ℕ} (hN : 2 ≤ N) (v : Fin N)
    (hv : v.val = n)
    (p : LegalPath (SimpleGraph.pathGraph N).Adj n ⟨0, by omega⟩ v) :
    ∀ j (hj : j ≤ n), (p.val ⟨j, by omega⟩).val = j := by
  intro j hj
  refine Nat.decreasingInduction
    (motive := fun k (hk : k ≤ n) => (p.val ⟨k, by omega⟩).val = k) ?_ ?_ hj
  · intro k hk ih
    have hadj := p.property.2.2 (⟨k, hk⟩ : Fin n)
    rw [SimpleGraph.pathGraph_adj] at hadj
    change (p.val ⟨k, by omega⟩).val + 1 = (p.val ⟨k + 1, by omega⟩).val ∨
      (p.val ⟨k + 1, by omega⟩).val + 1 = (p.val ⟨k, by omega⟩).val at hadj
    have hb := (prefix_bound_and_parity hN v p k (by omega)).1
    omega
  · have he := congrArg Fin.val p.property.2.1
    change (p.val (Fin.last n)).val = n
    exact he.trans hv

/-- Every nonreturning path fiber contains at most its strictly ascending path. -/
theorem path_fresh_fiber_subsingleton {N m : ℕ} (hN : 2 ≤ N) (v : Fin N)
    (hold : ¬ Nonempty (LegalPath (SimpleGraph.pathGraph N).Adj m ⟨0, by omega⟩ v)) :
    Subsingleton (LegalPath (SimpleGraph.pathGraph N).Adj
      (m + 1 + 1) ⟨0, by omega⟩ v) := by
  refine ⟨?_⟩
  intro p q
  have hv := path_fresh_endpoint hN v hold ⟨p⟩
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact (ascending_coordinates hN v hv p k.val (by omega)).trans
    (ascending_coordinates hN v hv q k.val (by omega)).symm


section GeneralGraph
variable {L : Type*} [Fintype L] [DecidableEq L]

private theorem full_of_singleton_fresh_fiber
    (R : L → L → Prop) (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ v, 0 < d v) (δ : ℝ) (hδ : 0 < δ)
    (m : ℕ) (s : L)
    (hfresh : ∀ v w : L,
      ¬ Nonempty (LegalPath R m s v) →
      Nonempty (LegalPath R (m + 1 + 1) s v) →
      ¬ Nonempty (LegalPath R m s w) →
      Nonempty (LegalPath R (m + 1 + 1) s w) → v = w)
    (hsmall : ∀ v : L, ¬ Nonempty (LegalPath R m s v) →
      Subsingleton (LegalPath R (m + 1 + 1) s v))
    (U : Subalgebra ℂ (C R (m + 1 + 1) s))
    (hiota : ∀ X : C R (m + 1) s, iota R (m + 1) s X ∈ U)
    (hE : lastProjection R d δ (m + 1) (by omega) s ∈ U) : U = ⊤ := by
  classical
  have hret : returningBlocks R m s ≤ U.toSubmodule := by
    rw [← weighted_path_returning_blocks R hR d hd δ hδ m s]
    apply Submodule.span_le.mpr
    rintro Z ⟨X, Y, rfl⟩
    exact U.mul_mem (U.mul_mem (hiota X) hE) (hiota Y)
  apply top_unique
  intro X _
  by_cases hex : ∃ v : L,
      ¬ Nonempty (LegalPath R m s v) ∧
      Nonempty (LegalPath R (m + 1 + 1) s v)
  · obtain ⟨v, hv, ⟨p⟩⟩ := hex
    let c : ℂ := X v p p
    have hrem : X - c • (1 : C R (m + 1 + 1) s) ∈
        returningBlocks R m s := by
      intro w hw
      ext x y
      have heq : v = w := hfresh v w hv ⟨p⟩ hw ⟨x⟩
      subst w
      let : Subsingleton (LegalPath R (m + 1 + 1) s v) := hsmall v hv
      have hx : x = p := Subsingleton.elim _ _
      have hy : y = p := Subsingleton.elim _ _
      subst x
      subst y
      simp [c]
    have hmem : X - c • (1 : C R (m + 1 + 1) s) ∈ U := hret hrem
    have hc : c • (1 : C R (m + 1 + 1) s) ∈ U := U.smul_mem U.one_mem c
    simpa only [sub_add_cancel] using U.add_mem hmem hc
  · apply hret
    intro v hv
    ext x y
    exact (hex ⟨v, hv, ⟨x⟩⟩).elim

end GeneralGraph

private theorem scalar_base {N n : ℕ} (hN : 2 ≤ N) (hn : n ≤ 1)
    (U : Subalgebra ℂ (C (SimpleGraph.pathGraph N).Adj n ⟨0, by omega⟩)) :
    U = ⊤ := by
  classical
  let v : Fin N := ⟨n, by omega⟩
  obtain ⟨p⟩ := (path_reachable_iff (n := n) hN v).mpr ⟨by simp [v], by simp [v]⟩
  have hsingle : Subsingleton (LegalPath (SimpleGraph.pathGraph N).Adj n
      ⟨0, by omega⟩ v) := by
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    funext k
    apply Fin.ext
    exact (ascending_coordinates (n := n) hN v rfl x k.val (by omega)).trans
      (ascending_coordinates (n := n) hN v rfl y k.val (by omega)).symm
  apply top_unique
  intro X _
  have hscalar : X = (X v p p) • (1 : C (SimpleGraph.pathGraph N).Adj n
      ⟨0, by omega⟩) := by
    funext w
    ext x y
    have hw := (path_reachable_iff hN w).mp ⟨x⟩
    have hwv : w = v := by apply Fin.ext; dsimp [v]; omega
    subst w
    let := hsingle
    have hx : x = p := Subsingleton.elim _ _
    have hy : y = p := Subsingleton.elim _ _
    subst x
    subst y
    simp
  rw [hscalar]
  exact U.smul_mem U.one_mem _

/-- Every endpoint-rooted A-path block algebra is generated by its literal local kernels,
with arbitrary positive weights and delta, at all depths including zero and one. -/
theorem weighted_path_full_generation (N : ℕ) (hN : 2 ≤ N)
    (d : Fin N → ℝ) (hd : ∀ v, 0 < d v) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    Algebra.adjoin ℂ
      {Z : C (SimpleGraph.pathGraph N).Adj n ⟨0, by omega⟩ |
        ∃ (i : ℕ) (hi : 0 < i ∧ i < n),
          Z = localProjection (SimpleGraph.pathGraph N).Adj d δ n ⟨0, by omega⟩ i hi}
      = ⊤ := by
  classical
  induction n with
  | zero => exact scalar_base (n := 0) hN (by omega) _
  | succ n ih =>
    cases n with
    | zero => exact scalar_base (n := 1) hN (by omega) _
    | succ m =>
      let R := (SimpleGraph.pathGraph N).Adj
      let s : Fin N := ⟨0, by omega⟩
      let U : Subalgebra ℂ (C R (m + 1 + 1) s) := Algebra.adjoin ℂ
        {Z | ∃ (i : ℕ) (hi : 0 < i ∧ i < m + 1 + 1),
          Z = localProjection R d δ (m + 1 + 1) s i hi}
      change U = ⊤
      apply full_of_singleton_fresh_fiber R
        (SimpleGraph.pathGraph N).symm d hd δ hδ m s
      · intro v w hv hnv hw hnw
        apply Fin.ext
        exact (path_fresh_endpoint hN v hv hnv).trans
          (path_fresh_endpoint hN w hw hnw).symm
      · intro v hv
        exact path_fresh_fiber_subsingleton hN v hv
      · intro X
        have hle : Algebra.adjoin ℂ
            {Z : C R (m + 1) s | ∃ (i : ℕ) (hi : 0 < i ∧ i < m + 1),
              Z = localProjection R d δ (m + 1) s i hi} ≤
            U.comap (iotaHom R (m + 1) s).toAlgHom := by
          apply Algebra.adjoin_le
          rintro Z ⟨i, hi, rfl⟩
          change iota R (m + 1) s (localProjection R d δ (m + 1) s i hi) ∈ U
          rw [(weighted_path_projection_naturality R d δ).1 (m + 1) s i hi]
          exact Algebra.subset_adjoin ⟨i, ⟨hi.1, by omega⟩, rfl⟩
        have htop : Algebra.adjoin ℂ
            {Z : C R (m + 1) s | ∃ (i : ℕ) (hi : 0 < i ∧ i < m + 1),
              Z = localProjection R d δ (m + 1) s i hi} = ⊤ := ih
        rw [htop] at hle
        exact hle (show X ∈ (⊤ : Subalgebra ℂ (C R (m + 1) s)) from trivial)
      · exact Algebra.subset_adjoin ⟨m + 1, ⟨by omega, by omega⟩, rfl⟩

#print axioms path_reachable_iff
#print axioms path_fresh_endpoint
#print axioms path_fresh_fiber_subsingleton
#print axioms weighted_path_full_generation

end D5.S3.Quantum.Algebra.Knot.WeightedPathFullGeneration

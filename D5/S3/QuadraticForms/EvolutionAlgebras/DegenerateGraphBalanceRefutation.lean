/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.claim; result=D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result; claim=D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.claim
   digest: Degenerate natural bases with graph balances two and one. -/

/-
admission_basis: open-problem-resolution (#21625; Refuted)
escape_witness: none
Direct frozen dependencies: D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction.IsEvolutionAlgebra
  (definition), statement_id: sha256:a405b0a97a285d91b9883661fe6a634975c919dac810b457c81496045475810d;
  no frozen theorem is used.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The claim retains the source's row-square coefficients and both path cardinalities.
Pi.basisFun, LinearMap.mul, LinearMap.compr₂ and LinearEquiv.transvection supply
standard constructions directly; no coordinate-type or standard-basis alias is introduced.
All theorem proof shapes are bind-only after expanding same-delivery helpers:
  cycle_balance_dvd_of_height: proof_shape: bind-only; escape_witness: none; consumer: old_balance
  dvd_graphBalance: proof_shape: bind-only; escape_witness: none; consumer: old_balance
  graphBalance_dvd_cycle: proof_shape: bind-only; escape_witness: none; consumers: old_balance, new_balance
  old_natural: proof_shape: bind-only; escape_witness: none; consumers: evolution, result
  new_natural: proof_shape: bind-only; escape_witness: none; consumer: result
  evolution: proof_shape: bind-only; escape_witness: none; consumer: result
  old_graph: proof_shape: bind-only; escape_witness: none; consumer: result
  new_graph: proof_shape: bind-only; escape_witness: none; consumer: result
  old_balance: proof_shape: bind-only; escape_witness: none; consumer: result
  new_balance: proof_shape: bind-only; escape_witness: none; consumer: result
  result: proof_shape: bind-only; escape_witness: none; consumer: external Question 27
-/

import Mathlib.LinearAlgebra.Transvection.Basic
import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import Mathlib.Combinatorics.Digraph.Basic

/-! Literal conventions for arXiv:2610.22248v1, Question 27 (final question),
and arXiv:2607.15154v1, Definitions 2.1, 2.2, 2.4 and 3.1.
The existing arbitrary-field D5 evolution-algebra predicate is reused.
Paths retain the actual directed edge, including when both opposing edges exist.
The two cardinalities below follow the displayed source formula literally:
a loop belongs to both sets. The nominated counterexamples are loop-free.
The gcd of an arbitrary set of integers is the absolute value of a generator
of its generated ideal; this also gives zero when all cycle balances are zero.
The four-dimensional algebra is over an arbitrary field; the final refutation uses ℚ. -/

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DegenerateGraphBalanceRefutation

attribute [local instance] Classical.propDecidable

open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

/-- Section 1.1: the row coefficient of b_j in b_i squared is nonzero. -/
def associatedGraph {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (B : Module.Basis ι k V) : Digraph ι where
  Adj i j := B.repr (μ (B i) (B i)) j ≠ 0

/-- Definition 2.2: vertices and actual arrows, each traversed in either direction. -/
structure Path {V : Type} (Γ : Digraph V) (n : ℕ) where
  vertex : Fin (n + 1) → V
  edge : Fin n → V × V
  isEdge : ∀ i : Fin n, Γ.Adj (edge i).1 (edge i).2
  traverses : ∀ i : Fin n,
    edge i = (vertex i.castSucc, vertex i.succ) ∨
      edge i = (vertex i.succ, vertex i.castSucc)

/-- Definition 2.2: a non-simple cycle is a path with v_0 = v_n. -/
def IsCycle {V : Type} {Γ : Digraph V} {n : ℕ} (p : Path Γ n) : Prop :=
  p.vertex 0 = p.vertex (Fin.last n)

/-- Definition 2.2, displayed formula: forward count minus backward count. -/
noncomputable def pathBalance {V : Type} {Γ : Digraph V} {n : ℕ}
    (p : Path Γ n) : ℤ :=
  ((Finset.univ.filter fun i : Fin n =>
    p.edge i = (p.vertex i.castSucc, p.vertex i.succ)).card : ℤ) -
  ((Finset.univ.filter fun i : Fin n =>
    p.edge i = (p.vertex i.succ, p.vertex i.castSucc)).card : ℤ)

/-- Definition 2.4: gcd of absolute balances of all cycles, with no length cutoff. -/
noncomputable def graphBalance {V : Type} (Γ : Digraph V) : ℕ :=
  (Submodule.IsPrincipal.generator
    (Ideal.span {z : ℤ | ∃ (n : ℕ) (p : Path Γ n),
      IsCycle p ∧ z = ((pathBalance p).natAbs : ℤ)})).natAbs

/-- The final independently stated question in Question 27, as a universal assertion.
All fields and all finite-dimensional evolution algebras are included, with no
annihilator, perfectness, characteristic or connectedness restriction. -/
def claim : Prop :=
  ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (μ : V →ₗ[k] V →ₗ[k] V),
    IsEvolutionAlgebra μ →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
        (B : Module.Basis ι k V) (F : Module.Basis κ k V),
        (∀ i j : ι, i ≠ j → μ (B i) (B j) = 0) →
        (∀ i j : κ, i ≠ j → μ (F i) (F j) = 0) →
        graphBalance (associatedGraph μ B) = graphBalance (associatedGraph μ F)

end D5.S3.QuadraticForms.EvolutionAlgebras.DegenerateGraphBalanceRefutation

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DegenerateGraphBalanceRefutation
open scoped BigOperators
open Submodule.IsPrincipal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000

private theorem cycle_balance_dvd_of_height {V : Type} {Γ : Digraph V}
    {d : ℕ} (h : V → ZMod d)
    (hn : ∀ i j, Γ.Adj i j → i ≠ j)
    (hs : ∀ i j, Γ.Adj i j → h j = h i + 1)
    {n : ℕ} (p : Path Γ n) (hc : IsCycle p) : (d : ℤ) ∣ pathBalance p := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hb : (pathBalance p : ZMod d) =
      ∑ i : Fin n, ((if p.edge i = (p.vertex i.castSucc, p.vertex i.succ)
        then (1 : ZMod d) else 0) -
        (if p.edge i = (p.vertex i.succ, p.vertex i.castSucc) then 1 else 0)) := by
    simp only [pathBalance, Int.cast_sub, Int.cast_natCast, Finset.sum_sub_distrib]
    congr 1 <;> symm <;> exact Finset.sum_boole _ (Finset.univ : Finset (Fin n))
  have heq (i : Fin n) :
      ((if p.edge i = (p.vertex i.castSucc, p.vertex i.succ) then (1 : ZMod d) else 0) -
      (if p.edge i = (p.vertex i.succ, p.vertex i.castSucc) then 1 else 0)) =
      h (p.vertex i.succ) - h (p.vertex i.castSucc) := by
    have he := p.isEdge i
    rcases p.traverses i with hf | hr
    · have ha : Γ.Adj (p.vertex i.castSucc) (p.vertex i.succ) := by simpa [hf] using he
      have hr : p.edge i ≠ (p.vertex i.succ, p.vertex i.castSucc) := by
        intro hh
        exact hn _ _ ha (congrArg Prod.fst (hf.symm.trans hh))
      rw [ite_eq_left hf, ite_eq_right hr, sub_zero, hs _ _ ha]
      ring
    · have ha : Γ.Adj (p.vertex i.succ) (p.vertex i.castSucc) := by simpa [hr] using he
      have hf : p.edge i ≠ (p.vertex i.castSucc, p.vertex i.succ) := by
        intro hh
        exact hn _ _ ha (congrArg Prod.fst (hr.symm.trans hh))
      rw [ite_eq_right hf, ite_eq_left hr, zero_sub, hs _ _ ha]
      ring
  rw [hb, Finset.sum_congr rfl (fun i _ => heq i), Finset.sum_sub_distrib]
  have ht := (Fin.sum_univ_succ (fun i => h (p.vertex i))).symm.trans
    (Fin.sum_univ_castSucc (fun i => h (p.vertex i)))
  have ht' : (∑ i : Fin n, h (p.vertex i.succ)) -
      ∑ i : Fin n, h (p.vertex i.castSucc) =
      h (p.vertex (Fin.last n)) - h (p.vertex 0) := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using ht
  rw [ht', ← hc, sub_self]

private theorem dvd_graphBalance {V : Type} (Γ : Digraph V) (d : ℕ)
    (hd : ∀ (n : ℕ) (p : Path Γ n), IsCycle p → (d : ℤ) ∣ pathBalance p) :
    d ∣ graphBalance Γ := by
  unfold graphBalance
  change Int.natAbs (d : ℤ) ∣ _
  apply Int.natAbs_dvd_natAbs.mpr
  apply dvd_generator_span_iff.mpr
  rintro z ⟨n, p, hp, rfl⟩
  exact Int.dvd_natAbs.mpr (hd n p hp)

private theorem graphBalance_dvd_cycle {V : Type} {Γ : Digraph V} {n : ℕ}
    (p : Path Γ n) (hc : IsCycle p) : graphBalance Γ ∣ (pathBalance p).natAbs := by
  have hg : generator (Ideal.span {z : ℤ | ∃ (n : ℕ) (p : Path Γ n),
      IsCycle p ∧ z = ((pathBalance p).natAbs : ℤ)}) ∣ ((pathBalance p).natAbs : ℤ) :=
    (mem_iff_generator_dvd _).mp (Ideal.subset_span ⟨n, p, hc, rfl⟩)
  simpa only [graphBalance, Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hg


private def rowMap (k : Type) [Field k] : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  LinearMap.pi ![LinearMap.proj 1, LinearMap.proj 0, LinearMap.proj 1, LinearMap.proj 2]

private def product (k : Type) [Field k] :
    (Fin 4 → k) →ₗ[k] (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  (LinearMap.mul k (Fin 4 → k)).compr₂ (rowMap k)

private def shear (k : Type) [Field k] : (Fin 4 → k) ≃ₗ[k] (Fin 4 → k) :=
  LinearEquiv.transvection (f := LinearMap.proj (R := k) (φ := fun _ : Fin 4 => k) 0)
    (v := Pi.single 3 1) (by simp)

private noncomputable def newBasis (k : Type) [Field k] : Module.Basis (Fin 4) k (Fin 4 → k) :=
  (Pi.basisFun k (Fin 4)).map (shear k)

private theorem old_natural (k : Type) [Field k] (i j : Fin 4) (hij : i ≠ j) :
    product k (Pi.basisFun k (Fin 4) i) (Pi.basisFun k (Fin 4) j) = 0 := by
  ext t
  fin_cases i <;> fin_cases j <;> fin_cases t <;>
    simp_all [product, rowMap, Pi.basisFun_apply]

private theorem new_natural (k : Type) [Field k] (i j : Fin 4) (hij : i ≠ j) :
    product k (newBasis k i) (newBasis k j) = 0 := by
  ext t
  fin_cases i <;> fin_cases j <;> fin_cases t <;>
    simp_all [product, rowMap, newBasis, Module.Basis.map_apply,
      shear, LinearEquiv.transvection, LinearMap.transvection, Pi.basisFun_apply]

private theorem evolution (k : Type) [Field k] :
    D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.IsEvolutionAlgebra
      (product k) := by
  refine ⟨?_, Fin 4, (Pi.basisFun k (Fin 4)), old_natural k⟩
  intro x y
  change rowMap k (x * y) = rowMap k (y * x)
  rw [mul_comm]

private def oldGraph : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3)

private def newGraph : Digraph (Fin 4) where
  Adj i j := oldGraph.Adj i j ∨ (i = 1 ∧ j = 3)

private theorem old_graph (k : Type) [Field k] :
    associatedGraph (product k) (Pi.basisFun k (Fin 4)) = oldGraph := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [associatedGraph, product, rowMap, oldGraph,
      Pi.basisFun_apply, Pi.basisFun_repr]

private theorem new_graph (k : Type) [Field k] :
    associatedGraph (product k) (newBasis k) = newGraph := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [associatedGraph, product, rowMap, newBasis, oldGraph, newGraph,
      Module.Basis.map_apply, Module.Basis.map_repr, shear,
      LinearEquiv.transvection, LinearMap.transvection,
      Pi.basisFun_apply, Pi.basisFun_repr, Pi.single_apply]


private def oldCycle : Path oldGraph 2 where
  vertex := ![0, 1, 0]
  edge := ![(0, 1), (1, 0)]
  isEdge := by intro i; fin_cases i <;> simp [oldGraph]
  traverses := by intro i; fin_cases i <;> simp

private def newCycle : Path newGraph 3 where
  vertex := ![1, 2, 3, 1]
  edge := ![(1, 2), (2, 3), (1, 3)]
  isEdge := by intro i; fin_cases i <;> simp [newGraph, oldGraph]
  traverses := by intro i; fin_cases i <;> simp

private theorem old_balance : graphBalance oldGraph = 2 := by
  apply Nat.dvd_antisymm
  · have hc : IsCycle oldCycle := rfl
    have hb : pathBalance oldCycle = 2 := by
      norm_num [pathBalance, oldCycle, Fin.card_filter_univ_succ, Finset.filter_singleton]
    simpa [hb] using graphBalance_dvd_cycle oldCycle hc
  · apply dvd_graphBalance
    intro n p hp
    apply cycle_balance_dvd_of_height (fun i : Fin 4 => (![0, 1, 0, 1] : Fin 4 → ZMod 2) i) _ _ p hp
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [oldGraph]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [oldGraph] <;> rfl

private theorem new_balance : graphBalance newGraph = 1 := by
  apply Nat.dvd_one.mp
  have hc : IsCycle newCycle := rfl
  have hb : pathBalance newCycle = 1 := by
    norm_num [pathBalance, newCycle, Fin.card_filter_univ_succ, Finset.filter_singleton]
  simpa [hb] using graphBalance_dvd_cycle newCycle hc

theorem result : ¬ claim := by
  intro h
  have hh := h ℚ (Fin 4 → ℚ) (product ℚ) (evolution ℚ)
    (Fin 4) (Fin 4) (Pi.basisFun ℚ (Fin 4)) (newBasis ℚ) (old_natural ℚ) (new_natural ℚ)
  rw [old_graph, new_graph, old_balance, new_balance] at hh
  norm_num at hh

end D5.S3.QuadraticForms.EvolutionAlgebras.DegenerateGraphBalanceRefutation

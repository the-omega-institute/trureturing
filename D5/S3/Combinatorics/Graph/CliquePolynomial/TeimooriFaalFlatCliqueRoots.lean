/- GID: D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.claim; result=D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.result; claim=D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.claim
   digest: A 12-vertex flat biconnected graph has a nonreal clique-polynomial root. -/

/-
proof_shape: cliquePoly: bind-only; source definition; consumers: claim, cliquePoly_R4, result.
proof_shape: IsFlat: bind-only; source definition; consumers: claim, r4_flat.
proof_shape: NoIsolatedTriangle: bind-only; source definition; consumers: claim, r4_noIsolatedTriangle.
proof_shape: claim: bind-only; source proposition; consumers: result.
proof_shape: block: bind-only; private witness data; consumers: r4Adj.
proof_shape: r4Adj: bind-only; private witness relation; consumers: R4, r4DecidableRel.
proof_shape: R4: bind-only; private witness graph; consumers: r4_cliqueFree, r4_flat, hpath.
proof_shape: r4DecidableRel: bind-only; decidability instance; consumers: r4_flat.
proof_shape: cyc: bind-only; private witness data; consumers: hpath, r4_biconnected.
proof_shape: pZ: bind-only; private witness polynomial; consumers: cliquePoly_R4, pZ_map_real.
proof_shape: p: bind-only; private witness polynomial; consumers: p_deriv, p_ne_zero, p_natDegree.
proof_shape: r4_cliqueFree: bind-only; consumers: result.
proof_shape: r4_flat: bind-only; consumers: result.
proof_shape: r4_noIsolatedTriangle: bind-only; consumers: result.
proof_shape: hpath: bind-only; consumers: r4_biconnected.
proof_shape: r4_biconnected: bind-only; consumers: result.
proof_shape: r4_c0: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c1: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c2: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c3: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c4: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c5: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c6: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c7: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c8: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c9: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c10: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c11: bind-only; consumers: cliquePoly_R4.
proof_shape: r4_c12: bind-only; consumers: cliquePoly_R4.
proof_shape: cliquePoly_R4: bind-only; consumers: result.
proof_shape: p_deriv: bind-only; consumers: p_deriv_deriv, p_deriv_ne_zero, p_deriv_root_unique, p_deriv_roots_nodup.
proof_shape: p_deriv_deriv: bind-only; consumers: p_deriv_roots_nodup.
proof_shape: p_ne_zero: bind-only; consumers: p_has_nonreal_root.
proof_shape: p_deriv_ne_zero: bind-only; consumers: p_deriv_roots_nodup, p_deriv_roots_card_le_one.
proof_shape: p_natDegree: bind-only; consumers: p_not_splits.
proof_shape: p_deriv_root_unique: bind-only; consumers: p_deriv_roots_card_le_one.
proof_shape: p_deriv_roots_nodup: bind-only; consumers: p_deriv_roots_card_le_one.
proof_shape: p_deriv_roots_card_le_one: bind-only; consumers: p_not_splits.
proof_shape: p_not_splits: bind-only; consumers: p_has_nonreal_root.
proof_shape: p_has_nonreal_root: bind-only; consumers: result.
proof_shape: pZ_map_real: bind-only; consumers: pZ_map_complex.
proof_shape: pZ_map_complex: bind-only; consumers: result.
proof_shape: result: bind-only; consumers: settles the source conjecture.
escape_witness: none.
admission_basis: open-problem-resolution (#19709; Refuted).
Direct frozen dependencies:
  claim, r4_biconnected, result:
    D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.Biconnected
    statement_id: sha256:94f147c0c9311c7c363894eb04d884810418759dafcde35970dff9dc49d73585
  Other declarations: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The graph predicates and clique polynomial retain the expressions of #19709;
2-connectedness uses the existing Biconnected definition and at least three vertices.
-/

import D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

namespace D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots

open Polynomial

set_option autoImplicit false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Page 1, equation (1): C(G, x) = ∑_{k=0}^{ω(G)} c_k(G)x^k, with c₀(G) = 1. -/
noncomputable def cliquePoly (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ[X] :=
  ∑ j ∈ Finset.range (Fintype.card V + 1), C ((G.cliqueFinset j).card : ℤ) * X ^ j

/-- Page 4, Definition 2.2: "A graph G is called flat if every edge of G belongs to at most two triangles of G." -/
def IsFlat (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v, G.Adj u v → (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card ≤ 2

/-- Page 6, Definition 4.1: "Moreover, a triangle is called isolated if its triangle value is zero." -/
def NoIsolatedTriangle (G : SimpleGraph V) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ∃ x, G.Adj u x ∧ G.Adj v x ∧ G.Adj w x

/-- Page 6, Conjecture 1: "The class of 2-connected K₅-free flat graphs without isolated
triangles has only clique roots. In particular, this class has always the clique root r = −1
of multiplicity 2." -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    3 ≤ Fintype.card V →
    D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected G →
    G.CliqueFree 5 → IsFlat G → NoIsolatedTriangle G →
      (∀ z : ℂ, aeval z (cliquePoly G) = 0 → z.im = 0) ∧ (cliquePoly G).rootMultiplicity (-1) = 2

private abbrev block (i : Fin 4) : Finset (Fin 12) :=
  match i.val with
  | 0 => {0, 1, 4, 5}
  | 1 => {1, 2, 6, 7}
  | 2 => {2, 3, 8, 9}
  | _ => {3, 0, 10, 11}

private abbrev r4Adj (u v : Fin 12) : Prop :=
  ∃ i : Fin 4, u ∈ block i ∧ v ∈ block i ∧ u ≠ v

private def R4 : SimpleGraph (Fin 12) where
  Adj := r4Adj
  symm := ⟨by
    intro u v h
    rcases h with ⟨i, hu, hv, hne⟩
    exact ⟨i, hv, hu, hne.symm⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨i, hu, _, hne⟩
    exact hne rfl⟩

private instance r4DecidableRel : DecidableRel R4.Adj := inferInstanceAs (DecidableRel r4Adj)

set_option maxRecDepth 100000 in
private lemma r4_cliqueFree : R4.CliqueFree 5 := by
  unfold SimpleGraph.CliqueFree
  decide +kernel

private lemma r4_flat : IsFlat R4 := by
  unfold IsFlat
  decide +kernel

private lemma r4_noIsolatedTriangle : NoIsolatedTriangle R4 := by
  unfold NoIsolatedTriangle
  decide +kernel

private abbrev cyc : List (Fin 12) := [4, 5, 0, 10, 11, 3, 8, 9, 2, 6, 7, 1]

private theorem hpath : ∀ v : Fin 12, (cyc.rotate (cyc.idxOf v + 1)).dropLast ≠ [] ∧
    ((cyc.rotate (cyc.idxOf v + 1)).dropLast).IsChain R4.Adj ∧
    v ∉ (cyc.rotate (cyc.idxOf v + 1)).dropLast ∧
    ∀ w, w ≠ v → w ∈ (cyc.rotate (cyc.idxOf v + 1)).dropLast := by
  simp only [cyc]
  decide +kernel

private theorem r4_biconnected :
    D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected R4 := by
  have hconn : ∀ {W : Type} (H : SimpleGraph W) (l : List W) (hne : l ≠ []),
      l.IsChain H.Adj → (∀ x, x ∈ l) → H.Connected := by
    intro W H l hne hc hall
    classical
    refine (SimpleGraph.connected_iff_exists_forall_reachable H).mpr ⟨l.head hne, fun x => ?_⟩
    refine ⟨(SimpleGraph.Walk.ofSupport l hne hc).takeUntil x ?_⟩
    rw [SimpleGraph.Walk.support_ofSupport]
    exact hall x
  have hcyc : cyc ≠ [] ∧ cyc.IsChain R4.Adj := by decide +kernel
  refine ⟨hconn R4 cyc hcyc.1 hcyc.2 (by decide +kernel), fun v => ?_⟩
  obtain ⟨hne, hc, hv, hw⟩ := hpath v
  have hs : ∀ a ∈ (cyc.rotate (cyc.idxOf v + 1)).dropLast, a ∈ ({v}ᶜ : Set (Fin 12)) :=
    fun a ha hav => hv (Set.mem_singleton_iff.mp hav ▸ ha)
  refine hconn _ (((cyc.rotate (cyc.idxOf v + 1)).dropLast).pmap Subtype.mk hs)
    (by rw [Ne, List.pmap_eq_nil_iff]; exact hne)
    (List.isChain_pmap_of_isChain (S := (R4.induce {v}ᶜ).Adj) (f := Subtype.mk)
      (fun a b _ _ h => h) hc hs) ?_
  intro x
  exact List.mem_pmap.mpr ⟨x.1, hw x.1 x.2, rfl⟩

private lemma r4_c0 : (R4.cliqueFinset 0).card = 1 := by
  have h : R4.cliqueFinset 0 = {∅} := by
    ext s
    simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_zero,
      Finset.mem_singleton]
  rw [h, Finset.card_singleton]

private lemma r4_c1 : (R4.cliqueFinset 1).card = 12 := by
  calc
    (R4.cliqueFinset 1).card = (Finset.univ.image fun v : Fin 12 => ({v} : Finset (Fin 12))).card := by
      apply congrArg Finset.card
      ext s
      simp only [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_one,
        Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩
    _ = 12 := by
      rw [Finset.card_image_of_injective _ Finset.singleton_injective]
      rfl

private lemma r4_c2 : (R4.cliqueFinset 2).card = 24 := by
  decide +kernel

private lemma r4_c3 : (R4.cliqueFinset 3).card = 16 := by
  decide +kernel

private lemma r4_c4 : (R4.cliqueFinset 4).card = 4 := by
  decide +kernel

private lemma r4_c5 : (R4.cliqueFinset 5).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 5) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c6 : (R4.cliqueFinset 6).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 6) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c7 : (R4.cliqueFinset 7).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 7) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c8 : (R4.cliqueFinset 8).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 8) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c9 : (R4.cliqueFinset 9).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 9) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c10 : (R4.cliqueFinset 10).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 10) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c11 : (R4.cliqueFinset 11).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 11) r4_cliqueFree).cliqueFinset]
  rfl
private lemma r4_c12 : (R4.cliqueFinset 12).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 5 ≤ 12) r4_cliqueFree).cliqueFinset]
  rfl

private noncomputable def pZ : ℤ[X] := 4 * (1 + X)^4 - 4 * X - 3

private lemma cliquePoly_R4 : cliquePoly R4 = pZ := by
  classical
  norm_num [cliquePoly, Finset.sum_range_succ, r4_c0, r4_c1, r4_c2, r4_c3, r4_c4,
    r4_c5, r4_c6, r4_c7, r4_c8, r4_c9, r4_c10, r4_c11, r4_c12, pZ,
    Polynomial.C_ofNat, Polynomial.C_pow] ; ring

noncomputable section

private def p : ℝ[X] := C 1 + C 12 * X + C 24 * X^2 + C 16 * X^3 + C 4 * X^4

private lemma p_deriv : p.derivative = 16 * (1 + X)^3 - 4 := by
  simp [p, derivative_add, derivative_mul, derivative_pow]
  norm_num [Polynomial.C_ofNat] ; ring

private lemma p_deriv_deriv : p.derivative.derivative = 48 * (1 + X)^2 := by
  rw [p_deriv]
  simp [derivative_sub, derivative_mul, derivative_pow]
  norm_num [Polynomial.C_ofNat] ; ring

private lemma p_ne_zero : p ≠ 0 := by
  intro h
  have hc := congrArg (fun q : ℝ[X] => q.eval 0) h
  norm_num [p] at hc

private lemma p_deriv_ne_zero : p.derivative ≠ 0 := by
  intro h
  have hc := congrArg (fun q : ℝ[X] => q.eval 0) h
  norm_num [p_deriv] at hc

private lemma p_natDegree : p.natDegree = 4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have hdeg : p.degree ≤ (4 : WithBot ℕ) := by
      rw [degree_le_iff_coeff_zero]
      intro n hn
      have hn' : 4 < n := by exact_mod_cast hn
      have h0 : n ≠ 0 := Nat.ne_zero_of_lt hn'
      have h1' : 1 ≠ n := by omega
      have h2 : n ≠ 2 := by omega
      have h3 : n ≠ 3 := by omega
      have h4 : n ≠ 4 := Ne.symm (Nat.ne_of_lt hn')
      simp [p, coeff_add, coeff_one, coeff_X, h0, h1', h2, h3, h4]
    exact natDegree_le_iff_degree_le.mpr hdeg
  · norm_num [p, coeff_add, coeff_one, coeff_C_mul_X_pow, coeff_C, coeff_X]

private lemma p_deriv_root_unique {x y : ℝ}
    (hx : p.derivative.IsRoot x) (hy : p.derivative.IsRoot y) : x = y := by
  have hx' : 4 * (x + 1)^3 = 1 := by
    rw [p_deriv, IsRoot] at hx
    norm_num at hx ⊢
    linarith
  have hy' : 4 * (y + 1)^3 = 1 := by
    rw [p_deriv, IsRoot] at hy
    norm_num at hy ⊢
    linarith
  have hc : (x + 1)^3 = (y + 1)^3 := by linarith
  have hinj : Function.Injective (fun t : ℝ => t ^ 3) := Odd.pow_injective (by decide)
  have hxy : x + 1 = y + 1 := hinj hc
  linarith

private lemma p_deriv_roots_nodup : p.derivative.roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  rw [count_roots]
  by_contra h
  have hm : 1 < p.derivative.rootMultiplicity x := Nat.lt_of_not_le h
  have hr := (one_lt_rootMultiplicity_iff_isRoot p_deriv_ne_zero).mp hm
  have hrr := hr.2
  rw [p_deriv_deriv, IsRoot] at hrr
  have hx : x = -1 := by
    norm_num at hrr
    nlinarith [sq_nonneg (x + 1)]
  subst x
  have hr0 := hr.1
  rw [p_deriv, IsRoot] at hr0
  norm_num at hr0

private lemma p_deriv_roots_card_le_one : p.derivative.roots.card ≤ 1 := by
  rw [← Multiset.toFinset_card_of_nodup p_deriv_roots_nodup]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply p_deriv_root_unique
  · exact (mem_roots p_deriv_ne_zero).mp (Multiset.mem_toFinset.mp hx)
  · exact (mem_roots p_deriv_ne_zero).mp (Multiset.mem_toFinset.mp hy)

private lemma p_not_splits : ¬ p.Splits := by
  intro hp
  have hc := Polynomial.card_roots_le_derivative p
  rw [← hp.natDegree_eq_card_roots, p_natDegree] at hc
  have hd := p_deriv_roots_card_le_one
  omega

private lemma p_has_nonreal_root : ¬ ∀ z : ℂ, aeval z (p.map (algebraMap ℝ ℂ)) = 0 → z.im = 0 := by
  intro hall
  apply p_not_splits
  apply Splits.of_splits_map (algebraMap ℝ ℂ)
  · exact IsAlgClosed.splits _
  · intro z hz
    have hz0 : aeval z (p.map (algebraMap ℝ ℂ)) = 0 := by
      exact (mem_roots (map_ne_zero p_ne_zero)).mp hz
    have him : z.im = 0 := hall z hz0
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [him]

end

private lemma pZ_map_real : pZ.map (algebraMap ℤ ℝ) = p := by
  norm_num [pZ, p, Polynomial.C_mul, ← Polynomial.C_mul, Polynomial.C_ofNat,
    Polynomial.C_pow] ; ring

private lemma pZ_map_complex : pZ.map (algebraMap ℤ ℂ) = p.map (algebraMap ℝ ℂ) := by
  rw [← pZ_map_real, Polynomial.map_map]
  apply congrArg (fun f : ℤ →+* ℂ => pZ.map f)
  ext n
  simp

theorem result : ¬ claim := by
  intro h
  have hh := h (Fin 12) R4 (by decide) r4_biconnected r4_cliqueFree r4_flat
    r4_noIsolatedTriangle
  have hall : ∀ z : ℂ, aeval z (cliquePoly R4) = 0 → z.im = 0 := hh.1
  apply p_has_nonreal_root
  intro z hz
  apply hall
  rw [cliquePoly_R4]
  calc
    aeval z pZ = eval₂ (algebraMap ℤ ℂ) z pZ := rfl
    _ = aeval z (p.map (algebraMap ℝ ℂ)) := by
      rw [aeval_def, ← pZ_map_complex]
      simp [eval₂_eq_eval_map, Algebra.algebraMap_self]
    _ = 0 := hz

end D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots

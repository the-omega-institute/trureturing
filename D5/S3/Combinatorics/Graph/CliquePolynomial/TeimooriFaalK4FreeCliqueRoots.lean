/- GID: D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.claim; result=D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.result; claim=D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalK4FreeCliqueRoots.claim
   digest: A connected seven-vertex K4-free graph has a nonreal clique-polynomial root. -/

/-
proof_shape: claim: bind-only; source proposition; consumer: result.
proof_shape: edges: bind-only; concrete graph data; consumer: F7.
proof_shape: F7: bind-only; concrete graph via SimpleGraph.fromRel; consumers: F7_cliqueFree, F7_path, F7_c0, F7_c1, F7_c2, F7_c3, result.
proof_shape: path: bind-only; concrete path data; consumers: F7_path, F7_connected.
proof_shape: F7_cliqueFree: bind-only; finite kernel decision; consumers: F7_c4, F7_c5, F7_c6, F7_c7, result.
proof_shape: F7_path: bind-only; finite kernel decision; consumer: F7_connected.
proof_shape: F7_connected: bind-only; spanning walk and reachability; consumer: result.
proof_shape: F7_c0: bind-only; finite kernel decision; consumer: cliquePoly_F7.
proof_shape: F7_c1: bind-only; finite kernel decision; consumer: cliquePoly_F7.
proof_shape: F7_c2: bind-only; finite kernel decision; consumer: cliquePoly_F7.
proof_shape: F7_c3: bind-only; finite kernel decision; consumer: cliquePoly_F7.
proof_shape: F7_c4: bind-only; CliqueFree.cliqueFinset; consumer: cliquePoly_F7.
proof_shape: F7_c5: bind-only; CliqueFree.mono; consumer: cliquePoly_F7.
proof_shape: F7_c6: bind-only; CliqueFree.mono; consumer: cliquePoly_F7.
proof_shape: F7_c7: bind-only; CliqueFree.mono; consumer: cliquePoly_F7.
proof_shape: pZ: bind-only; concrete integer polynomial; consumers: cliquePoly_F7, p_map_complex.
proof_shape: cliquePoly_F7: bind-only; coefficient normalization; consumer: result.
proof_shape: p: bind-only; concrete real polynomial; consumers: P_toPoly, p_ne_zero, p_map_complex.
proof_shape: P: bind-only; concrete cubic data; consumers: P_toPoly, p_not_splits.
proof_shape: P_toPoly: bind-only; coefficient normalization; consumer: p_not_splits.
proof_shape: p_ne_zero: bind-only; evaluation at zero; consumer: p_has_nonreal_root.
proof_shape: p_not_splits: bind-only; Cubic.discr_eq_prod_three_roots and square nonnegativity; consumer: p_has_nonreal_root.
proof_shape: p_map_complex: bind-only; coefficient-map normalization; consumer: result.
proof_shape: p_has_nonreal_root: bind-only; Splits.of_splits_map and IsAlgClosed.splits; consumer: result.
proof_shape: result: bind-only; instantiation, contradiction and coefficient-map normalization.
escape_witness: none.
admission_basis: open-problem-resolution (#22515; Refuted).
Direct frozen dependencies:
  claim, cliquePoly_F7, result:
    D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.cliquePoly
    statement_id: sha256:456df2bdbaf0a26ab0a3b42dd4d727af778b3816a8e0a64aadfb4ffd46461fe9
  Other declarations: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The claim retains the graph and polynomial expressions of #22515 and reuses the
existing cliquePoly owner directly. SimpleGraph.fromRel supplies symmetrization,
loop exclusion and the decidable adjacency instance for the finite edge data.
Only the seven-vertex counterexample is proved here; the uniform family with
unbounded vertex connectivity remains open in Lean.
-/

import D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots
import Mathlib.Algebra.CubicDiscriminant

namespace D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalK4FreeCliqueRoots

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000

/-- Conjecture 4.1, page 5: "Let G be a connected K₄-free graphs, then G has only clique roots." -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree 4 →
      ∀ (z : ℂ),
        Polynomial.aeval z
          (D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly G)
            = 0 →
          z.im = 0

private abbrev edges : Finset (Fin 7 × Fin 7) :=
  {(0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6),
   (2, 3), (2, 5), (3, 4), (3, 5), (4, 6), (5, 6)}

private abbrev F7 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ edges

private lemma F7_cliqueFree : F7.CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree
  decide +kernel

private abbrev path : List (Fin 7) := [0, 3, 1, 4, 6, 5, 2]

private lemma F7_path : path ≠ [] ∧ path.IsChain F7.Adj ∧ ∀ v : Fin 7, v ∈ path := by
  decide +kernel

private lemma F7_connected : F7.Connected := by
  have hconn : ∀ {W : Type} (H : SimpleGraph W) (l : List W) (hne : l ≠ []),
      l.IsChain H.Adj → (∀ x, x ∈ l) → H.Connected := by
    intro W H l hne hc hall
    classical
    refine (SimpleGraph.connected_iff_exists_forall_reachable H).mpr ⟨l.head hne, fun x => ?_⟩
    refine ⟨(SimpleGraph.Walk.ofSupport l hne hc).takeUntil x ?_⟩
    rw [SimpleGraph.Walk.support_ofSupport]
    exact hall x
  exact hconn F7 path F7_path.1 F7_path.2.1 F7_path.2.2

private lemma F7_c0 : (F7.cliqueFinset 0).card = 1 := by decide +kernel
private lemma F7_c1 : (F7.cliqueFinset 1).card = 7 := by decide +kernel
private lemma F7_c2 : (F7.cliqueFinset 2).card = 14 := by decide +kernel
private lemma F7_c3 : (F7.cliqueFinset 3).card = 9 := by decide +kernel
private lemma F7_c4 : (F7.cliqueFinset 4).card = 0 := by
  rw [F7_cliqueFree.cliqueFinset]
  rfl
private lemma F7_c5 : (F7.cliqueFinset 5).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 4 ≤ 5) F7_cliqueFree).cliqueFinset]
  rfl
private lemma F7_c6 : (F7.cliqueFinset 6).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 4 ≤ 6) F7_cliqueFree).cliqueFinset]
  rfl
private lemma F7_c7 : (F7.cliqueFinset 7).card = 0 := by
  rw [(SimpleGraph.CliqueFree.mono (by decide : 4 ≤ 7) F7_cliqueFree).cliqueFinset]
  rfl

private noncomputable def pZ : ℤ[X] := 1 + 7 * X + 14 * X^2 + 9 * X^3

private lemma cliquePoly_F7 :
    D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly F7 = pZ := by
  classical
  norm_num [D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly,
    Finset.sum_range_succ, F7_c0, F7_c1, F7_c2, F7_c3, F7_c4, F7_c5, F7_c6, F7_c7,
    pZ, Polynomial.C_ofNat, Polynomial.C_pow]

private noncomputable def p : ℝ[X] := C 1 + C 7 * X + C 14 * X^2 + C 9 * X^3
private def P : Cubic ℝ := ⟨9, 14, 7, 1⟩

private lemma P_toPoly : P.toPoly = p := by
  simp [P, Cubic.toPoly, p]
  ring

private lemma p_ne_zero : p ≠ 0 := by
  intro h
  have hc := congrArg (fun q : ℝ[X] => q.eval 0) h
  norm_num [p] at hc

private lemma p_not_splits : ¬ p.Splits := by
  intro hp
  have hp' : (P.toPoly.map (RingHom.id ℝ)).Splits := by
    simpa [P_toPoly, RingHom.id_apply] using hp
  have ha : P.a ≠ 0 := by norm_num [P]
  obtain ⟨x, y, z, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three (P := P) (φ := RingHom.id ℝ) ha).mp hp'
  have hd := Cubic.discr_eq_prod_three_roots (P := P) (φ := RingHom.id ℝ) ha hroots
  have hd' : P.discr = ((P.a : ℝ) * P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
    simpa [RingHom.id_apply] using hd
  have hnonneg : 0 ≤ P.discr := by
    rw [hd']
    positivity
  norm_num [P, Cubic.discr] at hnonneg

private lemma p_map_complex : pZ.map (algebraMap ℤ ℂ) = p.map (algebraMap ℝ ℂ) := by
  have hp : pZ.map (algebraMap ℤ ℝ) = p := by
    norm_num [pZ, p, Polynomial.C_mul, ← Polynomial.C_mul, Polynomial.C_ofNat,
      Polynomial.C_pow]
  rw [← hp, Polynomial.map_map]
  apply congrArg (fun f : ℤ →+* ℂ => pZ.map f)
  ext n
  simp

private lemma p_has_nonreal_root :
    ¬ ∀ z : ℂ, Polynomial.aeval z (p.map (algebraMap ℝ ℂ)) = 0 → z.im = 0 := by
  intro hall
  apply p_not_splits
  apply Splits.of_splits_map (algebraMap ℝ ℂ)
  · exact IsAlgClosed.splits _
  · intro z hz
    have hz0 : Polynomial.aeval z (p.map (algebraMap ℝ ℂ)) = 0 := by
      exact (mem_roots (map_ne_zero p_ne_zero)).mp hz
    have him : z.im = 0 := hall z hz0
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [him]

theorem result : ¬ claim := by
  intro h
  have hh := h (Fin 7) F7 F7_connected F7_cliqueFree
  have hall : ∀ z : ℂ, Polynomial.aeval z
      (D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalFlatCliqueRoots.cliquePoly F7) = 0 → z.im = 0 := hh
  apply p_has_nonreal_root
  intro z hz
  apply hall
  rw [cliquePoly_F7]
  calc
    Polynomial.aeval z pZ = Polynomial.eval₂ (algebraMap ℤ ℂ) z pZ := rfl
    _ = Polynomial.aeval z (p.map (algebraMap ℝ ℂ)) := by
      rw [Polynomial.aeval_def, ← p_map_complex]
      simp [Polynomial.eval₂_eq_eval_map, Algebra.algebraMap_self]
    _ = 0 := hz

end D5.S3.Combinatorics.Graph.CliquePolynomial.TeimooriFaalK4FreeCliqueRoots

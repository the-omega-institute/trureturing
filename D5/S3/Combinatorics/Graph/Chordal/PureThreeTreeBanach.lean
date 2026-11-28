/- GID: D5/S3/Combinatorics/Graph/Chordal/PureThreeTreeBanach
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Banach reconstruction and offline triangle tests bound each other on replicated three-trees. -/

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeClosure
import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import Mathlib.Analysis.Normed.Module.HahnBanach

compile_only_with_mathlib

/-! Omega original.

The bounded triangle-dual coefficient agrees with the universal Banach
coefficient on the pure replicated tree family.
-/

namespace Omega.PureThreeTree
open SimpleGraph Omega.GraphChains Omega.RollingCliques Finset
open scoped BigOperators
noncomputable section

variable {n k : ℕ}
local notation "V" => Vertex n k
local notation "B" => (triangleChain (G := graph n k))

private theorem graph_chordal : (graph n k).IsChordal := by
  classical
  intro x c hc hl
  obtain ⟨v, hv, hmax⟩ :=
    Finset.exists_max_image c.support.toFinset depth ⟨x, by simp⟩
  have hmem : v ∈ c.support := by simpa using hv
  let d := c.rotate v hmem
  have hd : d.IsCycle := hc.rotate hmem
  have hn : 4 ≤ d.length := by simpa [d] using hl
  have support (w : V) (hw : w ∈ d.support) : w ∈ c.support := by
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hmem
    · exact List.mem_of_mem_tail ((c.support_rotate v hmem).mem_iff.mp hw)
  have hs := support d.snd (d.getVert_mem_support 1)
  have hp := support d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hs, hp, rolling_clique data v.val
    ⟨hmax _ (by simpa using hs), (d.adj_snd hd.not_nil).symm⟩
    ⟨hmax _ (by simpa using hp), d.adj_penultimate hd.not_nil⟩
    (fun e => hd.snd_ne_penultimate (Subtype.ext e)), ?_⟩
  intro e
  have hm := Walk.adj_toSubgraph_iff_mem_edges.mpr ((c.rotate_edges v hmem).mem_iff.mpr e)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at hm
  rw [hd.neighborSet_toSubgraph_internal (by omega) (by omega)] at hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.sub_self] at hm
  have hend : d.length - 1 ∈ {i | i ≤ d.length - 1} := by simp
  have htwo : 2 ∈ {i | i ≤ d.length - 1} := by
    change 2 ≤ d.length - 1
    omega
  have hzero : 0 ∈ {i | i ≤ d.length - 1} := by simp
  rcases hm with hm | hm
  · have he := hd.getVert_injOn' hend hzero hm
    omega
  · have he := hd.getVert_injOn' hend htwo hm
    omega

private theorem clique_card (s : Finset V) (hs : (graph n k).IsClique (s : Set V)) :
    s.card ≤ 4 := by
  classical
  by_cases h : s.Nonempty
  · obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image s depth h
    by_cases hz : depth v = 0
    · let f (w : s) : Fin 3 := w.val.val.2
      have hf : Function.Injective f := by
        intro a b he
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · have ha : (a.val.val.1.stage).val = 0 := by
            have h := hmax a.val a.property
            change depth a.val = 0
            omega
          have hb : (b.val.val.1.stage).val = 0 := by
            have h := hmax b.val b.property
            change depth b.val = 0
            omega
          rw [History.stage_zero (Fin.ext ha), History.stage_zero (Fin.ext hb)]
        · exact he
      have hp := Fintype.card_le_of_injective f hf
      simp at hp
      omega
    · let f (w : ↥(s.erase v)) : ↥(parents v.val.1) := by
        have hm := Finset.mem_erase.mp w.property
        have ha : (graph n k).Adj w.val v := hs hm.2 hv hm.1
        obtain ⟨hpre, he⟩ := rolling_earlier data ha (hmax _ hm.2)
        have hlt : w.val.val.1.stage < v.val.1.stage := by
          apply lt_of_le_of_ne hpre.1
          intro he
          exact hz (equal_depth_edge_root ha.symm (congrArg Fin.val he.symm))
        refine ⟨(w.val.val.1.stage,w.val.val.2), ?_⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hlt, he.resolve_left (fun e => hlt.ne (congrArg History.stage e))⟩
      have hf : Function.Injective f := by
        intro a b he
        have het := congrArg Subtype.val he
        have h₁ := (rolling_earlier data
          (hs (Finset.mem_of_mem_erase a.property) hv (Finset.ne_of_mem_erase a.property))
          (hmax _ (Finset.mem_of_mem_erase a.property))).1
        have h₂ := (rolling_earlier data
          (hs (Finset.mem_of_mem_erase b.property) hv (Finset.ne_of_mem_erase b.property))
          (hmax _ (Finset.mem_of_mem_erase b.property))).1
        have hsab : a.val.val.1.stage = b.val.val.1.stage := congrArg Prod.fst het
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · apply History.IsPrefix.eq_of_stage_eq ?_ hsab
          exact ⟨hsab.le, fun i hi => (h₁.2 i hi).trans (h₂.2 i (hsab ▸ hi)).symm⟩
        · have hl := congrArg Prod.snd het
          change a.val.val.2 = b.val.val.2 at hl
          exact hl
      have hp := Fintype.card_le_of_injective f hf
      simp only [Fintype.card_coe, parents_card _ (Nat.pos_of_ne_zero hz)] at hp
      have hh := Finset.card_erase_add_one hv
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

universe u

/-- A coefficient uniformly valid for all Banach gains on the replicated tree. -/
def BanachFeasible (n k : ℕ) (R : ℝ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : Vertex n k → Vertex n k → E), (∀ x y, g y x = -g x y) →
    (∀ x y z, (graph n k).Adj x y → (graph n k).Adj y z → (graph n k).Adj x z →
      ‖g x y + g y z - g x z‖ ≤ 1) →
    ∃ p : Vertex n k → E, ∀ x y, (graph n k).Adj x y →
      ‖g x y - (p y - p x)‖ ≤ R

private def evaluate {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) : Chains V →ₗ[ℝ] E where
  toFun z := ∑ e : V × V, z e • g e.1 e.2
  map_add' x y := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by simp [smul_smul, Finset.smul_sum]

private theorem evaluate_edge {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (hg : ∀ x y, g y x = -g x y) (a b : V) :
    evaluate g (orientedEdge a b) = g a b := by
  have he (x y : V) : evaluate g (Pi.single (M := fun _ : V × V => ℝ) (x,y) 1) = g x y := by
    change (∑ e : V × V, (Pi.single (M := fun _ : V × V => ℝ) (x,y) 1 e) • g e.1 e.2) = _
    simp [Pi.single_apply, ite_smul]
  rw [orientedEdge, map_smul, map_sub, he, he, hg a b, sub_neg_eq_add, ← two_smul ℝ,
    smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

private theorem evaluation_bound {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (hg : ∀ x y, g y x = -g x y) (hgb : ∀ x y, ‖g x y‖ ≤ 3)
    (hgt : ∀ x y z, (graph n k).Adj x y → (graph n k).Adj y z → (graph n k).Adj x z →
      ‖g x y + g y z - g x z‖ ≤ 1) (c : Chains V) :
    ‖evaluate g c‖ ≤ dualNorm B c := by
  obtain ⟨φ, hφ, hφc⟩ := exists_dual_vector'' ℝ (evaluate g c)
  let f (e : V × V) := φ (g e.1 e.2)
  have happly (z : Chains V) : pairing f z = φ (evaluate g z) := by
    change (∑ e : V × V, φ (g e.1 e.2) * z e) = φ (∑ e : V × V, z e • g e.1 e.2)
    simp [map_sum, mul_comm]
  have hbound (z : E) : |φ z| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]
    have he := mul_le_mul_of_nonneg_right hφ (norm_nonneg z)
    exact (φ.le_opNorm z).trans (by simpa using he)
  have had : Admissible B f := by
    refine ⟨fun e => (hbound _).trans (hgb e.1 e.2), fun t => ?_⟩
    rw [happly, triangleChain, map_sub, map_add, evaluate_edge g hg, evaluate_edge g hg, evaluate_edge g hg]
    exact (hbound _).trans (hgt _ _ _ t.2.1 t.2.2.1 t.2.2.2)
  have hh := abs_pairing_le_dualNorm had c
  rw [happly, hφc] at hh
  change |‖evaluate g c‖| ≤ _ at hh
  simpa only [abs_of_nonneg (norm_nonneg _)] using hh

/-- A bounded chain fit implies the same universal Banach bound. The standard
simplicial estimate gives a gauge bounded by two before applying duality. -/
theorem offline_implies_banach {R : ℝ} (h : OfflineFeasible n k R) : BanachFeasible.{u} n k R := by
  classical
  obtain ⟨p,hp,hb,hr⟩ := h
  intro E _ _ _ g hg hgt
  obtain ⟨a,ha⟩ := (graph_chordal (n := n) (k := k)).exists_simplicial_banach_gain_potential
    3 (by decide) clique_card g 1 (by norm_num) hg hgt
  let g' (x y : V) := if (graph n k).Adj x y then g x y - (a y - a x) else 0
  have hrev (x y : V) : g' y x = -g' x y := by
    by_cases e : (graph n k).Adj x y
    · simp only [g', ite_eq_left e, ite_eq_left e.symm, hg x y]
      abel
    · have en : ¬(graph n k).Adj y x := fun he => e he.symm
      simp [g', e, en]
  have hbd (x y : V) : ‖g' x y‖ ≤ 3 := by
    by_cases e : (graph n k).Adj x y
    · simp only [g', ite_eq_left e]
      refine (ha x y e).trans ?_
      have hp : 0 ≤ ((3 - 1 : ℝ) / 3) ^ (Nat.card V - 1) := by positivity
      linarith
    · simp [g', e]
  have htri (x y z : V) (hxy : (graph n k).Adj x y) (hyz : (graph n k).Adj y z)
      (hxz : (graph n k).Adj x z) : ‖g' x y + g' y z - g' x z‖ ≤ 1 := by
    simpa [g', hxy, hyz, hxz, show g x y - (a y - a x) + (g y z - (a z - a y)) -
      (g x z - (a z - a x)) = g x y + g y z - g x z by abel] using hgt x y z hxy hyz hxz
  refine ⟨fun v => a v + evaluate g' (p v), fun x y e => ?_⟩
  have hh := (evaluation_bound g' hrev hbd htri (orientedEdge x y + p x - p y)).trans (hr x y e)
  rw [map_sub, map_add, evaluate_edge g' hrev, show g' x y = g x y - (a y - a x) by simp [g', e]] at hh
  have hcalc : g x y - (a y + evaluate g' (p y) - (a x + evaluate g' (p x))) =
      g x y - (a y - a x) + evaluate g' (p x) - evaluate g' (p y) := by abel
  rw [hcalc]
  exact hh

theorem banach_offline_relaxed {R S : ℝ} (h : BanachFeasible.{0} n k R)
    (hRS : R < S) : OfflineFeasible n k S := by
  by_contra hno
  have obstruction (p : V → Chains V) (hp : ∀ v, Supported (graph n k) (p v))
      (hb : ∀ v, boundary (p v) = Pi.single v 1 - Pi.single (root 0) 1) :
      ∃ u v, (graph n k).Adj u v ∧ S ≤ dualNorm B (orientedEdge u v + p u - p v) := by
    by_contra hn
    exact hno ⟨p, hp, hb, fun x y e => (not_le.mp (fun he => hn ⟨x,y,e,he⟩)).le⟩
  obtain ⟨E,N,M,hcomp,hfin,g,hg,htri,hobs⟩ :=
    gain_of_rooted_chain_obstruction (graph n k) graph_connected (root 0) S obstruction
  let := N
  let := M
  let := hcomp
  obtain ⟨p, hp⟩ := h E g hg htri
  obtain ⟨a,b,e,he⟩ := hobs p
  exact hRS.not_ge (he.trans (hp a b e))

end
end Omega.PureThreeTree

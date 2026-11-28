import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.PureThreeTreeCausal

compile_only_with_mathlib

/-! Omega original.

Transport of an ancestral rule across copies and comparison of the limiting
thresholds for the replicated and single-copy pure 3-tree families.
-/

namespace Omega.PureThreeTree
open SimpleGraph Omega.GraphChains Omega.RollingCliques Finset
open scoped BigOperators
noncomputable section

variable {n k : ℕ}

private def History.copyAlong (b : History n k) (c : History n 0) : History n k where
  stage := c.stage
  step i := ((c.step i).1, if i ≤ c.stage then (b.step i).2 else 0)
  root_step := by simp [b.root_step, c.root_step, rootStep]
  beyond i hi := by simp [not_le_of_gt hi, c.beyond i hi, rootStep]
  legal i hi hp := c.legal i hi hp
  nested j i l hil hl := c.nested j i l hil hl

private theorem copyAlong_prefix (b : History n k) {x y : History n 0}
    (h : x.IsPrefix y) : (b.copyAlong x).IsPrefix (b.copyAlong y) := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp [History.copyAlong, show i ≤ x.stage from hi,
    show i ≤ y.stage from hi.trans h.1, h.2 i hi]

private def copyAlong (b : History n k) (x : Vertex n 0) : Vertex n k :=
  ⟨(b.copyAlong x.val.1,x.val.2), x.property⟩

private theorem forget_copyAlong (b : History n k) (x : Vertex n 0) :
    forget (copyAlong b x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := (forget (copyAlong b x)).val.1) (c := x.val.1) rfl
    funext i
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have h := (x.val.1.step i).2.isLt
      change 0 = (x.val.1.step i).2.val
      omega
  · rfl

private theorem copyAlong_adj (b : History n k) {x y : Vertex n 0} (h : (graph n 0).Adj x y) :
    (graph n k).Adj (copyAlong b x) (copyAlong b y) := by
  refine ⟨fun h' => h.ne (by
    have e := congrArg forget (Subtype.ext h')
    simpa only [forget_copyAlong] using e), ?_⟩
  rcases h.2 with h | h | h
  · exact Or.inl (congrArg (History.copyAlong b) h)
  · exact Or.inr (Or.inl ⟨copyAlong_prefix b h.1, h.2⟩)
  · exact Or.inr (Or.inr ⟨copyAlong_prefix b h.1, h.2⟩)

private theorem copyAlong_root (b : History n k) (i : Fin 3) :
    copyAlong b (root i) = root i := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := (copyAlong b (root i)).val.1) (c := (root (n := n) (k := k) i).val.1) rfl
    funext t
    by_cases ht : t = 0
    · subst t
      exact (b.copyAlong History.initial).root_step
    · simp [copyAlong, History.copyAlong, History.initial, root, rootStep, ht]
  · rfl

private theorem copyAlong_forget (u : Vertex n k) : copyAlong u.val.1 (forget u) = u := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := (copyAlong u.val.1 (forget u)).val.1) (c := u.val.1) rfl
    funext t
    by_cases ht : t ≤ u.val.1.stage
    · change ((u.val.1.step t).1, if t ≤ u.val.1.stage then (u.val.1.step t).2 else 0) = _
      rw [ite_eq_left ht]
    · exact ((u.val.1.copyAlong (u.val.1.copyMap (fun _ => 0) rfl)).beyond t
        (lt_of_not_ge ht)).trans (u.val.1.beyond t (lt_of_not_ge ht)).symm
  · rfl

private theorem copyAlong_agrees {u v : Vertex n k} (h : pre u v) {x : Vertex n 0}
    (hx : pre x (forget u)) : copyAlong u.val.1 x = copyAlong v.val.1 x := by
  apply Subtype.ext
  apply Prod.ext
  · apply History.ext' (b := (copyAlong u.val.1 x).val.1) (c := (copyAlong v.val.1 x).val.1) rfl
    funext i
    change ((x.val.1.step i).1, if i ≤ x.val.1.stage then (u.val.1.step i).2 else 0) =
      ((x.val.1.step i).1, if i ≤ x.val.1.stage then (v.val.1.step i).2 else 0)
    by_cases hi : i ≤ x.val.1.stage
    · rw [ite_eq_left hi, ite_eq_left hi, h.2 i (hi.trans hx.1)]
    · simp [hi]
  · rfl

private theorem push_agrees {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {f g : X → Y} {z : Chains X}
    (h : ∀ e : X × X, z e ≠ 0 → f e.1 = g e.1 ∧ f e.2 = g e.2) :
    pushChain f z = pushChain g z := by
  classical
  unfold pushChain
  apply Finset.sum_congr rfl
  intro e _
  by_cases hz : z e = 0
  · simp [hz]
  · rw [(h e hz).1, (h e hz).2]

private theorem supported_push {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] {GX : SimpleGraph X} {GY : SimpleGraph Y}
    {f : X → Y} (hf : ∀ x y, GX.Adj x y → GY.Adj (f x) (f y))
    {z : Chains X} (hz : Supported GX z) : Supported GY (pushChain f z) := by
  classical
  intro e he
  simp only [pushChain, Finset.sum_apply, Pi.single_apply]
  apply Finset.sum_eq_zero
  intro a _
  split
  · rename_i h
    exact hz a (fun ha => he (h.symm ▸ hf _ _ ha))
  · rfl

/-- Copy indices can be restored one spine at a time without changing an edge
residual bound on the single-copy tree. -/
theorem causal_to_offline {R : ℝ} (h : CausalFeasible n R) : OfflineFeasible n k R := by
  classical
  obtain ⟨p, hb, hs, hr⟩ := h
  let q (v : Vertex n k) := pushChain (copyAlong v.val.1) (p (forget v))
  refine ⟨q, ?_, ?_, ?_⟩
  · intro v
    apply supported_push (fun _ _ hv => copyAlong_adj v.val.1 hv)
    intro e he
    exact hs _ _ _ (fun h => he h.2.2)
  · intro v
    change boundary (pushChain (copyAlong v.val.1) (p (forget v))) = _
    rw [push_single_boundary _ _ _ (hb _), copyAlong_forget, copyAlong_root]
  · have forward (u v : Vertex n k) (huv : (graph n k).Adj u v) (hd : depth u ≤ depth v) :
        dualNorm (triangleChain (G := graph n k)) (orientedEdge u v + q u - q v) ≤ R := by
      have hpref : pre u v := (rolling_earlier data huv hd).1
      let f := copyAlong v.val.1
      have hq : q u = pushChain f (p (forget u)) := by
        apply push_agrees
        intro e he
        have hs' : pre e.1 (forget u) ∧ pre e.2 (forget u) ∧ (graph n 0).Adj e.1 e.2 :=
          Classical.not_not.mp (fun hn => he (hs _ _ _ hn))
        exact ⟨copyAlong_agrees hpref hs'.1, copyAlong_agrees hpref hs'.2.1⟩
      have hfu : f (forget u) = u :=
        (copyAlong_agrees hpref (data.refl (forget u).val.1)).symm.trans (copyAlong_forget u)
      have hf : ∀ x y, (graph n 0).Adj x y → f x = f y ∨ (graph n k).Adj (f x) (f y) :=
        fun _ _ he => Or.inr (copyAlong_adj v.val.1 he)
      have he := dualNorm_pushChain_le f hf
        (orientedEdge (forget u) (forget v) + p (forget u) - p (forget v))
      rw [pushChain_sub, pushChain_add, pushChain_edge, hfu,
        show f (forget v) = v from copyAlong_forget v, ← hq] at he
      exact he.trans (hr _ _ (copyMap_edge _ rfl huv))
    intro u v e
    rcases le_total (depth u) (depth v) with h | h
    · exact forward u v e h
    · rw [show orientedEdge u v + q u - q v =
          -(orientedEdge v u + q v - q u) by rw [orientedEdge_reverse v u]; abel,
        dualNorm_neg_eq]
      exact forward v u e.symm h

private theorem causal_mono {R S : ℝ} (h : CausalFeasible n R) (hle : R ≤ S) :
    CausalFeasible n S := by
  obtain ⟨p,hb,hs,hr⟩ := h
  exact ⟨p,hb,hs,fun a b e => (hr a b e).trans hle⟩

/-- A uniform offline budget on every number of copies gives single-copy
causal rules at every positive relaxation. Conversely, arbitrary causal
rules at all positive relaxations retain that budget on every copy count. -/
theorem causal_offline_limit (R : ℝ) (hR : 0 ≤ R) :
    (∀ n k : ℕ, ∀ ε : ℝ, 0 < ε → OfflineFeasible n k (R + ε)) ↔
      (∀ n : ℕ, ∀ ε : ℝ, 0 < ε → CausalFeasible n (R + ε)) := by
  constructor
  · intro h n ε hε
    let S : ℝ := R + ε / 2
    have hS : 0 ≤ S := by dsimp [S]; positivity
    obtain ⟨k, hk⟩ := exists_nat_gt (max 0 (4 * S / ε))
    have hk₀ : (0 : ℝ) < k := (le_max_left ..).trans_lt hk
    have hk' : 0 < k := by exact_mod_cast hk₀
    have ho := offline_to_causal hS hk' (h n k (ε / 2) (by positivity))
    apply causal_mono ho
    have hb : 4 * S / ε ≤ (k : ℝ) := ((le_max_right ..).trans_lt hk).le
    have hc : 2 * S / (k : ℝ) ≤ ε / 2 := by
      apply (div_le_iff₀ hk₀).mpr
      have hd := (div_le_iff₀ hε).mp hb
      linarith
    dsimp [S] at hc ⊢
    linarith
  · intro h n k ε hε
    exact causal_to_offline (k := k) (h n ε hε)

/-- Failure of the causal bound on the single-copy tree at the sharp rescaled
budget yields a concrete finite-dimensional Banach obstruction on its replicated tree. -/
theorem banach_obstruction_of_causal {R : ℝ} (hR : 0 ≤ R) (hk : 0 < k)
    (h : ¬CausalFeasible n (R + 2 * R / (k : ℝ))) :
    ∃ (E : Type) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
      letI := N
      letI := S
      ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : Vertex n k → Vertex n k → E),
        (∀ u v, g v u = -g u v) ∧
        (∀ u v w, (graph n k).Adj u v → (graph n k).Adj v w → (graph n k).Adj u w →
          ‖g u v + g v w - g u w‖ ≤ 1) ∧
        ∀ φ : Vertex n k → E, ∃ u v, (graph n k).Adj u v ∧ R ≤ ‖g u v - (φ v - φ u)‖ := by
  apply gain_of_rooted_chain_obstruction (graph n k) graph_connected (root 0) R
  intro p hp hb
  by_contra hn
  apply h
  apply offline_to_causal hR hk
  refine ⟨p, hp, hb, fun u v he => ?_⟩
  exact (not_le.mp fun hR => hn ⟨u, v, he, hR⟩).le

end
end Omega.PureThreeTree

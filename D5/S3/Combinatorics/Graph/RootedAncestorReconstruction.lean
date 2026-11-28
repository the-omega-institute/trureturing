/- GID: D5/S3/Combinatorics/Graph/RootedAncestorReconstruction
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gain reconstruction on bounded ancestor graphs -/

import OmegaBuild.Commands
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! # Gain reconstruction on bounded ancestor graphs -/

namespace SimpleGraph

/-- Depth and ancestors indexed by absolute depth in a rooted forest.
For a rooted tree, these are obtained from the unique path from the root. -/
structure RootedAncestors (V : Type*) where
  depth : V → ℕ
  atDepth : V → ℕ → V
  depth_atDepth : ∀ v i, i ≤ depth v → depth (atDepth v i) = i
  atDepth_self : ∀ v, atDepth v (depth v) = v
  atDepth_atDepth : ∀ v i j, i ≤ j → j ≤ depth v →
    atDepth (atDepth v j) i = atDepth v i

namespace RootedAncestors

variable {V : Type*} (T : RootedAncestors V)

/-- The root paths of a tree form a coherent family of ancestors. -/
noncomputable def ofTree {S : SimpleGraph V} (hS : S.IsTree) (root : V) : RootedAncestors V := by
  classical
  let path (v : V) := (hS.existsUnique_path root v).exists.choose
  have hp (v : V) : (path v).IsPath := (hS.existsUnique_path root v).exists.choose_spec
  have path_prefix (v : V) (j : ℕ) : path ((path v).getVert j) = (path v).take j :=
    (hS.existsUnique_path root ((path v).getVert j)).unique (hp _) ((hp v).take j)
  refine ⟨fun v => (path v).length, fun v i => (path v).getVert i, ?_, ?_, ?_⟩
  · intro v i hi
    rw [path_prefix, Walk.take_length, min_eq_left hi]
  · intro v
    exact (path v).getVert_length
  · intro v i j hij _
    rw [path_prefix, Walk.take_getVert, min_eq_right hij]

/-- Distinct comparable vertices are joined when their depth difference is at most the width. -/
def graph (k : ℕ) : SimpleGraph V where
  Adj u v :=
    (T.depth u < T.depth v ∧ T.depth v ≤ T.depth u + k ∧ T.atDepth v (T.depth u) = u) ∨
    (T.depth v < T.depth u ∧ T.depth u ≤ T.depth v + k ∧ T.atDepth u (T.depth v) = v)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => lt_irrefl _ h.1) (fun h => lt_irrefl _ h.1)⟩

private theorem head_le (k s n : ℕ) : k * ((n + s) / k) - s ≤ n := by
  have := Nat.mul_div_le (n + s) k
  omega

private theorem span {v : V} {i j k : ℕ} (hij : i ≤ j) (hj : j ≤ T.depth v)
    (hk : j ≤ i + k) :
    T.atDepth v i = T.atDepth v j ∨ (T.graph k).Adj (T.atDepth v i) (T.atDepth v j) := by
  by_cases he : i = j
  · exact Or.inl (by rw [he])
  · apply Or.inr
    change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
    rw [T.depth_atDepth v i (hij.trans hj), T.depth_atDepth v j hj]
    exact Or.inl ⟨lt_of_le_of_ne hij he, hk, T.atDepth_atDepth v i j hij hj⟩

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def trunk (k s : ℕ) (g : V → V → E) (v : V) (m : ℕ) : E :=
  ∑ j ∈ Finset.range m, g (T.atDepth v (k * j - s)) (T.atDepth v (k * (j + 1) - s))

private noncomputable def phase (k s : ℕ) (g : V → V → E) (v : V) : E :=
  let m := (T.depth v + s) / k
  T.trunk k s g v m + g (T.atDepth v (k * m - s)) v

omit [NormedSpace ℝ E] in
private theorem trunk_restrict {u v : V} {m k s : ℕ}
    (hu : T.atDepth v (T.depth u) = u) (huv : T.depth u ≤ T.depth v)
    (hm : k * m - s ≤ T.depth u) (g : V → V → E) :
    T.trunk k s g u m = T.trunk k s g v m := by
  unfold trunk
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have h1 : k * j - s ≤ T.depth u :=
    (Nat.sub_le_sub_right (Nat.mul_le_mul_left k (by omega)) s).trans hm
  have h2 : k * (j + 1) - s ≤ T.depth u :=
    (Nat.sub_le_sub_right (Nat.mul_le_mul_left k (by omega)) s).trans hm
  rw [← hu, T.atDepth_atDepth v _ _ h1 huv, T.atDepth_atDepth v _ _ h2 huv]

omit [NormedSpace ℝ E] in
private theorem triangle {k : ℕ} {g : V → V → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hzero : ∀ v, g v v = 0) (hrev : ∀ v w, g w v = -g v w)
    (htri : ∀ v w x, (T.graph k).Adj v w → (T.graph k).Adj w x → (T.graph k).Adj v x →
      ‖g v w + g w x - g v x‖ ≤ ε)
    {a b c : V} (hab : a = b ∨ (T.graph k).Adj a b)
    (hbc : b = c ∨ (T.graph k).Adj b c)
    (hac : a = c ∨ (T.graph k).Adj a c) :
    ‖g a b + g b c - g a c‖ ≤ ε := by
  rcases hab with rfl | hab
  · simpa [hzero] using hε
  rcases hbc with rfl | hbc
  · simpa [hzero] using hε
  rcases hac with rfl | hac
  · simpa [hzero, hrev b a] using hε
  exact htri a b c hab hbc hac

private theorem phase_bound {k : ℕ} (hk : 0 < k) (s : Fin k)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ v w, g w v = -g v w)
    (htri : ∀ v w x, (T.graph k).Adj v w → (T.graph k).Adj w x → (T.graph k).Adj v x →
      ‖g v w + g w x - g v x‖ ≤ ε) {u v : V}
    (huv : (T.graph k).Adj u v) :
    ‖g u v - (T.phase k s g v - T.phase k s g u)‖ ≤
      ε * ((if (T.depth u + s.val) % k = 0 then 0 else 1) +
           (if (T.depth v + s.val) % k = 0 then 0 else 1)) := by
  have hzero (v : V) : g v v = 0 := by
    have h : (2 : ℝ) • g v v = 0 := by
      rw [two_smul]
      calc
        g v v + g v v = g v v + -g v v := congrArg (g v v + ·) (hrev v v)
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have ht {a b c : V} := T.triangle hε hzero hrev htri (a := a) (b := b) (c := c)
  have forward (u v : V) (huv : (T.graph k).Adj u v) (hu : T.depth u < T.depth v)
      (hv : T.depth v ≤ T.depth u + k) (ha : T.atDepth v (T.depth u) = u) :
      ‖g u v - (T.phase k s g v - T.phase k s g u)‖ ≤
        ε * ((if (T.depth u + s.val) % k = 0 then 0 else 1) +
          (if (T.depth v + s.val) % k = 0 then 0 else 1)) := by
    let a := (T.depth u + s.val) / k
    let b := (T.depth v + s.val) / k
    let i := k * a - s.val
    let j := k * b - s.val
    let x := T.atDepth v i
    let y := T.atDepth v j
    have hi : i ≤ T.depth u := head_le _ _ _
    have hj : j ≤ T.depth v := head_le _ _ _
    have ea := Nat.mod_add_div (T.depth u + s.val) k
    have eb := Nat.mod_add_div (T.depth v + s.val) k
    change (T.depth u + s.val) % k + k * a = T.depth u + s.val at ea
    change (T.depth v + s.val) % k + k * b = T.depth v + s.val at eb
    have ri := Nat.mod_lt (T.depth u + s.val) hk
    have rj := Nat.mod_lt (T.depth v + s.val) hk
    have hiu : T.depth u ≤ i + k := by dsimp [i]; omega
    have hjv : T.depth v ≤ j + k := by dsimp [j]; omega
    have hu0 (h : (T.depth u + s.val) % k = 0) : x = u := by
      change T.atDepth v i = u
      rw [show i = T.depth u by dsimp [i]; omega, ha]
    have hv0 (h : (T.depth v + s.val) % k = 0) : y = v := by
      change T.atDepth v j = v
      rw [show j = T.depth v by dsimp [j]; omega, T.atDepth_self]
    have hxu : x = u ∨ (T.graph k).Adj x u := ha ▸ T.span hi hu.le hiu
    have hyv : y = v ∨ (T.graph k).Adj y v := T.atDepth_self v ▸ T.span hj le_rfl hjv
    have hpa : T.phase k s g u = T.trunk k s g v a + g x u := by
      change T.trunk k s g u a + g (T.atDepth u i) u = _
      rw [T.trunk_restrict ha hu.le hi g]
      have hx : T.atDepth u i = x := by
        rw [← ha]
        exact T.atDepth_atDepth v i (T.depth u) hi hu.le
      rw [hx]
    have hpb : T.phase k s g v = T.trunk k s g v b + g y v := rfl
    have hab : a ≤ b := Nat.div_le_div_right (by omega)
    have hab' : b ≤ a + 1 := by
      dsimp [a,b]
      have h := Nat.div_le_div_right (c := k)
        (show T.depth v + s.val ≤ T.depth u + s.val + k by omega)
      simpa [Nat.add_div_right _ hk] using h
    rw [hpa, hpb]
    by_cases he : a = b
    · have hij : i = j := by simp [i, j, he]
      have hxy : x = y := congrArg (T.atDepth v) hij
      have hv' : (T.depth v + s.val) % k ≠ 0 := by
        intro hz
        have hdep : j = T.depth v := by dsimp [j]; omega
        omega
      rw [he, hxy, ite_eq_right hv']
      by_cases hz : (T.depth u + s.val) % k = 0
      · rw [ite_eq_left hz, ← hxy, hu0 hz, hzero]
        simpa using hε
      · rw [ite_eq_right hz]
        calc
          _ = ‖g y u + g u v - g y v‖ := by congr 1; abel
          _ ≤ ε := ht (hxy ▸ hxu) (.inr huv) hyv
          _ ≤ _ := by linarith
    · have hb : b = a + 1 := by omega
      have ek : k * b = k * a + k := by rw [hb, Nat.mul_succ]
      have hj' : j = k * a + k - s.val := by unfold j; rw [ek]
      have hui : T.depth u ≤ j := by omega
      have hxy := T.span (v := v) (i := i) (j := j) (k := k)
        (by dsimp [i]; omega) hj (by dsimp [i]; omega)
      have huy : u = y ∨ (T.graph k).Adj u y := ha ▸ T.span hui hj (by omega)
      have hstep : T.trunk k s g v b = T.trunk k s g v a + g x y := by
        change _ = _ + g (T.atDepth v (k * a - s.val)) (T.atDepth v (k * b - s.val))
        rw [hb, trunk, Finset.sum_range_succ]
        rfl
      have h₁ : ‖g x u + g u y - g x y‖ ≤ ε * (if (T.depth u + s.val) % k = 0 then 0 else 1) := by
        split_ifs with hz
        · rw [hu0 hz, hzero]; simp
        · simpa using ht hxu huy hxy
      have h₂ : ‖g u y + g y v - g u v‖ ≤ ε * (if (T.depth v + s.val) % k = 0 then 0 else 1) := by
        split_ifs with hz
        · rw [hv0 hz, hzero]; simp
        · simpa using ht huy hyv (.inr huv)
      rw [hstep]
      calc
        _ = ‖(g x u + g u y - g x y) - (g u y + g y v - g u v)‖ := by congr 1; abel
        _ ≤ ‖g x u + g u y - g x y‖ + ‖g u y + g y v - g u v‖ := norm_sub_le _ _
        _ ≤ _ := by rw [mul_add]; exact add_le_add h₁ h₂
  rcases huv with h | h
  · exact forward u v (.inl h) h.1 h.2.1 h.2.2
  · have hh := forward v u (.inl h) h.1 h.2.1 h.2.2
    rw [hrev u v] at hh
    rw [show g u v - (T.phase k s g v - T.phase k s g u) =
      -(-g u v - (T.phase k s g u - T.phase k s g v)) by abel, norm_neg]
    simpa only [add_comm] using hh

private theorem offset_count {k : ℕ} (hk : 0 < k) (a : ℕ) :
    (∑ s : Fin k, (if (a + s.val) % k = 0 then (0 : ℝ) else 1)) = (k : ℝ) - 1 := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  let x : Fin k := ⟨a % k, Nat.mod_lt a hk⟩
  have he (s : Fin k) : (a + s.val) % k = 0 ↔ s = -x := by
    have hr : (a + s.val) % k = (x + s).val := by simp [Fin.val_add, x, Nat.add_mod]
    rw [hr]
    change (x + s).val = (0 : Fin k).val ↔ _
    rw [Fin.val_inj]
    simpa [add_comm] using (add_eq_zero_iff_eq_neg : s + x = 0 ↔ s = -x)
  simp_rw [he]
  simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem,
    Nat.cast_sub (show 1 ≤ k by omega)]

/-- Averaging the compatible depth-offset potentials gives the width-dependent bound
on any graph of bounded ancestor distance. Branching is unrestricted. -/
theorem exists_banach_gain_potential {k : ℕ} (hk : 0 < k)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ v w, g w v = -g v w)
    (htri : ∀ v w x, (T.graph k).Adj v w → (T.graph k).Adj w x → (T.graph k).Adj v x →
      ‖g v w + g w x - g v x‖ ≤ ε) :
    ∃ p : V → E, ∀ u v, (T.graph k).Adj u v →
      ‖g u v - (p v - p u)‖ ≤ (2 - 2 / (k : ℝ)) * ε := by
  classical
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let p (v : V) := (k : ℝ)⁻¹ • ∑ s : Fin k, T.phase k s g v
  refine ⟨p, fun u v huv => ?_⟩
  let r (s : Fin k) := g u v - (T.phase k s g v - T.phase k s g u)
  have he : g u v - (p v - p u) = (k : ℝ)⁻¹ • ∑ s : Fin k, r s := by
    simp only [r, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hkr.ne', one_smul, p]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hkr)]
  have hsum : ‖∑ s, r s‖ ≤ ε * ((k : ℝ) - 1 + ((k : ℝ) - 1)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ s : Fin k, ε * ((if (T.depth u + s.val) % k = 0 then 0 else 1) +
          (if (T.depth v + s.val) % k = 0 then 0 else 1)) :=
        Finset.sum_le_sum fun s _ => T.phase_bound hk s g ε hε hrev htri huv
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, offset_count hk, offset_count hk]
  calc
    _ ≤ (k : ℝ)⁻¹ * (ε * ((k : ℝ) - 1 + ((k : ℝ) - 1))) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hkr.le)
    _ = _ := by field_simp; ring

end RootedAncestors
end SimpleGraph

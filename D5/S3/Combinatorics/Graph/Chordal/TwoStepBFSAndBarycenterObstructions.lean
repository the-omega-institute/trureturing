/- GID: D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chordal towers and bridged gadgets obstruct two BFS reconstruction schemes. -/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.WeightedTwoStepBFS
import Mathlib.Analysis.SpecificLimits.Basic
/-! # Obstructions for BFS reconstruction on chordal graphs -/
namespace SimpleGraph
open CliqueBoundedBanach (predecessors)
open scoped BigOperators
noncomputable section
variable {V : Type*}
private theorem mem_bfsPred [Fintype V] {G : SimpleGraph V} {o b u : V} :
    b ∈ bfsPred G o u ↔ G.Adj b u ∧ G.dist o b + 1 = G.dist o u := by
  classical
  simp [bfsPred, predecessors]

/-- The normalized potential obtained by averaging the incoming predecessor values. -/
def IsPureBFSBarycenter [Fintype V] (G : SimpleGraph V) (o : V)
    (g : V → V → ℝ) (φ : V → ℝ) : Prop :=
  φ o = 0 ∧ ∀ u ≠ o, (bfsPred G o u).Nonempty →
    φ u = ((bfsPred G o u).card : ℝ)⁻¹ * ∑ b ∈ bfsPred G o u, (φ b + g b u)
private theorem triangle_of_sorted {G : SimpleGraph V} {g : V → V → ℝ} (key : V → ℕ)
    (hskew : ∀ a b, g b a = -g a b)
    (h : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      key a ≤ key b → key b ≤ key c → |g a b + g b c - g a c| ≤ 1) :
    IsTriangleOneGain G g := by
  refine ⟨hskew, fun a b c hab hbc hac => ?_⟩
  let T := fun a b c => |g a b + g b c - g a c|
  have swap (a b c : V) : T b a c = T a b c := by
    dsimp [T]
    rw [hskew a b, ← abs_neg (g a b + g b c - g a c)]
    congr 1
    ring
  have cycle (a b c : V) : T b c a = T a b c := by
    dsimp [T]
    rw [hskew a c, hskew a b]
    congr 1
    ring
  change T a b c ≤ 1
  rcases le_total (key a) (key b) with h₁ | h₁
  · rcases le_total (key b) (key c) with h₂ | h₂
    · exact h a b c hab hbc hac h₁ h₂
    · rcases le_total (key a) (key c) with h₃ | h₃
      · rw [← cycle a b c, ← swap b c a, cycle a c b]
        exact h a c b hac hbc.symm hab h₃ h₂
      · rw [← cycle a b c, ← cycle b c a]
        exact h c a b hac.symm hab hbc.symm h₃ h₁
  · rcases le_total (key a) (key c) with h₂ | h₂
    · rw [← swap a b c]
      exact h b a c hab.symm hac hbc h₁ h₂
    · rcases le_total (key b) (key c) with h₃ | h₃
      · rw [← cycle a b c]
        exact h b c a hbc hac.symm hab.symm h₃ h₂
      · rw [← swap a b c, ← cycle b a c, ← cycle a c b]
        exact h c b a hbc.symm hab.symm hac.symm h₃ h₁
private def refinedRank [Fintype V] (key : V → ℕ) (v : V) : ℕ :=
  key v * Fintype.card V + (Fintype.equivFin V v).val
private theorem refinedRank_lt [Fintype V] {key : V → ℕ} {x y : V}
    (h : key x < key y) : refinedRank key x < refinedRank key y := by
  have hx := (Fintype.equivFin V x).isLt
  have hm := Nat.mul_le_mul_right (Fintype.card V) h
  rw [Nat.succ_mul] at hm
  unfold refinedRank
  omega
private theorem refinedRank_injective [Fintype V] (key : V → ℕ) :
    Function.Injective (refinedRank key) := by
  intro x y h
  have hk : key x = key y := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hl
    · exact (ne_of_lt (refinedRank_lt hl)) h
    · exact (ne_of_lt (refinedRank_lt hl)) h.symm
  apply (Fintype.equivFin V).injective
  apply Fin.ext
  unfold refinedRank at h
  rw [hk] at h
  omega
private theorem chordal_of_weak_order {G : SimpleGraph V} (key : V → ℕ)
    (h : ∀ v, G.IsClique {u | key v ≤ key u ∧ G.Adj v u}) : G.IsChordal := by
  classical
  intro v c hc hl
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image c.support.toFinset key ⟨v, by simp⟩
  have hzs : z ∈ c.support := by simpa using hz
  let d := c.rotate z hzs
  have hd : d.IsCycle := hc.rotate hzs
  have hn : 4 ≤ d.length := by simpa [d] using hl
  have support (x : V) (hx : x ∈ d.support) : x ∈ c.support := by
    rw [← Walk.cons_tail_support] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hzs
    · exact List.mem_of_mem_tail ((c.support_rotate z hzs).mem_iff.mp hx)
  have hs := support d.snd (d.getVert_mem_support 1)
  have hp := support d.penultimate (d.getVert_mem_support (d.length - 1))
  refine ⟨d.snd, d.penultimate, hs, hp, h z
    ⟨hmin _ (by simpa using hs), d.adj_snd hd.not_nil⟩
    ⟨hmin _ (by simpa using hp), (d.adj_penultimate hd.not_nil).symm⟩
    hd.snd_ne_penultimate, ?_⟩
  intro edge
  have mem := Walk.adj_toSubgraph_iff_mem_edges.mpr ((c.rotate_edges z hzs).mem_iff.mpr edge)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at mem
  rw [hd.neighborSet_toSubgraph_internal (by omega) (by omega)] at mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nat.sub_self] at mem
  rcases mem with hm | hm <;>
    have eq := hd.getVert_injOn' (by simp : d.length - 1 ∈ {n | n ≤ d.length - 1})
      (by simp <;> omega) hm <;> omega
private theorem height_le_walk {G : SimpleGraph V} {h : V → ℕ}
    (hlip : ∀ a b, G.Adj a b → h b ≤ h a + 1) {a b : V} (p : G.Walk a b) :
    h b ≤ h a + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    have := hlip a b hab
    simp only [Walk.length_cons]
    omega
/-- The root together with a distinguished column and the other vertices in each layer. -/
abbrev BarycenterVertex (m n : ℕ) := Option (Fin n × Fin m)
private def towerAdj {m n : ℕ} : BarycenterVertex m n → BarycenterVertex m n → Prop
  | none, none => False
  | none, some (i, _) | some (i, _), none => i.val = 0
  | some (i, j), some (k, l) =>
    (i = k ∧ j ≠ l) ∨
    (i.val + 1 = k.val ∧ (l.val ≠ 0 ∨ j.val = 0)) ∨
    (k.val + 1 = i.val ∧ (j.val ≠ 0 ∨ l.val = 0))

/-- Each layer is a clique, and only the distinguished column restricts incoming edges. -/
def barycenterTower (m n : ℕ) : SimpleGraph (BarycenterVertex m n) where
  Adj := towerAdj
  symm := ⟨by
    rintro (_ | ⟨i, j⟩) (_ | ⟨k, l⟩) h <;> simp only [towerAdj] at h ⊢
    all_goals grind⟩
  loopless := ⟨by
    rintro (_ | ⟨i, j⟩)
    · exact id
    · simp [towerAdj]⟩
private def towerHeight {m n : ℕ} : BarycenterVertex m n → ℕ
  | none => 0
  | some (i, _) => i.val + 1
private def towerRank {m n : ℕ} : BarycenterVertex m n → ℕ
  | none => 2 * (n + 1)
  | some (i, j) => 2 * (n - i.val) + if j.val = 0 then 0 else 1
private theorem tower_chordal (m n : ℕ) : (barycenterTower m n).IsChordal := by
  apply chordal_of_weak_order towerRank
  intro u v hv w hw hne
  change towerRank u ≤ towerRank v ∧ towerAdj u v at hv
  change towerRank u ≤ towerRank w ∧ towerAdj u w at hw
  change towerAdj v w
  rcases u with _ | ⟨i, j⟩ <;> rcases v with _ | ⟨k, l⟩ <;> rcases w with _ | ⟨s, t⟩ <;>
    simp only [towerRank, towerAdj] at hv hw ⊢ <;>
    simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, not_true_eq_false] at hne
  all_goals
    first | exact (hne rfl).elim | exact hv.2.elim | exact hw.2.elim | skip
  all_goals
    first | have := i.isLt | skip
    first | have := k.isLt | skip
    first | have := s.isLt | skip
    grind [Fin.ext_iff] <;> omega
private theorem tower_adj_height {m n : ℕ} {u v : BarycenterVertex m n}
    (h : (barycenterTower m n).Adj u v) : towerHeight v ≤ towerHeight u + 1 := by
  rcases u with _ | ⟨i, j⟩ <;> rcases v with _ | ⟨k, l⟩ <;>
    simp only [barycenterTower, towerAdj, towerHeight] at h ⊢
  all_goals grind [Fin.ext_iff]
private theorem tower_walk {m n : ℕ} (i : Fin n) (j : Fin m) :
    ∃ p : (barycenterTower m n).Walk none (some (i, j)), p.length = i.val + 1 := by
  have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
  generalize hi : i.val = d
  induction d generalizing i j with
  | zero => exact ⟨(show (barycenterTower m n).Adj none (some (i, j)) from hi).toWalk, by simp⟩
  | succ d ih =>
    let k : Fin n := ⟨d, by omega⟩
    let z : Fin m := ⟨0, hm⟩
    obtain ⟨p, hp⟩ := ih k z rfl
    have h : (barycenterTower m n).Adj (some (k, z)) (some (i, j)) :=
      Or.inr (Or.inl ⟨hi.symm, Or.inr rfl⟩)
    exact ⟨p.append h.toWalk, by simp [hp, k]⟩
private theorem tower_dist {m n : ℕ} (u : BarycenterVertex m n) :
    (barycenterTower m n).dist none u = towerHeight u := by
  rcases u with _ | ⟨i, j⟩
  · simp [towerHeight]
  obtain ⟨p, hp⟩ := tower_walk i j
  obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
  apply le_antisymm ((dist_le p).trans_eq hp)
  simpa [hq, towerHeight] using height_le_walk (fun _ _ => tower_adj_height) q
private theorem tower_connected (m n : ℕ) : (barycenterTower m n).Connected := by
  refine (connected_iff_exists_forall_reachable (G := barycenterTower m n)).2 ⟨none, ?_⟩
  rintro (_ | ⟨i, j⟩)
  · exact Reachable.rfl
  · exact (tower_walk i j).choose.reachable
private def towerForward {m n : ℕ} (x y : BarycenterVertex m n) : ℝ :=
  match x, y with
  | none, some (_, j) => if j.val = 0 then 0 else 1
  | some (_, j), some (_, l) => if l.val = 0 then 0 else if j.val = 0 then 1 else 2
  | _, _ => 0
/-- Incoming gains are zero into the distinguished column and one or two into its complement. -/
def barycenterGain (m n : ℕ) (x y : BarycenterVertex m n) : ℝ :=
  if towerHeight x < towerHeight y then towerForward x y
  else if towerHeight y < towerHeight x then -towerForward y x else 0
private theorem tower_gain (m n : ℕ) :
    IsTriangleOneGain (barycenterTower m n) (barycenterGain m n) := by
  apply triangle_of_sorted towerHeight
  · intro a b
    unfold barycenterGain
    rcases lt_trichotomy (towerHeight a) (towerHeight b) with h | h | h <;>
      simp [h, not_lt_of_gt]
  · intro a b c hab hbc hac h₁ h₂
    have h₃ := tower_adj_height hac
    rcases a with _ | ⟨i, x⟩ <;> rcases b with _ | ⟨j, y⟩ <;> rcases c with _ | ⟨k, z⟩ <;>
      simp only [barycenterTower, towerAdj, towerHeight] at hab hbc hac h₁ h₂ h₃
    all_goals try omega
    all_goals
      simp only [barycenterGain, towerHeight, towerForward]
      split_ifs <;> norm_num at * <;> grind [Fin.ext_iff]
private def towerValue (m i : ℕ) : ℝ :=
  (2 * (m : ℝ) - 1) - (2 * (m : ℝ) - 2) * (((m : ℝ) - 1) / m) ^ i
private theorem tower_value_succ {m i : ℕ} (hm : 0 < m) :
    towerValue m (i + 1) = (1 + ((m : ℝ) - 1) * (towerValue m i + 2)) / m := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  simp only [towerValue, pow_succ]
  field_simp
  ring
private def towerSolution {m n : ℕ} : BarycenterVertex m n → ℝ
  | none => 0
  | some (i, j) => if j.val = 0 then 0 else towerValue m i.val
private theorem tower_pred_first {m n : ℕ} {i : Fin n} (hi : i.val = 0) (j : Fin m) :
    bfsPred (barycenterTower m n) none (some (i, j)) = {none} := by
  classical
  ext b
  rcases b with _ | ⟨k, l⟩ <;>
    rw [mem_bfsPred, tower_dist, tower_dist] <;>
    simp [towerHeight, barycenterTower, towerAdj, hi]
private theorem tower_pred_next {m n : ℕ} {i k : Fin n} (hik : k.val + 1 = i.val) (j : Fin m) :
    bfsPred (barycenterTower m n) none (some (i, j)) =
      (Finset.univ.filter fun l : Fin m => j.val ≠ 0 ∨ l.val = 0).map
        ⟨fun l => some (k, l), fun _ _ h => congrArg Prod.snd (Option.some.inj h)⟩ := by
  classical
  ext b
  rcases b with _ | ⟨s, t⟩
  · rw [mem_bfsPred, tower_dist, tower_dist]
    simp [towerHeight, barycenterTower, towerAdj]
    omega
  · simp only [mem_bfsPred, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Option.some.injEq, Prod.mk.injEq, tower_dist, towerHeight]
    change towerAdj (some (s, t)) (some (i, j)) ∧ _ ↔ _
    simp only [towerAdj]
    constructor
    · intro ⟨he, hd⟩
      have hs : s = k := Fin.ext (by omega)
      subst s
      refine ⟨t, ?_, rfl⟩
      rcases he with ⟨he, _⟩ | ⟨_, he⟩ | ⟨he, _⟩
      · have := congrArg Fin.val he
        omega
      · exact he
      · omega
    · rintro ⟨l, hl, he⟩
      cases Option.some.inj he
      exact ⟨Or.inr (Or.inl ⟨hik, hl⟩), by omega⟩
private theorem tower_step {m n : ℕ} (hm : 0 < m) (φ : BarycenterVertex m n → ℝ)
    (i : Fin n) (j : Fin m)
    (hroot : φ none = 0)
    (hbefore : ∀ k : Fin n, k.val + 1 = i.val → ∀ l : Fin m,
      φ (some (k, l)) = towerSolution (some (k, l))) :
    let P := bfsPred (barycenterTower m n) none (some (i, j))
    P.Nonempty ∧ (P.card : ℝ)⁻¹ * (∑ b ∈ P, (φ b + barycenterGain m n b (some (i, j)))) =
      towerSolution (some (i, j)) := by
  classical
  dsimp only
  by_cases hi : i.val = 0
  · rw [tower_pred_first hi]
    norm_num [hroot, barycenterGain, towerForward, towerHeight, hi, towerSolution, towerValue]
  let k : Fin n := ⟨i.val - 1, by omega⟩
  let z : Fin m := ⟨0, hm⟩
  have hik : k.val + 1 = i.val := by dsimp [k]; omega
  have hlt : k.val + 1 < i.val + 1 := by omega
  rw [tower_pred_next hik]
  have hz (b : Fin m) : b.val = 0 ↔ b = z :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  by_cases hj : j.val = 0
  · have he : (Finset.univ.filter fun l : Fin m => j.val ≠ 0 ∨ l.val = 0) = {z} := by
      ext b
      simp [hj, hz b]
    rw [he]
    simp only [Finset.map_singleton, Finset.card_singleton, Nat.cast_one, inv_one, one_mul,
      Finset.sum_singleton, Function.Embedding.coeFn_mk]
    change ({some (k, z)} : Finset (BarycenterVertex m n)).Nonempty ∧
      φ (some (k, z)) + barycenterGain m n (some (k, z)) (some (i, j)) = towerSolution (some (i, j))
    rw [hbefore k hik z]
    simp [towerSolution, z, barycenterGain, towerHeight, towerForward, hlt, hj]
  have he : (Finset.univ.filter fun l : Fin m => j.val ≠ 0 ∨ l.val = 0) = Finset.univ := by
    simp [hj]
  rw [he]
  have heval (l : Fin m) :
      φ (some (k, l)) + barycenterGain m n (some (k, l)) (some (i, j)) =
        if l = z then 1 else towerValue m k.val + 2 := by
    rw [hbefore k hik l]
    by_cases hl : l.val = 0
    · simp [towerSolution, barycenterGain, towerHeight, towerForward, hlt, hj, (hz l).mp hl, z]
    · simp [towerSolution, barycenterGain, towerHeight, towerForward, hlt, hj, hl, mt (hz l).mpr hl]
  constructor
  · exact ⟨some (k, z), Finset.mem_map.mpr ⟨z, Finset.mem_univ _, rfl⟩⟩
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, Finset.sum_map]
  change _ * (∑ b : Fin m, (φ (some (k, b)) + barycenterGain m n (some (k, b)) (some (i, j)))) = _
  simp_rw [heval]
  have hzmem : z ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hzmem]
  have hf : ∀ b ∈ (Finset.univ : Finset (Fin m)).erase z,
      (if b = z then (1 : ℝ) else towerValue m k.val + 2) = towerValue m k.val + 2 :=
    fun b hb => ite_eq_right (Finset.mem_erase.mp hb).1
  rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hzmem]
  simp only [Finset.card_univ, Fintype.card_fin, ite_eq_left rfl, towerSolution, ite_eq_right hj, ← hik]
  rw [tower_value_succ hm, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  rw [div_eq_mul_inv]
  simp only [ite_true]
  ring
private theorem tower_eval {m n : ℕ} (hm : 0 < m) {φ : BarycenterVertex m n → ℝ}
    (hφ : IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ) :
    ∀ i j, φ (some (i, j)) = towerSolution (some (i, j)) := by
  intro i
  generalize hi : i.val = d
  induction d using Nat.strong_induction_on generalizing i with
  | h d ih =>
    intro j
    have hstep := tower_step hm φ i j hφ.1 (fun k hk => ih k.val (by omega) k rfl)
    exact (hφ.2 _ (by simp) hstep.1).trans hstep.2
/-- The exact tower values give arbitrarily large residuals for pure predecessor averaging. -/
theorem pure_predecessor_barycenter_unbounded :
    (∀ m n : ℕ, 2 ≤ m → 1 ≤ n →
      (barycenterTower m n).IsChordal ∧ (barycenterTower m n).Connected ∧
      IsTriangleOneGain (barycenterTower m n) (barycenterGain m n) ∧
      (∃ φ, IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ) ∧
      ∀ i : Fin n, ∀ j : Fin m, (barycenterTower m n).dist none (some (i, j)) = i.val + 1 ∧
        ∀ φ, IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ →
          φ (some (i, j)) = if j.val = 0 then 0 else
            (2 * (m : ℝ) - 1) - (2 * (m : ℝ) - 2) * (((m : ℝ) - 1) / m) ^ i.val) ∧
    ∀ M : ℝ, ∃ m n : ℕ, 2 ≤ m ∧ 1 ≤ n ∧
      (barycenterTower m n).IsChordal ∧ (barycenterTower m n).Connected ∧
      IsTriangleOneGain (barycenterTower m n) (barycenterGain m n) ∧
      ∃ u v, (barycenterTower m n).Adj u v ∧ ∀ φ,
        IsPureBFSBarycenter (barycenterTower m n) none (barycenterGain m n) φ →
          M < |barycenterGain m n u v - (φ v - φ u)| := by
  constructor
  · intro m n hm _
    exact ⟨tower_chordal m n, tower_connected m n, tower_gain m n,
      ⟨towerSolution, rfl, by
        rintro (_ | ⟨i, j⟩) hu _
        · exact (hu rfl).elim
        · exact (tower_step (by omega) towerSolution i j rfl (fun _ _ _ => rfl)).2.symm⟩, fun i j =>
        ⟨tower_dist _, fun _ hφ => tower_eval (by omega) hφ i j⟩⟩
  intro M
  obtain ⟨s, hs⟩ := exists_nat_gt (max 2 (M + 1))
  let m := s + 2
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by dsimp [m]; omega)
  have hlim : M < 2 * (m : ℝ) - 1 := by
    have := (le_max_right 2 (M + 1)).trans_lt hs
    push_cast [m]
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hpow : Filter.Tendsto (fun i : ℕ => (((m : ℝ) - 1) / m) ^ i)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (by linarith) (by linarith))
      ((div_lt_one (by linarith)).2 (by linarith))
  have ht : Filter.Tendsto (towerValue m) Filter.atTop (nhds (2 * (m : ℝ) - 1)) := by
    unfold towerValue
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
  obtain ⟨i, hi⟩ := (ht.eventually (lt_mem_nhds hlim)).exists
  let k : Fin (i + 1) := ⟨i, by omega⟩
  let a : Fin m := ⟨0, by dsimp [m]; omega⟩
  let b : Fin m := ⟨1, by dsimp [m]; omega⟩
  refine ⟨m, i + 1, by dsimp [m]; omega, by omega, tower_chordal _ _, tower_connected _ _,
    tower_gain _ _, some (k, a), some (k, b), Or.inl ⟨rfl, fun he => by have : (0 : ℕ) = 1 := congrArg Fin.val he; omega⟩, ?_⟩
  intro φ hφ
  rw [tower_eval (by dsimp [m]; omega) hφ k a, tower_eval (by dsimp [m]; omega) hφ k b]
  simp only [barycenterGain, towerHeight, lt_irrefl, ite_false, towerSolution,
    a, b, k, eq_self, ite_true, one_ne_zero, sub_zero, zero_sub, abs_neg]
  exact hi.trans_le (le_abs_self _)
inductive GadgetVertex (m : ℕ)
  | root
  | a (j : Fin m)
  | u (i : Fin m)
  | v (j : Fin m)
  | y (j : Fin m)
  deriving DecidableEq, Fintype
private abbrev GadgetVertices (m N : ℕ) := Fin N × GadgetVertex m
private def gadgetLocalAdj {m : ℕ} : GadgetVertex m → GadgetVertex m → Prop
  | .root, .a _ | .a _, .root => True
  | .a i, .a j | .u i, .u j => i ≠ j
  | .a _, .u _ | .u _, .a _ | .u _, .v _ | .v _, .u _ |
      .u _, .y _ | .y _, .u _ => True
  | .a i, .v j | .v i, .a j | .v i, .y j | .y i, .v j => i = j
  | _, _ => False
/-- Copies of the gadget with their distinguished roots joined by a path. -/
def bridgedGadget (m N : ℕ) : SimpleGraph (GadgetVertices m N) where
  Adj x y := (x.1 = y.1 ∧ gadgetLocalAdj x.2 y.2) ∨
    (x.2 = .root ∧ y.2 = .root ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))
  symm := ⟨by
    rintro ⟨k, x⟩ ⟨l, y⟩ h
    rcases h with ⟨h, hl⟩ | ⟨hx, hy, h⟩
    · exact Or.inl ⟨h.symm, by cases x <;> cases y <;> simp_all [gadgetLocalAdj, eq_comm]⟩
    · exact Or.inr ⟨hy, hx, h.symm⟩⟩
  loopless := ⟨by
    rintro ⟨k, x⟩ h
    rcases h with ⟨_, hl⟩ | ⟨_, _, h⟩
    · cases x <;> simp [gadgetLocalAdj] at hl
    · omega⟩
private def gadgetRank {m N : ℕ} : GadgetVertices m N → ℕ
  | (_, .y _) => 0
  | (_, .v _) => 1
  | (_, .u _) => 2
  | (_, .a _) => 3
  | (k, .root) => 4 + k.val
private def gadgetDepth {m : ℕ} : GadgetVertex m → ℕ
  | .root => 0
  | .a _ => 1
  | .u _ | .v _ => 2
  | .y _ => 3
set_option maxHeartbeats 1200000 in
private theorem gadget_chordal (m N : ℕ) : (bridgedGadget m N).IsChordal := by
  apply chordal_of_weak_order gadgetRank
  rintro ⟨k, x⟩ ⟨l, y⟩ hy ⟨s, z⟩ hz hne
  change gadgetRank (k, x) ≤ gadgetRank (l, y) ∧ (bridgedGadget m N).Adj (k, x) (l, y) at hy
  change gadgetRank (k, x) ≤ gadgetRank (s, z) ∧ (bridgedGadget m N).Adj (k, x) (s, z) at hz
  cases x <;> cases y <;> cases z <;>
    simp [bridgedGadget, gadgetLocalAdj, gadgetRank] at hy hz hne ⊢ <;>
    grind [Fin.ext_iff]
private theorem adjacent_local {m N : ℕ} (k : Fin N) {x y : GadgetVertex m}
    (h : gadgetLocalAdj x y) : (bridgedGadget m N).Adj (k, x) (k, y) :=
  Or.inl ⟨rfl, h⟩
private theorem gadget_local_walk {m N : ℕ} (hm : 0 < m) (k : Fin N) (x : GadgetVertex m) :
    ∃ p : (bridgedGadget m N).Walk (k, .root) (k, x), p.length = gadgetDepth x := by
  let z : Fin m := ⟨0, hm⟩
  have ra (j : Fin m) := adjacent_local k (show gadgetLocalAdj .root (.a j) from trivial)
  cases x with
  | root => exact ⟨.nil, rfl⟩
  | a j => exact ⟨(ra j).toWalk, rfl⟩
  | u i => exact ⟨.cons (ra z) (adjacent_local k (x := .a z) (y := .u i) trivial).toWalk, rfl⟩
  | v j => exact ⟨.cons (ra j) (adjacent_local k (x := .a j) (y := .v j) rfl).toWalk, rfl⟩
  | y j =>
    exact ⟨.cons (ra z) (.cons (adjacent_local k (y := .u z) trivial)
      (adjacent_local k (x := .u z) (y := .y j) trivial).toWalk), rfl⟩
private theorem gadget_connected {m N : ℕ} (hm : 0 < m) (hN : 0 < N) :
    (bridgedGadget m N).Connected := by
  let o : Fin N := ⟨0, hN⟩
  have reach (k : Fin N) : (bridgedGadget m N).Reachable (o, .root) (k, .root) := by
    generalize hk : k.val = d
    induction d generalizing k with
    | zero => exact (show o = k from Fin.ext hk.symm) ▸ Reachable.rfl
    | succ d ih =>
      let l : Fin N := ⟨d, by omega⟩
      have he : (bridgedGadget m N).Adj (l, .root) (k, .root) :=
        Or.inr ⟨rfl, rfl, Or.inl hk.symm⟩
      exact (ih l rfl).trans he.reachable
  have reach_all (x : GadgetVertices m N) : (bridgedGadget m N).Reachable (o, .root) x :=
    (reach x.1).trans (gadget_local_walk hm x.1 x.2).choose.reachable
  exact { preconnected := fun x y => (reach_all x).symm.trans (reach_all y), nonempty := ⟨(o, .root)⟩ }
private theorem gadget_dist {m N : ℕ} (hm : 0 < m) (hconn : (bridgedGadget m N).Connected)
    (r : GadgetVertices m N) (k : Fin N) (hr : r.1 ≠ k) (x : GadgetVertex m) :
    (bridgedGadget m N).dist r (k, x) = (bridgedGadget m N).dist r (k, .root) + gadgetDepth x := by
  let G := bridgedGadget m N
  let d := G.dist r (k, .root)
  let h := fun v : GadgetVertices m N =>
    if v.1 = k then d + gadgetDepth v.2 else G.dist r v
  obtain ⟨p, hp⟩ := gadget_local_walk hm k x
  have hupper : G.dist r (k, x) ≤ d + gadgetDepth x :=
    (hconn.dist_triangle (u := r) (v := (k, .root)) (w := (k, x))).trans
      (Nat.add_le_add_left ((dist_le p).trans_eq hp) d)
  apply le_antisymm hupper
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist r (k, x)
  have hlip (a b : GadgetVertices m N) (hab : G.Adj a b) : h b ≤ h a + 1 := by
    have hd : G.dist r b ≤ G.dist r a + 1 := by
      have h : G.dist r b ≤ G.dist r a + G.dist a b := hconn.dist_triangle
      rwa [dist_eq_one_iff_adj.mpr hab] at h
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    rcases hab with ⟨hij, hab⟩ | ⟨ha, hb, _⟩
    · change i = j at hij
      subst j
      by_cases hi : i = k
      · simp only [h, hi, ite_true]
        cases a <;> cases b <;> simp_all [gadgetDepth, gadgetLocalAdj] <;> omega
      · simp only [h, hi, ite_false]
        omega
    · change a = .root at ha
      change b = .root at hb
      subst a
      subst b
      by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all [h, d, gadgetDepth]
  simpa [h, hr, hq] using height_le_walk hlip q
private def gadgetFamily {m N : ℕ} (k : Fin N) (f : Fin m → GadgetVertex m) :
    Finset (GadgetVertices m N) := Finset.univ.image fun j => (k, f j)
private theorem mem_gadgetFamily {m N : ℕ} {k : Fin N} {f : Fin m → GadgetVertex m}
    {b : GadgetVertices m N} : b ∈ gadgetFamily k f ↔ ∃ t, (k, f t) = b := by
  simp [gadgetFamily]
private theorem sum_gadgetFamily {m N : ℕ} {k : Fin N} {f : Fin m → GadgetVertex m}
    (hf : Function.Injective f) (w : GadgetVertices m N → ℝ) :
    ∑ b ∈ gadgetFamily k f, w b = ∑ t, w (k, f t) := by
  apply Finset.sum_image
  intro a _ b _ h
  exact hf (congrArg Prod.snd h)
private theorem gadget_pred_u {m N : ℕ} {r : GadgetVertices m N} {k : Fin N}
    (d : ℕ) (hd : ∀ x : GadgetVertex m, (bridgedGadget m N).dist r (k, x) = d + gadgetDepth x)
    (i : Fin m) :
    bfsPred (bridgedGadget m N) r (k, .u i) =
      gadgetFamily k GadgetVertex.a := by
  classical
  ext b
  obtain ⟨l, b⟩ := b
  by_cases hl : l = k
  · subst l
    rw [mem_bfsPred, hd, hd]
    cases b <;> simp [bridgedGadget, gadgetLocalAdj, mem_gadgetFamily, gadgetDepth]
  · simp [mem_bfsPred, bridgedGadget, mem_gadgetFamily, hl, Ne.symm hl]
private theorem gadget_pred_y {m N : ℕ} {r : GadgetVertices m N} {k : Fin N}
    (d : ℕ) (hd : ∀ x : GadgetVertex m, (bridgedGadget m N).dist r (k, x) = d + gadgetDepth x)
    (j : Fin m) :
    bfsPred (bridgedGadget m N) r (k, .y j) =
      insert (k, .v j) (gadgetFamily k GadgetVertex.u) := by
  classical
  ext b
  obtain ⟨l, b⟩ := b
  by_cases hl : l = k
  · subst l
    rw [mem_bfsPred, hd, hd]
    cases b <;> simp [bridgedGadget, gadgetLocalAdj, mem_gadgetFamily, gadgetDepth]
  · simp [mem_bfsPred, bridgedGadget, mem_gadgetFamily, hl, Ne.symm hl]
private theorem gadget_tail_copy {m N : ℕ} {r : GadgetVertices m N} {k : Fin N} {d l : ℕ}
    (hd : (bridgedGadget m N).dist r (k, .root) = d) (hl : d < l)
    {x y : Tail (bridgedGadget m N) r l} (p : ((bridgedGadget m N).induce
      (Tail (bridgedGadget m N) r l)).Walk x y) : x.val.1 = k → y.val.1 = k := by
  induction p with
  | nil => exact id
  | @cons x z y hx _ ih =>
    intro hk
    apply ih
    change (bridgedGadget m N).Adj x.val z.val at hx
    rcases hx with ⟨he, _⟩ | ⟨hr, _, _⟩
    · exact he.symm.trans hk
    · have h := x.property
      change l ≤ (bridgedGadget m N).dist r x.val at h
      rw [show x.val = (k, .root) from Prod.ext hk hr, hd] at h
      omega
private theorem gadget_anchors {m N : ℕ} {r : GadgetVertices m N} {k : Fin N} {d : ℕ}
    (hd : ∀ x : GadgetVertex m, (bridgedGadget m N).dist r (k, x) = d + gadgetDepth x)
    {a : (l : ℕ) → Component (bridgedGadget m N) r (l + 1) → GadgetVertices m N}
    (ha : ValidShadowAnchors (bridgedGadget m N) r a) (i j : Fin m) :
    let G := bridgedGadget m N
    let C := componentOf G r (d + 2 + 1) (k, .y j) ((hd (.y j)).ge)
    let D := componentOf G r (d + 1 + 1) (k, .u i) ((hd (.u i)).ge)
    parent G r C = D ∧ a (d + 2) C = (k, .a j) ∧ a (d + 1) D = (k, .root) := by
  dsimp only
  let G := bridgedGadget m N
  have hy : G.dist r (k, .y j) = d + 2 + 1 := by simpa [gadgetDepth] using hd (.y j)
  have hu : G.dist r (k, .u i) = d + 2 := hd _
  let C := componentOf G r (d + 2 + 1) (k, .y j) hy.ge
  let D := componentOf G r (d + 1 + 1) (k, .u i) hu.ge
  have hp : parent G r C = D :=
    shadow_parent (mem_shadow_of_adj hu hy.ge (adjacent_local k (x := .u i) (y := .y j) trivial))
  let y : GadgetVertices m N := (k, .y j)
  have shadow_y (b) : b ∈ Shadow G r C ↔ b ∈ bfsPred G r y := by
    constructor
    · rintro ⟨hb, x, hx, hbx⟩
      obtain ⟨p⟩ := ConnectedComponent.exact ((ConnectedComponent.mem_supp_iff _ x).mp hx).symm
      have he : x.val = y := by
        cases p with
        | nil => rfl
        | @cons _ z _ h _ =>
          change G.Adj y z.val at h
          obtain ⟨⟨s, q⟩, hz⟩ := z
          rcases h with ⟨hs, h⟩ | ⟨h, _, _⟩
          · change k = s at hs
            subst s
            change d + 3 ≤ G.dist r (k, q) at hz
            rw [hd] at hz
            cases q <;> simp_all [y, gadgetLocalAdj, gadgetDepth] <;> omega
          · cases h
      apply mem_bfsPred.mpr
      change G.Adj b y ∧ G.dist r b + 1 = G.dist r y
      exact ⟨by rw [← he]; exact hbx, by rw [hb]; exact (hd (.y j)).symm⟩
    · intro hb
      obtain ⟨ha, hl⟩ := mem_bfsPred.mp hb
      change G.dist r b + 1 = G.dist r (k, .y j) at hl
      have he : G.dist r b = d + 2 := by omega
      exact mem_shadow_of_adj he (hd (.y j)).ge ha
  have shadow_u (b) : b ∈ Shadow G r D ↔ b ∈ gadgetFamily k GadgetVertex.a := by
    constructor
    · rintro ⟨hb, x, hx, hbx⟩
      obtain ⟨p⟩ := ConnectedComponent.exact ((ConnectedComponent.mem_supp_iff _ x).mp hx).symm
      have hk : x.val.1 = k := gadget_tail_copy (by simpa [gadgetDepth] using hd .root)
        (by omega) p rfl
      rcases hbx with ⟨he, _⟩ | ⟨_, he, _⟩
      · rcases b with ⟨l, b⟩
        change l = x.val.1 at he
        rw [hk] at he
        subst l
        rw [hd] at hb
        cases b <;> simp [gadgetDepth, mem_gadgetFamily] at hb ⊢ <;> omega
      · have hd' : d + 2 ≤ G.dist r x.val := x.property
        rw [show x.val = (k, .root) from Prod.ext hk he, hd] at hd'
        simp [gadgetDepth] at hd'
    · intro hb
      obtain ⟨j, rfl⟩ := mem_gadgetFamily.mp hb
      exact mem_shadow_of_adj (hd (.a j)) (hd (.u i)).ge (adjacent_local k trivial)
  have hV : (k, .v j) ∈ Shadow G r C :=
    (shadow_y _).mpr (gadget_pred_y d hd j ▸ Finset.mem_insert_self _ _)
  have ha₂ := (ha.2 (d + 1) C).2 _ hV
  have hforced : a (d + 2) C = (k, .a j) := by
    have haDist := (ha.2 (d + 1) C).1.1
    generalize he : a (d + 2) C = b at haDist ha₂ ⊢
    obtain ⟨l, b⟩ := b
    rcases ha₂ with ⟨rfl, hb⟩ | ⟨_, he, _⟩
    · rw [hd] at haDist
      cases b <;> simp_all [gadgetLocalAdj, gadgetDepth] <;> omega
    · cases he
  have haS : (k, .a j) ∈ Shadow G r D :=
    (shadow_u _).mpr (mem_gadgetFamily.mpr ⟨j, rfl⟩)
  have ho₁ := (ha.2 d D).1.1
  have ho₂ := (ha.2 d D).2 _ haS
  refine ⟨hp, hforced, ?_⟩
  generalize he : a (d + 1) D = b at ho₁ ho₂ ⊢
  obtain ⟨l, b⟩ := b
  rcases ho₂ with ⟨rfl, hb⟩ | ⟨_, he, _⟩
  · rw [hd] at ho₁
    cases b <;> simp_all [gadgetLocalAdj, gadgetDepth] <;> omega
  · cases he
private def rankedGain (rank : V → ℕ) (a b : V) : ℝ :=
  if rank a < rank b then 1 else if rank b < rank a then -1 else 0
private theorem ranked_gain {G : SimpleGraph V} {rank : V → ℕ}
    (hrank : Function.Injective rank) : IsTriangleOneGain G (rankedGain rank) := by
  apply triangle_of_sorted rank
  · intro a b
    rcases lt_trichotomy (rank a) (rank b) with h | h | h <;>
      simp [rankedGain, h, not_lt_of_gt]
  · intro a b c hab hbc _ hx hy
    have h₁ := hx.lt_of_ne (fun h => hab.ne (hrank h))
    have h₂ := hy.lt_of_ne (fun h => hbc.ne (hrank h))
    norm_num [rankedGain, h₁, h₂, h₁.trans h₂]
private def obstructionRank {m N : ℕ} (k : Fin N) (i j : Fin m) :
    GadgetVertices m N → ℕ
  | (l, x) => if l ≠ k then 0 else match x with
    | .root => 0
    | .a t => if t = j then 5 else 1
    | .u t => if t = i then 2 else 4
    | .v _ => 4
    | .y _ => 3
private theorem min_le_average {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℝ} {b : ℝ}
    (h : ∑ x, f x ≤ (Fintype.card ι : ℝ) * b) : ∃ x, f x ≤ b := by
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le (g := fun _ => b) Finset.univ_nonempty
    (by simpa [nsmul_eq_mul] using h)
  exact ⟨x, hx⟩
private theorem average_indicator [DecidableEq V] {s : Finset V} {w f : V → ℝ} {a : V} {c : ℝ}
    (ha : a ∈ s) (hs : ∑ b ∈ s, w b = 1) (hf : ∀ b ∈ s, f b = if b = a then 0 else c) :
    ∑ b ∈ s, w b * f b = c * (1 - w a) := by
  classical
  have he : ∀ b ∈ s, w b * f b = w b * c - (if b = a then w a * c else 0) := by
    intro b hb
    rw [hf b hb]
    by_cases e : b = a <;> simp [e]
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  simp [ha]
  ring
private theorem potential_at [Fintype V] {G : SimpleGraph V} {o u : V}
    {a : (k : ℕ) → Component G o (k + 1) → V} {w g : V → V → ℝ} {d : ℕ}
    (h : G.dist o u = d) : twoStepBFSPotential G o a w g u = potentialAt G o a w g u d h := by
  subst d
  rfl
private theorem gadget_signed_residual {m N : ℕ} {r : GadgetVertices m N}
    {k : Fin N} {d : ℕ}
    {a : (l : ℕ) → Component (bridgedGadget m N) r (l + 1) → GadgetVertices m N}
    {w : (GadgetVertices m N) → (GadgetVertices m N) → ℝ}
    (ha : ValidShadowAnchors (bridgedGadget m N) r a)
    (hw : ValidPredecessorWeights (bridgedGadget m N) r w) (hr : r.1 ≠ k)
    (hd : ∀ x : GadgetVertex m, (bridgedGadget m N).dist r (k, x) = d + gadgetDepth x)
    (i j : Fin m) :
    let u := (k, GadgetVertex.u i)
    let y := (k, GadgetVertex.y j)
    let g := rankedGain (refinedRank (obstructionRank k i j))
    let φ := twoStepBFSPotential (bridgedGadget m N) r a w g
    g u y - (φ y - φ u) = 4 - 2 * w u (k, .a j) - 2 * w y u := by
  classical
  dsimp only
  let G := bridgedGadget m N
  let u := (k, GadgetVertex.u i)
  let y := (k, GadgetVertex.y j)
  let c := (k, GadgetVertex.a j)
  let o := (k, (GadgetVertex.root : GadgetVertex m))
  let rank := obstructionRank k i j
  let g := rankedGain (refinedRank rank)
  have pos {x z} (h : rank x < rank z) : g x z = 1 :=
    ite_eq_left (refinedRank_lt h)
  have neg {x z} (h : rank z < rank x) : g x z = -1 := by
    have h' := refinedRank_lt h
    simp [g, rankedGain, h', not_lt_of_gt h']
  have hdu : G.dist r u = d + 1 + 1 := hd _
  have hdy : G.dist r y = d + 2 + 1 := hd _
  obtain ⟨hp, hc, ho⟩ := gadget_anchors hd ha i j
  rw [potential_at hdu, potential_at hdy]
  simp only [potentialAt]
  have step (C : Component G r (d + 2 + 1)) : transport g a (d + 2) C =
      transport g a (d + 1) (parent G r C) + g (a (d + 1) (parent G r C)) (a (d + 2) C) := rfl
  rw [step, hp, hc, ho]
  change g u y - ((_ + g o c + _) - (_ + _)) = _
  have hpu := gadget_pred_u d hd i
  have hpy := gadget_pred_y d hd j
  have hu : u ≠ r := fun h => hr (congrArg Prod.fst h).symm
  have hy : y ≠ r := fun h => hr (congrArg Prod.fst h).symm
  have hs₁ : ∑ b ∈ bfsPred G r u, w u b * (g o b + g b u) = 2 * (1 - w u c) := by
    refine average_indicator ?_ (hw.2.2 u hu) ?_
    · rw [hpu]
      exact mem_gadgetFamily.mpr ⟨j, rfl⟩
    intro b hb
    rw [hpu] at hb
    obtain ⟨t, rfl⟩ := mem_gadgetFamily.mp hb
    by_cases ht : t = j
    · subst t
      rw [pos (by simp [rank, obstructionRank, o, c]), neg (by simp [rank, obstructionRank, u, c])]
      norm_num [gadgetFamily, c]
    · rw [pos (by simp [rank, obstructionRank, o, gadgetFamily, ht]),
        pos (by simp [rank, obstructionRank, u, gadgetFamily, ht])]
      norm_num [gadgetFamily, c, ht]
  have hs₂ : ∑ b ∈ bfsPred G r y, w y b * (g c b + g b y) = -2 * (1 - w y u) := by
    refine average_indicator ?_ (hw.2.2 y hy) ?_
    · rw [hpy]
      exact Finset.mem_insert_of_mem (mem_gadgetFamily.mpr ⟨i, rfl⟩)
    intro b hb
    rw [hpy, Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · rw [neg (by simp [rank, obstructionRank, c]), neg (by simp [rank, obstructionRank, y])]
      norm_num [u]
    obtain ⟨t, rfl⟩ := mem_gadgetFamily.mp hb
    by_cases ht : t = i
    · subst t
      rw [neg (by simp [rank, obstructionRank, c, gadgetFamily]), pos (by simp [rank, obstructionRank, y, gadgetFamily])]
      norm_num [gadgetFamily, u]
    · rw [neg (by simp [rank, obstructionRank, c, gadgetFamily, ht]),
        neg (by simp [rank, obstructionRank, y, gadgetFamily, ht])]
      norm_num [gadgetFamily, u, ht]
  rw [hs₁, hs₂, pos (by simp [rank, obstructionRank, u, y]), pos (by simp [rank, obstructionRank, o, c])]
  ring
/-- Averaging two-step potentials over roots still permits a residual approaching four. -/
theorem twoStepBFS_root_averaging_lower_bound (m N : ℕ) (hm : 2 ≤ m) (hN : 2 ≤ N) :
    let G := bridgedGadget m N
    G.IsChordal ∧ G.Connected ∧
    ∀ (μ : GadgetVertices m N → ℝ), (∀ r, 0 ≤ μ r) → (∑ r, μ r = 1) →
      ∀ (a : (r : GadgetVertices m N) → (l : ℕ) → Component G r (l + 1) → GadgetVertices m N)
        (w : (GadgetVertices m N) → (GadgetVertices m N) → (GadgetVertices m N) → ℝ),
        (∀ r, ValidShadowAnchors G r (a r)) → (∀ r, ValidPredecessorWeights G r (w r)) →
        ∃ g : (GadgetVertices m N) → (GadgetVertices m N) → ℝ,
          IsTriangleOneGain G g ∧ ∃ u v, G.Adj u v ∧
            let Φ := fun x => ∑ r, μ r * twoStepBFSPotential G r (a r) (w r) g x
            4 - 4 / (m : ℝ) - 8 / (N : ℝ) ≤ |g u v - (Φ v - Φ u)| := by
  classical
  let G := bridgedGadget m N
  let W := GadgetVertices m N
  have hc := gadget_connected (m := m) (N := N) (by omega) (by omega)
  refine ⟨gadget_chordal m N, hc, ?_⟩
  intro μ hμ hmass a w ha hw
  have hmp : (0 : ℝ) < m := by positivity
  have hNp : (0 : ℝ) < N := by positivity
  let mass (k : Fin N) := ∑ r ∈ (Finset.univ : Finset W).filter (fun r => r.1 = k), μ r
  have hsum : ∑ k, mass k = 1 := by
    rw [← hmass]
    simpa only [Finset.mem_univ, Finset.filter_true] using
      (Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ Prod.fst μ)
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk⟩ := min_le_average (f := mass) (b := 1 / (N : ℝ)) (by
    rw [hsum, Fintype.card_fin, mul_one_div_cancel hNp.ne'])
  let inside := (Finset.univ : Finset W).filter (fun r => r.1 = k)
  let outside := (Finset.univ : Finset W).filter (fun r => r.1 ≠ k)
  let S := ∑ r ∈ outside, μ r
  have split (f : W → ℝ) : ∑ r ∈ inside, f r + ∑ r ∈ outside, f r = ∑ r, f r :=
    Finset.sum_filter_add_sum_filter_not _ (fun r => r.1 = k) f
  have hS : mass k + S = 1 := (split μ).trans hmass
  have hd (r : W) (hr : r.1 ≠ k) (x : GadgetVertex m) :=
    gadget_dist (by omega : 0 < m) hc r k hr x
  let cost (r : W) (i j : Fin m) := w r (k, .u i) (k, .a j) + w r (k, .y j) (k, .u i)
  have hcost (r : W) (hr : r.1 ≠ k) : ∑ p : Fin m × Fin m, cost r p.1 p.2 ≤ 2 * (m : ℝ) := by
    have su (i : Fin m) : ∑ j, w r (k, .u i) (k, .a j) = 1 := by
      have h := (hw r).2.2 (k, .u i) (fun h => hr (congrArg Prod.fst h).symm)
      simpa only [gadget_pred_u _ (hd r hr),
        sum_gadgetFamily (f := GadgetVertex.a) (fun _ _ h => GadgetVertex.a.inj h)] using h
    have sy (j : Fin m) : ∑ i, w r (k, .y j) (k, .u i) ≤ 1 := by
      have h := (hw r).2.2 (k, .y j) (fun h => hr (congrArg Prod.fst h).symm)
      rw [gadget_pred_y _ (hd r hr), Finset.sum_insert (by simp [mem_gadgetFamily]),
        sum_gadgetFamily (f := GadgetVertex.u) (fun _ _ h => GadgetVertex.u.inj h)] at h
      exact le_of_add_le_of_nonneg_right h.le ((hw r).1 _ _)
    rw [Fintype.sum_prod_type]
    simp only [cost, Finset.sum_add_distrib, su]
    rw [Finset.sum_comm (f := fun i j => w r (k, .y j) (k, .u i))]
    have hy := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun j _ => sy j)
    simp at hy ⊢
    linarith
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨⟨i, j⟩, hij⟩ := min_le_average
    (f := fun p : Fin m × Fin m => ∑ r ∈ outside, μ r * cost r p.1 p.2)
    (b := (2 / (m : ℝ)) * S) (by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      calc
        _ ≤ ∑ r ∈ outside, μ r * (2 * (m : ℝ)) := Finset.sum_le_sum fun r hr =>
          mul_le_mul_of_nonneg_left (hcost r (Finset.mem_filter.mp hr).2) (hμ r)
        _ = _ := by rw [← Finset.sum_mul]; simp [S, Nat.cast_mul]; field_simp)
  let u : W := (k, .u i)
  let v : W := (k, .y j)
  let rank := refinedRank (obstructionRank k i j)
  let g := rankedGain rank
  have huv : G.Adj u v := adjacent_local k trivial
  refine ⟨g, ranked_gain (refinedRank_injective _), u, v, huv, ?_⟩
  let φ (r : W) := twoStepBFSPotential G r (a r) (w r) g
  let residual (r : W) := g u v - (φ r v - φ r u)
  have ho : ∑ r ∈ outside, μ r * residual r ≥ 4 * S - 2 * ((2 / (m : ℝ)) * S) := by
    have h (r : W) (hr : r ∈ outside) : residual r = 4 - 2 * cost r i j := by
      have hr' := (Finset.mem_filter.mp hr).2
      have he := gadget_signed_residual (ha r) (hw r) hr' (hd r hr') i j
      dsimp only at he
      dsimp only [residual, cost, φ, g, rank, u, v]
      linarith
    rw [Finset.sum_congr rfl (fun r hr => congrArg (μ r * ·) (h r hr))]
    have he : ∑ r ∈ outside, μ r * (4 - 2 * cost r i j) =
        4 * S - 2 * ∑ r ∈ outside, μ r * cost r i j := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, S]
      rw [mul_comm _ (4 : ℝ)]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [he]
    linarith
  have hi : -4 * mass k ≤ ∑ r ∈ inside, μ r * residual r := by
    calc
      -4 * mass k = ∑ r ∈ inside, μ r * -4 := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
        (abs_le.mp (two_step_residual_bound (gadget_chordal m N) hc (ha r) (hw r)
          (ranked_gain (refinedRank_injective _)) huv)).1 (hμ r)
  have he : ∑ r, μ r * residual r = g u v - ((∑ r, μ r * φ r v) - ∑ r, μ r * φ r u) := by
    simp only [residual, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  have h₂ : 0 ≤ 4 / (m : ℝ) * mass k := mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => hμ r)
  have hfinal : 4 - 4 / (m : ℝ) - 8 / (N : ℝ) ≤ ∑ r, μ r * residual r := by
    rw [← split]
    have hx := congrArg (fun z : ℝ => (4 / (m : ℝ)) * z) hS
    change (4 / (m : ℝ)) * (mass k + S) = (4 / (m : ℝ)) * 1 at hx
    have hk' : 8 * mass k ≤ 8 / (N : ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 8)
    rw [show 2 * (2 / (m : ℝ) * S) = 4 / (m : ℝ) * S by ring] at ho
    linarith only [hi, ho, hS, hk', h₂, hx]
  exact (he ▸ hfinal).trans (le_abs_self _)
end
end SimpleGraph

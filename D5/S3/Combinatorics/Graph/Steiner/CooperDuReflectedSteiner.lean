/- GID: D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.claim; result=D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.result; claim=D5/S3/Combinatorics/Graph/Steiner/CooperDuReflectedSteiner.claim
   digest: A single 48-vertex star has a negative reflected Steiner H-eigenvalue at every even order at least four. -/

import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

compile_only_with_mathlib

/-!
# Cooper–Du reflected Steiner H-eigenvalues

The row equations use the first slot of the form with the reflection in the last slot.
See Cooper and Du, *Determinants of Steiner Distance Hypermatrices*,
arXiv:2505.10501v1, printed pp. 1, 9–10.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner

open SimpleGraph
open scoped BigOperators

private noncomputable def edgeCount {n : ℕ} {G : SimpleGraph (Fin n)}
    (H : G.Subgraph) : ℕ := by
  classical
  exact H.edgeSet.toFinset.card

private def SpanningCount {n k : ℕ} (G : SimpleGraph (Fin n)) (t : Fin k → Fin n)
    (e : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.Connected ∧ (∀ a, t a ∈ H.verts) ∧ edgeCount H = e

private theorem exists_spanning_count {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (t : Fin k → Fin n) : ∃ e, SpanningCount G t e :=
  ⟨_, ⊤, ⟨Subgraph.topIso.connected_iff.mpr hG⟩, fun _ => Set.mem_univ _, rfl⟩

/-- The minimum number of edges in a connected subgraph containing every tuple entry. -/
noncomputable def steinerEntry {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (t : Fin k → Fin n) : ℕ := by
  classical
  exact Nat.find (exists_spanning_count hG t)

/-- The multilinear form whose entries are the Steiner distances of the tuples. -/
noncomputable def steinerForm {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : G.Connected) (z : Fin k → Fin n → ℝ) : ℝ :=
  ∑ t : Fin k → Fin n, (steinerEntry hG t : ℝ) * ∏ a, z a (t a)

/-- Reflection through the span of the all-ones vector. -/
noncomputable def reflect {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * (∑ j, x j) / n - x i

/-- The order-`m + 2` contraction at first-slot basis vector `e_i`. -/
noncomputable def reflectedRow {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (m : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  steinerForm hG
    (Fin.cons (fun j => if j = i then 1 else 0) (Fin.snoc (fun _ : Fin m => x) (reflect x)))

/-- A real H-eigenpair for the order-`m + 2` tensor with reflection in the last slot. -/
def IsHEigenpair {n : ℕ} {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (m : ℕ) (x : Fin n → ℝ) (lam : ℝ) : Prop :=
  x ≠ 0 ∧ ∀ i, reflectedRow hG m x i = lam * x i ^ (m + 1)

/-- The proposed H-eigenvalue positivity at every even order at least four. -/
def claim : Prop :=
  ∀ (n k : ℕ), 3 ≤ n → 4 ≤ k → Even k →
    ∀ (G : SimpleGraph (Fin n)) (hG : G.IsTree) (x : Fin n → ℝ) (lam : ℝ),
      IsHEigenpair hG.connected (k - 2) x lam → 0 < lam

private def Crosses {n k : ℕ} (j : Fin n) (t : Fin k → Fin n) : Prop :=
  (∃ a, t a = j) ∧ (∃ a, t a ≠ j)

private instance instDecidableCrosses {n k : ℕ} (j : Fin n) (t : Fin k → Fin n) : Decidable (Crosses j t) := by
  unfold Crosses
  infer_instance

private noncomputable def cutLeaves {n k : ℕ} (r : Fin n) (t : Fin k → Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => j ≠ r ∧ Crosses j t)

private noncomputable def adjacentLeaves {n : ℕ} {r : Fin n}
    (H : (starGraph r).Subgraph) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (H.Adj r)

private theorem star_edgeCount {n : ℕ} {r : Fin n} (H : (starGraph r).Subgraph) :
    edgeCount H = (adjacentLeaves H).card := by
  classical
  have he : H.edgeSet.toFinset =
      (adjacentLeaves H).image (fun j => s(r, j)) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf a b =>
      simp only [Set.mem_toFinset, Subgraph.mem_edgeSet, Finset.mem_image,
        adjacentLeaves, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hab
        rcases (starGraph_adj.mp (H.adj_sub hab)).2 with h | h
        · subst a
          exact ⟨b, hab, rfl⟩
        · subst b
          exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨j, hj, he⟩
        have hm : s(r, j) ∈ H.edgeSet := Subgraph.mem_edgeSet.mpr hj
        exact Subgraph.mem_edgeSet.mp (he ▸ hm)
  unfold edgeCount
  rw [he]
  apply Finset.card_image_of_injective
  intro a b hab
  rcases Sym2.eq_iff.mp hab with h | h
  · exact h.2
  · exact h.2.trans h.1

private theorem star_leaf_forced {n k : ℕ} {r j : Fin n} {t : Fin k → Fin n}
    {H : (starGraph r).Subgraph} (hc : H.Connected) (ht : ∀ a, t a ∈ H.verts)
    (hj : j ≠ r) (hcross : Crosses j t) : H.Adj r j := by
  obtain ⟨⟨a, ha⟩, b, hb⟩ := hcross
  have hab : (⟨t a, ht a⟩ : H.verts) ≠ ⟨t b, ht b⟩ :=
    fun h => hb ((congrArg Subtype.val h).symm.trans ha)
  obtain ⟨p⟩ := hc ⟨t a, ht a⟩ ⟨t b, ht b⟩
  have hadj : H.Adj (t a) p.snd.val := p.adj_snd (p.not_nil_of_ne hab)
  have he := (starGraph_adj.mp (H.adj_sub hadj)).2.resolve_left (ha.trans_ne hj)
  have har := Eq.mp (congrArg (H.Adj (t a)) he) hadj
  exact Eq.mp (congrArg (H.Adj r) ha) har.symm

private theorem star_entry_card {n k : ℕ} (r : Fin n) (t : Fin (k + 1) → Fin n) :
    steinerEntry (connected_starGraph r) t = (cutLeaves r t).card := by
  classical
  apply Nat.le_antisymm
  · have hmin (e : ℕ) (h : SpanningCount (starGraph r) t e) :
        steinerEntry (connected_starGraph r) t ≤ e :=
      Nat.find_min' (exists_spanning_count (connected_starGraph r) t) h
    by_cases hconst : ∀ a, t a = t 0
    · apply hmin
      refine ⟨(starGraph r).singletonSubgraph (t 0), Subgraph.singletonSubgraph_connected, ?_, ?_⟩
      · intro a
        exact hconst a
      · have hempty : cutLeaves r t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          obtain ⟨_, ⟨a, ha⟩, b, hb⟩ := (Finset.mem_filter.mp hj).2
          exact hb ((hconst b).trans ((hconst a).symm.trans ha))
        simp [edgeCount, edgeSet_singletonSubgraph, hempty]
    · let leaves := cutLeaves r t
      let verts : Set (Fin n) := {v | v = r ∨ v ∈ leaves}
      let H := (⊤ : (starGraph r).Subgraph).induce verts
      have hcenter (j : Fin n) : H.Adj r j ↔ j ∈ leaves := by
        change (r = r ∨ r ∈ leaves) ∧ (j = r ∨ j ∈ leaves) ∧
          (starGraph r).Adj r j ↔ j ∈ leaves
        rw [starGraph_adj_center_iff]
        constructor
        · rintro ⟨_, hj | hj, hne⟩
          · exact (hne hj.symm).elim
          · exact hj
        · intro hj
          exact ⟨Or.inl rfl, Or.inr hj, (Finset.mem_filter.mp hj).2.1.symm⟩
      apply hmin
      refine ⟨H, ?_, ?_, ?_⟩
      · let center : H.verts := ⟨r, Or.inl rfl⟩
        apply Subgraph.Connected.mk
        apply Connected.of_isUniversal (v := center)
        rintro ⟨j, hj⟩ hne
        change H.Adj r j
        rcases hj with h | h
        · exact (hne (Subtype.ext h.symm)).elim
        · exact (hcenter j).mpr h
      · intro a
        change t a = r ∨ t a ∈ leaves
        by_cases ha : t a = r
        · exact Or.inl ha
        · right
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, ⟨a, rfl⟩, ?_⟩
          by_contra h
          push Not at h
          exact hconst fun b => (h b).trans (h 0).symm
      · rw [star_edgeCount]
        congr 1
        ext j
        simp [adjacentLeaves, hcenter, leaves]
  · obtain ⟨H, hc, ht, he⟩ := Nat.find_spec (exists_spanning_count (connected_starGraph r) t)
    rw [steinerEntry, ← he, star_edgeCount]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hne, hcross⟩ := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, star_leaf_forced hc ht hne hcross⟩


private theorem star_entry_sum {n k : ℕ} (r : Fin n) (t : Fin (k + 1) → Fin n) :
    (steinerEntry (connected_starGraph r) t : ℝ) =
      ∑ j ∈ Finset.univ.erase r, if Crosses j t then (1 : ℝ) else 0 := by
  classical
  have hf : cutLeaves r t = (Finset.univ.erase r).filter (fun j => Crosses j t) := by
    ext j
    simp [cutLeaves]
  rw [star_entry_card, hf, ← Finset.sum_filter]
  simp

/-- The contribution of the cut separating leaf `j` from the other vertices. -/
private noncomputable def cutForm {n k : ℕ} (j : Fin n) (z : Fin k → Fin n → ℝ) : ℝ :=
  (∏ a, ∑ v, z a v) - (∏ a, z a j) - (∏ a, ((∑ v, z a v) - z a j))

private theorem prod_mask {k : ℕ} (P : Fin k → Prop) [DecidablePred P]
    (f : Fin k → ℝ) :
    (∏ a, if P a then f a else 0) =
      if ∀ a, P a then ∏ a, f a else 0 := by
  split_ifs with h
  · simp only [h, ite_true]
  · obtain ⟨a, ha⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

private theorem sum_complement {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (∑ v, if v ≠ j then f v else 0) = (∑ v, f v) - f j := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ite_eq_right (not_not_intro rfl), add_zero]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_sub_cancel_right]
  exact Finset.sum_congr rfl fun v hv => ite_eq_left (Finset.ne_of_mem_erase hv)

private theorem cut_sum {n k : ℕ} (j : Fin n) (z : Fin (k + 1) → Fin n → ℝ) :
    (∑ t : Fin (k + 1) → Fin n, (if Crosses j t then (1 : ℝ) else 0) *
        ∏ a, z a (t a)) = cutForm j z := by
  classical
  have hweight (t : Fin (k + 1) → Fin n) :
      (if Crosses j t then (1 : ℝ) else 0) * (∏ a, z a (t a)) =
        (∏ a, z a (t a)) - (∏ a, if t a = j then z a (t a) else 0) -
          (∏ a, if t a ≠ j then z a (t a) else 0) := by
    rw [prod_mask, prod_mask]
    by_cases hhit : ∃ a, t a = j
    · by_cases hmiss : ∃ a, t a ≠ j
      · have hall : ¬∀ a, t a = j := fun h => hmiss.elim fun a ha => ha (h a)
        have hnone : ¬∀ a, t a ≠ j := fun h => hhit.elim fun a ha => h a ha
        simp [Crosses, hhit, hmiss, hall, hnone]
      · have hall : ∀ a, t a = j := fun a => not_not.mp fun ha => hmiss ⟨a, ha⟩
        simp [Crosses, hall]
    · have hnone : ∀ a, t a ≠ j := fun a ha => hhit ⟨a, ha⟩
      simp [Crosses, hnone]
  simp_rw [hweight, Finset.sum_sub_distrib]
  rw [← Fintype.prod_sum (fun a v => z a v),
    ← Fintype.prod_sum (fun a v => if v = j then z a v else 0),
    ← Fintype.prod_sum (fun a v => if v ≠ j then z a v else 0)]
  simp only [cutForm, Finset.sum_ite_eq', Finset.mem_univ, ite_true, sum_complement]

private theorem star_form {n k : ℕ} (r : Fin n) (z : Fin (k + 1) → Fin n → ℝ) :
    steinerForm (connected_starGraph r) z = ∑ j ∈ Finset.univ.erase r, cutForm j z := by
  classical
  simp_rw [steinerForm, star_entry_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => cut_sum j z


private def starVector (s : ℝ) (i : Fin 48) : ℝ :=
  if i = 0 then s + 47 else -1

private noncomputable def leafReflection (s : ℝ) : ℝ := 1 + s / 24

/-- A leaf cut at a first-slot vertex different from the isolated leaf. -/
private noncomputable def offCut (m : ℕ) (s : ℝ) : ℝ :=
  s ^ (m + 1) - (s + 1) ^ m * (s - leafReflection s)

/-- A leaf cut at its own isolated leaf, for an even number of unreflected copies. -/
private noncomputable def onCut (m : ℕ) (s : ℝ) : ℝ :=
  s ^ (m + 1) - leafReflection s

private theorem starVector_sum (s : ℝ) : ∑ i, starVector s i = s := by
  rw [Fin.sum_univ_succ]
  simp only [starVector, ite_true, Fin.succ_ne_zero, ite_false, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private theorem starVector_reflect_sum (s : ℝ) : ∑ i, reflect (starVector s) i = s := by
  simp only [reflect, starVector_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private theorem starVector_reflect_leaf (s : ℝ) {j : Fin 48} (hj : j ≠ 0) :
    reflect (starVector s) j = leafReflection s := by
  rw [reflect, starVector_sum]
  simp only [starVector, ite_eq_right hj, leafReflection]
  push_cast
  ring

private theorem product_slots {n : ℕ} (measure : (Fin n → ℝ) → ℝ)
    (m : ℕ) (e x y : Fin n → ℝ) :
    (∏ a, measure (Fin.cons (α := fun _ => Fin n → ℝ) e (Fin.snoc (fun _ : Fin m => x) y) a)) =
      measure e * measure x ^ m * measure y := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.prod_univ_castSucc]
  simp [mul_assoc]

private theorem star_cut_row (m : ℕ) (hm : Even m) (s : ℝ) (i j : Fin 48) (hj : j ≠ 0) :
    cutForm j (Fin.cons (fun v => if v = i then 1 else 0)
      (Fin.snoc (fun _ : Fin m => starVector s) (reflect (starVector s)))) =
      if j = i then onCut m s else offCut m s := by
  unfold cutForm
  rw [product_slots (fun v => ∑ u, v u),
    product_slots (fun v => v j),
    product_slots (fun v => (∑ u, v u) - v j)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, starVector_sum,
    starVector_reflect_sum, starVector_reflect_leaf s hj]
  simp only [starVector, ite_eq_right hj]
  by_cases hji : j = i
  · simp [hji, hm.neg_one_pow, onCut, pow_succ]
  · simp [hji, offCut, pow_succ, sub_neg_eq_add]

private theorem star_row (m : ℕ) (hm : Even m) (s : ℝ) (i : Fin 48) :
    reflectedRow (connected_starGraph 0) m (starVector s) i =
      if i = 0 then 47 * offCut m s else 46 * offCut m s + onCut m s := by
  classical
  rw [reflectedRow, star_form]
  let leaves : Finset (Fin 48) := Finset.univ.erase 0
  change (∑ j ∈ leaves, _) = _
  have hcard : leaves.card = 47 := by
    simp [leaves, Finset.card_erase_of_mem]
  by_cases hi : i = 0
  · subst i
    rw [ite_eq_left rfl]
    calc
      _ = ∑ _j ∈ leaves, offCut m s := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 := Finset.ne_of_mem_erase hj
        rw [star_cut_row m hm s 0 j hj0, ite_eq_right hj0]
      _ = _ := by simp [Finset.sum_const, hcard, nsmul_eq_mul]
  · rw [ite_eq_right hi]
    have hiMem : i ∈ leaves := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
    have hcard' : (leaves.erase i).card = 46 := by
      rw [Finset.card_erase_of_mem hiMem, hcard]
    rw [← Finset.sum_erase_add _ _ hiMem, star_cut_row m hm s i i hi, ite_eq_left rfl]
    congr 1
    calc
      _ = ∑ _j ∈ leaves.erase i, offCut m s := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
        rw [star_cut_row m hm s i j hj0, ite_eq_right (Finset.ne_of_mem_erase hj)]
      _ = _ := by simp [Finset.sum_const, hcard', nsmul_eq_mul]

/-- Eliminating the eigenvalue from the centre equation and one leaf equation. -/
private noncomputable def rowBalance (m : ℕ) (s : ℝ) : ℝ :=
  47 * offCut m s + (s + 47) ^ (m + 1) * (46 * offCut m s + onCut m s)

private theorem onCut_pos (m : ℕ) (hm : 2 ≤ m) {s : ℝ} (hs : 24 / 23 ≤ s) :
    0 < onCut m s := by
  have hs₁ : 1 < s := by linarith
  have hy : leafReflection s ≤ s := by unfold leafReflection; linarith
  have hpow : 1 < s ^ m := one_lt_pow₀ hs₁ (by omega)
  have hspow : s < s ^ (m + 1) := by
    calc
      s = 1 * s := (one_mul s).symm
      _ < s ^ m * s := mul_lt_mul_of_pos_right hpow (by linarith)
      _ = s ^ (m + 1) := (pow_succ s m).symm
  exact sub_pos.mpr (hy.trans_lt hspow)

private theorem balance_left_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < rowBalance m (24 / 23) := by
  have hy : leafReflection (24 / 23) = 24 / 23 := by norm_num [leafReflection]
  have hu : 0 < offCut m (24 / 23) := by
    unfold offCut
    rw [hy, sub_self, mul_zero, sub_zero]
    positivity
  have hv := onCut_pos m hm (s := 24 / 23) le_rfl
  unfold rowBalance
  positivity

private theorem balance_right_neg (m : ℕ) (hm : 2 ≤ m) :
    rowBalance m 2 < 0 := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = p + 2 := ⟨m - 2, by omega⟩
  have hpow : (2 : ℝ) ^ p ≤ 3 ^ p := pow_le_pow_left₀ (by norm_num) (by norm_num) p
  have hu : offCut (p + 2) 2 ≤ -(2 : ℝ) ^ p / 4 := by
    unfold offCut leafReflection
    rw [show p + 2 + 1 = p + 3 by omega, pow_add, pow_add]
    norm_num
    linarith
  have hv : onCut (p + 2) 2 = 8 * (2 : ℝ) ^ p - 13 / 12 := by
    unfold onCut leafReflection
    rw [show p + 2 + 1 = p + 3 by omega, pow_add]
    norm_num
    ring
  have hpowpos : 0 < (2 : ℝ) ^ p := by positivity
  have hu' : offCut (p + 2) 2 < 0 := by linarith
  have hleaf : 46 * offCut (p + 2) 2 + onCut (p + 2) 2 < 0 := by linarith
  unfold rowBalance
  exact add_neg (mul_neg_of_pos_of_neg (by norm_num) hu')
    (mul_neg_of_pos_of_neg (by positivity) hleaf)

private theorem balance_root (m : ℕ) (hm : 2 ≤ m) :
    ∃ s ∈ Set.Ioo (24 / 23 : ℝ) 2, rowBalance m s = 0 := by
  have hcont : Continuous (rowBalance m) := by
    unfold rowBalance onCut offCut leafReflection
    fun_prop
  have ha := balance_left_pos m hm
  have hb := balance_right_neg m hm
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' (f := rowBalance m)
    (by norm_num : (24 / 23 : ℝ) ≤ 2) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (rowBalance m 2) (rowBalance m (24 / 23)) from ⟨hb.le, ha.le⟩)
  refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, hz⟩
  · intro h
    exact ha.ne' (h.symm ▸ hz)
  · intro h
    exact hb.ne (h ▸ hz)

theorem star_negative (k : ℕ) (hk : 4 ≤ k) (hEven : Even k) :
    ∃ (x : Fin 48 → ℝ) (lam : ℝ), lam < 0 ∧
      IsHEigenpair (isTree_starGraph 0).connected (k - 2) x lam := by
  let m := k - 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmEven : Even m := by
    obtain ⟨q, hq⟩ := hEven
    exact ⟨q - 1, by dsimp [m]; omega⟩
  have hmOdd : Odd (m + 1) := by
    obtain ⟨q, hq⟩ := hmEven
    exact ⟨q, by omega⟩
  obtain ⟨s, hs, hz⟩ := balance_root m hm
  have hs₀ : 0 < s := lt_trans (by norm_num) hs.1
  have ha : 0 < s + 47 := by linarith
  have haPow : 0 < (s + 47) ^ (m + 1) := pow_pos ha _
  have hv : 0 < onCut m s := onCut_pos m hm hs.1.le
  have hu : offCut m s < 0 := by
    by_contra! h
    have hleaf : 0 < 46 * offCut m s + onCut m s := by positivity
    have hprod := mul_pos haPow hleaf
    unfold rowBalance at hz
    linarith
  let lam := 47 * offCut m s / (s + 47) ^ (m + 1)
  have hlam : lam < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hu) haPow
  have hlam_mul : lam * (s + 47) ^ (m + 1) = 47 * offCut m s :=
    div_mul_cancel₀ _ haPow.ne'
  have hleaf : 46 * offCut m s + onCut m s = -lam := by
    have hzero : (46 * offCut m s + onCut m s + lam) * (s + 47) ^ (m + 1) = 0 := by
      rw [add_mul, hlam_mul, mul_comm (46 * offCut m s + onCut m s), add_comm]
      exact hz
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hzero).resolve_right haPow.ne')
  refine ⟨starVector s, lam, hlam, ?_, ?_⟩
  · intro h
    have hzero : starVector s 0 = 0 := congrFun h 0
    exact ha.ne' (by simpa [starVector] using hzero)
  · intro i
    change reflectedRow (connected_starGraph 0) m (starVector s) i =
      lam * starVector s i ^ (m + 1)
    rw [star_row m hmEven]
    by_cases hi : i = 0
    · subst i
      exact hlam_mul.symm
    · simp [hi, starVector, hmOdd.neg_one_pow, hleaf]

theorem result : ¬ claim := by
  intro h
  obtain ⟨x, lam, hneg, heigen⟩ := star_negative 4 (by decide) ⟨2, by decide⟩
  exact hneg.not_gt (h 48 4 (by decide) (by decide) ⟨2, by decide⟩
    (starGraph 0) (isTree_starGraph 0) x lam heigen)

end D5.S3.Combinatorics.Graph.Steiner.CooperDuReflectedSteiner

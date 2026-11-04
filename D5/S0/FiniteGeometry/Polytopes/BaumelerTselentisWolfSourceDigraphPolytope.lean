/- GID: D5/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope
   generality: I
   mirror-B: D5/B/S0/FiniteGeometry/Polytopes/BaumelerTselentisWolfSourceDigraphPolytope
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Trivial and kefalopoda inequalities describe every source-digraph polytope. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#20672; Proved)
  Direct frozen dependencies: none.
Private helpers (all proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none):
  convex_kefalopoda: consumer source_subset; linear half-space normalization.
  source_subset: consumer result; convexHull_min and finite-sum bounds.
  fixed_source_box: consumer mixture; mem_convexHull_pi and vertex reconstruction.
  column_maxima: consumer result; exists_max_image and sum normalization.
  box_bound: consumer result; the two-coordinate inequality and nonnegativity.
  mixture: consumer result; Convex.sum_mem, order and field normalization.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21177
The arc subtype and adjacency expression are inlined in the public definitions;
the proofs use Mathlib's Set.indicator for the same adjacency function.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith

/-! Binding conventions for Ä. Baumeler, E.-E. Tselentis and S. Wolf, "Graphical Tests of Causality", arXiv:2511.22552v1
(27 November 2025).

* Section 2: a digraph D has V(D) = [n] and arcs in [n]²≠; "α(D) ∈ {0, 1}^{n(n−1)} for the adjacency vector with
  α(D)_{i,j} = 1 ⇔ ij ∈ A(D)". Here [n] is `Fin n`, an arc is a pair `(s, r)` with `s ≠ r`, and a digraph is a
  finite set of arcs.
* Theorem 3 and Definition 8: Γ(P_n^causal) is "the set of all digraphs on n vertices with at least one source vertex",
  deg_in(i) = 0, and "Q_n^src := conv(Γ(P_n^causal))".
* Definitions 9 and 13: for a fixed-point-free f the kefalopoda κ_f has arcs {f(i) i | i ∈ [n]}; "Q̃_n^src ⊆
  ℝ^{n(n−1)} is the set of vectors that satisfy" (−1_{i,j}, 0), (1_{i,j}, 1) for n ≥ 3, and (α(κ_f), n − 1), where
  (w, c) is the inequality w · x ≤ c.
* After Definition 13: "We know that Q̃_n^src = Q_n^src for n ≤ 4. In general, this identity is unsolved." -/

namespace D5.S0.FiniteGeometry.Polytopes.BaumelerTselentisWolfSourceDigraphPolytope

/-- Theorem 3: the digraph with arc set `A` has a source vertex, a vertex of in-degree `0`. -/
def HasSource {n : ℕ} (A : Finset ({p : Fin n × Fin n // p.1 ≠ p.2})) : Prop :=
  ∃ i : Fin n, ∀ e ∈ A, e.1.2 ≠ i

/-- Definition 8: the source-digraph polytope `Q_n^src`. -/
def sourcePolytope (n : ℕ) : Set ({p : Fin n × Fin n // p.1 ≠ p.2} → ℝ) :=
  convexHull ℝ {x | ∃ A : Finset ({p : Fin n × Fin n // p.1 ≠ p.2}), HasSource A ∧ x = (fun e => if e ∈ A then 1 else 0)}

/-- Definition 13: the polytope `Q̃_n^src` cut out by the trivial and kefalopoda inequalities. -/
def kefalopodaPolytope (n : ℕ) : Set ({p : Fin n × Fin n // p.1 ≠ p.2} → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (3 ≤ n → ∀ e, x e ≤ 1) ∧
    ∀ (f : Fin n → Fin n) (hf : ∀ i, f i ≠ i), ∑ i, x ⟨(f i, i), hf i⟩ ≤ (n : ℝ) - 1}

/-- The identity `Q̃_n^src = Q_n^src` after Definition 13. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → kefalopodaPolytope n = sourcePolytope n

open Finset

private theorem convex_kefalopoda (n : ℕ) : Convex ℝ (kefalopodaPolytope n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change 0 ≤ a * x e + b * y e
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · intro hn e
    change a * x e + b * y e ≤ 1
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx.2.1 hn e)),
      mul_nonneg hb (sub_nonneg.mpr (hy.2.1 hn e))]
  · intro f hf
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx.2.2 f hf)),
      mul_nonneg hb (sub_nonneg.mpr (hy.2.2 f hf))]

private theorem source_subset (n : ℕ) : sourcePolytope n ⊆ kefalopodaPolytope n := by
  classical
  apply convexHull_min ?_ (convex_kefalopoda n)
  rintro x ⟨A, ⟨i, hi⟩, rfl⟩
  have hadj : (fun e : {p : Fin n × Fin n // p.1 ≠ p.2} => if e ∈ A then (1 : ℝ) else 0) =
      (A : Set {p : Fin n × Fin n // p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ)) := by
    funext e
    simp [Set.indicator]
  rw [hadj]
  have hb (e : {p : Fin n × Fin n // p.1 ≠ p.2}) : 0 ≤ ((A : Set {p : Fin n × Fin n // p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ))) e ∧ ((A : Set {p : Fin n × Fin n // p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ))) e ≤ 1 := by
    exact ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) e,
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)⟩
  refine ⟨fun e => (hb e).1, fun _ e => (hb e).2, ?_⟩
  intro f hf
  have hz : ((A : Set {p : Fin n × Fin n // p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ))) ⟨(f i, i), hf i⟩ = 0 := by
    apply Set.indicator_of_notMem
    intro h
    exact hi _ h rfl
  have hsum : ∑ r ∈ univ.erase i, ((A : Set {p : Fin n × Fin n // p.1 ≠ p.2}).indicator (fun _ => (1 : ℝ))) ⟨(f r, r), hf r⟩ ≤ (n : ℝ) - 1 := by
    calc
      _ ≤ ∑ r ∈ univ.erase i, (1 : ℝ) := sum_le_sum fun r _ => (hb _).2
      _ = (n : ℝ) - 1 := by
        simp only [sum_const, card_erase_of_mem (mem_univ i), card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [Nat.cast_sub (by have := i.isLt; omega), Nat.cast_one]
  rw [← sum_erase_add _ _ (mem_univ i), hz, add_zero]
  exact hsum

private theorem fixed_source_box {n : ℕ} (i : Fin n) (y : {p : Fin n × Fin n // p.1 ≠ p.2} → ℝ)
    (hy0 : ∀ e, 0 ≤ y e) (hy1 : ∀ e, y e ≤ 1)
    (hyi : ∀ e, e.1.2 = i → y e = 0) : y ∈ sourcePolytope n := by
  classical
  let t : {p : Fin n × Fin n // p.1 ≠ p.2} → Set ℝ := fun e => if e.1.2 = i then {0} else {0, 1}
  have hpi : y ∈ convexHull ℝ (Set.univ.pi t) := by
    apply mem_convexHull_pi
    intro e _
    dsimp [t]
    split_ifs with h
    · simp [hyi e h]
    · rw [convexHull_pair, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hy0 e, hy1 e⟩
  apply convexHull_mono ?_ hpi
  intro z hz
  let A := univ.filter (fun e : {p : Fin n × Fin n // p.1 ≠ p.2} => z e = 1)
  have hz_cases (e : {p : Fin n × Fin n // p.1 ≠ p.2}) : z e = 0 ∨ z e = 1 := by
    have he := hz e (Set.mem_univ e)
    dsimp [t] at he
    split_ifs at he <;> simp_all
  refine ⟨A, ⟨i, ?_⟩, ?_⟩
  · intro e he h
    have he1 : z e = 1 := (mem_filter.mp he).2
    have he0 : z e = 0 := by simpa [t, h] using hz e (Set.mem_univ e)
    linarith
  · funext e
    rcases hz_cases e with he | he <;> simp [A, he]

private theorem column_maxima {n : ℕ} (hn : 2 ≤ n) (x : {p : Fin n × Fin n // p.1 ≠ p.2} → ℝ)
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e ≤ 1)
    (hk : ∀ (f : Fin n → Fin n) (hf : ∀ i, f i ≠ i),
      ∑ i, x ⟨(f i, i), hf i⟩ ≤ (n : ℝ) - 1) :
    ∃ m : Fin n → ℝ, (∀ r, 0 ≤ m r ∧ m r ≤ 1) ∧
      (∀ e, x e ≤ m e.1.2) ∧ ∑ r, m r ≤ (n : ℝ) - 1 := by
  classical
  have hc (r : Fin n) : (univ.filter fun e : {p : Fin n × Fin n // p.1 ≠ p.2} => e.1.2 = r).Nonempty := by
    obtain ⟨s, hs⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by simpa only [Fintype.card_fin] using (show 1 < n by omega)) r
    exact ⟨⟨(s, r), hs⟩, by simp⟩
  choose e he hem using fun r => exists_max_image
    (univ.filter fun e : {p : Fin n × Fin n // p.1 ≠ p.2} => e.1.2 = r) x (hc r)
  have her (r) : (e r).1.2 = r := (mem_filter.mp (he r)).2
  let f : Fin n → Fin n := fun r => (e r).1.1
  have hf (r) : f r ≠ r := by
    intro h
    exact (e r).2 (h.trans (her r).symm)
  refine ⟨fun r => x (e r), fun r => ⟨hx0 _, hx1 _⟩, ?_, ?_⟩
  · intro a
    exact hem _ a (by simp)
  · have heq (r) : (⟨(f r, r), hf r⟩ : {p : Fin n × Fin n // p.1 ≠ p.2}) = e r := by
      exact Subtype.ext (Prod.ext rfl (her r).symm)
    simpa only [heq] using hk f hf

private theorem box_bound {n : ℕ} (hn : 2 ≤ n) {x : {p : Fin n × Fin n // p.1 ≠ p.2} → ℝ}
    (hx : x ∈ kefalopodaPolytope n) : ∀ e, x e ≤ 1 := by
  classical
  by_cases h3 : 3 ≤ n
  · exact hx.2.1 h3
  have hn2 : n = 2 := by exact Nat.eq_of_le_of_lt_succ hn (lt_of_not_ge h3)
  subst n
  let f : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
  have hf : ∀ i, f i ≠ i := by
    intro i h
    apply Bool.not_ne_self (decide (i = 0))
    have hz : decide (f i = 0) = !decide (i = 0) := by
      by_cases hi : i = 0 <;> simp [f, hi]
    rw [← hz]
    exact congrArg (fun j : Fin 2 => decide (j = 0)) h
  have hk := hx.2.2 f hf
  intro e
  have he : e = ⟨(0, 1), by decide⟩ ∨ e = ⟨(1, 0), by decide⟩ := by
    rcases e with ⟨⟨s, r⟩, hsr⟩
    fin_cases s <;> fin_cases r <;> simp_all <;> exact (hsr rfl).elim
  norm_num [Fin.sum_univ_two, f] at hk
  rcases he with rfl | rfl <;> linarith [hx.1 ⟨(0, 1), by decide⟩, hx.1 ⟨(1, 0), by decide⟩]

private theorem mixture {n : ℕ} (x : {p : Fin n × Fin n // p.1 ≠ p.2} → ℝ) (m : Fin n → ℝ)
    (hx0 : ∀ e, 0 ≤ x e) (hm0 : ∀ r, 0 ≤ m r) (hm1 : ∀ r, m r ≤ 1)
    (hxm : ∀ e, x e ≤ m e.1.2) (hms : ∑ r, m r ≤ (n : ℝ) - 1) :
    x ∈ sourcePolytope n := by
  classical
  let c : Fin n → ℝ := fun r => 1 - m r
  let C : ℝ := ∑ r, c r
  have hc0 (r) : 0 ≤ c r := sub_nonneg.mpr (hm1 r)
  have hC : 1 ≤ C := by
    simp only [C, c, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let q : Fin n → ℝ := fun r => c r / C
  have hq0 (r) : 0 ≤ q r := div_nonneg (hc0 r) hCpos.le
  have hqs : ∑ r, q r = 1 := by
    simp only [q, div_eq_mul_inv, ← sum_mul]
    change C * C⁻¹ = 1
    exact mul_inv_cancel₀ (ne_of_gt hCpos)
  have hqc (r) : q r ≤ c r := by
    dsimp [q]
    exact div_le_self (hc0 r) hC
  have hq1 (r) : q r ≤ 1 := le_trans (hqc r) (sub_le_self 1 (hm0 r))
  have hxq (e : {p : Fin n × Fin n // p.1 ≠ p.2}) : x e ≤ 1 - q e.1.2 := by
    exact le_trans (hxm e) (le_sub_comm.mp (hqc e.1.2))
  let y : Fin n → {p : Fin n × Fin n // p.1 ≠ p.2} → ℝ := fun i e =>
    if e.1.2 = i then 0 else x e / (1 - q e.1.2)
  have hy (i) : y i ∈ sourcePolytope n := by
    apply fixed_source_box i (y i)
    · intro e
      dsimp [y]; split_ifs
      · exact le_rfl
      · exact div_nonneg (hx0 e) (sub_nonneg.mpr (hq1 _))
    · intro e
      dsimp [y]; split_ifs
      · exact zero_le_one
      · by_cases he : 1 - q e.1.2 = 0
        · simp [he]
        · exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr (hq1 _)) (Ne.symm he))).mpr (hxq e)
    · intro e he
      simp [y, he]
  have hmix : ∑ i, q i • y i = x := by
    funext e
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul]
    have hsum : ∑ i ∈ univ.erase e.1.2, q i = 1 - q e.1.2 := by
      have h := sum_erase_add univ q (mem_univ e.1.2)
      rw [hqs] at h
      linarith
    calc
      ∑ i, q i * y i e = ∑ i ∈ univ.erase e.1.2, q i * (x e / (1 - q e.1.2)) := by
        rw [← sum_erase_add _ _ (mem_univ e.1.2)]
        simp only [y, ite_eq_left rfl, mul_zero, add_zero]
        apply sum_congr rfl
        intro i hi
        rw [ite_eq_right (Ne.symm (mem_erase.mp hi).1)]
      _ = (1 - q e.1.2) * (x e / (1 - q e.1.2)) := by rw [← sum_mul, hsum]
      _ = x e := by
        by_cases he : 1 - q e.1.2 = 0
        · have hxz : x e = 0 := by linarith [hxq e, hx0 e]
          simp [he, hxz]
        · field_simp
  rw [← hmix]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hq0 i) hqs (fun i _ => hy i)

theorem result : claim := by
  intro n hn
  apply Set.Subset.antisymm ?_ (source_subset n)
  intro x hx
  obtain ⟨m, hm, hxm, hms⟩ := column_maxima hn x hx.1 (box_bound hn hx) hx.2.2
  exact mixture x m hx.1 (fun r => (hm r).1) (fun r => (hm r).2) hxm hms


end D5.S0.FiniteGeometry.Polytopes.BaumelerTselentisWolfSourceDigraphPolytope

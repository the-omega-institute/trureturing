/- GID: D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cycle-star edge irregularity strength attains both conjectured sharp bounds. -/

/-
result:
  proof_shape: content (explicit unbounded labeling, then matching leastness).
  escape_witness: labeling_upper (explicit unbounded feasible labeling).
  admission_basis: open-problem-resolution (#22868; Proved)
  Direct frozen dependencies: none.

All scalar, incidence and injectivity helpers are consumed bind-only steps.
labeling_upper constructs a labeling; strength_of_bounds and result use that
construction and the finite-cardinality lower bounds. No separate extension
result is exported. All direct dependencies are pinned Mathlib.
The natural skip expression is supplied by Fin.succAbove; label_leaf connects
its value to the arithmetic expression used in the estimates.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23027
-/


import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Definitions for Salma–Nagesh–Narahari, arXiv:2405.12263v1, Conjecture 3.1.
Vertex 0 is v; vertex i, for 1 ≤ i ≤ n - 1, is the source's v_i.
The strength predicate states that K is attained and is the least positive feasible bound.
-/

namespace D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity

/-- The source's vertex k-labeling; repeated vertex labels are allowed. -/
def IsKLabeling {V : Type} (K : ℕ) (φ : V → ℕ) : Prop :=
  ∀ x : V, 1 ≤ φ x ∧ φ x ≤ K

/-- The source's weight of the edge uv. -/
def edgeWeight {V : Type} (φ : V → ℕ) (u v : V) : ℕ :=
  φ u + φ v

/-- Equal weights imply equality of unordered edges. -/
def IsEdgeIrregularLabeling {V : Type} (G : SimpleGraph V) (K : ℕ)
    (φ : V → ℕ) : Prop :=
  IsKLabeling K φ ∧
    ∀ (u v x y : V), G.Adj u v → G.Adj x y →
      edgeWeight φ u v = edgeWeight φ x y → s(u, v) = s(x, y)

/-- The literal assertion es(G) = K, including existence of a feasible labeling. -/
def IsEdgeIrregularityStrength {V : Type} (G : SimpleGraph V) (K : ℕ) : Prop :=
  IsLeast {L : ℕ | 1 ≤ L ∧ ∃ φ : V → ℕ, IsEdgeIrregularLabeling G L φ} K

/-- CS_{k,n-k}, with precisely the vertex indices and edge ranges of Section 1.
`SimpleGraph.fromRel` makes the displayed edge relation undirected and loopless. -/
def cycleStar (k n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun a b : Fin n =>
    (a.val = 0 ∧
      ((1 ≤ b.val ∧ b.val ≤ n - k) ∨ b.val = n - k + 1 ∨ b.val = n - 1)) ∨
    (n - k + 1 ≤ a.val ∧ a.val ≤ n - 2 ∧ b.val = a.val + 1))

/-- Conjecture 3.1, with both source ranges and every parameter quantified.
For natural n, (n + 2) / 2 is exactly ceil((n + 1) / 2). -/
def claim : Prop :=
  ∀ (k : ℕ) (n : ℕ), 8 ≤ k → 1 ≤ n - k →
    ((k + 1 ≤ n ∧ n ≤ 2 * k - 4 →
        IsEdgeIrregularityStrength (cycleStar k n) ((n + 2) / 2)) ∧
      (2 * k - 3 ≤ n →
        IsEdgeIrregularityStrength (cycleStar k n) (n - k + 2)))

end D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity

namespace D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity
set_option maxHeartbeats 1200000

private def bump (K j : ℕ) : ℕ :=
  if K < j ∧ (j - K) % 2 = 1 then 1 else 0

private def y (K k j : ℕ) : ℕ :=
  (j + 1) / 2 + if K ≤ k - 2 then bump K j else 0

private theorem succAbove_value (e a n : ℕ) (he : e < n+1) (ha : a < n) :
    ((⟨e, he⟩ : Fin (n+1)).succAbove ⟨a, ha⟩).val =
      a + if e ≤ a then 1 else 0 := by
  by_cases h : a < e
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show (⟨a, ha⟩ : Fin n).castSucc < ⟨e, he⟩ from h)]
    simp only [Fin.val_castSucc, ite_eq_right (Nat.not_le.mpr h), Nat.add_zero]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show (⟨e, he⟩ : Fin (n+1)) ≤ (⟨a, ha⟩ : Fin n).castSucc from Nat.le_of_not_gt h)]
    simp only [Fin.val_succ, ite_eq_left (Nat.le_of_not_gt h)]

private theorem skip_props (e a : ℕ) :
    a ≤ (a + if e ≤ a then 1 else 0) ∧ (a + if e ≤ a then 1 else 0) ≤ a + 1 ∧ (a + if e ≤ a then 1 else 0) ≠ e := by
  have hn := Fin.succAbove_ne (⟨e, by omega⟩ : Fin (e+a+2))
    (⟨a, by omega⟩ : Fin (e+a+1))
  rw [ne_eq, Fin.ext_iff, succAbove_value] at hn
  exact ⟨by split_ifs <;> omega, by split_ifs <;> omega, hn⟩

private theorem skip_inj (e a b : ℕ) (h : (a + if e ≤ a then 1 else 0) = (b + if e ≤ b then 1 else 0)) : a = b := by
  let p : Fin (e+a+b+2) := ⟨e, by omega⟩
  let i : Fin (e+a+b+1) := ⟨a, by omega⟩
  let j : Fin (e+a+b+1) := ⟨b, by omega⟩
  have hf : p.succAbove i = p.succAbove j := by
    apply Fin.ext
    rw [succAbove_value, succAbove_value]
    exact h
  exact congrArg Fin.val (Fin.succAbove_right_injective hf)

private theorem y_bounds (K k j : ℕ) (hk : 4 ≤ k) (hK : k + 2 ≤ 2*K)
    (hj : 1 ≤ j) (hjk : j ≤ k - 1) : 1 ≤ y K k j ∧ y K k j ≤ K := by
  (unfold y bump; split_ifs <;> omega)

private theorem y_first (K k : ℕ) (hK : 2 ≤ K) : y K k 1 = 1 := by
  (unfold y bump; split_ifs <;> omega)

private theorem y_last (K k : ℕ) (hk : 4 ≤ k) (hK : k + 2 ≤ 2*K) :
    2 ≤ y K k (k-1) ∧
      (K ≤ k - 2 → k < K + y K k (k-1)) := by
  (unfold y bump; split_ifs <;> omega)

private theorem y_sum (K k j : ℕ) :
    y K k j + y K k (j+1) =
      if K ≤ k-2 ∧ K ≤ j then j+2 else j+1 := by
  (unfold y bump; split_ifs <;> omega)

private def Arc (k m a b : ℕ) : Prop :=
  (a = 0 ∧ ((1 ≤ b ∧ b ≤ m) ∨ b = m+1 ∨ b = m+k-1)) ∨
  (m+1 ≤ a ∧ a ≤ m+k-2 ∧ b = a+1)

private theorem arc_order {k m a b : ℕ} (hk : 4 ≤ k) (h : Arc k m a b) : a < b := by
  (rcases h with ⟨rfl, h | rfl | rfl⟩ | ⟨_, _, rfl⟩ <;> omega)

private theorem arc_adj {k m : ℕ} (hk : 4 ≤ k) (a b : Fin (m+k))
    (h : Arc k m a.val b.val) : (cycleStar k (m+k)).Adj a b := by
  change a ≠ b ∧ _
  refine ⟨fun he => Nat.ne_of_lt (arc_order hk h) (congrArg Fin.val he), Or.inl ?_⟩
  simpa only [Arc, Nat.add_sub_cancel] using h

private theorem adj_arc {k m : ℕ} {a b : Fin (m+k)}
    (h : (cycleStar k (m+k)).Adj a b) : Arc k m a.val b.val ∨ Arc k m b.val a.val := by
  (simpa only [cycleStar, SimpleGraph.fromRel_adj, Nat.add_sub_cancel, Arc] using h.2)

private def leftEnd (m i : ℕ) : ℕ := if i ≤ m+1 then 0 else i-1
private def rightEnd (k m i : ℕ) : ℕ :=
  if i ≤ m then i+1 else if i = m+1 then m+k-1 else i

private theorem indexed_arc {k m i : ℕ} (hk : 4 ≤ k) (hi : i < m+k) :
    Arc k m (leftEnd m i) (rightEnd k m i) ∧
      leftEnd m i < m+k ∧ rightEnd k m i < m+k := by
  unfold Arc leftEnd rightEnd
  split_ifs <;> omega

private theorem index_inj {k m i j : ℕ} (hk : 4 ≤ k)
    (hi : i < m+k) (hj : j < m+k)
    (hl : leftEnd m i = leftEnd m j)
    (hr : rightEnd k m i = rightEnd k m j) : i = j := by
  simp only [leftEnd, rightEnd] at hl hr
  split_ifs at hl hr <;> omega

private theorem labeling_lower {k m L : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    {φ : Fin (m+k) → ℕ} (hφ : IsEdgeIrregularLabeling (cycleStar k (m+k)) L φ) :
    m+2 ≤ L ∧ (m+k+2)/2 ≤ L := by
  let a (i : Fin (m+k)) : Fin (m+k) := ⟨leftEnd m i.val, (indexed_arc hk i.isLt).2.1⟩
  let b (i : Fin (m+k)) : Fin (m+k) := ⟨rightEnd k m i.val, (indexed_arc hk i.isLt).2.2⟩
  have hadj (i : Fin (m+k)) : (cycleStar k (m+k)).Adj (a i) (b i) :=
    arc_adj hk _ _ (indexed_arc hk i.isLt).1
  have hinj (i j : Fin (m+k)) (he : φ (a i) + φ (b i) = φ (a j) + φ (b j)) : i = j := by
    have hh := Sym2.eq_iff.mp (hφ.2 _ _ _ _ (hadj i) (hadj j) he)
    have hoi := arc_order hk (indexed_arc hk i.isLt).1
    have hoj := arc_order hk (indexed_arc hk j.isLt).1
    rcases hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Fin.ext (index_inj hk i.isLt j.isLt (congrArg Fin.val ha) (congrArg Fin.val hb))
    · have ha' := congrArg Fin.val ha
      have hb' := congrArg Fin.val hb
      change leftEnd m i.val = rightEnd k m j.val at ha'
      change rightEnd k m i.val = leftEnd m j.val at hb'
      omega
  have hcount : m+k ≤ 2*L-1 := by
    let f (i : Fin (m+k)) : Fin (2*L-1) :=
      ⟨φ (a i) + φ (b i) - 2, by have ha := hφ.1 (a i); have hb := hφ.1 (b i); omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply hinj
      have hij' := congrArg Fin.val hij
      have ha := hφ.1 (a i)
      have hb := hφ.1 (b i)
      have hc := hφ.1 (a j)
      have hd := hφ.1 (b j)
      change φ (a i) + φ (b i) - 2 = φ (a j) + φ (b j) - 2 at hij'
      omega
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hdegree : m+2 ≤ L := by
    let f (i : Fin (m+2)) : Fin L :=
      ⟨φ (b ⟨i.val, by omega⟩) - 1, by have hb := hφ.1 (b ⟨i.val, by omega⟩); omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      have hi : i.val < m+k := by omega
      have hj : j.val < m+k := by omega
      have ha : a ⟨i.val, hi⟩ = a ⟨j.val, hj⟩ := by
        apply Fin.ext
        dsimp [a, leftEnd]
        simp only [ite_eq_left (by omega : i.val ≤ m+1), ite_eq_left (by omega : j.val ≤ m+1)]
      have hb := hφ.1 (b ⟨i.val, hi⟩)
      have hc := hφ.1 (b ⟨j.val, hj⟩)
      have hij' := congrArg Fin.val hij
      change φ (b ⟨i.val, hi⟩) - 1 = φ (b ⟨j.val, hj⟩) - 1 at hij'
      have hs : φ (a ⟨i.val, hi⟩) + φ (b ⟨i.val, hi⟩) =
          φ (a ⟨j.val, hj⟩) + φ (b ⟨j.val, hj⟩) := by rw [ha]; omega
      have hij : (⟨i.val, hi⟩ : Fin (m+k)) = ⟨j.val, hj⟩ := hinj ⟨i.val, hi⟩ ⟨j.val, hj⟩ hs
      exact Fin.ext (congrArg (fun z : Fin (m+k) => z.val) hij)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact ⟨hdegree, by omega⟩

private def base (K k : ℕ) : ℕ := if K ≤ k-2 then k-K else 1
private def label (K k m t : ℕ) : ℕ :=
  if t = 0 then K else if t ≤ m then
    let e := y K k (k-1)
    let a := base K k + t
    ((⟨e, by omega⟩ : Fin (e+a+2)).succAbove
      (⟨a, by omega⟩ : Fin (e+a+1))).val
  else y K k (t-m)

private theorem label_root (K k m : ℕ) : label K k m 0 = K := by
  exact Nat.add_zero K

private theorem label_path {K k m j : ℕ} (hj : 1 ≤ j) :
    label K k m (m+j) = y K k j := by
  (simp only [label, ite_eq_right (by omega : m+j ≠ 0), ite_eq_right (by omega : ¬m+j ≤ m), Nat.add_sub_cancel_left])

private theorem label_leaf {K k m t : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) :
    label K k m t = (base K k + t) +
      if y K k (k-1) ≤ base K k + t then 1 else 0 := by
  simp only [label, ite_eq_right (by omega : t ≠ 0), ite_eq_left htm]
  exact succAbove_value _ _ _ _ _

private theorem label_bounds {K k m t : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKM : m+2 ≤ K) (hKN : m+k+1 ≤ 2*K) (ht : t < m+k) :
    1 ≤ label K k m t ∧ label K k m t ≤ K := by
  by_cases hz : t = 0
  · subst t; rw [label_root]; omega
  by_cases hl : t ≤ m
  · rw [label_leaf (by omega) hl]
    have hs := skip_props (y K k (k-1)) (base K k+t)
    unfold base at hs ⊢
    split_ifs at hs ⊢ <;> omega
  · have heq : t = m+(t-m) := by omega
    rw [heq, label_path (by omega)]
    apply y_bounds _ _ _ hk (by omega) (by omega) (by omega)

private theorem neighbor_inj {K k m t u : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKN : m+k+1 ≤ 2*K)
    (ht : Arc k m 0 t) (hu : Arc k m 0 u)
    (he : label K k m t = label K k m u) : t = u := by
  simp [Arc] at ht hu
  have hlast := y_last K k hk (by omega)
  have hfirst := y_first K k (by omega)
  have hp : label K k m (m+1) = 1 := (label_path (by omega)).trans hfirst
  have hq : label K k m (m+k-1) = y K k (k-1) := by
    rw [show m+k-1=m+(k-1) by omega, label_path (by omega)]
  rcases ht with ⟨ht, htm⟩ | rfl | rfl <;>
    rcases hu with ⟨hu, hum⟩ | rfl | rfl
  · rw [label_leaf ht htm, label_leaf hu hum] at he
    have hi := skip_inj (y K k (k-1)) (base K k+t) (base K k+u) he
    omega
  · rw [label_leaf ht htm, hp] at he
    have hs := skip_props (y K k (k-1)) (base K k+t)
    have hbase : 2 ≤ base K k + t := by unfold base; split_ifs <;> omega
    omega
  · rw [label_leaf ht htm, hq] at he
    exact ((skip_props _ _).2.2 he).elim
  · rw [label_leaf hu hum, hp] at he
    have hs := skip_props (y K k (k-1)) (base K k+u)
    have hbase : 2 ≤ base K k + u := by unfold base; split_ifs <;> omega
    omega
  · rfl
  · rw [hp, hq] at he; omega
  · rw [label_leaf hu hum, hq] at he
    exact ((skip_props _ _).2.2 he.symm).elim
  · rw [hp, hq] at he; omega
  · rfl

private theorem path_sum {K k m a : ℕ} (ha : m+1 ≤ a) :
    label K k m a + label K k m (a+1) =
      if K ≤ k-2 ∧ K ≤ a-m then a-m+2 else a-m+1 := by
  have heq : a = m+(a-m) := by omega
  rw [heq, label_path (by omega), show m+(a-m)+1=m+(a-m+1) by omega,
    label_path (by omega), y_sum]
  simp only [Nat.add_sub_cancel_left]

private theorem hub_path_disjoint {K k m t a : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKM : m+2 ≤ K) (hKN : m+k+1 ≤ 2*K)
    (ht : Arc k m 0 t) (ha : m+1 ≤ a) (hak : a ≤ m+k-2) :
    K + label K k m t ≠ label K k m a + label K k m (a+1) := by
  simp [Arc] at ht
  have hpos := label_bounds hk hm hKM hKN (show t < m+k by rcases ht with ⟨_,_⟩ | rfl | rfl <;> omega)
  rw [path_sum ha]
  by_cases hs : K ≤ k-2
  · have hlast := (y_last K k hk (by omega)).2 hs
    rcases ht with ⟨ht,htm⟩ | rfl | rfl
    · rw [label_leaf ht htm, base, ite_eq_left hs]
      have hl := (skip_props (y K k (k-1)) (k-K+t)).1
      split_ifs <;> omega
    · rw [label_path (by omega), y_first K k (by omega)]
      split_ifs <;> omega
    · rw [show m+k-1=m+(k-1) by omega, label_path (by omega)]
      split_ifs <;> omega
  · split_ifs <;> omega

private theorem arc_weight_inj {K k m a b c d : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKM : m+2 ≤ K) (hKN : m+k+1 ≤ 2*K)
    (hab : Arc k m a b) (hcd : Arc k m c d)
    (he : label K k m a + label K k m b = label K k m c + label K k m d) :
    a = c ∧ b = d := by
  rcases hab with ⟨rfl,hb⟩ | ⟨ha,hak,rfl⟩ <;>
    rcases hcd with ⟨rfl,hd⟩ | ⟨hc,hck,rfl⟩
  · rw [label_root] at he
    exact ⟨rfl, neighbor_inj hk hm hKN (Or.inl ⟨rfl, hb⟩) (Or.inl ⟨rfl, hd⟩) (by omega)⟩
  · rw [label_root] at he
    exact (hub_path_disjoint hk hm hKM hKN (Or.inl ⟨rfl, hb⟩) hc hck he).elim
  · rw [label_root] at he
    exact (hub_path_disjoint hk hm hKM hKN (Or.inl ⟨rfl, hd⟩) ha hak he.symm).elim
  · rw [path_sum ha, path_sum hc] at he
    have hac : a = c := by split_ifs at he <;> omega
    exact ⟨hac, by omega⟩

private theorem labeling_upper {k m K : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKM : m+2 ≤ K) (hKN : m+k+1 ≤ 2*K) :
    ∃ φ : Fin (m+k) → ℕ, IsEdgeIrregularLabeling (cycleStar k (m+k)) K φ := by
  refine ⟨fun t => label K k m t.val, ?_, ?_⟩
  · intro t; exact label_bounds hk hm hKM hKN t.isLt
  · intro a b c d hab hcd he
    rcases adj_arc hab with hab | hab <;> rcases adj_arc hcd with hcd | hcd
    · have h := arc_weight_inj hk hm hKM hKN hab hcd he
      exact congrArg₂ (fun x y : Fin (m+k) => s(x,y)) (Fin.ext h.1) (Fin.ext h.2)
    · have h := arc_weight_inj hk hm hKM hKN hab hcd (by unfold edgeWeight at he; dsimp at he; omega)
      exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩)
    · have h := arc_weight_inj hk hm hKM hKN hab hcd (by unfold edgeWeight at he; dsimp at he; omega)
      exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext h.2, Fin.ext h.1⟩)
    · have h := arc_weight_inj hk hm hKM hKN hab hcd (by unfold edgeWeight at he; dsimp at he; omega)
      exact congrArg₂ (fun x y : Fin (m+k) => s(x,y)) (Fin.ext h.2) (Fin.ext h.1)

private theorem strength_of_bounds {k m K : ℕ} (hk : 4 ≤ k) (hm : 1 ≤ m)
    (hKM : m+2 ≤ K) (hKN : m+k+1 ≤ 2*K)
    (heq : K = max (m+2) ((m+k+2)/2)) :
    IsEdgeIrregularityStrength (cycleStar k (m+k)) K := by
  refine ⟨⟨by omega, labeling_upper hk hm hKM hKN⟩, ?_⟩
  intro L hL
  obtain ⟨φ, hφ⟩ := hL.2
  have h := labeling_lower hk hm hφ
  rw [heq]
  exact max_le h.1 h.2

theorem result : D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity.claim := by
  intro k n hk hm
  have hn : n = (n-k)+k := by omega
  constructor
  · intro hr
    rw [hn]
    apply strength_of_bounds (by omega) hm <;> omega
  · intro hr
    rw [hn]
    apply strength_of_bounds (by omega) hm <;> omega

end D5.S3.Combinatorics.EdgeLabeling.CycleStarIrregularity

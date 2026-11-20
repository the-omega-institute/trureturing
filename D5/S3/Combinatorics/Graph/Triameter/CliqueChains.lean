/- GID: D5/S3/Combinatorics/Graph/Triameter/CliqueChains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Triameter/CliqueChains
   mirror-E: none(waiver:universal-finite-graph-theorem)
   anchors: []
   utility: none
   digest: Equality in the triameter bound by independence classifies chains of split cliques. -/

/-
admission_basis: escape-witness
The independent companions of each block force its fiber to be a clique.
The converse compares the clique cover with the perimeter of the lifted feet.
-/

module

public import D5.S3.Combinatorics.Graph.Triameter.DistanceProjection
import Mathlib.Algebra.BigOperators.Fin

/-! # Equality in the triameter bound by independence -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Triameter


open SimpleGraph

namespace EvenLegTriangle

/-- The two vertices of block `t` on leg `i`. -/
private def peripheralBlock (q : Fin 3 → ℕ) (i : Fin 3) (t : ℕ) (ht : t ≤ q i) :
    Finset (Vertex q) :=
  {⟨i, ⟨2 * t - 1, by omega⟩⟩, ⟨i, ⟨2 * t, by omega⟩⟩}

private abbrev BlockIndex (q : Fin 3 → ℕ) := Σ i : Fin 3, Fin (q i)

private theorem sigma_fin_ext {n : Fin 3 → ℕ} {x y : Σ i : Fin 3, Fin (n i)}
    (hleg : x.1 = y.1) (hval : x.2.val = y.2.val) : x = y := by
  obtain ⟨i, a⟩ := x
  obtain ⟨j, b⟩ := y
  change i = j at hleg
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hval)

private theorem apart_of_depth_gap {q : Fin 3 → ℕ} {x y : Vertex q}
    (hgap : x.2.val + 2 ≤ y.2.val) : x ≠ y ∧ ¬ (H q).Adj x y := by
  constructor
  · rintro rfl
    omega
  · rintro (⟨_, h | h⟩ | ⟨_, _, h⟩) <;> omega

private theorem apart_of_different_legs {q : Fin 3 → ℕ} {x y : Vertex q}
    (hleg : x.1 ≠ y.1) (hpos : 0 < x.2.val ∨ 0 < y.2.val) :
    x ≠ y ∧ ¬ (H q).Adj x y := by
  constructor
  · rintro rfl
    exact hleg rfl
  · rintro (⟨h, _⟩ | ⟨_, hx, hy⟩)
    · exact hleg h
    · omega

/-- Every marked peripheral block has one companion per peripheral block overall. -/
private theorem peripheral_companions (q : Fin 3 → ℕ) (i : Fin 3) (t : ℕ)
    (ht₀ : 1 ≤ t) (ht : t ≤ q i) :
    ∃ A : Finset (Vertex q),
      A.card = q 0 + q 1 + q 2 ∧
      (H q).IsIndepSet (↑A : Set (Vertex q)) ∧
      ∀ x ∈ A, ∀ y ∈ peripheralBlock q i t ht, x ≠ y ∧ ¬ (H q).Adj x y := by
  obtain ⟨j, hji⟩ := exists_ne i
  let mark : BlockIndex q := ⟨i, ⟨t - 1, by omega⟩⟩
  let root : Vertex q := ⟨j, ⟨0, by omega⟩⟩
  -- Use odd depths before the mark and even depths after it or on other legs.
  let depth (b : BlockIndex q) : ℕ :=
    if b.1 = i ∧ b.2.val + 1 < t then 2 * b.2.val + 1 else 2 * b.2.val + 2
  let regular (b : BlockIndex q) : Vertex q :=
    ⟨b.1, ⟨depth b, by
      have hb := b.2.isLt
      dsimp only [depth]
      split <;> omega⟩⟩
  have depth_pos (b : BlockIndex q) : 0 < depth b := by
    dsimp only [depth]
    split <;> omega
  have depth_gap {a b : BlockIndex q} (hleg : a.1 = b.1)
      (hlt : a.2.val < b.2.val) : depth a + 2 ≤ depth b := by
    dsimp only [depth]
    by_cases ha : a.1 = i ∧ a.2.val + 1 < t
    · rw [ite_eq_left ha]
      split <;> omega
    · have hb : ¬ (b.1 = i ∧ b.2.val + 1 < t) := by
        rintro ⟨hbi, hbt⟩
        exact ha ⟨hleg.trans hbi, by omega⟩
      rw [ite_eq_right ha, ite_eq_right hb]
      omega
  have regular_apart {a b : BlockIndex q} (hab : a ≠ b) :
      regular a ≠ regular b ∧ ¬ (H q).Adj (regular a) (regular b) := by
    by_cases hleg : a.1 = b.1
    · have hval : a.2.val ≠ b.2.val := fun h => hab (sigma_fin_ext hleg h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · exact apart_of_depth_gap (depth_gap hleg hlt)
      · obtain ⟨hne, hna⟩ :=
          apart_of_depth_gap (q := q) (x := regular b) (y := regular a)
            (depth_gap hleg.symm hgt)
        exact ⟨Ne.symm hne, fun h => hna h.symm⟩
    · exact apart_of_different_legs hleg (Or.inl (depth_pos a))
  have root_apart (b : BlockIndex q) :
      root ≠ regular b ∧ ¬ (H q).Adj root (regular b) := by
    by_cases hleg : j = b.1
    · have hbi : b.1 ≠ i := hleg ▸ hji
      apply apart_of_depth_gap
      change 0 + 2 ≤ depth b
      simp [depth, hbi]
    · exact apart_of_different_legs hleg (Or.inr (depth_pos b))
  -- The marked block's index instead supplies the root on the other leg.
  let select (b : BlockIndex q) : Vertex q :=
    if b = mark then root else regular b
  have select_apart {a b : BlockIndex q} (hab : a ≠ b) :
      select a ≠ select b ∧ ¬ (H q).Adj (select a) (select b) := by
    by_cases ha : a = mark
    · have hb : b ≠ mark := fun hb => hab (ha.trans hb.symm)
      simpa [select, ha, hb] using root_apart b
    · by_cases hb : b = mark
      · obtain ⟨hne, hna⟩ := root_apart a
        simpa [select, ha, hb] using
          show regular a ≠ root ∧ ¬ (H q).Adj (regular a) root from
            ⟨Ne.symm hne, fun h => hna h.symm⟩
      · simpa [select, ha, hb] using regular_apart hab
  have select_remote (b : BlockIndex q) (y : Vertex q)
      (hy : y ∈ peripheralBlock q i t ht) :
      select b ≠ y ∧ ¬ (H q).Adj (select b) y := by
    have hy_coords : y.1 = i ∧ (y.2.val = 2 * t - 1 ∨ y.2.val = 2 * t) := by
      simp only [peripheralBlock, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    obtain ⟨hy_leg, hy_depth⟩ := hy_coords
    by_cases hb : b = mark
    · simp only [select, ite_eq_left hb]
      exact apart_of_different_legs (fun h => hji (h.trans hy_leg))
        (Or.inr (by omega))
    · simp only [select, ite_eq_right hb]
      by_cases hbi : b.1 = i
      · have hindex : b.2.val + 1 ≠ t := by
          intro h
          apply hb
          exact sigma_fin_ext hbi (show b.2.val = t - 1 by omega)
        by_cases hbefore : b.2.val + 1 < t
        · apply apart_of_depth_gap
          change depth b + 2 ≤ y.2.val
          have hcond : b.1 = i ∧ b.2.val + 1 < t := ⟨hbi, hbefore⟩
          simp only [depth, ite_eq_left hcond]
          omega
        · have hcond : ¬ (b.1 = i ∧ b.2.val + 1 < t) := fun h => hbefore h.2
          have hgap : y.2.val + 2 ≤ (regular b).2.val := by
            change y.2.val + 2 ≤ depth b
            simp only [depth, ite_eq_right hcond]
            omega
          obtain ⟨hne, hna⟩ := apart_of_depth_gap hgap
          exact ⟨Ne.symm hne, fun h => hna h.symm⟩
      · exact apart_of_different_legs (fun h => hbi (h.trans hy_leg))
          (Or.inl (depth_pos b))
  let embedding : BlockIndex q ↪ Vertex q :=
    ⟨select, fun _ _ h => by
      by_contra hne
      exact (select_apart hne).1 h⟩
  refine ⟨Finset.univ.map embedding, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    change (Finset.univ.sigma fun i : Fin 3 => (Finset.univ : Finset (Fin (q i)))).card =
      q 0 + q 1 + q 2
    simp [Fin.sum_univ_three]
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact (select_apart (fun h => hxy (congrArg embedding h))).2
  · intro x hx y hy
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hx
    exact select_remote b y hy

end EvenLegTriangle

open EvenLegTriangle (H Vertex peripheralBlock)

abbrev BlockIndex (q : Fin 3 → ℕ) := Option (Σ i : Fin 3, Fin (q i))

/-- The root layers share one block. Each successive pair of positive depths is one block. -/
def block {q : Fin 3 → ℕ} (x : Vertex q) : BlockIndex q :=
  if h : x.2.val = 0 then none else
    some ⟨x.1, ⟨(x.2.val - 1) / 2, by have := x.2.isLt; omega⟩⟩

/-- Consecutive layers across two successive cliques on the same chain. -/
def Interface {q : Fin 3 → ℕ} (x y : Vertex q) : Prop :=
  x.1 = y.1 ∧
    ((x.2.val % 2 = 0 ∧ x.2.val + 1 = y.2.val) ∨
      (y.2.val % 2 = 0 ∧ y.2.val + 1 = x.2.val))

private theorem coords_eq {L : Fin 3 → ℕ} {x y : Σ i : Fin 3, Fin (L i)}
    (hi : x.1 = y.1) (hd : x.2.val = y.2.val) : x = y := by
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  change i = j at hi
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hd)

private theorem block_eq_iff {q : Fin 3 → ℕ} (x y : Vertex q) :
    block x = block y ↔
      (x.2.val = 0 ∧ y.2.val = 0) ∨
      (x.2.val ≠ 0 ∧ y.2.val ≠ 0 ∧ x.1 = y.1 ∧ (x.2.val - 1) / 2 = (y.2.val - 1) / 2) := by
  by_cases hx : x.2.val = 0 <;> by_cases hy : y.2.val = 0
  · simp [block, hx, hy]
  · simp [block, hx, hy]
  · simp [block, hx, hy]
  · unfold block
    rw [dite_eq_right hx, dite_eq_right hy, Option.some.injEq]
    constructor
    · intro h
      exact Or.inr ⟨hx, hy, congrArg (fun b : Σ i : Fin 3, Fin (q i) => b.1) h,
        congrArg (fun b : Σ i : Fin 3, Fin (q i) => b.2.val) h⟩
    · rintro (⟨h, _⟩ | ⟨_, _, hi, hd⟩)
      · exact (hx h).elim
      · exact coords_eq hi hd

private theorem model_adj_iff {q : Fin 3 → ℕ} {x y : Vertex q} :
    (H q).Adj x y ↔ x ≠ y ∧ (block x = block y ∨ Interface x y) := by
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    change (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨
      (x.1 ≠ y.1 ∧ x.2.val = 0 ∧ y.2.val = 0) at h
    rcases h with ⟨hi, hs | hs⟩ | ⟨_, hx, hy⟩
    · by_cases he : x.2.val % 2 = 0
      · exact Or.inr ⟨hi, Or.inl ⟨he, hs⟩⟩
      · exact Or.inl ((block_eq_iff x y).mpr (Or.inr ⟨by omega, by omega, hi, by omega⟩))
    · by_cases he : y.2.val % 2 = 0
      · exact Or.inr ⟨hi, Or.inr ⟨he, hs⟩⟩
      · exact Or.inl ((block_eq_iff x y).mpr (Or.inr ⟨by omega, by omega, hi, by omega⟩))
    · exact Or.inl ((block_eq_iff x y).mpr (Or.inl ⟨hx, hy⟩))
  · rintro ⟨hne, h | h⟩
    · rcases (block_eq_iff x y).mp h with ⟨hx, hy⟩ | ⟨hx, hy, hi, hd⟩
      · exact Or.inr ⟨fun hi => hne (coords_eq hi (hx.trans hy.symm)), hx, hy⟩
      · have hdepth : x.2.val ≠ y.2.val := fun h => hne (coords_eq hi h)
        exact Or.inl ⟨hi, by omega⟩
    · rcases h with ⟨hi, ⟨_, hs⟩ | ⟨_, hs⟩⟩
      · exact Or.inl ⟨hi, Or.inl hs⟩
      · exact Or.inl ⟨hi, Or.inr hs⟩

private theorem interface_ne {q : Fin 3 → ℕ} {x y : Vertex q} (h : Interface x y) : x ≠ y := by
  rintro rfl
  rcases h.2 with ⟨_, hs⟩ | ⟨_, hs⟩ <;> omega

private theorem peripheral_mem {q : Fin 3 → ℕ} {x : Vertex q} (i : Fin 3) (t : ℕ)
    (ht : t ≤ q i) (hi : x.1 = i)
    (hd : x.2.val = 2 * t - 1 ∨ x.2.val = 2 * t) :
    x ∈ peripheralBlock q i t ht := by
  simp only [peripheralBlock, Finset.mem_insert, Finset.mem_singleton]
  rcases hd with h | h
  · exact Or.inl (coords_eq hi h)
  · exact Or.inr (coords_eq hi h)

private theorem roots_companions (q : Fin 3 → ℕ) :
    ∃ A : Finset (Vertex q), A.card = q 0 + q 1 + q 2 ∧ (H q).IsIndepSet (A : Set (Vertex q)) ∧
      ∀ x ∈ A, ∀ y : Vertex q, y.2.val = 0 → x ≠ y ∧ ¬(H q).Adj x y := by
  let positiveEven : (Σ i : Fin 3, Fin (q i)) → Vertex q := fun x =>
    ⟨x.1, ⟨2 * (x.2.val + 1), by have := x.2.isLt; omega⟩⟩
  have evenCoords (x : Σ i : Fin 3, Fin (q i)) : (positiveEven x).2.val = 2 * (x.2.val + 1) :=
    rfl
  let emb : (Σ i : Fin 3, Fin (q i)) ↪ Vertex q :=
    ⟨positiveEven, fun x y h => by
      have hleg : x.1 = y.1 := congrArg (fun z : Vertex q => z.1) h
      apply coords_eq hleg
      have hd := congrArg (fun z : Vertex q => z.2.val) h
      change (positiveEven x).2.val = (positiveEven y).2.val at hd
      rw [evenCoords, evenCoords] at hd
      omega⟩
  refine ⟨Finset.univ.map emb, by simp [Fintype.card_sigma, Fin.sum_univ_three], ?_, ?_⟩
  · rw [isIndepSet_iff]
    intro x hx y hy _ hadj
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    have ha := evenCoords a
    have hb := evenCoords b
    rcases hadj with ⟨_, hs | hs⟩ | ⟨_, hz, _⟩
    · change (positiveEven a).2.val + 1 = (positiveEven b).2.val at hs
      omega
    · change (positiveEven b).2.val + 1 = (positiveEven a).2.val at hs
      omega
    · change (positiveEven a).2.val = 0 at hz
      omega
  · intro x hx y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    have ha := evenCoords a
    refine ⟨?_, ?_⟩
    · intro h
      have hd : (positiveEven a).2.val = y.2.val := congrArg (fun z : Vertex q => z.2.val) h
      omega
    · rintro (⟨_, hs | hs⟩ | ⟨_, hz, _⟩)
      · change (positiveEven a).2.val + 1 = y.2.val at hs
        omega
      · change y.2.val + 1 = (positiveEven a).2.val at hs
        omega
      · change (positiveEven a).2.val = 0 at hz
        omega

private theorem block_companions {q : Fin 3 → ℕ} {u v : Vertex q} (h : block u = block v) :
    ∃ A : Finset (Vertex q), A.card = q 0 + q 1 + q 2 ∧ (H q).IsIndepSet (A : Set (Vertex q)) ∧
      ∀ z ∈ A, (z ≠ u ∧ ¬(H q).Adj z u) ∧ (z ≠ v ∧ ¬(H q).Adj z v) := by
  rcases (block_eq_iff u v).mp h with ⟨hu, hv⟩ | ⟨hu, hv, hleg, hdepth⟩
  · obtain ⟨A, hA, hi, hr⟩ := roots_companions q
    exact ⟨A, hA, hi, fun z hz => ⟨hr z hz u hu, hr z hz v hv⟩⟩
  · let t := (u.2.val - 1) / 2 + 1
    have ht₀ : 1 ≤ t := by dsimp [t]; omega
    have ht : t ≤ q u.1 := by
      have hd := u.2.isLt
      dsimp [t]
      omega
    have hum : u ∈ peripheralBlock q u.1 t ht := by
      apply peripheral_mem _ _ _ rfl
      dsimp [t]
      omega
    have hvm : v ∈ peripheralBlock q u.1 t ht := by
      apply peripheral_mem _ _ _ hleg.symm
      dsimp [t]
      omega
    obtain ⟨A, hA, hi, hr⟩ := EvenLegTriangle.peripheral_companions q u.1 t ht₀ ht
    exact ⟨A, hA, hi, fun z hz => ⟨hr z hz u hum, hr z hz v hvm⟩⟩

private theorem indep_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Finset V}
    (hB : G.IsIndepSet (B : Set V)) {x : V} (hx : ∀ b ∈ B, ¬ G.Adj b x) :
    G.IsIndepSet (↑(insert x B) : Set V) := by
  rw [isIndepSet_iff] at hB ⊢
  simp only [Finset.coe_insert]
  rintro u (rfl | hu) v (rfl | hv) huv h
  · exact huv rfl
  · exact hx v hv h.symm
  · exact hx u hu h
  · exact hB (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv h

private theorem clique_of_equal_block {V : Type*} [Finite V] {G : SimpleGraph V}
    {q : Fin 3 → ℕ} {f : V → Vertex q} (hs : Function.Surjective f)
    (hedge : ∀ x y, G.Adj x y → f x = f y ∨ (H q).Adj (f x) (f y))
    (hα : G.indepNum = q 0 + q 1 + q 2 + 1)
    {x y : V} (hne : x ≠ y) (hb : block (f x) = block (f y)) : G.Adj x y := by
  classical
  by_contra hxy
  obtain ⟨A, hA, hAi, hAr⟩ := block_companions hb
  let g : Vertex q → V := fun z => (hs z).choose
  have hg (z : Vertex q) : f (g z) = z := (hs z).choose_spec
  let emb : Vertex q ↪ V := ⟨g, fun a b h => (hg a).symm.trans ((congrArg f h).trans (hg b))⟩
  let B := A.map emb
  have hB : G.IsIndepSet (B : Set V) := by
    rw [isIndepSet_iff] at hAi ⊢
    intro a ha b hb hab h
    obtain ⟨i, hii, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨j, hjj, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    have hh := hedge (g i) (g j) h
    rw [hg, hg] at hh
    exact hh.elim (fun he => hab (congrArg g he))
      (hAi (Finset.mem_coe.mpr hii) (Finset.mem_coe.mpr hjj) (fun he => hab (congrArg g he)))
  have hr (b : V) (hb : b ∈ B) :
      (b ≠ x ∧ ¬ G.Adj b x) ∧ (b ≠ y ∧ ¬ G.Adj b y) := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨hx, hy⟩ := hAr z hz
    have lift (w : V) (h : z ≠ f w ∧ ¬(H q).Adj z (f w)) :
        g z ≠ w ∧ ¬ G.Adj (g z) w := by
      constructor
      · intro he
        exact h.1 ((hg z).symm.trans (congrArg f he))
      · intro ha
        have hh := hedge _ _ ha
        rw [hg] at hh
        exact hh.elim h.1 h.2
    exact ⟨lift x hx, lift y hy⟩
  have hxB : x ∉ B := fun h => (hr x h).1.1 rfl
  have hyB : y ∉ B := fun h => (hr y h).2.1 rfl
  have hyI := indep_insert hB (fun b hb => (hr b hb).2.2)
  have hxyI := indep_insert hyI (x := x) (by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact fun hh => hxy hh.symm
    · exact (hr b hb).1.2)
  have hcard := hxyI.card_le_indepNum
  have hcardB : B.card = A.card := Finset.card_map _
  rw [Finset.card_insert_of_notMem (by simp [hne, hxB]), Finset.card_insert_of_notMem hyB,
    hcardB, hA, hα] at hcard
  omega

/-- Fibers are layers. The central clique has three layers, and every other clique has two. -/
structure CliqueChains {V : Type*} (G : SimpleGraph V) (q : Fin 3 → ℕ)
    (f : V → Vertex q) : Prop where
  layers_nonempty : Function.Surjective f
  within_cliques : ∀ x y, x ≠ y → block (f x) = block (f y) → G.Adj x y
  allowed_edges : ∀ x y, G.Adj x y → block (f x) = block (f y) ∨ Interface (f x) (f y)
  interfaces_nonempty : ∀ u v, Interface u v → ∃ x y, G.Adj x y ∧ f x = u ∧ f y = v

private theorem equality_clique_chains {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected) (h : triameter G = 4 * G.indepNum - 1) :
    ∃ (q : Fin 3 → ℕ) (f : V → Vertex q), CliqueChains G q f := by
  obtain ⟨q, f, hα, hs, hmap, hlift⟩ := k1_equality_projection hc h
  refine ⟨q, f, ⟨hs, fun x y hn hb => clique_of_equal_block hs hmap hα hn hb, ?_, ?_⟩⟩
  · intro x y hxy
    exact (hmap x y hxy).elim (fun hh => Or.inl (congrArg block hh))
      (fun hh => (model_adj_iff.mp hh).2)
  · intro u v huv
    exact hlift u v (model_adj_iff.mpr ⟨interface_ne huv, Or.inr huv⟩)

private theorem clique_chains_indepNum_le {V : Type*} {G : SimpleGraph V}
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    G.indepNum ≤ q 0 + q 1 + q 2 + 1 := by
  classical
  obtain ⟨A, hA⟩ := G.exists_isNIndepSet_indepNum
  have hi := hA.isIndepSet
  rw [isIndepSet_iff] at hi
  have injective : Set.InjOn (block ∘ f) (A : Set V) := by
    intro x hx y hy hb
    by_contra hne
    exact hi hx hy hne (h.within_cliques x y hne hb)
  have hcard := Finset.card_le_card_of_injOn (block ∘ f)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) injective
  rw [hA.card_eq] at hcard
  simpa [BlockIndex, Fintype.card_sigma, Fin.sum_univ_three] using hcard

private theorem clique_chains_triameter_ge {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    4 * (q 0 + q 1 + q 2) + 3 ≤ triameter G := by
  apply triameter_ge_of_evenLegTriangle hc h.layers_nonempty
  intro x y hxy
  by_cases he : f x = f y
  · exact Or.inl he
  · exact Or.inr (model_adj_iff.mpr ⟨he, h.allowed_edges x y hxy⟩)

private theorem clique_chains_equality {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hc : G.Connected)
    {q : Fin 3 → ℕ} {f : V → Vertex q} (h : CliqueChains G q f) :
    triameter G = 4 * G.indepNum - 1 := by
  have hα := clique_chains_indepNum_le h
  have hlo := clique_chains_triameter_ge hc h
  have hhi := triameter_le_indepNum hc
  omega

/-- Hak–Kozerenko Question 1 at k = 1, including connected graphs of order one or two. -/
theorem question1 {V : Type*} [Fintype V] {G : SimpleGraph V} (hc : G.Connected) :
    triameter G = 4 * G.indepNum - 1 ↔
      ∃ (q : Fin 3 → ℕ) (f : V → Vertex q), CliqueChains G q f := by
  refine ⟨equality_clique_chains hc, ?_⟩
  rintro ⟨q, f, h⟩
  exact clique_chains_equality hc h

end D5.S3.Combinatorics.Graph.Triameter

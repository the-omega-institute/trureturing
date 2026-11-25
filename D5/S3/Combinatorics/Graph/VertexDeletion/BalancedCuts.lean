/- GID: D5/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/VertexDeletion/BalancedCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced cuts uniquely maximize pair and largest-component damage. -/

import D5.S3.Combinatorics.Graph.VertexDeletion.TailComponents

/-! Balanced cuts uniquely maximize pair and largest-component damage. -/

set_option autoImplicit false
set_option linter.style.openClassical false

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private def tailEmbedding (p t b k : ℕ) : Fin t ↪ Vertex p t b k where
  toFun := tailVertex
  inj' := fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val (Sum.inl.inj h)))

private theorem deletedTailIndices_map_subset {p t b k : ℕ} (D : Finset (Vertex p t b k)) :
    (deletedTailIndices D).map (tailEmbedding p t b k) ⊆ D := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
  exact (mem_deletedTailIndices D i).mp hi

/-- Equality in the run-count bound makes every deletion a tail cut with a surviving
successor, and the initial tail index survives. -/
private theorem uniform_saturated_tail_cuts {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card = b + 1) :
    let t := uniformTailLength b k q
    let I := deletedTailIndices D
    I.card = b ∧ I.map (tailEmbedding (2 * b) t b k) = D ∧
      (∃ i : Fin t, i.val = 0 ∧ tailVertex i ∉ D) ∧
      ∀ c ∈ I, ∃ i : Fin t, i.val = c.val + 1 ∧ tailVertex i ∉ D := by
  dsimp only
  let J := positiveTailComponents (uniformHub b) D
  let I := deletedTailIndices D
  have hCount : J.card ≤ I.card + 1 :=
    (uniform_tail_component_count_and_mass hb hk hq D hD).1
  have hSub := deletedTailIndices_map_subset D
  have hLe := Finset.card_le_card hSub
  rw [Finset.card_map, hD] at hLe
  change I.card ≤ b at hLe
  have hI : I.card = b := by change J.card = b + 1 at hJ; omega
  have hMap : I.map (tailEmbedding (2 * b) (uniformTailLength b k q) b k) = D :=
    Finset.eq_of_subset_of_card_le hSub (by rw [Finset.card_map, hD, hI])
  let run (C : ↥J) := (positiveTailComponent_has_run (uniformHub b) D C.property).choose
  have represents (C : ↥J) : (run C).component (uniformHub b) = C.val :=
    (positiveTailComponent_has_run (uniformHub b) D C.property).choose_spec
  let f : ↥J → Option ↥I := fun C => (run C).predecessorOrFirst D
  have hf : Function.Injective f := by
    intro C C' h
    have same := TailRun.predecessorOrFirst_injective D h
    exact Subtype.ext ((represents C).symm.trans
      ((congrArg (TailRun.component (uniformHub b) D) same).trans (represents C')))
  have hs : Function.Surjective f := by
    apply (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf, by rw [Fintype.card_coe, Fintype.card_option, Fintype.card_coe, hI, hJ]⟩ |>.2
  refine ⟨hI, hMap, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hs none
    change (run C).predecessorOrFirst D = none at hC
    refine ⟨(run C).first, ?_, (run C).survives _ le_rfl (run C).ordered⟩
    by_contra h
    simp [TailRun.predecessorOrFirst, h] at hC
  · intro c hc
    obtain ⟨C, hC⟩ := hs (some ⟨c, hc⟩)
    change (run C).predecessorOrFirst D = some ⟨c, hc⟩ at hC
    refine ⟨(run C).first, ?_, (run C).survives _ le_rfl (run C).ordered⟩
    by_cases h : (run C).first.val = 0
    · simp [TailRun.predecessorOrFirst, h] at hC
    · have he : (run C).first.val - 1 = c.val := by
        simpa [TailRun.predecessorOrFirst, h, Subtype.ext_iff, Fin.ext_iff] using hC
      omega

private def prefixVertex {p t b k : ℕ} :
    Vertex p 0 b k → Vertex p t b k
  | .inl i => .inl (i.castAdd t)
  | .inr leaf => .inr leaf

private theorem prefixVertex_position_lt {p t b k : ℕ} (hub : Fin b → Fin p)
    (v : Vertex p 0 b k) : position hub (prefixVertex (t := t) v) < p := by
  cases v with
  | inl i => exact i.isLt
  | inr leaf => exact (hub leaf.1).isLt

private theorem nonTail_or_tail {p t b k : ℕ} (v : Vertex p t b k) :
    (∃ a : Vertex p 0 b k, prefixVertex a = v) ∨ (∃ i : Fin t, tailVertex i = v) := by
  cases v with
  | inr leaf => exact Or.inl ⟨Sum.inr leaf, rfl⟩
  | inl j =>
    by_cases h : j.val < p
    · exact Or.inl ⟨Sum.inl ⟨j.val, by omega⟩, rfl⟩
    · have hj := j.isLt
      exact Or.inr ⟨⟨j.val - p, by omega⟩, congrArg Sum.inl (Fin.ext (by
        change p + (j.val - p) = j.val
        omega))⟩

section IntactPrefix

variable {p t b k : ℕ} (hub : Fin b → Fin p) (D : Finset (Vertex p t b k))
variable (hMap : (deletedTailIndices D).map (tailEmbedding p t b k) = D)
include hMap

private theorem below_prefix_not_deleted {v : Vertex p t b k}
    (hv : position hub v < p) : v ∉ D := by
  intro h
  rw [← hMap] at h
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp h
  change p + i.val < p at hv
  omega

private def intactPrefixVertex (a : Vertex p 0 b k) : survivors D :=
  ⟨prefixVertex a, below_prefix_not_deleted hub D hMap (prefixVertex_position_lt hub a)⟩

/-- Each prefix spine vertex and each of its private leaves is connected to tail zero. -/
private theorem intact_prefix_reaches_zero
    (z : Fin t) (hz : z.val = 0) (hSurv : tailVertex z ∉ D)
    (a : Vertex p 0 b k) :
    (survivorGraph (host hub) D).Reachable (intactPrefixVertex hub D hMap a)
      (survivingTailVertex D z hSurv) := by
  let G := survivorGraph (host hub) D
  let spine (n : ℕ) (hn : n ≤ p) : survivors D :=
    ⟨Sum.inl ⟨n, by have := z.isLt; omega⟩, by
      by_cases h : n < p
      · exact below_prefix_not_deleted hub D hMap h
      · have he : n = p + z.val := by omega
        have e : (Sum.inl ⟨n, by have := z.isLt; omega⟩ : Vertex p t b k) = tailVertex z :=
          congrArg Sum.inl (Fin.ext he)
        exact fun hdel => hSurv (e ▸ hdel)⟩
  have steps (n : ℕ) (hn : n ≤ p) : G.Reachable (spine n hn) (spine p le_rfl) := by
    induction hn using Nat.decreasingInduction with
    | self => exact SimpleGraph.Reachable.rfl
    | of_succ n hn ih =>
      refine (SimpleGraph.Adj.reachable ?_).trans ih
      exact induce_adj.mpr (pathGraph_adj.mpr (Or.inl (show n + 1 = n + 1 from rfl)))
  have hEnd : spine p le_rfl = survivingTailVertex D z hSurv :=
    Subtype.ext (congrArg Sum.inl (Fin.ext (by change p = p + z.val; omega)))
  rw [← hEnd]
  cases a with
  | inl i => exact steps i.val (by have := i.isLt; omega)
  | inr leaf =>
    have hHub := (hub leaf.1).isLt
    refine (SimpleGraph.Adj.reachable ?_).trans (steps (hub leaf.1).val hHub.le)
    exact induce_adj.mpr (show _ = (hub leaf.1).castAdd t from rfl)

private theorem intact_prefix_component
    (z : Fin t) (hz : z.val = 0) (hSurv : tailVertex z ∉ D) (a : Vertex p 0 b k) :
    (survivorGraph (host hub) D).connectedComponentMk (intactPrefixVertex hub D hMap a) =
      (survivorGraph (host hub) D).connectedComponentMk (survivingTailVertex D z hSurv) :=
  ConnectedComponent.eq.mpr (intact_prefix_reaches_zero hub D hMap z hz hSurv a)

/-- An intact prefix attached to tail zero leaves no component without a tail vertex. -/
private theorem intact_prefix_components_exhaust
    (z : Fin t) (hz : z.val = 0) (hSurv : tailVertex z ∉ D) :
    positiveTailComponents hub D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro C
  obtain ⟨v, rfl⟩ := Quot.mk_surjective C
  rcases nonTail_or_tail v.val with ⟨a, ha⟩ | ⟨i, hi⟩
  · have hv : intactPrefixVertex hub D hMap a = v := Subtype.ext ha
    exact Finset.mem_image.mpr ⟨survivingTailVertex D z hSurv,
      survivingTailVertex_mem hub D z hSurv, by
        change _ = (survivorGraph (host hub) D).connectedComponentMk v
        exact (intact_prefix_component hub D hMap z hz hSurv a).symm.trans (congrArg _ hv)⟩
  · have h : tailVertex i ∉ D := hi ▸ v.property
    exact Finset.mem_image.mpr ⟨survivingTailVertex D i h,
      survivingTailVertex_mem hub D i h, congrArg _ (Subtype.ext hi)⟩

end IntactPrefix

private theorem uniform_full_tail_components_exhaust {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card = b + 1) :
    positiveTailComponents (uniformHub b) D = Finset.univ := by
  obtain ⟨_, hMap, ⟨z, hz, hSurv⟩, _⟩ := uniform_saturated_tail_cuts hb hk hq D hD hJ
  exact intact_prefix_components_exhaust (uniformHub b) D hMap z hz hSurv

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem tail_in_run_iff {p t b k : ℕ} (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) (r : TailRun D) (i : Fin t) (hi : tailVertex i ∉ D) :
    survivingTailVertex D i hi ∈ (r.component hub).supp ↔
      r.first.val ≤ i.val ∧ i.val ≤ r.last.val := by
  rw [ConnectedComponent.mem_supp_iff]
  refine ⟨fun hc => ?_, fun h => (r.component_eq hub D i h.1 h.2).symm⟩
  have hf := r.survives r.first le_rfl r.ordered
  constructor
  · by_contra! h
    let j : Fin t := ⟨r.first.val - 1, by have := r.first.isLt; omega⟩
    have hj : j.val + 1 = r.first.val := by dsimp [j]; omega
    exact ((tail_component_eq_iff hub D hi hf h.le).mp hc j (by omega) (by omega))
      (r.leftMax j hj)
  · by_contra! h
    let j : Fin t := ⟨r.last.val + 1, by have := i.isLt; omega⟩
    exact ((tail_component_eq_iff hub D hf hi (r.ordered.trans h.le)).mp hc.symm
      j (r.ordered.trans (Nat.le_succ _)) h) (r.rightMax j rfl)

private theorem intact_prefix_run_size {p t b k : ℕ} (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k))
    (hMap : (deletedTailIndices D).map (tailEmbedding p t b k) = D)
    (z : Fin t) (hz : z.val = 0) (hSurv : tailVertex z ∉ D) (r : TailRun D) :
    (r.component hub).supp.toFinset.card =
      r.last.val + 1 - r.first.val + (if r.first.val = 0 then p + b * k else 0) := by
  let s := (r.component hub).supp.toFinset
  let isTail := fun v : survivors D => p ≤ position hub v.val
  have hTail : (s.filter isTail).card = r.last.val + 1 - r.first.val := by
    rw [← Fin.card_Icc (a := r.first) (b := r.last)]
    symm
    have inside (i : Fin t) (hi : i ∈ Finset.Icc r.first r.last) :
        r.first.val ≤ i.val ∧ i.val ≤ r.last.val :=
      (Finset.mem_Icc.mp hi : r.first ≤ i ∧ i ≤ r.last)
    let f (i : Fin t) (hi : i ∈ Finset.Icc r.first r.last) :=
      survivingTailVertex D i (r.survives i (inside i hi).1 (inside i hi).2)
    refine Finset.card_bij f ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr
        ((tail_in_run_iff hub D r i _).mpr (inside i hi)), Nat.le_add_right p i.val⟩
    · intro i hi j hj h
      exact (tailEmbedding p t b k).injective (congrArg Subtype.val h)
    · intro v hv
      have h := Finset.mem_filter.mp hv
      obtain ⟨i, hi, rfl⟩ := exists_survivingTailVertex hub D (v := v)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩)
      have hi' := (tail_in_run_iff hub D r i hi).mp (Set.mem_toFinset.mp h.1)
      exact ⟨i, Finset.mem_Icc.mpr hi', rfl⟩
  have hPrefix (a : Vertex p 0 b k) :
      intactPrefixVertex hub D hMap a ∈ (r.component hub).supp ↔ r.first.val = 0 := by
    rw [ConnectedComponent.mem_supp_iff, intact_prefix_component hub D hMap z hz hSurv]
    simp only [← ConnectedComponent.mem_supp_iff, tail_in_run_iff hub D r z hSurv,
      hz, Nat.le_zero, Nat.zero_le, and_true]
  have hNonTail : (s.filter (fun v => ¬ isTail v)).card =
      if r.first.val = 0 then p + b * k else 0 := by
    split_ifs with hfirst
    · have hCard : (Finset.univ : Finset (Vertex p 0 b k)).card = p + b * k := by simp
      rw [← hCard]
      symm
      apply Finset.card_nbij (intactPrefixVertex hub D hMap)
      · intro a _
        exact Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr ((hPrefix a).mpr hfirst),
          (prefixVertex_position_lt hub a).not_ge⟩
      · intro a _ a' _ h
        have hv : prefixVertex (t := t) a = prefixVertex a' := congrArg Subtype.val h
        cases a with
        | inl i =>
          cases a' with
          | inl j =>
            have e : i.castAdd t = j.castAdd t := Sum.inl.inj
              (show Sum.inl (i.castAdd t) = (Sum.inl (j.castAdd t) : Vertex p t b k) from hv)
            exact congrArg Sum.inl (Fin.ext (congrArg (fun i : Fin (p + t) => i.val) e))
          | inr leaf => exact nomatch hv
        | inr leaf =>
          cases a' with
          | inl j => exact nomatch hv
          | inr leaf' => exact congrArg Sum.inr (Sum.inr.inj hv)
      · intro v hv
        rcases nonTail_or_tail v.val with ⟨a, ha⟩ | ⟨i, hi⟩
        · exact ⟨a, Finset.mem_univ _, Subtype.ext ha⟩
        · have h := (Finset.mem_filter.mp hv).2
          exact (h (show p ≤ position hub v.val from
            hi ▸ Nat.le_add_right p i.val)).elim
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have h := Finset.mem_filter.mp hv
      rcases nonTail_or_tail v.val with ⟨a, ha⟩ | ⟨i, hi⟩
      · have hv' : intactPrefixVertex hub D hMap a = v := Subtype.ext ha
        exact hfirst ((hPrefix a).mp (hv' ▸ Set.mem_toFinset.mp h.1))
      · apply h.2
        change p ≤ position hub v.val
        rw [← hi]
        exact Nat.le_add_right p i.val
  rw [← Finset.card_filter_add_card_filter_not (s := s) isTail, hTail, hNonTail]

/-- The actual component of each maximal tail run has its interval size plus
the full prefix mass exactly for the run beginning at index zero. -/
private theorem uniform_full_tail_run_size {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card = b + 1)
    (r : TailRun D) :
    (r.component (uniformHub b)).supp.toFinset.card =
      r.last.val + 1 - r.first.val + (if r.first.val = 0 then b * (k + 2) else 0) := by
  obtain ⟨_, hm, ⟨z, hz, hs⟩, _⟩ := uniform_saturated_tail_cuts hb hk hq D hD hJ
  have hPrefix : 2 * b + b * k = b * (k + 2) := by ring
  simpa only [hPrefix] using intact_prefix_run_size (uniformHub b) D hm z hz hs r

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem run_component_mem {p t b k : ℕ} (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) (r : TailRun D) :
    r.component hub ∈ positiveTailComponents hub D :=
  Finset.mem_image.mpr ⟨_, survivingTailVertex_mem hub D _ _, rfl⟩

private theorem card_of_exhaust {α : Type*} [Fintype α] (J : Finset α)
    (h : J = Finset.univ) : Fintype.card α = J.card := by rw [h, Finset.card_univ]

private theorem uniform_saturated_component_card {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card = b + 1) :
    Fintype.card (survivorGraph (host (uniformHub b)) D).ConnectedComponent = b + 1 := by
  have h := card_of_exhaust (positiveTailComponents (uniformHub b) D)
    (uniform_full_tail_components_exhaust hb hk hq D hD hJ)
  exact h.trans hJ

/-- The desired zero-based cut coordinate, also defined at b where it gives
the exclusive right end of the tail. -/
private def uniformCutPosition (b k q j : ℕ) : ℕ := (j + 1) * q - b * (k + 2) + j

private theorem uniform_cut_position_affine {b k q : ℕ} (hP : b * (k + 2) ≤ q) (j : ℕ) :
    uniformCutPosition b k q j = (q - b * (k + 2)) + j * (q + 1) := by
  unfold uniformCutPosition
  rw [Nat.add_mul j 1 q, Nat.one_mul, Nat.add_sub_assoc hP, Nat.mul_add j q 1, Nat.mul_one]
  omega

private theorem uniform_cut_position_strictMono {b k q : ℕ} (hP : b * (k + 2) ≤ q) :
    StrictMono (uniformCutPosition b k q) := by
  intro i j hij
  rw [uniform_cut_position_affine hP, uniform_cut_position_affine hP]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij (Nat.succ_pos q)) _

private theorem uniform_cut_position_at_budget {b k q : ℕ}
    (hP : b * (k + 2) ≤ q) :
    uniformCutPosition b k q b = uniformTailLength b k q := by
  unfold uniformCutPosition uniformTailLength
  have h : b * (k + 2) ≤ (b + 1) * q :=
    hP.trans (Nat.le_mul_of_pos_left q (Nat.succ_pos b))
  rw [Nat.add_comm ((b + 1) * q) b, Nat.add_sub_assoc h, Nat.add_comm]

theorem uniform_prefix_le_q {b k q : ℕ} (hq : 2 * b * (k + 2) ≤ q) :
    b * (k + 2) ≤ q := by
  rw [Nat.mul_assoc] at hq
  omega

theorem uniform_prefix_lt_q {b k q : ℕ} (hb : 2 ≤ b)
    (hq : 2 * b * (k + 2) ≤ q) : b * (k + 2) < q := by
  rw [Nat.mul_assoc] at hq
  have hPos : 0 < b * (k + 2) := Nat.mul_pos (by omega) (by omega)
  omega

private def uniformBalancedCutIndex {b k q : ℕ}
    (hq : 2 * b * (k + 2) ≤ q) (j : Fin b) : Fin (uniformTailLength b k q) :=
  ⟨uniformCutPosition b k q j.val, by
    rw [← uniform_cut_position_at_budget (uniform_prefix_le_q hq)]
    exact uniform_cut_position_strictMono (uniform_prefix_le_q hq) j.isLt⟩

/-- The actual exact-budget deletion, formed by casting the cut coordinates
into the tail and embedding them into the uniform host. -/
def uniformBalancedDeletion {b k q : ℕ}
    (hq : 2 * b * (k + 2) ≤ q) : Finset (UniformVertex b k q) :=
  Finset.univ.map
    (Function.Embedding.trans
      ⟨uniformBalancedCutIndex hq,
        (show StrictMono (uniformBalancedCutIndex hq) from fun _ _ h =>
          uniform_cut_position_strictMono (uniform_prefix_le_q hq) h).injective⟩
      (tailEmbedding (2 * b) (uniformTailLength b k q) b k))

private theorem uniform_balanced_tail_mem {b k q : ℕ}
    (hq : 2 * b * (k + 2) ≤ q) (i : Fin (uniformTailLength b k q)) :
    tailVertex i ∈ uniformBalancedDeletion hq ↔
      ∃ j : Fin b, uniformCutPosition b k q j.val = i.val := by
  rw [uniformBalancedDeletion, Finset.mem_map]
  constructor
  · rintro ⟨j, _, hj⟩
    exact ⟨j, congrArg Fin.val ((tailEmbedding (2 * b) _ b k).injective hj)⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ _, congrArg tailVertex (Fin.ext hj)⟩

theorem uniform_balanced_deletion_card {b k q : ℕ} (hq : 2 * b * (k + 2) ≤ q) :
    (uniformBalancedDeletion hq).card = b := by
  simp [uniformBalancedDeletion]

private def uniformRunStart (b k q i : ℕ) : ℕ :=
  if i = 0 then 0 else uniformCutPosition b k q (i - 1) + 1

private theorem uniform_run_gap {b k q : ℕ} (hb : 2 ≤ b)
    (hq : 2 * b * (k + 2) ≤ q) (i : ℕ) :
    uniformRunStart b k q i < uniformCutPosition b k q i ∧
      uniformCutPosition b k q i - uniformRunStart b k q i =
        if i = 0 then q - b * (k + 2) else q := by
  have hP := uniform_prefix_lt_q hb hq
  cases i with
  | zero =>
    simpa [uniformRunStart, uniformCutPosition] using (Nat.sub_pos_of_lt hP)
  | succ i =>
    simp only [uniformRunStart, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    rw [uniform_cut_position_affine hP.le, uniform_cut_position_affine hP.le,
      Nat.succ_mul]
    omega

private def uniformBalancedRun {b k q : ℕ} (hb : 2 ≤ b)
    (hq : 2 * b * (k + 2) ≤ q) (i : Fin (b + 1)) : TailRun (uniformBalancedDeletion hq) := by
  have hP := uniform_prefix_le_q hq
  have hMono := uniform_cut_position_strictMono hP
  have hGap := (uniform_run_gap hb hq i.val).1
  have hEnd : uniformCutPosition b k q i.val ≤ uniformTailLength b k q := by
    rw [← uniform_cut_position_at_budget hP]
    exact hMono.monotone (by have := i.isLt; omega)
  have hPrev (hi : i.val ≠ 0) :
      uniformRunStart b k q i.val = uniformCutPosition b k q (i.val - 1) + 1 := by
    simp [uniformRunStart, hi]
  refine ⟨⟨uniformRunStart b k q i.val, hGap.trans_le hEnd⟩,
    ⟨uniformCutPosition b k q i.val - 1, by omega⟩, by dsimp; omega, ?_, ?_, ?_⟩
  · intro x hl hr hx
    change uniformRunStart b k q i.val ≤ x.val at hl
    change x.val ≤ uniformCutPosition b k q i.val - 1 at hr
    obtain ⟨j, hj⟩ := (uniform_balanced_tail_mem hq x).mp hx
    by_cases hj' : j.val < i.val
    · have h := hMono.monotone (show j.val ≤ i.val - 1 by omega)
      rw [hPrev (by omega)] at hl
      omega
    · have h := hMono.monotone (show i.val ≤ j.val by omega)
      omega
  · intro x hx
    change x.val + 1 = uniformRunStart b k q i.val at hx
    have hi : i.val ≠ 0 := by
      intro h
      simp [uniformRunStart, h] at hx
    rw [hPrev hi] at hx
    exact (uniform_balanced_tail_mem hq x).mpr ⟨⟨i.val - 1, by have := i.isLt; omega⟩,
      by dsimp; omega⟩
  · intro x hx
    change uniformCutPosition b k q i.val - 1 + 1 = x.val at hx
    have hi : i.val < b := by
      have hxb := x.isLt
      have hib := i.isLt
      by_contra! h
      have he : i.val = b := by omega
      rw [he, uniform_cut_position_at_budget hP] at hx
      omega
    exact (uniform_balanced_tail_mem hq x).mpr ⟨⟨i.val, hi⟩, by dsimp; omega⟩

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem uniform_balanced_run_start_strictMono {b k q : ℕ}
    (hb : 2 ≤ b) (hq : 2 * b * (k + 2) ≤ q) :
    StrictMono (uniformRunStart b k q) := by
  intro i j hij
  have hj : j ≠ 0 := by omega
  have hi := (uniform_run_gap hb hq i).1
  have h := (uniform_cut_position_strictMono (uniform_prefix_le_q hq)).monotone
    (show i ≤ j - 1 by omega)
  simpa only [uniformRunStart, hj, ite_false] using hi.trans (Nat.lt_succ_of_le h)

set_option maxHeartbeats 1000000 in
/-- The explicit gaps are positive and index every actual survivor component.
The prefix adds exactly the mass subtracted from the first gap. -/
theorem uniform_balanced_deletion_profile {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q) :
    let D := uniformBalancedDeletion hq
    let G := survivorGraph (host (uniformHub b)) D
    Function.Bijective (fun i : Fin (b + 1) =>
      (uniformBalancedRun hb hq i).component (uniformHub b)) ∧
    (∀ i : Fin (b + 1), (uniformBalancedRun hb hq i).last.val + 1 -
      (uniformBalancedRun hb hq i).first.val =
      if i.val = 0 then q - b * (k + 2) else q) ∧
    Fintype.card G.ConnectedComponent = b + 1 ∧
    ∀ C : G.ConnectedComponent, C.supp.toFinset.card = q := by
  dsimp only
  let D := uniformBalancedDeletion hq
  let G := survivorGraph (host (uniformHub b)) D
  let J := positiveTailComponents (uniformHub b) D
  let r := uniformBalancedRun hb hq
  let f (i : Fin (b + 1)) : G.ConnectedComponent := (r i).component (uniformHub b)
  have hi : Function.Injective f := by
    intro i j h
    have hRun := tail_run_component_injective (uniformHub b) D h
    have hStart : uniformRunStart b k q i.val = uniformRunStart b k q j.val :=
      congrArg (fun r : TailRun D => r.first.val) hRun
    exact Fin.ext ((uniform_balanced_run_start_strictMono hb hq).injective hStart)
  have hLower : b + 1 ≤ J.card := by
    let into (i : Fin (b + 1)) : ↥J := ⟨f i, run_component_mem (uniformHub b) D (r i)⟩
    exact (Fintype.card_fin _).symm.trans_le
      ((Fintype.card_le_of_injective into (fun _ _ h => hi (congrArg Subtype.val h))).trans_eq
        (Fintype.card_coe J))
  have hD := uniform_balanced_deletion_card hq
  have hUpper : J.card ≤ b + 1 := by
    have hc := (uniform_tail_component_count_and_mass hb hk hq D hD).1
    change J.card ≤ (deletedTailIndices D).card + 1 at hc
    have hSub := Finset.card_le_card (deletedTailIndices_map_subset D)
    rw [Finset.card_map, hD] at hSub
    omega
  have hJ := hUpper.antisymm hLower
  have hCard := uniform_saturated_component_card hb hk hq D hD hJ
  have hBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hi, (Fintype.card_fin _).trans hCard.symm⟩
  have hGap (i : Fin (b + 1)) :
      (r i).last.val + 1 - (r i).first.val =
      if i.val = 0 then q - b * (k + 2) else q := by
    change uniformCutPosition b k q i.val - 1 + 1 - uniformRunStart b k q i.val = _
    have h := uniform_run_gap hb hq i.val
    omega
  refine ⟨hBij, hGap, hCard, fun C => ?_⟩
  obtain ⟨i, rfl⟩ := hBij.2 C
  have hSize := uniform_full_tail_run_size hb hk hq D hD hJ (r i)
  change (f i).supp.toFinset.card = _ at hSize
  rw [hSize, hGap i]
  change (if i.val = 0 then q - b * (k + 2) else q) +
    (if uniformRunStart b k q i.val = 0 then b * (k + 2) else 0) = q
  have hP := uniform_prefix_le_q hq
  by_cases hz : i.val = 0
  · simp [uniformRunStart, hz, Nat.sub_add_cancel hP]
  · simp [uniformRunStart, hz]

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

private theorem tail_run_start_at {p t b k : ℕ} (hub : Fin b → Fin p)
    (D : Finset (Vertex p t b k)) (i : Fin t) (hi : tailVertex i ∉ D)
    (hPrev : ∀ j : Fin t, j.val + 1 = i.val → tailVertex j ∈ D) :
    ∃ r : TailRun D, r.first.val = i.val := by
  have hMem := survivingTailVertex_mem hub D i hi
  obtain ⟨r, hr⟩ := positiveTailComponent_has_run hub D
    (Finset.mem_image.mpr ⟨_, hMem, rfl⟩)
  have h := (tail_in_run_iff hub D r i hi).mp
    ((ConnectedComponent.mem_supp_iff _ _).2 hr.symm)
  refine ⟨r, ?_⟩
  by_contra hne
  let j : Fin t := ⟨i.val - 1, by have := i.isLt; omega⟩
  exact r.survives j (by dsimp [j]; omega) (by dsimp [j]; omega)
    (hPrev j (by dsimp [j]; omega))

set_option maxHeartbeats 1200000 in
/-- Once the full sizes are all q, the end of each run recovers the next cut
and fixes the start of the following run. -/
private theorem uniform_recover_balanced_deletion {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b)
    (hJ : (positiveTailComponents (uniformHub b) D).card = b + 1)
    (hSize : ∀ C : (survivorGraph (host (uniformHub b)) D).ConnectedComponent,
      C.supp.toFinset.card = q) : D = uniformBalancedDeletion hq := by
  obtain ⟨_, _, ⟨z, hz, hs⟩, hSucc⟩ := uniform_saturated_tail_cuts hb hk hq D hD hJ
  have hEnd (i : ℕ) (r : TailRun D) (hr : r.first.val = uniformRunStart b k q i) :
      r.last.val + 1 = uniformCutPosition b k q i := by
    have hSize' := (hSize (r.component (uniformHub b))).symm.trans
      (uniform_full_tail_run_size hb hk hq D hD hJ r)
    rw [hr] at hSize'
    have hGap := uniform_run_gap hb hq i
    have hLe := r.ordered
    rw [hr] at hLe
    by_cases hi : i = 0
    · subst i
      have hs0 : uniformRunStart b k q 0 = 0 := rfl
      have hc : uniformCutPosition b k q 0 = q - b * (k + 2) := by simp [uniformCutPosition]
      rw [hs0] at hSize'
      simp only [Nat.sub_zero, ite_true] at hSize'
      rw [hc]
      have hP := uniform_prefix_le_q hq
      omega
    · have hs0 : uniformRunStart b k q i ≠ 0 := by simp [uniformRunStart, hi]
      simp only [hs0, ite_false, Nat.add_zero] at hSize'
      simp only [hi, ite_false] at hGap
      omega
  have runs (i : ℕ) (hi : i ≤ b) :
      ∃ r : TailRun D, r.first.val = uniformRunStart b k q i ∧
        r.last.val + 1 = uniformCutPosition b k q i := by
    induction i with
    | zero =>
      obtain ⟨r, hr⟩ := tail_run_start_at (uniformHub b) D z hs
        (fun j hj => by omega)
      have hFirst : r.first.val = uniformRunStart b k q 0 := by
        simpa [uniformRunStart, hz] using hr
      exact ⟨r, hFirst, hEnd 0 r hFirst⟩
    | succ i ih =>
      obtain ⟨r, _, hr⟩ := ih (by omega)
      let j : Fin b := ⟨i, by omega⟩
      let c := uniformBalancedCutIndex hq j
      have hc : r.last.val + 1 = c.val := hr
      have hDeleted := r.rightMax c hc
      obtain ⟨x, hx, hSurv⟩ := hSucc c ((mem_deletedTailIndices D c).mpr hDeleted)
      obtain ⟨s, hFirst⟩ := tail_run_start_at (uniformHub b) D x hSurv (fun y hy => by
        have he : y = c := Fin.ext (by omega)
        exact he.symm ▸ hDeleted)
      have hFirst' : s.first.val = uniformRunStart b k q (i + 1) := by
        simpa [uniformRunStart, show c.val = uniformCutPosition b k q i from rfl] using
          hFirst.trans hx
      exact ⟨s, hFirst', hEnd _ s hFirst'⟩
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    rw [uniformBalancedDeletion, Finset.mem_map] at hv
    obtain ⟨j, _, rfl⟩ := hv
    obtain ⟨r, _, hr⟩ := runs j.val j.isLt.le
    exact r.rightMax (uniformBalancedCutIndex hq j) hr
  · rw [hD, uniform_balanced_deletion_card]

end Ugurlu33528

namespace Ugurlu33528

open SimpleGraph
open scoped BigOperators Classical

theorem component_profile_score_formulas {V : Type*} [DecidableEq V] [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (D : Finset V) :
    let G := survivorGraph H D
    pcDamage H D = (Fintype.card V).choose 2 -
      ∑ C : G.ConnectedComponent, C.supp.toFinset.card.choose 2 := by
  simp only [pcDamage, componentSizes, Multiset.map_map, Function.comp_def,
    Finset.sum_eq_multiset_sum]

private theorem component_profile_uniform_sup {V : Type*} [DecidableEq V] [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (D : Finset V) (q : ℕ)
    (hPos : 0 < Fintype.card (survivorGraph H D).ConnectedComponent)
    (hSize : ∀ C : (survivorGraph H D).ConnectedComponent, C.supp.toFinset.card = q) :
    (componentSizes H D).sup = q := by
  apply Nat.le_antisymm
  · refine Multiset.sup_le.mpr (fun c hc => ?_)
    obtain ⟨C, _, rfl⟩ := Multiset.mem_map.mp hc
    exact (hSize C).le
  · let := Fintype.card_pos_iff.mp hPos
    let C := Classical.arbitrary (survivorGraph H D).ConnectedComponent
    rw [← hSize C]
    exact Multiset.le_sup (Multiset.mem_map.mpr ⟨C, Finset.mem_univ C, rfl⟩)

private theorem fixed_sum_pair_comparison {α : Type*} [Fintype α] (c : α → ℕ) (q : ℕ)
    (hTotal : ∑ i, c i = Fintype.card α * q) :
    Fintype.card α * q.choose 2 ≤ ∑ i, (c i).choose 2 ∧
      ((∑ i, (c i).choose 2) = Fintype.card α * q.choose 2 → ∀ i, c i = q) := by
  let m := Fintype.card α
  let v (i : α) : ℤ := (c i : ℤ) - q
  let pairs := ∑ i, (c i).choose 2
  let sqs := ∑ i, c i ^ 2
  have hPairs : 2 * pairs + m * q = sqs := by
    change 2 * (∑ i, (c i).choose 2) + m * q = _
    rw [← hTotal, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => twice_choose_two_add (c i))
  have hBal : 2 * (m * q.choose 2) + m * q = m * q ^ 2 := by
    calc
      _ = m * (2 * q.choose 2 + q) := by ring
      _ = _ := by rw [twice_choose_two_add]
  have hCastTotal : (∑ i, (c i : ℤ)) = (m : ℤ) * q := by
    rw [← Nat.cast_sum, hTotal, Nat.cast_mul]
  have hCastSqs : (∑ i, (c i : ℤ)^2) = (sqs : ℤ) := by
    simp [sqs, Nat.cast_sum, Nat.cast_pow]
  have hConst : (∑ _ : α, (q : ℤ)^2) = (m : ℤ) * (q : ℤ)^2 := by
    simp [m]
  have hVar : (∑ i, v i ^ 2) = (sqs : ℤ) - (m : ℤ) * (q : ℤ)^2 := by
    calc
      _ = ∑ i, ((c i : ℤ)^2 - (2 * (q : ℤ)) * (c i : ℤ) + (q : ℤ)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [v]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hCastSqs, hCastTotal, hConst]
        ring
  have hNonneg : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hLe : m * q ^ 2 ≤ sqs := by
    have h : (m : ℤ) * (q : ℤ)^2 ≤ (sqs : ℤ) := by omega
    exact_mod_cast h
  refine ⟨by change m * q.choose 2 ≤ pairs; omega, fun he i => ?_⟩
  change pairs = m * q.choose 2 at he
  have hSqEq : sqs = m * q ^ 2 := by omega
  have hVarZero : (∑ i, v i ^ 2) = 0 := by
    rw [hVar, hSqEq]
    simp
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp
    hVarZero i (Finset.mem_univ i)
  have hv : v i = 0 := by simpa [pow_two] using h
  dsimp [v] at hv
  omega

private theorem fixed_sum_sup_comparison {α : Type*} [Fintype α] (c : α → ℕ) (q M : ℕ)
    (hPos : 0 < Fintype.card α) (hTotal : ∑ i, c i = Fintype.card α * q)
    (hUpper : ∀ i, c i ≤ M) :
    q ≤ M ∧ (M = q → ∀ i, c i = q) := by
  have hLe : (∑ i, c i) ≤ ∑ _ : α, M := Finset.sum_le_sum fun i _ => hUpper i
  rw [hTotal, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] at hLe
  refine ⟨(Nat.mul_le_mul_left_iff hPos).mp hLe, fun he i => ?_⟩
  have hEach (j : α) : c j ≤ q := he ▸ hUpper j
  have hs : (∑ j, c j) = ∑ _ : α, q := by
    rw [hTotal, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hEach j)).mp hs i (Finset.mem_univ i)

theorem balanced_pair_target_positive {m q n : ℕ} (hm : 2 ≤ m) (hq : 0 < q)
    (hn : m * q ≤ n) : m * q.choose 2 < n.choose 2 := by
  have hm' : m < m * m := by
    simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (show 1 < m by omega)
      (show 0 < m by omega)
  have hSq : m * q ^ 2 < (m * q) ^ 2 := by
    calc
      _ < (m * m) * q ^ 2 := Nat.mul_lt_mul_of_pos_right hm' (Nat.pow_pos hq)
      _ = _ := by ring
  have hb : 2 * (m * q.choose 2) + m * q = m * q ^ 2 := by
    calc
      _ = m * (2 * q.choose 2 + q) := by ring
      _ = _ := by rw [twice_choose_two_add]
  have hc := twice_choose_two_add (m * q)
  have hLe := Nat.choose_le_choose 2 hn
  omega

private theorem uniform_component_total {b k q : ℕ} (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b) :
    (∑ C : (survivorGraph (host (uniformHub b)) D).ConnectedComponent,
      C.supp.toFinset.card) = (b + 1) * q := by
  calc
    _ = Fintype.card (survivors D) := sum_component_card _
    _ = (Dᶜ).card := Fintype.card_ofFinset _ (by simp [survivors])
    _ = _ := uniform_survivor_card hq D hD

theorem scores_of_equal_component_sizes {V : Type*} [DecidableEq V] [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (D : Finset V) (m q : ℕ)
    (hCard : Fintype.card (survivorGraph H D).ConnectedComponent = m)
    (hm : 0 < m)
    (hSize : ∀ C : (survivorGraph H D).ConnectedComponent, C.supp.toFinset.card = q) :
    pcDamage H D = (Fintype.card V).choose 2 - m * q.choose 2 ∧
    lccDamage H D = Fintype.card V - q := by
  let G := survivorGraph H D
  let c (C : G.ConnectedComponent) := C.supp.toFinset.card
  have hPairs : (∑ C, (c C).choose 2) = m * q.choose 2 := by
    calc
      _ = Fintype.card G.ConnectedComponent * q.choose 2 :=
        Finset.sum_const_nat (fun C _ => congrArg (fun n : ℕ => n.choose 2) (hSize C))
      _ = _ := congrArg (fun i => i * q.choose 2) hCard
  have hSup := component_profile_uniform_sup H D q (hCard.symm ▸ hm) hSize
  have hp : pcDamage H D = (Fintype.card V).choose 2 - ∑ C, (c C).choose 2 :=
    component_profile_score_formulas H D
  exact ⟨hp.trans (congrArg (fun x : ℕ => (Fintype.card V).choose 2 - x) hPairs),
    congrArg (fun x : ℕ => Fintype.card V - x) hSup⟩

set_option maxHeartbeats 2000000 in
-- Elaborate the cardinality and reachability comparisons in one proof.
theorem uniform_balanced_deletion_scores {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q) :
    let n := Fintype.card (UniformVertex b k q)
    pcDamage (host (uniformHub b)) (uniformBalancedDeletion hq) =
      n.choose 2 - (b + 1) * q.choose 2 ∧
    lccDamage (host (uniformHub b)) (uniformBalancedDeletion hq) = n - q := by
  obtain ⟨_, _, hCard, hSize⟩ := uniform_balanced_deletion_profile hb hk hq
  exact scores_of_equal_component_sizes (host (uniformHub b)) (uniformBalancedDeletion hq)
    (b + 1) q hCard (Nat.succ_pos b) hSize

private theorem scores_of_eq_graph {V : Type*} [DecidableEq V] [Fintype V]
    {H K : SimpleGraph V} [dH : DecidableRel H.Adj] [dK : DecidableRel K.Adj]
    (he : H = K) (D : Finset V) :
    pcDamage H D = pcDamage K D ∧ lccDamage H D = lccDamage K D := by
  cases he
  have he : dH = dK := Subsingleton.elim _ _
  cases he
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1200000 in
/-- Both exact-budget objectives are maximized by the displayed balanced cut.
Equality for either objective recovers that cut. -/
theorem uniform_balanced_deletion_unique_optimizer {b k q : ℕ}
    (hb : 2 ≤ b) (hk : 1 ≤ k) (hq : 2 * b * (k + 2) ≤ q)
    (D : Finset (UniformVertex b k q)) (hD : D.card = b) :
    let H : SimpleGraph (UniformVertex b k q) := host (uniformHub b)
    let B := uniformBalancedDeletion hq
    pcDamage H D ≤ pcDamage H B ∧ lccDamage H D ≤ lccDamage H B ∧
      ((pcDamage H D = pcDamage H B ∨ lccDamage H D = lccDamage H B) ↔ D = B) := by
  dsimp only
  let H : SimpleGraph (UniformVertex b k q) := host (uniformHub b)
  let G := survivorGraph H D
  let B := uniformBalancedDeletion hq
  let J := positiveTailComponents (uniformHub b) D
  let n := Fintype.card (UniformVertex b k q)
  let c (C : G.ConnectedComponent) := C.supp.toFinset.card
  let M := (componentSizes H D).sup
  let pairs := ∑ C : G.ConnectedComponent, (c C).choose 2
  have hGraph : uniformHost b k q = H := rfl
  obtain ⟨hPcD, hLccD⟩ := scores_of_eq_graph hGraph D
  obtain ⟨hBPc, hBLcc⟩ := uniform_balanced_deletion_scores hb hk hq
  change pcDamage H B = n.choose 2 - (b + 1) * q.choose 2 at hBPc
  change lccDamage H B = n - q at hBLcc
  by_cases hs : J.card ≤ b
  · obtain ⟨_, hp, hl⟩ :=
      uniform_fewer_tail_components_strict_score_comparisons hb hk hq D hD hs
    have hpH : pcDamage H D < n.choose 2 - (b + 1) * q.choose 2 := hPcD.symm.trans_lt hp
    have hlH : lccDamage H D < n - q := hLccD.symm.trans_lt hl
    have hp' : pcDamage H D < pcDamage H B := by
      rw [hBPc]
      exact hpH
    have hl' : lccDamage H D < lccDamage H B := by
      rw [hBLcc]
      exact hlH
    refine ⟨hp'.le, hl'.le, ⟨?_, ?_⟩⟩
    · intro he
      exact (he.elim hp'.ne hl'.ne).elim
    · intro h
      exact Or.inl (congrArg (pcDamage H) h)
  have hCount : J.card ≤ (deletedTailIndices D).card + 1 :=
    (uniform_tail_component_count_and_mass hb hk hq D hD).1
  have hDeleted := Finset.card_le_card (deletedTailIndices_map_subset D)
  rw [Finset.card_map, hD] at hDeleted
  have hJ : J.card = b + 1 := by omega
  have hCard : Fintype.card G.ConnectedComponent = b + 1 :=
    uniform_saturated_component_card hb hk hq D hD hJ
  have hTotal : (∑ C, c C) = Fintype.card G.ConnectedComponent * q := by
    rw [hCard]
    exact uniform_component_total hq D hD
  have hPairs := fixed_sum_pair_comparison c q hTotal
  rw [hCard] at hPairs
  have hSizeLe (C : G.ConnectedComponent) : c C ≤ M :=
    Multiset.le_sup (Multiset.mem_map.mpr ⟨C, Finset.mem_univ _, rfl⟩)
  have hM := fixed_sum_sup_comparison c q M (by rw [hCard]; omega) hTotal hSizeLe
  have hp : pcDamage H D = n.choose 2 - pairs := component_profile_score_formulas H D
  have hl : lccDamage H D = n - M := rfl
  have hSn : (b + 1) * q ≤ n := by
    simpa only [uniform_survivor_card hq D hD] using Finset.card_le_univ (Dᶜ)
  have hq0 := (uniform_prefix_lt_q hb hq).pos
  have hPcPos := balanced_pair_target_positive (show 2 ≤ b + 1 by omega) hq0 hSn
  have hLccPos : q < n := by
    apply lt_of_lt_of_le _ hSn
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_add_of_pos_left (Nat.mul_pos (by omega) hq0)
  refine ⟨?_, ?_, ⟨?_, fun h => Or.inl (congrArg (pcDamage H) h)⟩⟩
  · rw [hp, hBPc]
    exact Nat.sub_le_sub_left hPairs.1 _
  · rw [hl, hBLcc]
    exact Nat.sub_le_sub_left hM.1 _
  · intro he
    apply uniform_recover_balanced_deletion hb hk hq D hD hJ
    rcases he with he | he
    · rw [hp, hBPc] at he
      exact hPairs.2 (by omega)
    · rw [hl, hBLcc] at he
      exact hM.2 (by omega)

end Ugurlu33528

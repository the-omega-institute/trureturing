/- GID: D5/S3/HomologicalAlgebra/SplitQuadraticSupport
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree-three supports partition by their unique full hyperbolic pair. -/

module

public import D5.S3.HomologicalAlgebra.SplitQuadraticCubic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Factorization of a cubic on the zero cone of a split quadratic form. -/

public section

open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.SplitQuadraticSupport

open SplitQuadraticCubic (Bit quadratic form evaluate)

variable {ι : Type*} [DecidableEq ι]

private def pair (i : ι) : Finset (ι × Bool) := {(i, false), (i, true)}

private theorem card_pair (i : ι) : (pair i).card = 2 := by simp [pair]

private theorem pair_subset_iff (i : ι) (s : Finset (ι × Bool)) :
    pair i ⊆ s ↔ (i, false) ∈ s ∧ (i, true) ∈ s := by
  simp [pair, Finset.insert_subset_iff]

private theorem pair_unique {s : Finset (ι × Bool)} (hs : s.card ≤ 3)
    {i j : ι} (hi : pair i ⊆ s) (hj : pair j ⊆ s) : i = j := by
  by_contra hij
  have hd : Disjoint (pair i) (pair j) := by simp [pair, Ne.symm hij]
  have hcard := Finset.card_le_card (Finset.union_subset hi hj)
  rw [Finset.card_union_of_disjoint hd, card_pair, card_pair] at hcard
  omega

private def supportsWithPair (s : Finset (ι × Bool)) (i : ι) :
    Finset (Finset (ι × Bool)) :=
  if pair i ⊆ s then insert (pair i) ((s.filter fun p => p.1 ≠ i).image
    fun p => insert p (pair i)) else ∅

private theorem mem_supportsWithPair (s t : Finset (ι × Bool)) (i : ι) :
    t ∈ supportsWithPair s i ↔ t ⊆ s ∧ pair i ⊆ t ∧ t.card ≤ 3 := by
  constructor
  · by_cases his : pair i ⊆ s
    · simp only [supportsWithPair, his, ite_true, Finset.mem_insert, Finset.mem_image,
        Finset.mem_filter]
      rintro (rfl | ⟨p, ⟨hps, hpi⟩, rfl⟩)
      · exact ⟨his, Finset.Subset.refl _, by simp [card_pair]⟩
      have hp : p ∉ pair i := by
        intro hm
        rcases (by simpa [pair] using hm : p = (i, false) ∨ p = (i, true)) with he | he <;>
          exact hpi (congrArg Prod.fst he)
      exact ⟨Finset.insert_subset hps his, Finset.subset_insert _ _,
        by rw [Finset.card_insert_of_notMem hp, card_pair]⟩
    · simp [supportsWithPair, his]
  · rintro ⟨hts, hit, ht⟩
    rw [supportsWithPair, ite_eq_left (hit.trans hts)]
    have hd := Finset.card_sdiff_of_subset hit
    rw [card_pair] at hd
    have hunion := Finset.sdiff_union_of_subset hit
    by_cases hz : t \ pair i = ∅
    · rw [hz, Finset.empty_union] at hunion
      exact Finset.mem_insert.mpr (Or.inl hunion.symm)
    · have hOne : (t \ pair i).card = 1 := by
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
        omega
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hOne
      have hpt : p ∈ t \ pair i := by rw [hp]; exact Finset.mem_singleton_self _
      obtain ⟨hpt, hpnot⟩ := Finset.mem_sdiff.mp hpt
      have hpi : p.1 ≠ i := by
        rintro he
        apply hpnot
        obtain ⟨j, e⟩ := p
        change j = i at he
        subst j
        cases e <;> simp [pair]
      rw [hp, Finset.singleton_union] at hunion
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨hts hpt, hpi⟩, hunion⟩))

private theorem sum_supportsWithPair (c : Finset (ι × Bool) → Bit)
    (s : Finset (ι × Bool)) (i : ι) (hi : pair i ⊆ s) :
    (∑ t ∈ supportsWithPair s i, c t) =
      c (pair i) + ∑ p ∈ s with p.1 ≠ i, c (insert p (pair i)) := by
  have hp {p : ι × Bool} (h : p ∈ s.filter (fun q => q.1 ≠ i)) :
      p ∉ pair i := by
    intro ha
    apply (Finset.mem_filter.mp h).2
    rcases (by simpa [pair] using ha : p = (i, false) ∨ p = (i, true)) with he | he <;>
      exact congrArg Prod.fst he
  have hn : pair i ∉ (s.filter (fun p => p.1 ≠ i)).image (fun p => insert p (pair i)) := by
    rintro h
    obtain ⟨p, hps, he⟩ := Finset.mem_image.mp h
    exact hp hps (he ▸ Finset.mem_insert_self _ _)
  rw [supportsWithPair, ite_eq_left hi, Finset.sum_insert hn, Finset.sum_image]
  intro p hps q hqs he
  change insert p (pair i) = insert q (pair i) at he
  have hm : p ∈ insert q (pair i) := by rw [← he]; exact Finset.mem_insert_self _ _
  exact (Finset.mem_insert.mp hm).resolve_right (hp hps)

variable [Fintype ι]

private theorem sum_pair_partition (c : Finset (ι × Bool) → Bit)
    (hlarge : ∀ t, 3 < t.card → c t = 0)
    (hfree : ∀ t, (∀ i, (i, false) ∈ t → (i, true) ∉ t) → c t = 0)
    (s : Finset (ι × Bool)) :
    (∑ t ∈ s.powerset, c t) = ∑ i, ∑ t ∈ supportsWithPair s i, c t := by
  classical
  have hd : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (supportsWithPair s) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro t hit hjt
    obtain ⟨_, hi, ht⟩ := (mem_supportsWithPair s t i).mp hit
    obtain ⟨_, hj, _⟩ := (mem_supportsWithPair s t j).mp hjt
    exact hij (pair_unique ht hi hj)
  rw [← Finset.sum_biUnion hd]
  symm
  apply Finset.sum_subset
  · intro t ht
    obtain ⟨i, _, hit⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_powerset.mpr ((mem_supportsWithPair s t i).mp hit).1
  · intro t ht hnot
    by_cases hlarge' : 3 < t.card
    · exact hlarge t hlarge'
    apply hfree
    intro i hi hj
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (mem_supportsWithPair s t i).mpr
      ⟨Finset.mem_powerset.mp ht, (pair_subset_iff i t).mpr ⟨hi, hj⟩,
        Nat.le_of_not_gt hlarge'⟩⟩

/-- The monomial supports of a cubic vanishing on the split quadratic
zero cone determine a single affine quotient by that quadratic form. -/
theorem factor_support_sum [Nontrivial ι] (c : Finset (ι × Bool) → Bit)
    (hdegree : ∀ t, 3 < t.card → c t = 0)
    (hvanish : ∀ s : Finset (ι × Bool),
      (∑ i, ((if (i, false) ∈ s then 1 else 0) *
        (if (i, true) ∈ s then 1 else 0) : Bit)) = 0 → ∑ t ∈ s.powerset, c t = 0) :
    ∃ a : Bit, ∃ B C : ι → Bit, ∀ s : Finset (ι × Bool),
      let x : ι → Bit := fun i => if (i, false) ∈ s then 1 else 0
      let y : ι → Bit := fun i => if (i, true) ∈ s then 1 else 0
      (∑ t ∈ s.powerset, c t) = quadratic x y * (a + form B x + form C y) := by
  classical
  have hfree : ∀ t, (∀ i, (i, false) ∈ t → (i, true) ∉ t) → c t = 0 := by
    apply SplitQuadraticCubic.coefficient_zero_on_pair_free
    intro t ht
    apply hvanish
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : (i, false) ∈ t
    · simp [hi, ht i hi]
    · simp [hi]
  let a (i : ι) := c (pair i)
  let B (i j : ι) := if j = i then 0 else c (insert (j, false) (pair i))
  let C (i j : ι) := if j = i then 0 else c (insert (j, true) (pair i))
  let support (x y : ι → Bit) : Finset (ι × Bool) :=
    Finset.univ.filter (fun p => (if p.2 then y p.1 else x p.1) = 1)
  have hbits : ∀ b : Bit, b = 0 ∨ b = 1 := by decide +kernel
  have hp (x y : ι → Bit) (i : ι) :
      pair i ⊆ support x y ↔ x i = 1 ∧ y i = 1 := by
    simp [pair_subset_iff, support]
  have heval (x y : ι → Bit) :
      (∑ t ∈ (support x y).powerset, c t) = evaluate a B C x y := by
    rw [sum_pair_partition c hdegree hfree, evaluate]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : pair i ⊆ support x y
    · obtain ⟨hx, hy⟩ := (hp x y i).mp hi
      have hsums :
          (∑ p ∈ support x y with p.1 ≠ i, c (insert p (pair i))) =
            ∑ j, (B i j * x j + C i j * y j) := by
        have hfilter : (support x y).filter (fun p => p.1 ≠ i) =
            Finset.univ.filter (fun p : ι × Bool =>
              (if p.2 then y p.1 else x p.1) = 1 ∧ p.1 ≠ i) := by
          ext p
          simp [support]
        rw [hfilter, Finset.sum_filter, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        rw [Fintype.sum_bool]
        rcases hbits (x j) with hX | hX <;> rcases hbits (y j) with hY | hY <;>
          by_cases hji : j = i <;> simp [B, C, hX, hY, hji, add_comm]
      rw [sum_supportsWithPair c _ _ hi, hsums, Finset.sum_add_distrib,
        hx, hy, one_mul, one_mul]
      simp only [a, form, add_assoc]
    · rw [supportsWithPair, ite_eq_right hi, Finset.sum_empty]
      rcases hbits (x i) with h0 | h1
      · simp [h0]
      · have hy : y i = 0 := (hbits (y i)).resolve_right (fun h => hi ((hp x y i).mpr ⟨h1, h⟩))
        simp [hy]
  have hV (x y : ι → Bit) (h : quadratic x y = 0) : evaluate a B C x y = 0 := by
    rw [← heval]
    apply hvanish
    have select (b : Bit) : (if b = 1 then 1 else 0 : Bit) = b := by
      rcases hbits b with hb | hb <;> simp [hb]
    simpa [quadratic, support, select] using h
  obtain ⟨a₀, B₀, C₀, hf⟩ := SplitQuadraticCubic.factor_of_vanish a B C
    (by simp [B]) (by simp [C]) hV
  refine ⟨a₀, B₀, C₀, fun s => ?_⟩
  let x : ι → Bit := fun i => if (i, false) ∈ s then 1 else 0
  let y : ι → Bit := fun i => if (i, true) ∈ s then 1 else 0
  have hs : support x y = s := by
    ext p
    obtain ⟨i, e⟩ := p
    cases e <;> simp [support, x, y]
  change (∑ t ∈ s.powerset, c t) = _
  calc
    (∑ t ∈ s.powerset, c t) = evaluate a B C x y := by simpa only [hs] using heval x y
    _ = _ := hf x y

end D5.S3.HomologicalAlgebra.SplitQuadraticSupport

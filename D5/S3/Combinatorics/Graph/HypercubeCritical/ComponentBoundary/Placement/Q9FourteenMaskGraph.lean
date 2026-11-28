import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-! A counting obstruction for a nine-vertex contact graph. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskGraph

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem degree_profile (hV : Fintype.card V = 9) (hE : G.edgeFinset.card = 14)
    (hmin : ∀ x, 3 ≤ G.degree x) :
    ∃ v, G.degree v = 4 ∧ ∀ x, x ≠ v → G.degree x = 3 := by
  classical
  let excess (x : V) := G.degree x - 3
  have hdegree (x : V) : G.degree x = 3 + excess x := by
    have hx := hmin x
    dsimp only [excess]
    omega
  have hsumConst : (∑ _ : V, (3 : ℕ)) = 27 := by
    rw [sum_const, card_univ, hV, nsmul_eq_mul]
    decide
  have hsum : (∑ x, excess x) = 1 := by
    have h : (∑ x : V, G.degree x) = 27 + ∑ x, excess x := by
      rw [← hsumConst, ← sum_add_distrib]
      exact sum_congr rfl fun x _ => hdegree x
    rw [G.sum_degrees_eq_twice_card_edges, hE] at h
    omega
  have hexists : ∃ v, 0 < excess v := by
    by_contra h
    have hzero (x : V) : excess x = 0 :=
      Nat.eq_zero_of_not_pos fun hx => h ⟨x, hx⟩
    simp only [hzero, sum_const_zero] at hsum
    omega
  obtain ⟨v, hvPos⟩ := hexists
  have hrest : (∑ x ∈ univ.erase v, excess x) + excess v = 1 :=
    (sum_erase_add univ excess (mem_univ v)).trans hsum
  refine ⟨v, ?_, fun x hx => ?_⟩
  · rw [hdegree]
    omega
  · have hxLe : excess x ≤ ∑ y ∈ univ.erase v, excess y :=
      single_le_sum (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hx, mem_univ x⟩)
    rw [hdegree]
    omega

private theorem adj_iff_of_three_neighbors {x a b c : V}
    (hx : G.degree x = 3) (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (y : V) :
    G.Adj x y ↔ y = a ∨ y = b ∨ y = c := by
  classical
  have hrow : ({a, b, c} : Finset V) = G.neighborFinset x := by
    apply eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      apply (G.mem_neighborFinset x z).mpr
      rcases hz with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
    · rw [G.card_neighborFinset_eq_degree, hx,
        card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩]
  rw [← G.mem_neighborFinset x y, ← hrow]
  simp only [mem_insert, mem_singleton]

/-- The square law and a second common neighbor at every cubic edge with a
common neighbor exclude fourteen edges on nine vertices. -/
theorem fourteen_edges_on_nine_vertices_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 9) (hE : G.edgeFinset.card = 14)
    (hmin : ∀ x, 3 ≤ G.degree x)
    (hSquare : ∀ ⦃a v c : V⦄, G.Adj a v → G.Adj a c → v ≠ c →
      G.degree a = 3 → G.degree v = 3 →
      ∃ d, d ≠ a ∧ G.Adj v d ∧ G.Adj c d)
    (hSecond : ∀ ⦃x y w : V⦄, G.Adj x y →
      G.degree x = 3 → G.degree y = 3 → G.Adj x w → G.Adj y w →
      ∃ z, z ≠ w ∧ G.Adj x z ∧ G.Adj y z) : False := by
  classical
  obtain ⟨v, hv, hcubic⟩ := degree_profile hV hE hmin
  let A := G.neighborFinset v
  let B : Finset V := univ \ insert v A
  let N (S : Finset V) (x : V) := S.filter (G.Adj x)
  have memA {x : V} : x ∈ A ↔ G.Adj v x := G.mem_neighborFinset v x
  have memB {x : V} : x ∈ B ↔ x ≠ v ∧ x ∉ A := by
    simp only [B, mem_sdiff, mem_univ, true_and, mem_insert, not_or]
  have memN {S : Finset V} {x y : V} : y ∈ N S x ↔ y ∈ S ∧ G.Adj x y :=
    mem_filter
  have vNotA : v ∉ A := fun h => G.irrefl (memA.mp h)
  have cardA : A.card = 4 := (G.card_neighborFinset_eq_degree v).trans hv
  have cardB : B.card = 4 := by
    change (univ \ insert v A).card = 4
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV,
      card_insert_of_notMem vNotA, cardA]
  have cubicA {a : V} (ha : a ∈ A) : G.degree a = 3 := hcubic a (memA.mp ha).ne'
  have cubicB {b : V} (hb : b ∈ B) : G.degree b = 3 := hcubic b (memB.mp hb).1
  have notAdjHub {b : V} (hb : b ∈ B) : ¬G.Adj b v :=
    fun h => (memB.mp hb).2 (memA.mpr h.symm)
  have splitNeighbors (x : V) :
      (N A x).card + (N B x).card = ((G.neighborFinset x).erase v).card := by
    have hdisj : Disjoint (N A x) (N B x) := disjoint_left.mpr fun _ ha hb =>
      (memB.mp (memN.mp hb).1).2 (memN.mp ha).1
    rw [← card_union_of_disjoint hdisj]
    apply congrArg Finset.card
    ext y
    simp only [mem_union, memN, mem_erase, G.mem_neighborFinset x y, memB]
    constructor
    · rintro (⟨ha, hxy⟩ | ⟨hb, hxy⟩)
      · exact ⟨(memA.mp ha).ne', hxy⟩
      · exact ⟨hb.1, hxy⟩
    · rintro ⟨hy, hxy⟩
      by_cases ha : y ∈ A
      · exact Or.inl ⟨ha, hxy⟩
      · exact Or.inr ⟨⟨hy, ha⟩, hxy⟩
  have budgetA {a : V} (ha : a ∈ A) : (N A a).card + (N B a).card = 2 := by
    rw [splitNeighbors, card_erase_of_mem
      ((G.mem_neighborFinset a v).mpr (memA.mp ha).symm),
      G.card_neighborFinset_eq_degree, cubicA ha]
  have budgetB {b : V} (hb : b ∈ B) : (N A b).card + (N B b).card = 3 := by
    rw [splitNeighbors, erase_eq_of_notMem
      (fun h => notAdjHub hb ((G.mem_neighborFinset b v).mp h)),
      G.card_neighborFinset_eq_degree, cubicB hb]
  have touched {b : V} (hb : b ∈ B) (hpos : 0 < (N A b).card) :
      2 ≤ (N A b).card := by
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    have ⟨haA, hba⟩ := memN.mp ha
    obtain ⟨d, hda, hbd, hvd⟩ :=
      hSquare hba.symm (memA.mp haA).symm (memB.mp hb).1 (cubicA haA) (cubicB hb)
    exact Nat.succ_le_of_lt
      (one_lt_card.mpr ⟨a, ha, d, memN.mpr ⟨memA.mpr hvd, hbd⟩, hda.symm⟩)
  have untouched {b : V} (hb : b ∈ B) (hz : (N A b).card = 0) :
      N B b = B.erase b := by
    apply eq_of_subset_of_card_le
    · intro x hx
      exact mem_erase.mpr ⟨(memN.mp hx).2.ne', (memN.mp hx).1⟩
    · rw [card_erase_of_mem hb, cardB]
      have h := budgetB hb
      omega
  have crossCount : (∑ a ∈ A, (N B a).card) = ∑ b ∈ B, (N A b).card := by
    calc
      (∑ a ∈ A, (N B a).card) = ∑ b ∈ B, (A.bipartiteBelow G.Adj b).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := A) (t := B) G.Adj
      _ = ∑ b ∈ B, (N A b).card := by
        refine sum_congr rfl fun b _ => congrArg Finset.card ?_
        ext a
        rw [mem_bipartiteBelow, memN, G.adj_comm a b]
  have constA : (∑ _ ∈ A, (2 : ℕ)) = 8 := by
    rw [sum_const, cardA, nsmul_eq_mul]
    decide
  have constB : (∑ _ ∈ B, (2 : ℕ)) = 8 := by
    rw [sum_const, cardB, nsmul_eq_mul]
    decide
  have upperA (a : V) (ha : a ∈ A) : (N B a).card ≤ 2 := by
    have h := budgetA ha
    omega
  by_cases hall : ∀ b ∈ B, 0 < (N A b).card
  · -- All four vertices of B meet A. The two bounds on the cross count coincide.
    have lowerB (b : V) (hb : b ∈ B) : 2 ≤ (N A b).card := touched hb (hall b hb)
    have hUpper : (∑ a ∈ A, (N B a).card) ≤ 8 := by
      rw [← constA]
      exact sum_le_sum upperA
    have hLower : 8 ≤ ∑ b ∈ B, (N A b).card := by
      rw [← constB]
      exact sum_le_sum lowerB
    have crossA {a : V} (ha : a ∈ A) : (N B a).card = 2 := by
      by_contra hne
      have hlt : (∑ a ∈ A, (N B a).card) < ∑ _ ∈ A, (2 : ℕ) :=
        sum_lt_sum upperA ⟨a, ha, lt_of_le_of_ne (upperA a ha) hne⟩
      rw [constA, crossCount] at hlt
      exact (not_lt_of_ge hLower) hlt
    have crossB {b : V} (hb : b ∈ B) : (N A b).card = 2 := by
      by_contra hne
      have hlt : (∑ _ ∈ B, (2 : ℕ)) < ∑ b ∈ B, (N A b).card :=
        sum_lt_sum lowerB ⟨b, hb, lt_of_le_of_ne (lowerB b hb) (Ne.symm hne)⟩
      rw [constB, ← crossCount] at hlt
      exact (not_lt_of_ge hUpper) hlt
    have innerB {b : V} (hb : b ∈ B) : (N B b).card = 1 := by
      have h := budgetB hb
      rw [crossB hb] at h
      omega
    obtain ⟨b, hb⟩ := card_pos.mp (show 0 < B.card by rw [cardB]; decide)
    obtain ⟨a, ha⟩ := card_pos.mp (hall b hb)
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < (N B b).card by rw [innerB hb]; decide)
    have ⟨haA, hba⟩ := memN.mp ha
    have ⟨hcB, hbc⟩ := memN.mp hc
    have hac : a ≠ c := fun h => (memB.mp hcB).2 (h ▸ haA)
    obtain ⟨d, hdb, had, hcd⟩ := hSquare hba hbc hac (cubicB hb) (cubicA haA)
    have hdNotA : d ∉ A := by
      intro hdA
      have hpos : 0 < (N A a).card := card_pos.mpr ⟨d, memN.mpr ⟨hdA, had⟩⟩
      have h := budgetA haA
      rw [crossA haA] at h
      omega
    have hdB : d ∈ B := memB.mpr ⟨fun h => notAdjHub hcB (h ▸ hcd), hdNotA⟩
    have htwo : 1 < (N B c).card :=
      one_lt_card.mpr ⟨d, memN.mpr ⟨hdB, hcd⟩, b, memN.mpr ⟨hb, hbc.symm⟩, hdb⟩
    rw [innerB hcB] at htwo
    omega
  · -- An untouched vertex uses all its edges in B and lowers the cross count.
    have hexists : ∃ u ∈ B, (N A u).card = 0 := by
      by_contra h
      exact hall fun b hb => Nat.pos_of_ne_zero fun hz => h ⟨b, hb, hz⟩
    obtain ⟨u, hu, huZero⟩ := hexists
    have adjU {b : V} (hb : b ∈ B) (hbu : b ≠ u) : G.Adj b u := by
      have hm : b ∈ N B u := by
        rw [untouched hu huZero]
        exact mem_erase.mpr ⟨hbu, hb⟩
      exact (memN.mp hm).2.symm
    have upperB (b : V) (hb : b ∈ B) : (N A b).card ≤ 2 := by
      by_cases hbu : b = u
      · subst b
        rw [huZero]
        omega
      · have hpos : 0 < (N B b).card := card_pos.mpr ⟨u, memN.mpr ⟨hu, adjU hb hbu⟩⟩
        have h := budgetB hb
        omega
    have crossLt : (∑ a ∈ A, (N B a).card) < 8 := by
      have hlt : (∑ b ∈ B, (N A b).card) < ∑ _ ∈ B, (2 : ℕ) :=
        sum_lt_sum upperB ⟨u, hu, by rw [huZero]; decide⟩
      rwa [← crossCount, constB] at hlt
    have hEdge : ∃ a ∈ A, (N A a).Nonempty := by
      by_contra h
      have hfull (a : V) (ha : a ∈ A) : (N B a).card = 2 := by
        have hz : (N A a).card = 0 :=
          Nat.eq_zero_of_not_pos fun hpos => h ⟨a, ha, card_pos.mp hpos⟩
        have h := budgetA ha
        omega
      have heq : (∑ a ∈ A, (N B a).card) = 8 :=
        (sum_congr rfl hfull).trans constA
      omega
    obtain ⟨a, haA, a', ha'⟩ := hEdge
    have ⟨ha'A, haa'⟩ := memN.mp ha'
    obtain ⟨d, hdv, had, ha'd⟩ :=
      hSecond haa' (cubicA haA) (cubicA ha'A) (memA.mp haA).symm (memA.mp ha'A).symm
    have rowA := adj_iff_of_three_neighbors (cubicA haA)
      (memA.mp haA).symm haa' had (memA.mp ha'A).ne hdv.symm ha'd.ne
    by_cases hdA : d ∈ A
    · -- A triangle inside A exhausts the degrees of its three vertices.
      let T : Finset V := {a, a', d}
      have subT : T ⊆ A := by
        intro z hz
        change z ∈ ({a, a', d} : Finset V) at hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact haA
        · exact ha'A
        · exact hdA
      have cardT : T.card = 3 := card_triple_eq_three_iff.mpr ⟨haa'.ne, had.ne, ha'd.ne⟩
      have hleft : (A \ T).card = 1 := by
        rw [card_sdiff_of_subset subT, cardA, cardT]
      obtain ⟨w, hw⟩ := card_eq_one.mp hleft
      have outsideT {z : V} : z ∈ A \ T ↔ z = w := by rw [hw, mem_singleton]
      have ⟨hwA, hwT⟩ := mem_sdiff.mp (outsideT.mpr (Eq.refl w))
      have rowA' := adj_iff_of_three_neighbors (cubicA ha'A)
        (memA.mp ha'A).symm haa'.symm ha'd (memA.mp haA).ne hdv.symm had.ne
      have rowD := adj_iff_of_three_neighbors (cubicA hdA)
        (memA.mp hdA).symm had.symm ha'd.symm (memA.mp haA).ne (memA.mp ha'A).ne haa'.ne
      have confined {t z : V} (ht : t ∈ T) (htz : G.Adj t z) : z = v ∨ z ∈ T := by
        have ht' : t = a ∨ t = a' ∨ t = d := by simpa [T] using ht
        rcases ht' with rfl | rfl | rfl
        · rcases (rowA z).mp htz with rfl | rfl | rfl <;> simp [T]
        · rcases (rowA' z).mp htz with rfl | rfl | rfl <;> simp [T]
        · rcases (rowD z).mp htz with rfl | rfl | rfl <;> simp [T]
      have wNoA : (N A w).card = 0 := by
        apply card_eq_zero.mpr
        apply filter_eq_empty_iff.mpr
        intro z hzA hwz
        by_cases hzT : z ∈ T
        · rcases confined hzT hwz.symm with h | h
          · exact (memA.mp hwA).ne' h
          · exact hwT h
        · exact hwz.ne' (outsideT.mp (mem_sdiff.mpr ⟨hzA, hzT⟩))
      have wHasB : 0 < (N B w).card := by
        have h := budgetA hwA
        omega
      obtain ⟨b, hb⟩ := card_pos.mp wHasB
      have ⟨hbB, hwb⟩ := memN.mp hb
      have bHasA : 0 < (N A b).card := card_pos.mpr ⟨w, memN.mpr ⟨hwA, hwb.symm⟩⟩
      have sub : N A b ⊆ ({w} : Finset V) := by
        intro z hz
        have ⟨hzA, hbz⟩ := memN.mp hz
        have hzT : z ∉ T := by
          intro ht
          rcases confined ht hbz.symm with h | h
          · exact (memB.mp hbB).1 h
          · exact (memB.mp hbB).2 (subT h)
        exact mem_singleton.mpr (outsideT.mp (mem_sdiff.mpr ⟨hzA, hzT⟩))
      have hlo := touched hbB bHasA
      have hhi := card_le_card sub
      rw [card_singleton] at hhi
      omega
    · -- The second common neighbor in B is adjacent to the untouched vertex.
      have hdB : d ∈ B := memB.mpr ⟨hdv, hdA⟩
      have hdu : d ≠ u := by
        intro h
        have hpos : 0 < (N A u).card :=
          card_pos.mpr ⟨a, memN.mpr ⟨haA, h ▸ had.symm⟩⟩
        omega
      obtain ⟨z, hzd, haz, huz⟩ :=
        hSquare had.symm (adjU hdB hdu) (fun h => (memB.mp hu).2 (h ▸ haA))
          (cubicB hdB) (cubicA haA)
      rcases (rowA z).mp haz with hzv | hza' | hze
      · exact notAdjHub hu (hzv ▸ huz)
      · have hpos : 0 < (N A u).card := card_pos.mpr ⟨a', memN.mpr ⟨ha'A, hza' ▸ huz⟩⟩
        omega
      · exact hzd hze

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskGraph

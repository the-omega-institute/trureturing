/- GID: D5/S3/Combinatorics/TwoLayerSolidPartitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoLayerSolidPartitions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves W. Meeussen's 2025 conjecture in OEIS A381265: the two-layer solid partitions with first layer a plane partition of n and second layer a plane partition of 3 number 3(2 A000219(n) - A000990(n) - 2 A000041(n) + 1). -/

/-
proof_shape: result: content
escape_witness: form (2): the conclusion `result` itself, produced on its live path by the
  classification of the six plane partitions of 3 (three lines, three corners), the complement
  counts through the coordinate-permutation bijection of lower sets, the restriction to a
  coordinate plane and to an axis, and the Young-diagram correspondence between lower sets of
  n cells of N^2 and the partitions of n (`toYoung`, `youngPartition`)
admission_basis: open-problem-resolution (issue #10460)
Direct frozen dependencies: D5/S3/Combinatorics/SolidPartitionFirstColumn (`IsSolidPartition`),
  D5/S1/Words/Compositions/ZeroPrependedFirstSumsOddParts (`cellsOfRowLens_card`, `rowLens_sum`)
-/

import D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts
import D5.S3.Combinatorics.SolidPartitionFirstColumn
import Mathlib.Data.Pi.Interval
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoLayerSolidPartitions

open D5.S3.Combinatorics.SolidPartitionFirstColumn (IsSolidPartition)
open D5.S1.Words.Compositions.ZeroPrependedFirstSumsOddParts (rowLens_sum cellsOfRowLens_card)

/-!
OEIS A381265 (Wouter Meeussen, 2025): the number of solid (3D) partitions with two layers whose
second layer is a plane partition of 3, the first layer being a plane partition of `n`. The
entry conjectures that it equals `3 (2 A000219(n) - A000990(n) - 2 A000041(n) + 1)`, with
A000219 the plane partitions, A000990 the plane partitions with at most two rows and A000041
the partitions of `n`. A plane partition of `n` is a lower set of `n` cells of `ℕ³`
(`IsSolidPartition` at `d = 3`).
-/


/-- A000219: the plane partitions of `n`, as lower sets of `n` cells of `ℕ³`. -/
noncomputable def planeCount (n : ℕ) : ℕ := {I : Finset (Fin 3 → ℕ) | IsSolidPartition n I}.ncard

/-- A000990: the plane partitions of `n` with at most two rows (first coordinate at most 1). -/
noncomputable def twoRowCount (n : ℕ) : ℕ :=
  {I : Finset (Fin 3 → ℕ) | IsSolidPartition n I ∧ ∀ c ∈ I, c 0 ≤ 1}.ncard

/-- A381265: the two-layer solid partitions whose first layer is a plane partition of `n` and
whose second layer is a plane partition of 3 contained in it. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : Finset (Fin 3 → ℕ) × Finset (Fin 3 → ℕ) |
    IsSolidPartition n p.1 ∧ IsSolidPartition 3 p.2 ∧ p.2 ⊆ p.1}.ncard

/-- Meeussen's conjecture (OEIS A381265, 2025), with A000041 the partitions of `n`. -/
def claim : Prop :=
  ∀ n : ℕ, (a n : ℤ) =
    3 * (2 * (planeCount n : ℤ) - twoRowCount n - 2 * Fintype.card (Nat.Partition n) + 1)

/-- The cell `t e_k`. -/
private def e (k : Fin 3) (t : ℕ) : Fin 3 → ℕ := Pi.single k t

/-- The cells `0`, `e_k` and `2 e_k`. -/
private def T : Finset (Fin 3 → ℕ) := {0, e 0 1, e 1 1, e 2 1, e 0 2, e 1 2, e 2 2}

/-- The three lines `{0, e_k, 2 e_k}` and the three corners `{0, e_i, e_j}`. -/
private def six : Finset (Finset (Fin 3 → ℕ)) :=
  {{0, e 0 1, e 0 2}, {0, e 1 1, e 1 2}, {0, e 2 1, e 2 2},
   {0, e 0 1, e 1 1}, {0, e 0 1, e 2 1}, {0, e 1 1, e 2 1}}

open Classical in
private noncomputable def F (d n : ℕ) : Finset (Finset (Fin d → ℕ)) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range n).powerset.filter (IsSolidPartition n)

/-- Lower sets of `n` cells of `ℕ²` are the Young diagrams with `n` cells. -/
private def toYoung (n : ℕ) :
    {I : Finset (Fin 2 → ℕ) // IsLowerSet (I : Set (Fin 2 → ℕ)) ∧ I.card = n} ≃
      {μ : YoungDiagram // μ.cells.card = n} where
  toFun I := ⟨⟨I.1.map (OrderIso.finTwoArrowIso ℕ).toEquiv.toEmbedding, by
      rw [Finset.coe_map]
      exact I.2.1.image (OrderIso.finTwoArrowIso ℕ)⟩, by
      simpa using I.2.2⟩
  invFun μ := ⟨μ.1.cells.map (OrderIso.finTwoArrowIso ℕ).symm.toEquiv.toEmbedding, by
      rw [Finset.coe_map]
      exact μ.1.isLowerSet.image (OrderIso.finTwoArrowIso ℕ).symm, by simpa using μ.2⟩
  left_inv I := by
    apply Subtype.ext
    ext c
    simp
  right_inv μ := by
    apply Subtype.ext
    apply YoungDiagram.ext
    ext c
    simp

/-- Young diagrams with `n` cells correspond to partitions of `n` (row lengths). -/
private noncomputable def youngPartition (n : ℕ) :
    {μ : YoungDiagram // μ.cells.card = n} ≃ Nat.Partition n where
  toFun μ := ⟨μ.1.rowLens, fun hx => YoungDiagram.pos_of_mem_rowLens μ.1 _ hx, by
    rw [Multiset.sum_coe, rowLens_sum, μ.2]⟩
  invFun p := ⟨YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·))
      (Multiset.pairwise_sort _ _).sortedGE, by
    have h := p.parts_sum
    rw [← Multiset.sort_eq p.parts (· ≥ ·), Multiset.sum_coe] at h
    change (YoungDiagram.cellsOfRowLens _).card = n
    rw [cellsOfRowLens_card, h]⟩
  left_inv μ := by
    apply Subtype.ext
    have hs : Multiset.sort (μ.1.rowLens : Multiset ℕ) (· ≥ ·) = μ.1.rowLens :=
      (Multiset.coe_sort _ _).trans (List.mergeSort_eq_self _ μ.1.rowLens_sorted.pairwise)
    dsimp only
    simp only [hs, YoungDiagram.ofRowLens_to_rowLens_eq_self]
  right_inv p := by
    apply Nat.Partition.ext
    dsimp only
    rw [YoungDiagram.rowLens_ofRowLens_eq_self]
    · exact Multiset.sort_eq _ _
    · intro x hx
      exact p.parts_pos ((Multiset.mem_sort _).mp hx)

theorem result : claim := by
  classical
  intro n
  -- lower sets of `n` cells form a finite family
  have mem_F : ∀ (d : ℕ) (I : Finset (Fin d → ℕ)), I ∈ F d n ↔ IsSolidPartition n I := by
    intro d I
    unfold F
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact fun h => h.2
    · intro hI
      refine ⟨fun c hc => ?_, hI⟩
      rw [Fintype.mem_piFinset]
      intro i
      have h := Finset.card_le_card
        (fun c' (hc' : c' ∈ Finset.Iic c) => hI.1 (Finset.mem_Iic.mp hc') hc)
      rw [Pi.card_Iic, hI.2] at h
      simp only [Nat.card_Iic] at h
      have hi : c i + 1 ≤ ∏ j, (c j + 1) :=
        Finset.single_le_prod' (fun j _ => Nat.le_add_left 1 (c j)) (Finset.mem_univ i)
      rw [Finset.mem_range]
      omega
  have ncard_eq : ∀ (d : ℕ) (p : Finset (Fin d → ℕ) → Prop),
      {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ p I}.ncard = ((F d n).filter p).card := by
    intro d p
    rw [← Set.ncard_coe_finset]
    congr 1
    ext I
    simp [mem_F]
  have hplane : planeCount n = (F 3 n).card := by
    have := ncard_eq 3 (fun _ => True)
    simpa [planeCount] using this
  have htwo : twoRowCount n = ((F 3 n).filter fun P => ∀ c ∈ P, c 0 ≤ 1).card := by
    unfold twoRowCount
    rw [ncard_eq 3 (fun P => ∀ c ∈ P, c 0 ≤ 1)]
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  -- lower sets of `n` cells of `ℕ²` are the Young diagrams of the partitions of `n`
  have hpart : Fintype.card (Nat.Partition n) = (F 2 n).card := by
    have hyoung : {I : Finset (Fin 2 → ℕ) | IsLowerSet (I : Set (Fin 2 → ℕ)) ∧ I.card = n}.ncard =
        Fintype.card (Nat.Partition n) := by
      rw [← Nat.card_coe_set_eq]
      exact (Nat.card_congr ((toYoung n).trans (youngPartition n))).trans
        Nat.card_eq_fintype_card
    rw [← hyoung]
    simpa [IsSolidPartition] using ncard_eq 2 (fun _ => True)
  -- permuting the coordinates is a bijection on lower sets of `n` cells
  have perm_mem : ∀ (σ : Equiv.Perm (Fin 3)) (P : Finset (Fin 3 → ℕ)),
      IsSolidPartition n P → IsSolidPartition n (P.image fun c => c ∘ σ) := by
    intro σ P hP
    refine ⟨?_, ?_⟩
    · intro x y hyx hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx ⊢
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨y ∘ σ.symm, hP.1 (fun i => ?_) hc, by funext i; simp⟩
      have := hyx (σ.symm i)
      simpa using this
    · rw [Finset.card_image_of_injective _ (fun x y h => by
        funext i; simpa using congrFun h (σ.symm i)), hP.2]
  have card_perm : ∀ (σ : Equiv.Perm (Fin 3)) (p : (Fin 3 → ℕ) → Prop),
      ((F 3 n).filter fun P => ∀ c ∈ P, p c).card =
        ((F 3 n).filter fun P => ∀ c ∈ P, p (c ∘ σ.symm)).card := by
    intro σ p
    refine Finset.card_bij' (fun P _ => P.image fun c => c ∘ σ)
      (fun P _ => P.image fun c => c ∘ σ.symm) ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_filter, mem_F] at hP ⊢
      refine ⟨perm_mem σ P hP.1, fun c hc => ?_⟩
      simp only [Finset.mem_image] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      simpa [Function.comp_def] using hP.2 c' hc'
    · intro P hP
      rw [Finset.mem_filter, mem_F] at hP ⊢
      refine ⟨perm_mem σ.symm P hP.1, fun c hc => ?_⟩
      simp only [Finset.mem_image] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      exact hP.2 c' hc'
    · intro P _
      ext c
      simp [Finset.mem_image, Function.comp_def]
    · intro P _
      ext c
      simp [Finset.mem_image, Function.comp_def]
  -- every cell of a lower set of `n` cells has coordinates below `n`
  have box : ∀ (d : ℕ) (I : Finset (Fin d → ℕ)), IsSolidPartition n I → ∀ c ∈ I, ∀ i, c i < n := by
    intro d I hI c hc i
    have h := (Fintype.mem_piFinset.mp
      (Finset.mem_powerset.mp (Finset.mem_filter.mp ((mem_F d I).mpr hI)).1 hc)) i
    exact Finset.mem_range.mp h
  -- lower sets in the plane `c 2 = 0` are the lower sets of `ℕ²`
  have card_plane : ((F 3 n).filter fun P => ∀ c ∈ P, c 2 = 0).card = (F 2 n).card := by
    have hlast : (2 : Fin 3) = Fin.last 2 := rfl
    refine Finset.card_bij' (fun P _ => P.image Fin.init)
      (fun Q _ => Q.image fun x => Fin.snoc x 0) ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_filter, mem_F] at hP
      rw [mem_F]
      obtain ⟨⟨hlow, hcard⟩, h2⟩ := hP
      have hinj : Set.InjOn Fin.init (P : Set (Fin 3 → ℕ)) := by
        intro x hx y hy hxy
        rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hxy, ← hlast, h2 x hx, h2 y hy]
      refine ⟨?_, by rw [Finset.card_image_of_injOn hinj, hcard]⟩
      intro u v hvu hu
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu ⊢
      obtain ⟨c, hc, rfl⟩ := hu
      refine ⟨Fin.snoc v 0, hlow (?_ : (Fin.snoc v 0 : Fin 3 → ℕ) ≤ c) hc, Fin.init_snoc _ _⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · show (Fin.snoc v 0 : Fin 3 → ℕ) (Fin.last 2) ≤ c (Fin.last 2)
        rw [Fin.snoc_last]
        exact Nat.zero_le _
      · simpa [Fin.snoc_castSucc, Fin.init] using hvu j
    · intro Q hQ
      rw [mem_F] at hQ
      rw [Finset.mem_filter, mem_F]
      obtain ⟨hlow, hcard⟩ := hQ
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro u v hvu hu
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hu ⊢
        obtain ⟨x, hx, rfl⟩ := hu
        have hv2 : v (Fin.last 2) = 0 := by
          have := hvu (Fin.last 2)
          simp only [Fin.snoc_last] at this
          omega
        refine ⟨Fin.init v, hlow (fun j => ?_) hx, ?_⟩
        · have := hvu j.castSucc
          simpa [Fin.init] using this
        · rw [← hv2]
          exact Fin.snoc_init_self v
      · rw [Finset.card_image_of_injective _ (fun x y h => by
          simpa using congrArg Fin.init h), hcard]
      · intro c hc
        simp only [Finset.mem_image] at hc
        obtain ⟨x, hx, rfl⟩ := hc
        rw [hlast, Fin.snoc_last]
    · intro P hP
      rw [Finset.mem_filter] at hP
      ext c
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, ⟨c', hc', rfl⟩, rfl⟩
        rw [show (0 : ℕ) = c' (Fin.last 2) by rw [← hlast]; exact (hP.2 c' hc').symm,
          Fin.snoc_init_self]
        exact hc'
      · intro hc
        refine ⟨Fin.init c, ⟨c, hc, rfl⟩, ?_⟩
        rw [show (0 : ℕ) = c (Fin.last 2) by rw [← hlast]; exact (hP.2 c hc).symm,
          Fin.snoc_init_self]
    · intro Q _
      ext x
      simp [Finset.mem_image, Fin.init_snoc]
  -- a lower set of `n` cells on the third axis is the segment `0, …, (n - 1) e_2`
  have card_axis : ((F 3 n).filter fun P => ∀ c ∈ P, c 0 = 0 ∧ c 1 = 0).card = 1 := by
    have hseg_inj : Function.Injective fun t : ℕ => (![0, 0, t] : Fin 3 → ℕ) := by
      intro s t h
      simpa using congrFun h 2
    rw [Finset.card_eq_one]
    refine ⟨(Finset.range n).image fun t => ![0, 0, t], ?_⟩
    ext P
    rw [Finset.mem_filter, mem_F, Finset.mem_singleton]
    constructor
    · rintro ⟨hP, hax⟩
      apply Finset.eq_of_subset_of_card_le
      · intro c hc
        rw [Finset.mem_image]
        refine ⟨c 2, Finset.mem_range.mpr (box 3 P hP c hc 2), ?_⟩
        funext i
        fin_cases i <;> simp [(hax c hc).1, (hax c hc).2]
      · rw [Finset.card_image_of_injective _ hseg_inj, Finset.card_range, hP.2]
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro u v hvu hu
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hu ⊢
        obtain ⟨t, ht, rfl⟩ := hu
        refine ⟨v 2, by have := hvu 2; simp at this; omega, ?_⟩
        funext i
        fin_cases i
        · have := hvu 0; simp at this ⊢; omega
        · have := hvu 1; simp at this ⊢; omega
        · simp
      · rw [Finset.card_image_of_injective _ hseg_inj, Finset.card_range]
      · intro c hc
        simp only [Finset.mem_image] at hc
        obtain ⟨t, _, rfl⟩ := hc
        simp
  -- the six lower sets of three cells
  have memT : ∀ c : Fin 3 → ℕ, ∏ i, (c i + 1) ≤ 3 → c ∈ T := by
    intro c hc
    rw [Fin.prod_univ_three] at hc
    have h0 : c 0 ≤ 2 := by
      have := Nat.le_mul_of_pos_right (c 0 + 1) (show 0 < (c 1 + 1) * (c 2 + 1) by positivity)
      rw [← mul_assoc] at this
      omega
    have h1 : c 1 ≤ 2 := by
      have := Nat.le_mul_of_pos_right (c 1 + 1) (show 0 < (c 0 + 1) * (c 2 + 1) by positivity)
      rw [show (c 1 + 1) * ((c 0 + 1) * (c 2 + 1)) = (c 0 + 1) * (c 1 + 1) * (c 2 + 1) by ring]
        at this
      omega
    have h2 : c 2 ≤ 2 := by
      have := Nat.le_mul_of_pos_left (c 2 + 1) (show 0 < (c 0 + 1) * (c 1 + 1) by positivity)
      omega
    have hc' : c = ![c 0, c 1, c 2] := by
      funext i; fin_cases i <;> rfl
    rw [hc']
    interval_cases h0' : c 0 <;> interval_cases h1' : c 1 <;> interval_cases h2' : c 2 <;>
      first | decide | (norm_num at hc)
  have downT : ∀ c c' : Fin 3 → ℕ, c ∈ T → c' ≤ c → c' ∈ T := by
    intro c c' hc hle
    apply memT
    have hcT : ∏ i, (c i + 1) ≤ 3 := by
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    calc ∏ i, (c' i + 1) ≤ ∏ i, (c i + 1) :=
          Finset.prod_le_prod' (fun i _ => Nat.add_le_add_right (hle i) 1)
      _ ≤ 3 := hcT
  have hsix : T.powerset.filter
      (fun P => P.card = 3 ∧ ∀ c ∈ P, ∀ c' ∈ T, (∀ i, c' i ≤ c i) → c' ∈ P) = six := by
    decide
  have three : ∀ Q : Finset (Fin 3 → ℕ), IsSolidPartition 3 Q ↔ Q ∈ six := by
    intro Q
    constructor
    · intro hQ
      rw [← hsix, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun c hc => memT c ?_, hQ.2, fun c hc c' _ hle => hQ.1 (show c' ≤ c from hle) hc⟩
      have h := Finset.card_le_card
        (fun c' (hc' : c' ∈ Finset.Iic c) => hQ.1 (Finset.mem_Iic.mp hc') hc)
      rw [Pi.card_Iic] at h
      simpa [Nat.card_Iic, hQ.2] using h
    · intro hQ
      rw [← hsix, Finset.mem_filter, Finset.mem_powerset] at hQ
      obtain ⟨hQT, hcard, hR⟩ := hQ
      refine ⟨fun x y hyx hx => ?_, hcard⟩
      exact hR x hx y (downT x y (hQT hx) hyx) hyx
  -- a line lies in a lower set exactly when some cell has `k`-th coordinate at least 2
  have e_le : ∀ (k : Fin 3) (t : ℕ) (c : Fin 3 → ℕ), t ≤ c k → e k t ≤ c := by
    intro k t c h j
    by_cases hj : j = k
    · subst hj; simpa [e] using h
    · simp [e, hj]
  have line_sub : ∀ (k : Fin 3) (P : Finset (Fin 3 → ℕ)), IsLowerSet (P : Set (Fin 3 → ℕ)) →
      (({0, e k 1, e k 2} : Finset (Fin 3 → ℕ)) ⊆ P ↔ ¬ ∀ c ∈ P, c k ≤ 1) := by
    intro k P hP
    constructor
    · intro h hall
      have := hall (e k 2) (h (by simp))
      simp [e] at this
    · intro h
      push Not at h
      obtain ⟨c, hc, hck⟩ := h
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hP (fun j => Nat.zero_le _) hc
      · exact hP (e_le k 1 c (by omega)) hc
      · exact hP (e_le k 2 c (by omega)) hc
  have corner_sub : ∀ (i j : Fin 3) (P : Finset (Fin 3 → ℕ)), IsLowerSet (P : Set (Fin 3 → ℕ)) →
      (({0, e i 1, e j 1} : Finset (Fin 3 → ℕ)) ⊆ P ↔
        (¬ ∀ c ∈ P, c i = 0) ∧ ¬ ∀ c ∈ P, c j = 0) := by
    intro i j P hP
    have single : ∀ k, (e k 1 ∈ P ↔ ¬ ∀ c ∈ P, c k = 0) := by
      intro k
      constructor
      · intro h hall
        have := hall _ h
        simp [e] at this
      · intro h
        push Not at h
        obtain ⟨c, hc, hck⟩ := h
        exact hP (e_le k 1 c (by omega)) hc
    constructor
    · intro h
      exact ⟨(single i).mp (h (by simp)), (single j).mp (h (by simp))⟩
    · rintro ⟨hi, hj⟩ q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact hP (fun k => Nat.zero_le _) ((single i).mpr hi)
      · exact (single i).mpr hi
      · exact (single j).mpr hj
  -- count the pairs by their second layer
  have hsum : a n = ∑ Q ∈ six, ((F 3 n).filter fun P => Q ⊆ P).card := by
    have hset : {p : Finset (Fin 3 → ℕ) × Finset (Fin 3 → ℕ) |
        IsSolidPartition n p.1 ∧ IsSolidPartition 3 p.2 ∧ p.2 ⊆ p.1} =
        ↑((F 3 n ×ˢ six).filter fun p => p.2 ⊆ p.1) := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_product, mem_F, three]
      tauto
    unfold a
    rw [hset, Set.ncard_coe_finset, Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [Finset.card_filter]
  -- a line is contained in `P` unless all cells have `k`-th coordinate at most 1
  have hline : ∀ k : Fin 3, ((F 3 n).filter fun P => ({0, e k 1, e k 2} : Finset _) ⊆ P).card +
      ((F 3 n).filter fun P => ∀ c ∈ P, c 0 ≤ 1).card = (F 3 n).card := by
    intro k
    have hk : ((F 3 n).filter fun P => ∀ c ∈ P, c k ≤ 1).card =
        ((F 3 n).filter fun P => ∀ c ∈ P, c 0 ≤ 1).card := by
      have h := (card_perm (Equiv.swap 0 k) (fun c => c 0 ≤ 1)).symm
      simp only [Function.comp_def, Equiv.symm_swap, Equiv.swap_apply_left] at h
      convert h using 3
    have hQ : ((F 3 n).filter fun P => ({0, e k 1, e k 2} : Finset _) ⊆ P) =
        (F 3 n).filter fun P => ¬ ∀ c ∈ P, c k ≤ 1 :=
      Finset.filter_congr fun P hP => line_sub k P ((mem_F 3 P).mp hP).1
    rw [hQ, ← hk, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  -- lower sets in the coordinate plane `c i = 0`
  have hA : ∀ i : Fin 3, ((F 3 n).filter fun P => ∀ c ∈ P, c i = 0).card = (F 2 n).card := by
    intro i
    rw [← card_plane]
    have h := (card_perm (Equiv.swap 2 i) (fun c => c 2 = 0)).symm
    simp only [Function.comp_def, Equiv.symm_swap, Equiv.swap_apply_left] at h
    convert h using 3
  -- a corner is contained in `P` unless all cells lie in one of two coordinate planes
  have hcorner : ∀ i j : Fin 3,
      ((F 3 n).filter fun P => ∀ c ∈ P, c i = 0 ∧ c j = 0).card = 1 →
      ((F 3 n).filter fun P => ({0, e i 1, e j 1} : Finset _) ⊆ P).card + 2 * (F 2 n).card =
        (F 3 n).card + 1 := by
    intro i j hij
    have hQ : ((F 3 n).filter fun P => ({0, e i 1, e j 1} : Finset _) ⊆ P) =
        (F 3 n).filter fun P => ¬ ((∀ c ∈ P, c i = 0) ∨ ∀ c ∈ P, c j = 0) :=
      Finset.filter_congr fun P hP => by
        rw [corner_sub i j P ((mem_F 3 P).mp hP).1, not_or]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := F 3 n) (fun P => (∀ c ∈ P, c i = 0) ∨ ∀ c ∈ P, c j = 0)
    have hunion := Finset.card_union_add_card_inter
      ((F 3 n).filter fun P => ∀ c ∈ P, c i = 0) ((F 3 n).filter fun P => ∀ c ∈ P, c j = 0)
    rw [← Finset.filter_or, ← Finset.filter_and, hA i, hA j] at hunion
    have hand : ((F 3 n).filter fun P => (∀ c ∈ P, c i = 0) ∧ ∀ c ∈ P, c j = 0).card = 1 := by
      rw [← hij]
      congr 1
      exact Finset.filter_congr fun P _ =>
        ⟨fun h c hc => ⟨h.1 c hc, h.2 c hc⟩,
          fun h => ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩⟩
    rw [hQ]
    omega
  have hax01 := card_axis
  have hax02 : ((F 3 n).filter fun P => ∀ c ∈ P, c 0 = 0 ∧ c 2 = 0).card = 1 := by
    rw [← card_axis]
    have h := (card_perm (Equiv.swap 1 2) (fun c => c 0 = 0 ∧ c 1 = 0)).symm
    have h0 : (Equiv.swap (1 : Fin 3) 2).symm 0 = 0 := by decide
    have h1 : (Equiv.swap (1 : Fin 3) 2).symm 1 = 2 := by decide
    simp only [Function.comp_apply, h0, h1] at h
    convert h using 3
  have hax12 : ((F 3 n).filter fun P => ∀ c ∈ P, c 1 = 0 ∧ c 2 = 0).card = 1 := by
    rw [← card_axis]
    have h := (card_perm (finRotate 3).symm (fun c => c 0 = 0 ∧ c 1 = 0)).symm
    have h0 : (finRotate 3).symm.symm 0 = 1 := by decide
    have h1 : (finRotate 3).symm.symm 1 = 2 := by decide
    simp only [Function.comp_apply, h0, h1] at h
    convert h using 3
  -- assemble
  have hsum' : a n = ∑ Q ∈ six, ((F 3 n).filter fun P => Q ⊆ P).card := hsum
  rw [six, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hsum'
  have l0 := hline 0
  have l1 := hline 1
  have l2 := hline 2
  have c01 := hcorner 0 1 hax01
  have c02 := hcorner 0 2 hax02
  have c12 := hcorner 1 2 hax12
  rw [hsum', hplane, htwo, hpart]
  push_cast
  omega

end D5.S3.Combinatorics.TwoLayerSolidPartitions

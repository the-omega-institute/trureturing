/- GID: D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.claim; result=D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.result; claim=D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.claim
   digest: Actual partition cardinalities refute universal excedance parity positivity at twenty-eight. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Parity
namespace D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation

private def listPartitions : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, r, _ => if r = 0 then [[]] else []
  | fuel + 1, r, b => if r = 0 then [[]] else
      (List.range (min r b)).flatMap fun a =>
        (listPartitions fuel (r - (a + 1)) (a + 1)).map ((a + 1) :: ·)

private theorem complete (fuel r b : ℕ) (q : List ℕ)
    (hlen : q.length ≤ fuel) (hsum : q.sum = r)
    (hord : q.Pairwise (· ≥ ·)) (hpos : ∀ a ∈ q, 0 < a)
    (hbound : ∀ a ∈ q, a ≤ b) : q ∈ listPartitions fuel r b := by
  induction fuel generalizing r b q with
  | zero =>
    have : q = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst q
    simp_all [listPartitions]
  | succ fuel ih =>
    cases q with
    | nil => simp_all [listPartitions]
    | cons a q =>
      have ha := hpos a (by simp)
      have hab := hbound a (by simp)
      have hsum' : a + q.sum = r := by simpa using hsum
      have har : a ≤ r := by omega
      have hr : r ≠ 0 := by omega
      simp only [listPartitions, ite_eq_right hr, List.mem_flatMap]
      refine ⟨a-1, List.mem_range.mpr (by omega), ?_⟩
      have ha' : a - 1 + 1 = a := by omega
      rw [ha']
      apply List.mem_map.mpr
      refine ⟨q, ih (r-a) a q (by simpa using hlen) (by omega) hord.of_cons
        (fun x hx => hpos x (by simp [hx]))
        (fun x hx => (List.pairwise_cons.mp hord).1 x hx), rfl⟩

private theorem sound (fuel r b : ℕ) (q : List ℕ)
    (hq : q ∈ listPartitions fuel r b) :
    q.sum = r ∧ q.Pairwise (· ≥ ·) ∧ ∀ a ∈ q, 0 < a ∧ a ≤ b := by
  induction fuel generalizing r b q with
  | zero =>
    by_cases hr : r = 0
    · simp only [listPartitions, hr, ite_true, List.mem_singleton] at hq
      subst q
      simp [hr]
    · simp [listPartitions, hr] at hq
  | succ fuel ih =>
    by_cases hr : r = 0
    · simp only [listPartitions, hr, ite_true, List.mem_singleton] at hq
      subst q
      simp [hr]
    · simp only [listPartitions, ite_eq_right hr, List.mem_flatMap] at hq
      obtain ⟨a, ha, hq⟩ := hq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
      have hq := ht
      have ha' := List.mem_range.mp ha
      obtain ⟨hs, ho, hp⟩ := ih _ _ _ hq
      refine ⟨by simp only [List.sum_cons]; omega, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun x hx => (hp x hx).2, ho⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · constructor <;> omega
        · obtain ⟨hxp, hxb⟩ := hp x hx
          constructor <;> omega

private theorem enumeration_nodup (fuel r b : ℕ) :
    (listPartitions fuel r b).Nodup := by
  induction fuel generalizing r b with
  | zero => by_cases h : r = 0 <;> simp [listPartitions, h]
  | succ fuel ih =>
    by_cases h : r = 0
    · simp [listPartitions, h]
    · simp only [listPartitions, ite_eq_right h]
      apply List.nodup_flatMap.mpr
      constructor
      · intro a ha
        exact (ih _ _).map (by intro x y h; exact List.cons.inj h |>.2)
      · apply List.nodup_range.imp
        intro a b hab q hqa hqb
        obtain ⟨qa, hqa, heqa⟩ := List.mem_map.mp hqa
        obtain ⟨qb, hqb, heqb⟩ := List.mem_map.mp hqb
        have := List.cons.inj (heqa.trans heqb.symm) |>.1
        exact hab (by omega)

private def asPartition (n : ℕ) (q : {q // q ∈ listPartitions n n n}) : Nat.Partition n where
  parts := q.val
  parts_pos := by
    intro a ha
    exact ((sound n n n q.val q.property).2.2 a (by simpa using ha)).1
  parts_sum := by simpa using (sound n n n q.val q.property).1

private theorem asPartition_injective (n : ℕ) : Function.Injective (asPartition n) := by
  intro a b h
  apply Subtype.ext
  have hp := congrArg Nat.Partition.parts h
  exact (Multiset.coe_eq_coe.mp hp).eq_of_pairwise'
    (sound n n n a.val a.property).2.1 (sound n n n b.val b.property).2.1

private def enumPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  ⟨↑((listPartitions n n n).attach.map (asPartition n)), by
    exact ((enumeration_nodup n n n).attach.map (asPartition_injective n))⟩

private theorem enum_complete (n : ℕ) (p : Nat.Partition n) : p ∈ enumPartitions n := by
  let q := p.parts.sort (· ≥ ·)
  have hcoe : (q : Multiset ℕ) = p.parts := Multiset.sort_eq _ _
  have hsum : (q : Multiset ℕ).sum = n := hcoe ▸ p.parts_sum
  have hpos : ∀ a ∈ q, 0 < a := by
    intro a ha
    exact p.parts_pos ((Multiset.mem_sort _).mp ha)
  have hlen : q.length ≤ n := by
    have := List.length_le_sum_of_one_le q (fun a ha => hpos a ha)
    simpa only [← Multiset.sum_coe, hsum] using this
  have hmem : q ∈ listPartitions n n n := complete n n n q hlen
    (by simpa using hsum) (Multiset.pairwise_sort _ _) hpos (by
      intro a ha
      exact p.le_of_mem_parts ((Multiset.mem_sort _).mp ha))
  change p ∈ ((listPartitions n n n).attach.map (asPartition n))
  apply List.mem_map.mpr
  refine ⟨⟨q, hmem⟩, List.mem_attach _ _, ?_⟩
  exact Nat.Partition.ext hcoe

/-- The full multiset of parts in weakly decreasing order. -/
def decreasingParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

/-- The number of one-based indices whose part exceeds the index. -/
def excedances {n : ℕ} (p : Nat.Partition n) : ℕ :=
  (Finset.univ.filter (fun i : Fin (decreasingParts p).length =>
    (decreasingParts p).get i > i.val + 1)).card

/-- The cardinality of all actual partitions with even excedance count. -/
noncomputable def evenCount (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {p : Nat.Partition n // Even (excedances p)}

/-- The cardinality of all actual partitions with odd excedance count. -/
noncomputable def oddCount (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {p : Nat.Partition n // Odd (excedances p)}

/-- The original all-n strict even-minus-odd positivity assertion. -/
def claim : Prop := ∀ n : ℕ, 12 ≤ n → evenCount n > oddCount n

private theorem evenCount_enum (n : ℕ) :
    evenCount n = ((enumPartitions n).filter (fun p => Even (excedances p))).card := by
  unfold evenCount
  exact Fintype.card_of_finset' (p := {p : Nat.Partition n | Even (excedances p)})
    _ (fun p => by simp only [Finset.mem_filter, Set.mem_ofPred_eq]; exact and_iff_right (enum_complete n p))

private theorem oddCount_enum (n : ℕ) :
    oddCount n = ((enumPartitions n).filter (fun p => Odd (excedances p))).card := by
  unfold oddCount
  exact Fintype.card_of_finset' (p := {p : Nat.Partition n | Odd (excedances p)})
    _ (fun p => by simp only [Finset.mem_filter, Set.mem_ofPred_eq]; exact and_iff_right (enum_complete n p))

private def rawExcedances (q : List ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin q.length => q.get i > i.val + 1)).card

private theorem excedances_asPartition (n : ℕ)
    (q : {q // q ∈ listPartitions n n n}) :
    excedances (asPartition n q) = rawExcedances q.val := by
  have hs : decreasingParts (asPartition n q) = q.val :=
    List.mergeSort_eq_self _ (sound n n n q.val q.property).2.1
  change rawExcedances (decreasingParts (asPartition n q)) = rawExcedances q.val
  exact congrArg rawExcedances hs

private theorem filter_enum (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((enumPartitions n).filter (fun p => P (excedances p))).card =
      ((listPartitions n n n).filter (fun q => P (rawExcedances q))).length := by
  change (((listPartitions n n n).attach.map (asPartition n)).filter
    (fun p => decide (P (excedances p)))).length = _
  rw [List.filter_map, List.length_map]
  conv_rhs => rw [← List.attach_map_subtype_val (listPartitions n n n)]
  rw [List.filter_map, List.length_map]
  congr 2
  funext q
  simp only [Function.comp_apply, excedances_asPartition]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem actual_counts28 : evenCount 28 = 1850 ∧ oddCount 28 = 1868 := by
  rw [evenCount_enum, oddCount_enum, filter_enum, filter_enum]
  decide

/-- The original universal assertion fails at n = 28. -/
theorem result : ¬ claim := by
  intro h
  have h28 := h 28 (by decide)
  rw [actual_counts28.1, actual_counts28.2] at h28
  exact (by decide : ¬ (1850 > 1868)) h28

end D5.S3.Combinatorics.Partitions.AndrewsHopkinsExcedanceParityRefutation

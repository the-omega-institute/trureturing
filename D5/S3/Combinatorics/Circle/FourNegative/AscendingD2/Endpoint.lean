/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Endpoint
   mirror-E: none(waiver:source-equivalence-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical permutation and a fresh first ear for every independent two-at-most-a-less-b-less-c gap tuple. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

/-! The complete strict ascending d=2 chamber; unrestricted J and C3.1 remain open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn
  Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn paired_table
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
open private shiftedSupport shifted_good shifted_sum table_positive four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private Choice Choice.p Choice.q Choice.r Choice.pq Choice.pr Choice.qr Choice.good coeff
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private Coeff oldMass newMass margins from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option maxHeartbeats 1600000 in
private theorem realize (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (choice : Choice a b c (2 ^ a) (2 ^ b) (2 ^ c)) :
    ∃ sigma : List (Fin (a + b + c + 2)),
      OriginalOrder (a + b + c + 2) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧
      OriginalOrder (a + b + c + 2 + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + 2) sigma 0) := by
  classical
  let R : ℤ := 2 ^ a
  let T : ℤ := 2 ^ b
  let Z : ℤ := 2 ^ c
  let k := a + b + c + 2
  let t : ℕ := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
  let A : ℤ := t
  let N := modulus k
  let M := modulus (k + 1)
  let C := 2 * R * T * Z - 1
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * t)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * (t : ℤ)))
  let P := shiftedSupport a b c (Choice.p choice)
  let Q := shiftedSupport a b c (Choice.q choice)
  let S := shiftedSupport a b c (Choice.r choice)
  let G := Finset.range k \ (P ∪ Q ∪ S ∪ {a + b + c + 1, c + b + 1, c + 1, 1})
  let word := P.toList ++ (a + b + c + 1) :: Q.toList ++ (c + b + 1) :: S.toList ++ (c + 1) :: G.toList ++ [1]
  have hA : A = 1 + R + R * T + R * T * Z := by dsimp [A, t, R, T, Z]; push_cast; simp only [pow_add]
  have hN : N = 4 * R * T * Z - 1 := by dsimp [N, modulus, k, R, T, Z]; simp only [pow_add] <;> ring
  have hNC : N = 2 * C + 1 := by rw [hN]; dsimp [C]; ring
  have hM : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  have hhalf : N/2 = C := by omega
  have hmhalf : M/2 = N := by omega
  have tab : Table a b c R T Z f g := by
    have h := paired_table a b c ha hb hc
    dsimp only at h
    have ht : (t : ℤ) = 1 + (2 : ℤ) ^ a + 2 ^ (a + b) + 2 ^ (a + b + c) := by simp only [t, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    simpa only [f, g, N, M, k, ht, R, T, Z] using h
  have hR : 0 < R := by dsimp [R]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have Pgood := shifted_good a b c ha hb hc (Choice.p choice)
  have Qgood := shifted_good a b c ha hb hc (Choice.q choice)
  have Sgood := shifted_good a b c ha hb hc (Choice.r choice)
  have hp : word.Perm (List.range k) :=
    four_perm k (a + b + c + 1) (c + b + 1) (c + 1) 1 P Q S Pgood Qgood Sgood
      (Choice.pq choice) (Choice.pr choice) (Choice.qr choice) (by simp; omega) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl|rfl|rfl|rfl <;> dsimp [k] <;> omega)
  have Ggood (i : ℕ) (hi : i ∈ G) :
      i < k ∧ i ≠ a + b + c + 1 ∧ i ≠ c + b + 1 ∧ i ≠ c + 1 ∧ i ≠ 1 := by
    have h := Finset.mem_sdiff.mp hi
    refine ⟨Finset.mem_range.mp h.1, ?_, ?_, ?_, ?_⟩
    all_goals intro heq; apply h.2; simp only [heq, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, or_true, true_or]

  have posP (i : ℕ) (hi : i ∈ P.toList) : 0 ≤ f i ∧ 0 ≤ g i :=
    table_positive a b c R T Z f g hR hT hZ tab i (Pgood i (Finset.mem_toList.mp hi))
  have posQ (i : ℕ) (hi : i ∈ Q.toList) : 0 ≤ f i ∧ 0 ≤ g i :=
    table_positive a b c R T Z f g hR hT hZ tab i (Qgood i (Finset.mem_toList.mp hi))
  have posS (i : ℕ) (hi : i ∈ S.toList) : 0 ≤ f i ∧ 0 ≤ g i :=
    table_positive a b c R T Z f g hR hT hZ tab i (Sgood i (Finset.mem_toList.mp hi))
  have posG (i : ℕ) (hi : i ∈ G.toList) : 0 ≤ f i ∧ 0 ≤ g i :=
    table_positive a b c R T Z f g hR hT hZ tab i (Ggood i (Finset.mem_toList.mp hi))
  have pf : (P.toList.map f).sum = oldMass R T Z (coeff a b c (Choice.p choice)) :=
    shifted_sum a b c (Choice.p choice) f _ _ _ (Table.v tab) (Table.w tab) (Table.x tab)
  have qf : (Q.toList.map f).sum = oldMass R T Z (coeff a b c (Choice.q choice)) :=
    shifted_sum a b c (Choice.q choice) f _ _ _ (Table.v tab) (Table.w tab) (Table.x tab)
  have sf : (S.toList.map f).sum = oldMass R T Z (coeff a b c (Choice.r choice)) :=
    shifted_sum a b c (Choice.r choice) f _ _ _ (Table.v tab) (Table.w tab) (Table.x tab)
  have pg : (P.toList.map g).sum = newMass R T Z (coeff a b c (Choice.p choice)) :=
    shifted_sum a b c (Choice.p choice) g _ _ _ (Table.vn tab) (Table.wn tab) (Table.xn tab)
  have qg : (Q.toList.map g).sum = newMass R T Z (coeff a b c (Choice.q choice)) :=
    shifted_sum a b c (Choice.q choice) g _ _ _ (Table.vn tab) (Table.wn tab) (Table.xn tab)
  have sg : (S.toList.map g).sum = newMass R T Z (coeff a b c (Choice.r choice)) :=
    shifted_sum a b c (Choice.r choice) g _ _ _ (Table.vn tab) (Table.wn tab) (Table.xn tab)
  have good := (Choice.good choice)
  change margins R T Z (coeff a b c (Choice.p choice)) (coeff a b c (Choice.q choice)) (coeff a b c (Choice.r choice)) at good
  dsimp only [margins] at good
  rw [←hA, ←pf, ←qf, ←sf, ←pg, ←qg, ←sg, ←(Table.nx tab), ←(Table.nw tab), ←(Table.nv tab), ←(Table.nu tab),
    ←(Table.nxn tab), ←(Table.nwn tab), ←(Table.nvn tab), ←(Table.nun tab)] at good
  rw [←hN] at good
  change 0 ≤ A ∧ A ≤ N ∧ _ at good
  obtain ⟨hA0, hAN, h1, h2, h3, h4, h5, h6, h7, h8, j1, j2, j3, j4, j5, j6, j7, j8⟩ := good
  have hz : ((List.range k).map f).sum = 0 := by
    exact ThreeNegativeEqualOuterSourceBridge.source_zero k t (by dsimp [k]; omega)
  have hword0 : (word.map f).sum = 0 := (hp.map f).sum_eq.trans hz
  have hplus : (k :: word).Perm (List.range (k + 1)) := by
    apply Multiset.coe_eq_coe.mp
    rw [List.range_succ]
    change {k} + (word : Multiset ℕ) = (List.range k : Multiset ℕ) + {k}
    rw [Multiset.coe_eq_coe.mpr hp]; ac_rfl
  have hzg : ((List.range (k + 1)).map g).sum = 0 := by
    have h := ThreeNegativeEqualOuterSourceBridge.source_zero (k + 1) (2 * t) (by dsimp [k]; omega)
    simpa only [g, M, Nat.cast_mul, Nat.cast_ofNat] using h
  have hear : g k = A := by
    dsimp [g]
    rw [show (2 : ℤ) ^ k * (2 * (t : ℤ)) = 2 ^ (k + 1) * t by rw [pow_succ]; ring,
      centered_full_period (k + 1) t]
    change centered M A = A
    unfold centered
    rw [hmhalf, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have hwordg : A + (word.map g).sum = 0 := by
    have h := (hplus.map g).sum_eq.trans hzg
    simpa only [List.map_cons, List.sum_cons, hear] using h
  have hsOld : InStrip f C 0 word := by
    apply four_strip f P.toList Q.toList S.toList G.toList (a + b + c + 1) (c + b + 1) (c + 1) 1 C 0
      (fun i hi => (posP i hi).1) (fun i hi => (posQ i hi).1)
      (fun i hi => (posS i hi).1) (fun i hi => (posG i hi).1) (by omega)
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · simpa only [zero_add] using hword0
  have hsNew : InStrip g N A word := by
    apply four_strip g P.toList Q.toList S.toList G.toList (a + b + c + 1) (c + b + 1) (c + 1) 1 N A
      (fun i hi => (posP i hi).2) (fun i hi => (posQ i hi).2)
      (fun i hi => (posS i hi).2) (fun i hi => (posG i hi).2) hA0
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · exact hwordg
  refine ⟨word.map (label k (by dsimp [k]; omega)), ?_, ?_⟩
  · apply lift_order k t (by dsimp [k]; omega) word hp
    · simpa only [N, hhalf] using hsOld
    · exact hz
  · have he := marked_word k 0 (by dsimp [k]; omega) [] word rfl hp
    simp only [List.nil_append] at he
    rw [he]
    apply lift_order (k + 1) (2 * t) (by dsimp [k]; omega) (k :: word) hplus
    · change InStrip g (M/2) 0 (k :: word)
      rw [hmhalf]
      change 0 ≤ (0 : ℤ) ∧ 0 ≤ N ∧ InStrip g N (0 + g k) word
      rw [hear, zero_add]
      exact ⟨le_rfl, by omega, hsNew⟩
    · simpa only [g, M, Nat.cast_mul, Nat.cast_ofNat] using hzg

open SourceWidth PeriodicShortening RunFirstEarTransport
open private large_choice small_choice tail_choice from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

private theorem finite_order (k t : ℕ) (word : List (Fin k))
    (hp : word.Perm (List.finRange k)) (hz : (word.map (actualSource k t)).sum = 0)
    (hs : ∀ n : Fin (k + 1), ((word.take n.val).map (actualSource k t)).sum ∈
      Set.Icc (0 : ℤ) (modulus k/2)) : OriginalOrder k t word := by
  refine ⟨hp, hz, ?_⟩
  intro n
  have hl : word.length = k := by have := hp.length_eq; simpa using this
  by_cases hn : n ≤ k
  · exact hs ⟨n, by omega⟩
  · rw [List.take_of_length_le (by omega), hz]
    have h := hs ⟨0, by omega⟩
    simpa using h

/-- Every independent 2≤a<b<c has a complete literal physical first-ear joint order.
Both complete integer totals vanish and both orders include every natural take-prefix. -/
theorem actualSource_strict_ascending_d2_joint_lift (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a < b) (hbc : b < c) :
    ∃ sigma : List (Fin (a + b + c + 2)),
      OriginalOrder (a + b + c + 2) (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) sigma ∧
      OriginalOrder (a + b + c + 2 + 1) (2 * (1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)))
        (earWord (a + b + c + 2) sigma 0) := by
  by_cases ha4 : 4 ≤ a
  · exact realize a b c ha (by omega) (by omega) (large_choice a b c ha4 hab hbc)
  by_cases hb4 : 4 ≤ b
  · exact realize a b c ha (by omega) (by omega)
      (small_choice a b c (by omega) hb4 hbc)
  have ha2 : a = 2 := by omega
  have hb3 : b = 3 := by omega
  subst a b
  by_cases hc7 : 7 ≤ c
  · exact realize 2 3 c (by decide) (by decide) (by omega) (tail_choice c hc7)
  have hc : c = 4 ∨ c = 5 ∨ c = 6 := by omega
  rcases hc with rfl|rfl|rfl
  · refine ⟨[9, 2, 8, 7, 10, 4, 6, 5, 0, 3, 1], ?_, ?_⟩
    all_goals apply finite_order <;> decide
  · refine ⟨[8, 2, 9, 10, 3, 11, 5, 7, 6, 0, 4, 1], ?_, ?_⟩
    all_goals apply finite_order <;> decide
  · refine ⟨[9, 3, 10, 11, 4, 12, 6, 8, 7, 0, 5, 2, 1], ?_, ?_⟩
    all_goals apply finite_order <;> decide

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2

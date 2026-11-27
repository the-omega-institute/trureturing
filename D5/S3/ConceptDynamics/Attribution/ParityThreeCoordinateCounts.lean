/- GID: D5/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityThreeCoordinateCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp integer constraints on three simultaneous coordinate fixed counts. -/

import D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
import D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum
import D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Sign

/-! Integer orbit tables and their sharp three-coordinate fixed-count bounds. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts

open Finset MulAction

open CoordinateFlagCoupling
open ParitySeedBudget

open ParitySeedOptimization ParityThreeOrbitTable

private theorem odd_sum_forces_fixed {k a b f g : ℕ}
    (hSum : a + b = k) (odd : k % 2 = 1)
    (hF : f % 2 = a % 2) (hG : g % 2 = b % 2) :
    1 ≤ f + g := by
  by_cases hf : f = 0
  · by_cases hg : g = 0
    · have aa : a % 2 = 0 := hF.symm.trans (by simp [hf])
      have bb : b % 2 = 0 := hG.symm.trans (by simp [hg])
      have evenK : k % 2 = 0 := by rw [← hSum, Nat.add_mod, aa, bb]
      exact (Nat.zero_ne_one (evenK.symm.trans odd)).elim
    · omega
  · omega

private theorem odd_from_other_even {k a b c d : ℕ}
    (sum : a + b + c + d = k) (odd : k % 2 = 1)
    (evenB : b % 2 = 0) (evenC : c % 2 = 0) (evenD : d % 2 = 0) :
    1 ≤ a := by
  by_cases ha : a = 0
  · have evenK : k % 2 = 0 := by
      rw [← sum, Nat.add_mod _ d, Nat.add_mod _ c, Nat.add_mod _ b, ha, evenB, evenC, evenD]
    exact (Nat.zero_ne_one (evenK.symm.trans odd)).elim
  · exact Nat.pos_of_ne_zero ha

private theorem odd_coordinate_cut (k u v w : ℕ)
    (A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ x₀ x₁ y z C D F₂ F₃ G₂ G₃ : ℕ)
    (odd : k % 2 = 1)
    (colA : A₀ + A₁ + A₂ + A₃ = k) (colB : B₀ + B₁ + B₂ + B₃ = k)
    (row : A₁ + B₁ + 2 * x₁ + 2 * (y + z) = 2 * k)
    (iCap : 2 * u + A₀ + B₀ + A₁ + B₁ + 2 * x₀ + 2 * x₁ ≤ 4 * k)
    (otherCap : 2 * C + 2 * D + F₂ + F₃ + G₂ + G₃ ≤ 2 * (v + w))
    (extra : A₁ % 2 ≤ 2 * (v + w) ∧ B₁ % 2 ≤ 2 * (v + w))
    (parityC : C % 2 = y % 2) (parityD : D % 2 = z % 2)
    (parityF₂ : F₂ % 2 = A₂ % 2) (parityF₃ : F₃ % 2 = A₃ % 2)
    (parityG₂ : G₂ % 2 = B₂ % 2) (parityG₃ : G₃ % 2 = B₃ % 2) :
    u ≤ v + w + 2 * (k - 1) := by
  by_contra notLe
  have bad := Nat.lt_of_not_ge notLe
  have posK : 0 < k := Nat.pos_of_ne_zero (fun h => by simp [h] at odd)
  by_cases max : u = 2 * k
  · have noCross : A₀ = 0 ∧ B₀ = 0 ∧ A₁ = 0 ∧ B₁ = 0 ∧ x₁ = 0 := by
      clear * - max iCap
      omega
    obtain ⟨a₀, b₀, a₁, b₁, hx⟩ := noCross
    have yz : y + z = k := by
      simpa [a₁, b₁, hx, Nat.mul_right_inj (by decide : 2 ≠ 0)] using row
    have ac : A₂ + A₃ = k := by simpa [a₀, a₁] using colA
    have bc : B₂ + B₃ = k := by simpa [b₀, b₁] using colB
    have hC := odd_sum_forces_fixed yz odd parityC parityD
    have hF := odd_sum_forces_fixed ac odd parityF₂ parityF₃
    have hG := odd_sum_forces_fixed bc odd parityG₂ parityG₃
    clear * - otherCap hC hF hG posK max bad
    omega
  · have ⟨near, hv, hw⟩ : u = 2 * k - 1 ∧ v = 0 ∧ w = 0 := by
      clear * - bad max iCap posK
      omega
    have ⟨hc, hd, hf₂, hf₃, hg₂, hg₃⟩ :
        C = 0 ∧ D = 0 ∧ F₂ = 0 ∧ F₃ = 0 ∧ G₂ = 0 ∧ G₃ = 0 := by
      clear * - otherCap hv hw
      omega
    have ⟨evenA, evenB⟩ : A₁ % 2 = 0 ∧ B₁ % 2 = 0 := by simpa [hv, hw] using extra
    have hA := odd_from_other_even colA odd evenA (by simpa [hf₂] using parityF₂.symm)
      (by simpa [hf₃] using parityF₃.symm)
    have hB := odd_from_other_even colB odd evenB (by simpa [hg₂] using parityG₂.symm)
      (by simpa [hg₃] using parityG₃.symm)
    have evenY : y % 2 = 0 := by simpa [hc] using parityC.symm
    have evenZ : z % 2 = 0 := by simpa [hd] using parityD.symm
    have notFull : y + z ≠ k := by
      intro sum
      have evenK : k % 2 = 0 := by rw [← sum, Nat.add_mod, evenY, evenZ]
      exact Nat.zero_ne_one (evenK.symm.trans odd)
    have hRow : 2 ≤ A₁ + B₁ + 2 * x₁ := by
      clear * - row notFull
      omega
    clear * - near iCap posK hA hB hRow
    omega

private theorem colour_sum_two (f : ZMod 2 → ℕ) : (∑ d, f d) = f 0 + f 1 := by
  have universe_eq : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [universe_eq, sum_insert (by decide : 0 ∉ ({1} : Finset (ZMod 2))), sum_singleton]

private theorem odd_table_coordinate_zero {k : ℕ} {u : Fin 3 → ℕ}
    (table : OrbitTable k (fun i => 4 * u i)) (odd : k % 2 = 1) :
    u 0 ≤ u 1 + u 2 + 2 * (k - 1) := by
  let o := table.ordinary
  let s := table.special
  let b := table.ordinaryFixed
  let d := table.specialFixed
  have colA := table.specialCols 0
  have colB := table.specialCols 1
  have colOrdinary := table.ordinaryCols 0
  have row := table.rows 1
  have totalZero := table.totals 0
  have totalOne := table.totals 1
  have totalTwo := table.totals 2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, colour_sum_two] at colA colB colOrdinary row
  norm_num [Fin.sum_univ_succ, colour_sum_two, leftWord, rightWord] at totalZero totalOne totalTwo
  have iCap : 2 * u 0 + s 0 0 + s 0 1 + s 1 0 + s 1 1 + 2 * o 0 0 + 2 * o 1 0 ≤ 4 * k := by
    have b₂ := table.ordinaryBounds 2 0 0
    have b₃ := table.ordinaryBounds 3 0 0
    have f₂ := table.specialBounds 2 0 0
    have f₃ := table.specialBounds 3 0 0
    have g₂ := table.specialBounds 2 1 0
    have g₃ := table.specialBounds 3 1 0
    dsimp [o, s] at *
    omega
  have otherCap :
      2 * b 1 1 1 + 2 * b 1 2 2 + d 2 0 2 + d 3 0 1 + d 2 1 2 + d 3 1 1 ≤
        2 * (u 1 + u 2) := by
    dsimp [b, d] at *
    omega
  have extraA : s 1 0 % 2 ≤ 2 * (u 1 + u 2) := by
    have h := table.specialParity 1 0 1
    dsimp [s] at *
    omega
  have extraB : s 1 1 % 2 ≤ 2 * (u 1 + u 2) := by
    have h := table.specialParity 1 1 1
    dsimp [s] at *
    omega
  apply odd_coordinate_cut k (u 0) (u 1) (u 2)
    (s 0 0) (s 1 0) (s 2 0) (s 3 0) (s 0 1) (s 1 1) (s 2 1) (s 3 1)
    (o 0 0) (o 1 0) (o 1 1) (o 1 2) (b 1 1 1) (b 1 2 2)
    (d 2 0 2) (d 3 0 1) (d 2 1 2) (d 3 1 1)
    odd _ _ _ iCap otherCap ⟨extraA, extraB⟩
    (table.ordinaryParity 1 1 1) (table.ordinaryParity 1 2 2)
    (table.specialParity 2 0 2) (table.specialParity 3 0 1)
    (table.specialParity 2 1 2) (table.specialParity 3 1 1)
  all_goals clear * - colA colB row o s
  all_goals dsimp [s, o] at *
  all_goals omega

private theorem swapped_left_bit (a c i : Fin 3) (p : Fin 4) :
    leftWord (Equiv.swap a.succ c.succ p) (Equiv.swap a c i) = leftWord p i :=
  (by decide : ∀ (a c i : Fin 3) (p : Fin 4),
    leftWord (Equiv.swap a.succ c.succ p) (Equiv.swap a c i) = leftWord p i) a c i p

private theorem swapped_right_bit (a c i j : Fin 3) :
    rightWord (Equiv.swap a c j).succ (Equiv.swap a c i) = rightWord j.succ i :=
  (by decide : ∀ (a c i j : Fin 3),
    rightWord (Equiv.swap a c j).succ (Equiv.swap a c i) = rightWord j.succ i) a c i j

private def swap_coordinates {k : ℕ} {z : Fin 3 → ℕ} (table : OrbitTable k z) (a c : Fin 3) :
    OrbitTable k (fun i => z (Equiv.swap a c i)) := by
  let P := Equiv.swap a.succ c.succ
  let Q := Equiv.swap a c
  refine ⟨fun p j => table.ordinary (P p) (Q j), fun p d => table.special (P p) d,
    fun p j i => table.ordinaryFixed (P p) (Q j) (Q i), fun p d i => table.specialFixed (P p) d (Q i),
    ?_, ?_, ?_,
    fun p j i => table.ordinaryBounds (P p) (Q j) (Q i),
    fun p j i => table.ordinaryParity (P p) (Q j) (Q i),
    fun p d i => table.specialBounds (P p) d (Q i),
    fun p d i => table.specialParity (P p) d (Q i), ?_⟩
  · intro p
    rw [Equiv.sum_comp Q (table.ordinary (P p)), table.rows]
  · intro j
    rw [Equiv.sum_comp P (fun p => table.ordinary p (Q j)), table.ordinaryCols]
  · intro d
    rw [Equiv.sum_comp P (fun p => table.special p d), table.specialCols]
  · intro i
    have ordinary :
      (∑ p : Fin 4, ∑ j : Fin 3, if leftWord p i && rightWord j.succ i then
        table.ordinaryFixed (P p) (Q j) (Q i) else 0) =
      ∑ p : Fin 4, ∑ j : Fin 3, if leftWord p (Q i) && rightWord j.succ (Q i) then
        table.ordinaryFixed p j (Q i) else 0 := by
      rw [← Equiv.sum_comp P (fun p : Fin 4 => ∑ j : Fin 3, if leftWord p (Q i) &&
        rightWord j.succ (Q i) then table.ordinaryFixed p j (Q i) else 0)]
      apply sum_congr rfl
      intro p _
      rw [← Equiv.sum_comp Q (fun j : Fin 3 => if leftWord (P p) (Q i) &&
        rightWord j.succ (Q i) then table.ordinaryFixed (P p) j (Q i) else 0)]
      apply sum_congr rfl
      intro j _
      simp only [P, Q, swapped_left_bit, swapped_right_bit]
    have special :
      (∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p i then table.specialFixed (P p) d (Q i) else 0) =
      ∑ p : Fin 4, ∑ d : ZMod 2, if leftWord p (Q i) then table.specialFixed p d (Q i) else 0 := by
      rw [← Equiv.sum_comp P (fun p : Fin 4 => ∑ d : ZMod 2,
        if leftWord p (Q i) then table.specialFixed p d (Q i) else 0)]
      apply sum_congr rfl
      intro p _
      simp only [P, Q, swapped_left_bit]
    rw [ordinary, special]
    exact table.totals (Q i)

private structure BudgetTwoCoupling where
  firstMatch : Fin 4 → Fin 4
  secondMatch : Fin 4 → Fin 4
  specialFirstColour : Fin 4 → ℕ

private def BudgetTwoCoupling.pooled (c : BudgetTwoCoupling) (p q : Fin 4) : ℕ :=
  (if c.firstMatch p = q then 1 else 0) + (if c.secondMatch p = q then 1 else 0)

private def BudgetTwoCoupling.special (c : BudgetTwoCoupling) (p : Fin 4) (colour : Fin 2) : ℕ :=
  if colour = 0 then c.specialFirstColour p else 2 * c.pooled p 0 - c.specialFirstColour p

private def BudgetTwoCoupling.valid (c : BudgetTwoCoupling) : Bool :=
  decide (∀ p, ∑ q, c.pooled p q = 2) &&
  decide (∀ q, ∑ p, c.pooled p q = 2) &&
  decide (∀ p, c.specialFirstColour p ≤ 2 * c.pooled p 0) &&
  decide (∀ colour, ∑ p, c.special p colour = 2)

private def budgetTwoCouplings : Fin 4 → BudgetTwoCoupling :=
  ![⟨![1, 0, 3, 2], ![1, 3, 0, 2], ![0, 0, 2, 0]⟩,
    ⟨![2, 0, 3, 1], ![2, 0, 3, 1], ![0, 2, 0, 0]⟩,
    ⟨![1, 2, 3, 0], ![2, 0, 3, 1], ![0, 0, 0, 2]⟩,
    ⟨![1, 0, 3, 2], ![1, 0, 3, 2], ![0, 2, 0, 0]⟩]

private abbrev Cell := Fin 4 × (Fin 3 ⊕ Fin 2)

private def cells : List Cell :=
  (List.finRange 4).flatMap fun p =>
    (List.finRange 3).map (fun j => (p, Sum.inl j)) ++
      (List.finRange 2).map (fun d => (p, Sum.inr d))

private def BudgetTwoCoupling.multiplicity (c : BudgetTwoCoupling) : Cell → ℕ
  | (p, .inl j) => c.pooled p j.succ
  | (p, .inr d) => c.special p d

private def BudgetTwoCoupling.fixed (c : BudgetTwoCoupling) (mask : ℕ) (cell : Cell) : ℕ :=
  if c.multiplicity cell = 2 ∧ mask.testBit ((cells.filter fun a => c.multiplicity a = 2).idxOf cell) then
    2
  else
    c.multiplicity cell % 2

private theorem fixed_law (c : BudgetTwoCoupling) (mask : ℕ) (cell : Cell) :
    c.fixed mask cell ≤ c.multiplicity cell ∧
      c.fixed mask cell % 2 = c.multiplicity cell % 2 := by
  unfold BudgetTwoCoupling.fixed
  split
  · rename_i h
    simp [h.1]
  · omega

private def BudgetTwoCoupling.total (c : BudgetTwoCoupling) (i : Fin 3) (mask : ℕ) : ℕ :=
  4 * (∑ p : Fin 4, ∑ j : Fin 3, if leftWord p i && rightWord j.succ i then
    c.fixed mask (p, .inl j) else 0) +
  2 * (∑ p : Fin 4, ∑ d : Fin 2, if leftWord p i then c.fixed mask (p, .inr d) else 0)

private def baseCount : Fin 4 → Fin 3 → ℕ :=
  ![![0, 0, 2], ![0, 0, 0], ![1, 1, 0], ![0, 0, 0]]

private def ordinaryBit : Fin 4 → Fin 3 → ℕ :=
  ![![0, 8, 0], ![16, 0, 8], ![0, 0, 2], ![0, 16, 8]]

private def firstSpecialBit : Fin 4 → Fin 3 → ℕ :=
  ![![4, 2, 2], ![0, 2, 2], ![4, 1, 1], ![0, 2, 2]]

private def secondSpecialBit : Fin 4 → Fin 3 → ℕ :=
  ![![0, 0, 4], ![0, 4, 4], ![0, 4, 0], ![0, 4, 4]]

private def selectedMask (r : Fin 4) (i : Fin 3) (a b c : Bool) : ℕ :=
  (if a then ordinaryBit r i else 0) +
    (if b then firstSpecialBit r i else 0) + (if c then secondSpecialBit r i else 0)

private theorem selected_total (r : Fin 4) (i : Fin 3) (a b c : Bool) :
    (budgetTwoCouplings r).total i (selectedMask r i a b c) =
      4 * (baseCount r i + (if a = true ∧ (ordinaryBit r i ≠ 0) then 2 else 0) +
        (if b = true ∧ (firstSpecialBit r i ≠ 0) then 1 else 0) +
        (if c = true ∧ (secondSpecialBit r i ≠ 0) then 1 else 0)) := by
  fin_cases r <;> fin_cases i <;> cases a <;> cases b <;> cases c <;> rfl

private def SelectionCondition (r : Fin 4) (i : Fin 3) (u : ℕ) : Prop :=
  ∃ a b c : Bool, u = baseCount r i + (if a = true ∧ (ordinaryBit r i ≠ 0) then 2 else 0) +
    (if b = true ∧ (firstSpecialBit r i ≠ 0) then 1 else 0) +
    (if c = true ∧ (secondSpecialBit r i ≠ 0) then 1 else 0)

private theorem select_no_ordinary (r : Fin 4) (i : Fin 3) (u : ℕ)
    (lower : baseCount r i ≤ u)
    (upper : u ≤ baseCount r i + (if firstSpecialBit r i ≠ 0 then 1 else 0) +
      (if secondSpecialBit r i ≠ 0 then 1 else 0)) :
    ∃ b c : Bool, u = baseCount r i + (if b = true ∧ (firstSpecialBit r i ≠ 0) then 1 else 0) +
      (if c = true ∧ (secondSpecialBit r i ≠ 0) then 1 else 0) := by
  let m := baseCount r i
  by_cases first : firstSpecialBit r i ≠ 0
  · by_cases second : secondSpecialBit r i ≠ 0
    · refine ⟨decide (m < u), decide (m + 1 < u), ?_⟩
      simp [first, second] at upper ⊢
      split <;> split <;> omega
    · refine ⟨decide (m < u), false, ?_⟩
      simp [first, second] at upper ⊢
      split <;> omega
  · refine ⟨false, decide (m < u), ?_⟩
    by_cases second : secondSpecialBit r i ≠ 0
    · simp [first, second] at upper ⊢
      split <;> omega
    · simp [first, second] at upper ⊢
      omega

private theorem select_range (r : Fin 4) (i : Fin 3) (u : ℕ)
    (lower : baseCount r i ≤ u)
    (upper : u ≤ baseCount r i + (if ordinaryBit r i ≠ 0 then 2 else 0) +
      (if firstSpecialBit r i ≠ 0 then 1 else 0) +
      (if secondSpecialBit r i ≠ 0 then 1 else 0))
    (middle : ordinaryBit r i ≠ 0 → u = baseCount r i + 1 →
      firstSpecialBit r i ≠ 0 ∨ secondSpecialBit r i ≠ 0) : SelectionCondition r i u := by
  by_cases ho : ordinaryBit r i ≠ 0
  · by_cases atLeastTwo : baseCount r i + 2 ≤ u
    · obtain ⟨b, c, h⟩ := select_no_ordinary r i (u - 2) (by omega)
        (by rw [ite_eq_left ho] at upper; omega)
      refine ⟨true, b, c, ?_⟩
      have ordinary : (true = true ∧ ordinaryBit r i ≠ 0) := ⟨rfl, ho⟩
      rw [ite_eq_left ordinary]
      omega
    · by_cases exactBase : u = baseCount r i
      · exact ⟨false, false, false, by simpa using exactBase⟩
      · have next : u = baseCount r i + 1 := by omega
        rcases middle ho next with first | second
        · exact ⟨false, true, false, by simpa [first] using next⟩
        · exact ⟨false, false, true, by simpa [second] using next⟩
  · obtain ⟨b, c, eq⟩ := select_no_ordinary r i u lower (by simpa [ho] using upper)
    exact ⟨false, b, c, by simpa using eq⟩

private theorem select_coupling (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4) (xy : u 0 ≤ u 1) (yz : u 1 ≤ u 2)
    (cap : u 0 + u 1 + u 2 ≤ 8) :
    ∃ r : Fin 4, ∀ i, SelectionCondition r i (u i) := by
  have hz := bounds 2
  have hy := bounds 1
  have hx : u 0 ≤ 2 := by omega
  by_cases xZero : u 0 = 0
  · refine ⟨3, fun i => select_range 3 i (u i) ?_ ?_ ?_⟩
    all_goals
      fin_cases i <;> norm_num [baseCount, ordinaryBit, firstSpecialBit, secondSpecialBit] <;> omega
  · by_cases xOne : u 0 = 1
    · by_cases zSmall : u 2 ≤ 3
      · refine ⟨2, fun i => select_range 2 i (u i) ?_ ?_ ?_⟩
        all_goals
          fin_cases i <;> norm_num [baseCount, ordinaryBit, firstSpecialBit, secondSpecialBit] <;> omega
      · refine ⟨0, fun i => select_range 0 i (u i) ?_ ?_ ?_⟩
        all_goals
          fin_cases i <;> norm_num [baseCount, ordinaryBit, firstSpecialBit, secondSpecialBit] <;> omega
    · have xTwo : u 0 = 2 := by omega
      by_cases ySmall : u 1 ≤ 2
      · refine ⟨1, fun i => select_range 1 i (u i) ?_ ?_ ?_⟩
        all_goals
          fin_cases i <;> norm_num [baseCount, ordinaryBit, firstSpecialBit, secondSpecialBit] <;> omega
      · refine ⟨2, fun i => select_range 2 i (u i) ?_ ?_ ?_⟩
        all_goals
          fin_cases i <;> norm_num [baseCount, ordinaryBit, firstSpecialBit, secondSpecialBit] <;> omega

private theorem table_at_budget_two (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4) (order₁ : u 0 ≤ u 1) (order₂ : u 1 ≤ u 2)
    (cap : u 0 + u 1 + u 2 ≤ 8) : Nonempty (OrbitTable 2 (fun i => 4 * u i)) := by
  obtain ⟨r, choices⟩ := select_coupling u bounds order₁ order₂ cap
  let coupling := budgetTwoCouplings r
  have valid : coupling.valid = true := by
    fin_cases r <;> rfl
  have masks (i : Fin 3) : ∃ mask : ℕ, coupling.total i mask = 4 * u i := by
    obtain ⟨a, b, c, chosen⟩ := choices i
    exact ⟨selectedMask r i a b c, (selected_total r i a b c).trans (congrArg (4 * ·) chosen.symm)⟩
  choose mask total using masks
  unfold BudgetTwoCoupling.valid at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨rows, cols⟩, specialBound⟩, specialCols⟩ := valid
  let colour := (ZMod.finEquiv 2).toEquiv
  let o (p : Fin 4) (j : Fin 3) := coupling.multiplicity (p, .inl j)
  let s (p : Fin 4) (d : ZMod 2) := coupling.multiplicity (p, .inr (colour.symm d))
  let b (p : Fin 4) (j i : Fin 3) := coupling.fixed (mask i) (p, .inl j)
  let a (p : Fin 4) (d : ZMod 2) (i : Fin 3) := coupling.fixed (mask i) (p, .inr (colour.symm d))
  refine ⟨⟨o, s, b, a, ?_, fun j => cols j.succ, fun d => specialCols (colour.symm d),
    fun p j i => (fixed_law coupling _ (p, .inl j)).1,
    fun p j i => (fixed_law coupling _ (p, .inl j)).2,
    fun p d i => (fixed_law coupling _ (p, .inr (colour.symm d))).1,
    fun p d i => (fixed_law coupling _ (p, .inr (colour.symm d))).2, ?_⟩⟩
  · intro p
    have left := rows p
    rw [Fin.sum_univ_succ] at left
    have colourSum : (∑ d : ZMod 2, s p d) = 2 * coupling.pooled p 0 := by
      rw [← Equiv.sum_comp colour (s p)]
      simp only [s, Equiv.symm_apply_apply]
      rw [Fin.sum_univ_two]
      simp only [BudgetTwoCoupling.multiplicity, BudgetTwoCoupling.special,
        show (1 : Fin 2) ≠ 0 by decide, ite_false]
      exact Nat.add_sub_of_le (specialBound p)
    rw [colourSum]
    change 2 * coupling.pooled p 0 + 2 * (∑ j : Fin 3, coupling.pooled p j.succ) = _
    omega
  · intro i
    have read := total i
    unfold BudgetTwoCoupling.total at read
    simp only [b]
    have colourSum (p : Fin 4) :
        (∑ d : ZMod 2, if leftWord p i then a p d i else 0) =
          ∑ d : Fin 2, if leftWord p i then coupling.fixed (mask i) (p, Sum.inr d) else 0 := by
      rw [← Equiv.sum_comp colour (fun d : ZMod 2 => if leftWord p i then a p d i else 0)]
      simp only [a, Equiv.symm_apply_apply]
    simp_rw [colourSum]
    exact read.symm

private theorem table_permute {k : ℕ} {z : Fin 3 → ℕ} (table : Nonempty (OrbitTable k z))
    (σ : Equiv.Perm (Fin 3)) : Nonempty (OrbitTable k (z ∘ σ)) := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => exact table
  | mul_swap σ a c distinct rest =>
    obtain ⟨T⟩ := rest
    exact ⟨swap_coordinates T a c⟩

private theorem table_at_budget_two_any_order (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4) (cap : ∑ i, u i ≤ 8) :
    Nonempty (OrbitTable 2 (fun i => 4 * u i)) := by
  let σ := Tuple.sort u
  have ordered := Tuple.monotone_sort u
  have total : (∑ i, u (σ i)) ≤ 8 := by
    rw [Equiv.sum_comp σ u]
    exact cap
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at total
  have numerals : u (σ 0) + u (σ 1) + u (σ 2) ≤ 8 := by
    simpa [add_assoc] using total
  have sorted := table_at_budget_two (u ∘ σ) (fun i => bounds (σ i))
    (ordered (by decide : (0 : Fin 3) ≤ 1)) (ordered (by decide : (1 : Fin 3) ≤ 2)) numerals
  simpa only [Function.comp_def, σ.apply_symm_apply] using table_permute sorted σ.symm

private theorem table_at_budget_one (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 2) (cap : u 0 + u 1 + u 2 ≤ 4)
    (t₀ : u 0 ≤ u 1 + u 2) (t₁ : u 1 ≤ u 0 + u 2) (t₂ : u 2 ≤ u 0 + u 1) :
    Nonempty (OrbitTable 1 (fun i => 4 * u i)) := by
  apply (exact_orbit_table 1 _).mp
  apply (D5.S3.ConceptDynamics.Attribution.ParityMinimumSeedSpectrum.exact_minimal_budget_fixed_counts
    1 (fun i => 4 * u i)).mpr
  refine ⟨fun i => 2 - u i, fun i => ?_, fun e even => ?_⟩
  · have hi := bounds i
    change 2 - u i ≤ 2 ∧ 4 * u i = 4 * (2 - (2 - u i))
    omega
  · obtain ⟨p, hp⟩ := leftProfile_bijective.surjective ⟨e, even⟩
    have profileEq : bitProfile (leftWord p) = e := congrArg Subtype.val hp
    have h0 := bounds 0
    have h1 := bounds 1
    have h2 := bounds 2
    subst e
    change 2 ≤ ∑ i, if bitProfile (leftWord p) i = 0 then 2 - u i else 2 - (2 - u i)
    fin_cases p <;> simp [leftWord, bitProfile, Fin.sum_univ_succ] <;> omega

private def zero_table : OrbitTable 0 (fun _ => 0) where
  ordinary _ _ := 0
  special _ _ := 0
  ordinaryFixed _ _ _ := 0
  specialFixed _ _ _ := 0
  rows := by simp
  ordinaryCols := by simp
  specialCols := by simp
  ordinaryBounds := by simp
  ordinaryParity := by simp
  specialBounds := by simp
  specialParity := by simp
  totals := by simp

private def add_tables {k l : ℕ} {z w : Fin 3 → ℕ}
    (A : OrbitTable k z) (B : OrbitTable l w) : OrbitTable (k + l) (fun i => z i + w i) := by
  refine ⟨fun p j => A.ordinary p j + B.ordinary p j,
    fun p d => A.special p d + B.special p d,
    fun p j i => A.ordinaryFixed p j i + B.ordinaryFixed p j i,
    fun p d i => A.specialFixed p d i + B.specialFixed p d i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have a := A.rows p
    have b := B.rows p
    simp only [sum_add_distrib]
    omega
  · intro j
    simp [sum_add_distrib, A.ordinaryCols, B.ordinaryCols]
  · intro d
    simp [sum_add_distrib, A.specialCols, B.specialCols]
  · intro p j i
    exact Nat.add_le_add (A.ordinaryBounds p j i) (B.ordinaryBounds p j i)
  · intro p j i
    rw [Nat.add_mod, A.ordinaryParity, B.ordinaryParity, ← Nat.add_mod]
  · intro p d i
    exact Nat.add_le_add (A.specialBounds p d i) (B.specialBounds p d i)
  · intro p d i
    rw [Nat.add_mod, A.specialParity, B.specialParity, ← Nat.add_mod]
  · intro i
    have add_if (P : Prop) [Decidable P] (x y : ℕ) :
        (if P then x + y else 0) = (if P then x else 0) + (if P then y else 0) := by
      by_cases h : P <;> simp [h]
    simp only [A.totals i, B.totals i, add_if, sum_add_distrib, Nat.mul_add]
    omega

private theorem split_three_caps (c₀ c₁ c₂ t : ℕ) (h : t ≤ c₀ + c₁ + c₂) :
    ∃ a b c : ℕ, a ≤ c₀ ∧ b ≤ c₁ ∧ c ≤ c₂ ∧ a + b + c=t := by
  refine ⟨min t c₀, min (t - c₀) c₁, t - c₀ - c₁, ?_⟩
  omega

private theorem split_even_budget (m x y z : ℕ)
    (hx : x ≤ 4 * (m + 1)) (hy : y ≤ 4 * (m + 1)) (hz : z ≤ 4 * (m + 1))
    (total : x + y + z ≤ 8 * (m + 1)) :
    ∃ a b c : ℕ, a ≤ min x 4 ∧ b ≤ min y 4 ∧ c ≤ min z 4 ∧ a + b + c ≤ 8 ∧
      x - a ≤ 4 * m ∧ y - b ≤ 4 * m ∧ z - c ≤ 4 * m ∧ (x - a) + (y - b) + (z - c) ≤ 8 * m := by
  let Lx := x - 4 * m
  let Ly := y - 4 * m
  let Lz := z - 4 * m
  let Ux := min x 4
  let Uy := min y 4
  let Uz := min z 4
  let T := max (Lx + Ly + Lz) (x + y + z - 8 * m)
  have lx : Lx ≤ Ux := by dsimp [Lx, Ux]; omega
  have ly : Ly ≤ Uy := by dsimp [Ly, Uy]; omega
  have lz : Lz ≤ Uz := by dsimp [Lz, Uz]; omega
  have lowTotal : Lx + Ly + Lz ≤ 8 := by
    dsimp [Lx, Ly, Lz]
    omega
  have highTotal : x + y + z - 8 * m ≤ Ux + Uy + Uz := by
    dsimp [Ux, Uy, Uz]
    omega
  have target : T - (Lx + Ly + Lz) ≤ (Ux - Lx) + (Uy - Ly) + (Uz - Lz) := by
    dsimp [T]
    omega
  obtain ⟨a, b, c, ha, hb, hc, sum⟩ := split_three_caps _ _ _ _ target
  refine ⟨Lx + a, Ly + b, Lz + c, ?_⟩
  unfold T at sum
  dsimp [Lx, Ly, Lz, Ux, Uy, Uz] at *
  omega

private theorem split_odd_budget_sorted (m x y z : ℕ)
    (mpos : 2 ≤ m) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z ≤ 2 * m + 2) (total : x + y + z ≤ 4 * m + 4)
    (cut : z ≤ x + y + 2 * m) :
    ∃ a b c : ℕ, a ≤ min x 2 ∧ b ≤ min y 2 ∧ c ≤ min z 2 ∧
      a + b + c ≤ 4 ∧ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧
      x - a ≤ 2 * m ∧ y - b ≤ 2 * m ∧ z - c ≤ 2 * m ∧ (x - a) + (y - b) + (z - c) ≤ 4 * m := by
  by_cases largeY : 2 ≤ y
  · exact ⟨0, 2, 2, by omega⟩
  · by_cases threePositive : 1 ≤ x
    · by_cases largeZ : 2 ≤ z
      · exact ⟨1, 1, 2, by omega⟩
      · exact ⟨0, 0, 0, by omega⟩
    · by_cases highZ : 2 * m < z
      · exact ⟨0, 1, 1, by omega⟩
      · exact ⟨0, 0, 0, by omega⟩

private theorem trio_sum (u : Fin 3 → ℕ) : (∑ i, u i) = u 0 + u 1 + u 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem table_at_even_budget (m : ℕ) (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 4 * m) (cap : ∑ i, u i ≤ 8 * m) :
    Nonempty (OrbitTable (2 * m) (fun i => 4 * u i)) := by
  induction m generalizing u with
  | zero =>
    have h : (fun i => 4 * u i) = fun _ => 0 := by
      funext i
      have hi := bounds i
      omega
    simpa [h] using (show Nonempty (OrbitTable 0 (fun _ => 0)) from ⟨zero_table⟩)
  | succ m ih =>
    obtain ⟨a, b, c, ha, hb, hc, abc, ax, byy, cz, total⟩ :=
      split_even_budget m (u 0) (u 1) (u 2) (bounds 0) (bounds 1) (bounds 2)
        ((trio_sum u) ▸ cap)
    let block : Fin 3 → ℕ := ![a, b, c]
    let remain : Fin 3 → ℕ := fun i => u i - block i
    have boundedBlock (i : Fin 3) : block i ≤ 4 := by
      fin_cases i
      · exact ha.trans (min_le_right _ _)
      · exact hb.trans (min_le_right _ _)
      · exact hc.trans (min_le_right _ _)
    have blockCap : ∑ i, block i ≤ 8 := by simpa [trio_sum, block] using abc
    have boundedRemain (i : Fin 3) : remain i ≤ 4 * m := by
      fin_cases i <;> assumption
    have remainCap : ∑ i, remain i ≤ 8 * m := by simpa [trio_sum, remain, block] using total
    obtain ⟨A⟩ := table_at_budget_two_any_order block boundedBlock blockCap
    obtain ⟨B⟩ := ih remain boundedRemain remainCap
    have combine : (fun i => 4 * block i + 4 * remain i) = (fun i => 4 * u i) := by
      funext i
      fin_cases i
      · have h := ha.trans (min_le_left _ _)
        change 4 * a + 4 * (u 0 - a) = 4 * u 0
        omega
      · have h := hb.trans (min_le_left _ _)
        change 4 * b + 4 * (u 1 - b) = 4 * u 1
        omega
      · have h := hc.trans (min_le_left _ _)
        change 4 * c + 4 * (u 2 - c) = 4 * u 2
        omega
    have budget : 2 + 2 * m = 2 * (m + 1) := by omega
    exact budget ▸ combine ▸ ⟨add_tables A B⟩

private theorem table_at_odd_budget_sorted (m : ℕ) (u : Fin 3 → ℕ)
    (ordered₁ : u 0 ≤ u 1) (ordered₂ : u 1 ≤ u 2)
    (bounds : ∀ i, u i ≤ 2 * (2 * m + 1)) (cap : ∑ i, u i ≤ 4 * (2 * m + 1))
    (cuts : ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (2 * m)) :
    Nonempty (OrbitTable (2 * m + 1) (fun i => 4 * u i)) := by
  by_cases hm : m = 0
  · subst m
    apply table_at_budget_one u
    · exact bounds
    · exact (trio_sum u) ▸ cap
    all_goals
      have a := cuts 0
      have b := cuts 1
      have c := cuts 2
      rw [trio_sum] at a b c
      omega
  · have mpos : 2 ≤ 2 * m := by omega
    have zBound := bounds 2
    have zCap := (trio_sum u) ▸ cap
    have zCut := (trio_sum u) ▸ cuts 2
    obtain ⟨a, b, c, ha, hb, hc, blockCap, ta, tb, tc, ax, byy, cz, remCap⟩ :=
      split_odd_budget_sorted (2 * m) (u 0) (u 1) (u 2) mpos ordered₁ ordered₂
        (by omega) (by omega) (by omega)
    let block : Fin 3 → ℕ := ![a, b, c]
    let remain : Fin 3 → ℕ := fun i => u i - block i
    have boundedBlock (i : Fin 3) : block i ≤ 2 := by
      fin_cases i
      · exact ha.trans (min_le_right _ _)
      · exact hb.trans (min_le_right _ _)
      · exact hc.trans (min_le_right _ _)
    have boundedRemain (i : Fin 3) : remain i ≤ 4 * m := by
      fin_cases i
      · change u 0 - a ≤ 4 * m
        omega
      · change u 1 - b ≤ 4 * m
        omega
      · change u 2 - c ≤ 4 * m
        omega
    have remainCap : ∑ i, remain i ≤ 8 * m := by
      rw [trio_sum]
      change (u 0 - a) + (u 1 - b) + (u 2 - c) ≤ 8 * m
      omega
    obtain ⟨A⟩ := table_at_budget_one block boundedBlock blockCap ta tb tc
    obtain ⟨B⟩ := table_at_even_budget m remain boundedRemain remainCap
    have combine : (fun i => 4 * remain i + 4 * block i) = (fun i => 4 * u i) := by
      funext i
      fin_cases i
      · have h := ha.trans (min_le_left _ _)
        change 4 * (u 0 - a) + 4 * a = 4 * u 0
        omega
      · have h := hb.trans (min_le_left _ _)
        change 4 * (u 1 - b) + 4 * b = 4 * u 1
        omega
      · have h := hc.trans (min_le_left _ _)
        change 4 * (u 2 - c) + 4 * c = 4 * u 2
        omega
    exact combine ▸ ⟨add_tables B A⟩

private theorem table_at_budget (k : ℕ) (u : Fin 3 → ℕ)
    (bounds : ∀ i, u i ≤ 2 * k) (cap : ∑ i, u i ≤ 4 * k)
    (cuts : k % 2 = 1 → ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (k - 1)) :
    Nonempty (OrbitTable k (fun i => 4 * u i)) := by
  let m := k/2
  by_cases odd : k % 2 = 1
  · have eq : k = 2 * m + 1 := by dsimp [m]; omega
    let σ := Tuple.sort u
    have ordered := Tuple.monotone_sort u
    have sameTotal : (∑ i, u (σ i)) = ∑ i, u i := Equiv.sum_comp σ u
    have sorted := table_at_odd_budget_sorted m (u ∘ σ)
      (ordered (by decide : (0 : Fin 3) ≤ 1)) (ordered (by decide : (1 : Fin 3) ≤ 2))
      (fun i => eq ▸ bounds (σ i))
      (by rw [show (∑ i, (u ∘ σ) i) = ∑ i, u i from sameTotal]; exact eq ▸ cap)
      (fun i => by
        have h := cuts odd (σ i)
        change 2 * u (σ i) ≤ (∑ j, u (σ j)) + 2 * (2 * m)
        rw [sameTotal]
        omega)
    have antirelabel := table_permute sorted σ.symm
    simpa only [Function.comp_def, σ.apply_symm_apply, ← eq] using antirelabel
  · have eq : k = 2 * m := by dsimp [m]; omega
    have b (i : Fin 3) : u i ≤ 4 * m := by have hi := bounds i; omega
    have c : (∑ i, u i) ≤ 8 * m := by omega
    simpa only [← eq] using table_at_even_budget m u b c

private theorem odd_cuts_for_table {k : ℕ} {u : Fin 3 → ℕ}
    (table : OrbitTable k (fun i => 4 * u i)) (odd : k % 2 = 1) (i : Fin 3) :
    2 * u i ≤ (∑ j, u j) + 2 * (k - 1) := by
  let σ := Equiv.swap 0 i
  have onZero : σ 0 = i := by simp [σ]
  have total := Equiv.sum_comp σ u
  rw [trio_sum] at total
  have relabelled : OrbitTable k (fun j => 4 * u (σ j)) := swap_coordinates table 0 i
  have cut := odd_table_coordinate_zero relabelled odd
  simp only [onZero] at cut total
  omega

private theorem normalized_feasible_bounds {k : ℕ} {u : Fin 3 → ℕ}
    (h : RealizableSeedCounts 1 k (fun i => 4 * u i)) :
    (∀ i, u i ≤ 2 * k) ∧ (∑ i, u i) ≤ 4 * k := by
  obtain ⟨v, hv, dominates⟩ := seed_vector_dominated h
  obtain ⟨bounded, wall⟩ := hv
  have front (i : Fin 3) : u i ≤ v i := by
    have hi := dominates i
    change 4 * u i ≤ 4 * v i at hi
    omega
  have upper (i : Fin 3) : v i ≤ 2 * k := by
    have hi := bounded i
    change v i ≤ k * 2 at hi
    omega
  refine ⟨fun i => (front i).trans (upper i), ?_⟩
  change (∑ i : Fin 3, (k * 2 - v i)) = k * 2 at wall
  rw [trio_sum] at wall ⊢
  have a := upper 0
  have b := upper 1
  have c := upper 2
  have d := front 0
  have e := front 1
  have f := front 2
  omega

/-- In dimension three the coordinate and total bounds, together with the odd-budget
cuts, characterize simultaneous fixed counts under both uniform parity marginals. -/
theorem exact_three_coordinate_counts (k : ℕ) (z : Fin 3 → ℕ) :
    RealizableSeedCounts 1 k z ↔
      ∃ u : Fin 3 → ℕ, (∀ i, z i = 4 * u i) ∧ (∀ i, u i ≤ 2 * k) ∧
        (∑ i, u i) ≤ 4 * k ∧ (k % 2 = 1 → ∀ i, 2 * u i ≤ (∑ j, u j) + 2 * (k - 1)) := by
  constructor
  · intro realized
    have divisible (i : Fin 3) : 4 ∣ z i := by
      obtain ⟨S, _, _, f, card, equiv, ⟨margin, rows, cols⟩, fixed⟩ := realized
      rw [← fixed i]
      exact D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.coordinate_fixed_count_four_dvd
        f equiv margin rows cols i
    choose u hu using divisible
    have eq : z = fun i => 4 * u i := funext hu
    have realized' := eq ▸ realized
    obtain ⟨bounds, cap⟩ := normalized_feasible_bounds realized'
    obtain ⟨table⟩ := (exact_orbit_table k _).mp realized'
    exact ⟨u, hu, bounds, cap, fun odd i => odd_cuts_for_table table odd i⟩
  · rintro ⟨u, hu, bounds, cap, cuts⟩
    have eq : (fun i => 4 * u i) = z := (funext hu).symm
    obtain ⟨table⟩ := table_at_budget k u bounds cap cuts
    exact eq ▸ (exact_orbit_table k _).mpr ⟨table⟩

end D5.S3.ConceptDynamics.Attribution.ParityThreeCoordinateCounts

end

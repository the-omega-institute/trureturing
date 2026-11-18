/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalRowReduction
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalRowReduction
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The actual nonunit-row reduction needs only three times the larger width below p squared. -/

import D5.S3.Arith.CharacterSums.PascadiMinusRows

/-! The sharper normalized-row estimate keeps the original six-width condition
after the all-center comparison doubles both literal intervals. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem memRowBox {X Y : ℕ} {h : ReturnRows} :
    h ∈ literalRowBox X Y ↔
      (∀ i, -(X : ℤ) ≤ h.1 i ∧ h.1 i ≤ X) ∧
      (∀ i, -(Y : ℤ) ≤ h.2 i ∧ h.2 i ≤ Y) := by
  simp only [literalRowBox, Finset.product_eq_sprod, Finset.mem_product,
    Fintype.mem_piFinset, Finset.mem_Icc]

private theorem memRows {p X Y : ℕ} {g : ZMod (p^3)} {h : ReturnRows} :
    h ∈ rowSolutions p X Y g ↔ h ∈ literalRowBox X Y ∧
      RowEquations g (fun i => (h.1 i : ZMod (p^3)))
        (fun i => (h.2 i : ZMod (p^3))) := by
  classical
  simp only [rowSolutions, Finset.mem_filter]

private theorem normalized_square_three {p Y : ℕ} (hp : p.Prime)
    (hY : 3*Y < p^2) : (2*(Y/p)+1)^2 ≤ 2*Y+1 := by
  have hp0 := hp.pos
  have hk := Nat.div_mul_le_self Y p
  have hkp : 3*(Y/p) < p := by nlinarith [Nat.mul_le_mul_left 3 hk]
  by_cases hz : Y/p = 0
  · simp [hz]
  · have hk1 : 1 ≤ Y/p := by omega
    have hpk : 3*(Y/p)+1 ≤ p := by omega
    have hksq : Y/p ≤ (Y/p)^2 := by
      simpa only [mul_one, pow_two] using Nat.mul_le_mul_left (Y/p) hk1
    have hmul := Nat.mul_le_mul_left (Y/p) hpk
    nlinarith

private theorem first_divisible_three {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 3*Y < p^2) (g : ZMod (p^3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i).card ≤
      4*(2*Y+1)^2 := by
  have h := divisible_row_count (X := X) (Y := Y) hp (by omega) hY g
  have hdiv := Nat.div_le_div_right hXY (c := p)
  have hnorm := normalized_square_three hp hY
  have hnormX : (2*(X/p)+1)^2 ≤ 2*Y+1 :=
    (Nat.pow_le_pow_left (by omega : 2*(X/p)+1 ≤ 2*(Y/p)+1) 2).trans hnorm
  nlinarith

private theorem row_swap_widen {p X Y : ℕ} (hXY : X ≤ Y) {g : ZMod (p^3)}
    {h : ReturnRows} (hh : h ∈ rowSolutions p X Y g) :
    h.swap ∈ rowSolutions p Y Y g := by
  have hh' := memRows.mp hh
  have hb := memRowBox.mp hh'.1
  apply memRows.mpr
  refine ⟨memRowBox.mpr ⟨hb.2, ?_⟩, hh'.2.transpose_rows⟩
  intro i
  change -(Y : ℤ) ≤ h.1 i ∧ h.1 i ≤ Y
  have := hb.1 i
  have hXY' : (X : ℤ) ≤ Y := by exact_mod_cast hXY
  exact ⟨by omega, by omega⟩

private theorem second_divisible_three {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 3*Y < p^2) (g : ZMod (p^3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.2 i).card ≤
      4*(2*Y+1)^2 := by
  classical
  have hcard : ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.2 i).card ≤
      ((rowSolutions p Y Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro h hh
      have hh' := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨row_swap_widen hXY hh'.1, hh'.2⟩
    · intro h _ k _ he
      exact Prod.swap_injective he
  exact hcard.trans (first_divisible_three hp le_rfl hY g)

private theorem rotate_injective (j : Fin 3) : Function.Injective (rotateRows j) := by
  intro h k he
  apply Prod.ext <;> funext i
  · have := congrArg (fun q : ReturnRows => q.1 (i-j)) he
    simpa only [rotateRows, sub_add_cancel] using this
  · have := congrArg (fun q : ReturnRows => q.2 (i-j)) he
    simpa only [rotateRows, sub_add_cancel] using this

private theorem rows_rotate {p X Y : ℕ} {g : ZMod (p^3)}
    {h : ReturnRows} (hh : h ∈ rowSolutions p X Y g) (j : Fin 3) :
    rotateRows j h ∈ rowSolutions p X Y g := by
  have hh' := memRows.mp hh
  have hb := memRowBox.mp hh'.1
  apply memRows.mpr
  refine ⟨memRowBox.mpr ⟨fun i => hb.1 _, fun i => hb.2 _⟩, ?_⟩
  have e := hh'.2
  have e1 := e.cycle_columns
  have e2 := e1.cycle_columns
  fin_cases j
  · simpa [rotateRows] using e
  · simpa [rotateRows] using e1
  · convert e2 using 1 <;> ext i <;> fin_cases i <;> rfl

private theorem unit_chart_count {p X Y : ℕ} (g : ZMod (p^3)) (j : Fin 3) :
    ((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 j*h.2 j).card ≤
      ((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 2*h.2 2).card := by
  classical
  apply Finset.card_le_card_of_injOn (rotateRows (j-2))
  · intro h hh
    have hh' := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨rows_rotate hh'.1 _, ?_⟩
    simpa [rotateRows, add_sub_cancel] using hh'.2
  · intro h _ k _ he
    exact rotate_injective _ he

private theorem rows_count_three {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 3*Y < p^2) (g : ZMod (p^3)) :
    (rowSolutions p X Y g).card ≤
      3*((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 2*h.2 2).card+
        8*(2*Y+1)^2 := by
  classical
  let s := rowSolutions p X Y g
  let G (j : Fin 3) := s.filter fun h => ¬ (p : ℤ) ∣ h.1 j*h.2 j
  let B := s.filter fun h => ∀ i, (p : ℤ) ∣ h.1 i
  let C := s.filter fun h => ∀ i, (p : ℤ) ∣ h.2 i
  have hsub : s ⊆ Finset.univ.biUnion G ∪ (B ∪ C) := by
    intro h hh
    by_cases hx : ∀ i, (p : ℤ) ∣ h.1 i
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh, hx⟩))
    by_cases hy : ∀ i, (p : ℤ) ∣ h.2 i
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh, hy⟩))
    obtain ⟨j, hj⟩ := (memRows.mp hh).2.unit_column hp hx hy
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hh, hj⟩⟩)
  have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_union_le B C
  have h2 := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 3)) G
    (G 2).card (fun j _ => unit_chart_count g j)
  have hB := first_divisible_three hp hXY hY g
  have hC := second_divisible_three hp hXY hY g
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  change B.card ≤ _ at hB
  change C.card ≤ _ at hC
  change s.card ≤ 3*(G 2).card+8*(2*Y+1)^2
  omega

/-- The actual nonunit-row reduction under the sharper three-width cutoff.
It preserves the original six-width hypothesis after doubling the two intervals
for the scalar-center comparison. No row or tuple count is assumed. -/
theorem Nminus_le_three_Uminus_of_three_width {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 3*Y < p^2)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂) :
    Nminus p X Y a₁ a₂ ≤ 3*Uminus p X Y a₁ a₂+8*(2*Y+1)^2 := by
  have h := rows_count_three hp hXY hY (a₁*a₂)
  simpa only [Nminus, Uminus, minusSolutions_eq_rowSolutions hp X Y a₁ a₂ ha₁ ha₂,
    mul_comm] using h

end
end D5.S3.Arith.CharacterSums.Original

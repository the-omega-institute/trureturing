import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.MaskInventory

/-! Arithmetic translation of the five symbolic charts in
   uxwv-c2-a3-full-tail-20261102.py.  This file proves arithmetic and binary
   inventories only; it contains no claim about centered-source strips. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

def normalOrder : Fin 4 → Fin 4 := ![0, 3, 2, 1]
def c2Order (e : ℕ) : Fin 4 → Fin 4 :=
  if e = 4 then ![2, 3, 0, 1] else normalOrder

def c2Alpha (e : ℕ) : ℕ :=
  if e = 4 then 45
  else if e % 4 = 1 then (7 * 2 ^ e - 4) / 5
  else if e % 4 = 2 then (19 * 2 ^ e - 16) / 20
  else if e % 4 = 3 then (17 * 2 ^ e - 16) / 20
  else (17 * 2 ^ e - 52) / 20

/-- Rows are banks; columns are U,V,W,X.  The dyadic low scale is part of
the definition.  e=d-3, ell=b-d-1, h=2^e and q=h*2^ell. -/
def c2Banks (e ell : ℕ) : Fin 4 → Fin 4 → ℕ :=
  let h := 2 ^ e
  let t := 2 ^ ell
  let q := h * t
  let alpha := c2Alpha e
  if e = 4 then
    ![![45,0,0,0], ![0,0,7*q,0], ![18,1,0,0], ![0,0,q-1,3]]
  else if e % 4 = 1 then
    ![![alpha,0,4*q,0], ![0,0,0,3],
      ![4*h-1-alpha,0,q,0], ![0,1,3*q-1,0]]
  else if e % 4 = 2 then
    ![![alpha,0,5*q,0], ![0,0,0,3],
      ![4*h-1-alpha,0,0,0], ![0,1,3*q-1,0]]
  else if e % 4 = 3 then
    ![![alpha,0,5*q,0], ![0,0,2*q,2],
      ![4*h-1-alpha,0,0,0], ![0,1,q-1,1]]
  else
    ![![alpha,0,5*q,0], ![0,0,2*q+4*t,2],
      ![4*h-1-alpha,0,0,0], ![0,1,q-1-4*t,1]]

theorem c2_residues (k : ℕ) :
    (2 : ℕ) ^ (4*k+1) % 5 = 2 ∧
    (2 : ℕ) ^ (4*k+2) % 20 = 4 ∧
    (2 : ℕ) ^ (4*k+3) % 20 = 8 ∧
    (2 : ℕ) ^ (4*k+4) % 20 = 16 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 4*(k+1)+1 = (4*k+1)+4 by omega, pow_add, Nat.mul_mod, ih.1]
      norm_num
    · rw [show 4*(k+1)+2 = (4*k+2)+4 by omega, pow_add, Nat.mul_mod, ih.2.1]
      norm_num
    · rw [show 4*(k+1)+3 = (4*k+3)+4 by omega, pow_add, Nat.mul_mod, ih.2.2.1]
      norm_num
    · rw [show 4*(k+1)+4 = (4*k+4)+4 by omega, pow_add, Nat.mul_mod, ih.2.2.2]
      norm_num

/-- Exact equations, with natural subtraction justified by the lower bounds.
These equations include integrality, rather than assuming an integral alpha. -/
theorem c2_alpha_exact (e : ℕ) (he : 1 ≤ e) :
    if e = 4 then c2Alpha e = 45
    else if e % 4 = 1 then 5 * c2Alpha e + 4 = 7 * 2 ^ e
    else if e % 4 = 2 then 20 * c2Alpha e + 16 = 19 * 2 ^ e
    else if e % 4 = 3 then 20 * c2Alpha e + 16 = 17 * 2 ^ e
    else 8 ≤ e ∧ 20 * c2Alpha e + 52 = 17 * 2 ^ e := by
  have hd := Nat.mod_add_div e 4
  have hr := Nat.mod_lt e (by decide : 0 < 4)
  by_cases h4 : e = 4
  · simp [h4, c2Alpha]
  · simp only [h4, ite_false]
    by_cases h1 : e % 4 = 1
    · simp only [h1, ite_true]
      have heq : e = 4 * (e / 4) + 1 := by omega
      have hm : 2 ^ e % 5 = 2 := by rw [heq]; exact (c2_residues (e/4)).1
      have hl : 2 ≤ (2 : ℕ) ^ e := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
      simp [c2Alpha, h4, h1, ite_false, ite_true]
      omega
    · simp only [h1, ite_false]
      by_cases h2 : e % 4 = 2
      · simp only [h2, ite_true]
        have heq : e = 4 * (e / 4) + 2 := by omega
        have hm : 2 ^ e % 20 = 4 := by rw [heq]; exact (c2_residues (e/4)).2.1
        have hl : 4 ≤ (2 : ℕ) ^ e := by
          simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ e by omega)
        simp [c2Alpha, h4, h1, h2, ite_false, ite_true]
        omega
      · simp only [h2, ite_false]
        by_cases h3 : e % 4 = 3
        · simp only [h3, ite_true]
          have heq : e = 4 * (e / 4) + 3 := by omega
          have hm : 2 ^ e % 20 = 8 := by rw [heq]; exact (c2_residues (e/4)).2.2.1
          have hl : 8 ≤ (2 : ℕ) ^ e := by
            simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ e by omega)
          simp [c2Alpha, h4, h1, h2, h3, ite_false, ite_true]
          omega
        · simp only [h3, ite_false]
          have he8 : 8 ≤ e := by omega
          have heq : e = 4 * (e / 4 - 1) + 4 := by omega
          have hm : 2 ^ e % 20 = 16 := by rw [heq]; exact (c2_residues (e/4-1)).2.2.2
          have hl : 256 ≤ (2 : ℕ) ^ e := by
            simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he8
          refine ⟨he8, ?_⟩
          simp [c2Alpha, h4, h1, h2, h3, ite_false]
          omega

theorem c2_alpha_capacity (e : ℕ) (he : 1 ≤ e) :
    c2Alpha e < 4 * 2 ^ e := by
  have hx := c2_alpha_exact e he
  have hp : 2 ≤ (2 : ℕ) ^ e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  by_cases h4 : e = 4
  · subst e; norm_num [c2Alpha]
  · simp only [h4, ite_false] at hx
    split_ifs at hx <;> omega

theorem c2_transfer (e ell : ℕ) (he : 8 ≤ e) :
    4 * 2 ^ ell = (2 : ℕ) ^ (ell + 2) ∧
    4 * 2 ^ ell < 2 ^ e * 2 ^ ell ∧
    SecondPeakHighD.Submask (4 * 2 ^ ell) (2 ^ e * 2 ^ ell - 1) := by
  have h4 : 4 < (2 : ℕ) ^ e := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
    norm_num at hh
    omega
  have hr := reserve_below e ell 4 h4
  refine ⟨by simp only [pow_add, show (2 : ℕ)^2 = 4 by decide]; omega, ?_, ?_⟩
  · simpa only [pow_add] using hr.1
  · simpa only [pow_add] using hr.2

/-- Every column is a disjoint, complete binary inventory.  In the exceptional
e=4 row the U complement is 18 and V is in bank 2. -/
theorem c2_inventory (e ell : ℕ) (he : 1 ≤ e) :
    ∀ chain : Fin 4, MaskInventory
      ((![e+2, 1, e+ell+3, 2] : Fin 4 → ℕ) chain)
      (fun bank => c2Banks e ell bank chain) := by
  have hp := Nat.two_pow_pos e
  have hq : 2 ^ e * 2 ^ ell = (2 : ℕ) ^ (e + ell) := (pow_add _ _ _).symm
  have hU : MaskInventory (e+2)
      ![c2Alpha e, 0, 4*2^e-1-c2Alpha e, 0] := by
    apply inventory_02
    have ha := c2_alpha_capacity e he
    have hh : (2 : ℕ) ^ (e+2) = 4 * 2 ^ e := by
      simp only [pow_add, show (2 : ℕ)^2 = 4 by decide]; omega
    rw [hh]
    omega
  by_cases h4 : e = 4
  · subst e
    have hW := w_inventory 4 ell 0 3 ![0,7,0,0] (by decide)
      (by apply inventory_of_finite_bits <;> decide)
    intro chain
    fin_cases chain
    · convert (show MaskInventory 6 ![45,0,18,0] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks])
    · convert (show MaskInventory 1 ![0,0,1,0] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks])
    · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, wMasks, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    · convert (show MaskInventory 2 ![0,0,0,3] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks])
  · by_cases h1 : e % 4 = 1
    · have hW := w_inventory e ell 0 3 ![4,0,1,2] hp
        (by apply inventory_of_finite_bits <;> decide)
      intro chain
      fin_cases chain
      · convert hU using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1])
      · convert (show MaskInventory 1 ![0,0,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1])
      · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, wMasks, h4, h1, ← Nat.succ_mul])
      · convert (show MaskInventory 2 ![0,3,0,0] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1])
    · by_cases h2 : e % 4 = 2
      · have hW := w_inventory e ell 0 3 ![5,0,0,2] hp
          (by apply inventory_of_finite_bits <;> decide)
        intro chain
        fin_cases chain
        · convert hU using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2])
        · convert (show MaskInventory 1 ![0,0,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2])
        · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, wMasks, h4, h1, h2, ← Nat.succ_mul])
        · convert (show MaskInventory 2 ![0,3,0,0] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2])
      · by_cases h3 : e % 4 = 3
        · have hW := w_inventory e ell 0 3 ![5,2,0,0] hp
            (by apply inventory_of_finite_bits <;> decide)
          intro chain
          fin_cases chain
          · convert hU using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])
          · convert (show MaskInventory 1 ![0,0,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])
          · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, wMasks, h4, h1, h2, h3])
          · convert (show MaskInventory 2 ![0,2,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])
        · have hx := c2_alpha_exact e he
          simp only [h4, h1, h2, h3, ite_false] at hx
          have ht := c2_transfer e ell hx.1
          have hR : 4 < (2 : ℕ) ^ e := by
            have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hx.1
            norm_num at hh
            omega
          have hW := w_inventory e ell 4 3 ![5,2,0,0] hR
            (by apply inventory_of_finite_bits <;> decide)
          -- The complete low inventory here is the complementary pair
          -- 4*2^ell and q-1-4*2^ell.  ht identifies the moved single bit.
          have hsingle := ht.1
          intro chain
          fin_cases chain
          · convert hU using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])
          · convert (show MaskInventory 1 ![0,0,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])
          · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, wMasks, h4, h1, h2, h3, hsingle])
          · convert (show MaskInventory 2 ![0,2,0,1] from by apply inventory_of_finite_bits <;> decide) using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [c2Banks, h4, h1, h2, h3])

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

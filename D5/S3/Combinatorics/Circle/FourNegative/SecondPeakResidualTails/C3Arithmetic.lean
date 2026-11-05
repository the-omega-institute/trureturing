import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Arithmetic

/- UNCOMPILED.  Literal fixed tables and the two universal tails are from
   uxwv-c3-a5-full-tail-20261102.py.  e=1 is auxiliary; the original public
   c=3,a=5 family starts at d>=7, hence e=d-5>=2. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

def c3Alpha (e : ℕ) : ℕ :=
  if e < 8 then
    match e with
    | 1 => 5
    | 2 => 10
    | 3 => 14
    | 4 => 32
    | 5 => 68
    | 6 => 140
    | _ => 228
  else if e % 2 = 0 then (43 * 2 ^ e - 40) / 24
  else (43 * 2 ^ e - 128) / 24

def c3R (e : ℕ) : ℕ :=
  if e < 8 then
    match e with
    | 1 => 1
    | 2 => 0
    | 3 => 7
    | 4 => 7
    | 5 => 7
    | 6 => 7
    | _ => 1
  else if e % 2 = 0 then 2 else 10

def c3High (e : ℕ) : Fin 4 → ℕ :=
  if e < 8 then
    match e with
    | 1 => ![24,4,2,1]
    | 2 => ![25,4,2,0]
    | 3 => ![26,4,0,1]
    | 4 => ![26,4,0,1]
    | 5 => ![26,4,0,1]
    | 6 => ![26,4,0,1]
    | _ => ![27,4,0,0]
  else ![27,4,0,0]

def c3Banks (e ell : ℕ) : Fin 4 → Fin 4 → ℕ :=
  let h := 2 ^ e
  let t := 2 ^ ell
  let q := h * t
  let p := c3High e
  let R := c3R e
  let alpha := c3Alpha e
  ![![alpha,0,p 0*q,0], ![0,0,p 1*q+R*t,12],
    ![16*h-1-alpha,0,p 2*q,0], ![0,3,p 3*q+q-1-R*t,3]]

theorem c3_residues (k : ℕ) :
    (2 : ℕ) ^ (2*k+3) % 24 = 8 ∧
    (2 : ℕ) ^ (2*k+4) % 24 = 16 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    constructor
    · rw [show 2*(k+1)+3 = (2*k+3)+2 by omega, pow_add, Nat.mul_mod, ih.1]
      norm_num
    · rw [show 2*(k+1)+4 = (2*k+4)+2 by omega, pow_add, Nat.mul_mod, ih.2]
      norm_num

theorem c3_tail_exact (e : ℕ) (he : 8 ≤ e) :
    if e % 2 = 0 then
      c3R e = 2 ∧ 24 * c3Alpha e + 40 = 43 * 2 ^ e
    else 9 ≤ e ∧ c3R e = 10 ∧ 24 * c3Alpha e + 128 = 43 * 2 ^ e := by
  have hn : ¬ e < 8 := by omega
  have hdiv := Nat.mod_add_div e 2
  have hmod := Nat.mod_lt e (by decide : 0 < 2)
  have hpow : 256 ≤ (2 : ℕ) ^ e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  by_cases hp : e % 2 = 0
  · simp only [hp, ite_true]
    have heq : e = 2*(e/2-2)+4 := by omega
    have hm : 2 ^ e % 24 = 16 := by rw [heq]; exact (c3_residues (e/2-2)).2
    refine ⟨by simp [c3R, hn, hp], ?_⟩
    simp only [c3Alpha, hn, hp, ite_false, ite_true]
    omega
  · simp only [hp, ite_false]
    have he9 : 9 ≤ e := by omega
    have heq : e = 2*(e/2-1)+3 := by omega
    have hm : 2 ^ e % 24 = 8 := by rw [heq]; exact (c3_residues (e/2-1)).1
    refine ⟨he9, by simp [c3R, hn, hp], ?_⟩
    simp only [c3Alpha, hn, hp, ite_false]
    omega

theorem c3_capacities (e : ℕ) (he : 1 ≤ e) :
    c3Alpha e < 16 * 2 ^ e ∧ c3R e < 2 ^ e := by
  by_cases hs : e < 8
  · have he7 : e ≤ 7 := by omega
    interval_cases e <;> norm_num [c3Alpha, c3R]
  · have he8 : 8 ≤ e := by omega
    have hx := c3_tail_exact e he8
    have hpow : 256 ≤ (2 : ℕ) ^ e := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he8
    split_ifs at hx <;> omega

theorem c3_high_inventory (e : ℕ) (he : 1 ≤ e) : MaskInventory 5 (c3High e) := by
  by_cases hs : e < 8
  · have he7 : e ≤ 7 := by omega
    interval_cases e <;> norm_num only [c3High] <;> apply inventory_of_finite_bits <;> decide
  · simp only [c3High, hs, ite_false]
    apply inventory_of_finite_bits <;> decide

/-- The restored 2q term is present in both first fixed charts; beta is
always 12, while alpha is the U mask. -/
theorem c3_inventory (e ell : ℕ) (he : 1 ≤ e) :
    ∀ chain : Fin 4, MaskInventory
      ((![e+4, 2, e+ell+5, 4] : Fin 4 → ℕ) chain)
      (fun bank => c3Banks e ell bank chain) := by
  have hc := c3_capacities e he
  have hU : MaskInventory (e+4)
      ![c3Alpha e,0,16*2^e-1-c3Alpha e,0] := by
    apply inventory_02
    have hh : (2 : ℕ) ^ (e+4) = 16 * 2 ^ e := by
      simp only [pow_add, show (2 : ℕ)^4 = 16 by decide]; omega
    rw [hh]
    omega
  have hW := w_inventory e ell (c3R e) 5 (c3High e) hc.2 (c3_high_inventory e he)
  intro chain
  fin_cases chain
  · convert hU using 1 <;> ext bank <;> fin_cases bank <;> simp [c3Banks]
  · convert (show MaskInventory 2 ![0,0,0,3] from by apply inventory_of_finite_bits <;> decide) using 1 <;> ext bank <;> fin_cases bank <;> simp [c3Banks]
  · convert hW using 1 <;> ext bank <;> fin_cases bank <;> simp [c3Banks, wMasks]
  · convert (show MaskInventory 4 ![0,12,0,3] from by apply inventory_of_finite_bits <;> decide) using 1 <;> ext bank <;> fin_cases bank <;> simp [c3Banks]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

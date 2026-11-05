import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.DiagonalSelector
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Arithmetic

/-! Prepared residual construction.  Here d=2*c+delta, b=d+1+ell and a=c+1.
   The four boundary schedules are retained literally. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

def diagonalExponent (c delta : ℕ) : ℕ := c + delta - 1
def diagonalH (c delta : ℕ) : ℕ := 2 ^ diagonalExponent c delta

def diagonalAlpha (c delta : ℕ) : ℕ :=
  let z := 2 ^ c
  if delta = 0 then z*z/4+3*z/8-1
  else if delta = 1 then z
  else if delta = 2 then z*z-5*z/2
  else if delta = 3 then 17*z/4+4
  else (diagonalAlphaInt (z : ℤ) (diagonalH c delta : ℤ)).toNat

def diagonalR (c delta : ℕ) : ℕ :=
  let z := 2 ^ c
  if delta = 0 then 0
  else if delta = 1 then z-3
  else if delta = 2 then 0
  else if delta = 3 then 7*z/2-16
  else (diagonalRInt (z : ℤ) (diagonalH c delta : ℤ)).toNat

def diagonalHigh (c delta : ℕ) : Fin 4 → ℕ :=
  let z := 2 ^ c
  if delta = 0 then ![z-3,2,z,0]
  else if delta = 2 then ![z+1,2,z-4,0]
  else ![2*z-4,2,0,1]

def diagonalBanks (c delta ell : ℕ) : Fin 4 → Fin 4 → ℕ :=
  let z := 2 ^ c
  let h := diagonalH c delta
  let t := 2 ^ ell
  let q := h*t
  let alpha := diagonalAlpha c delta
  let R := diagonalR c delta
  let p := diagonalHigh c delta
  ![![alpha,0,p 0*q,0], ![0,0,p 1*q+R*t,z-2],
    ![z*h-1-alpha,0,p 2*q,0], ![0,z/2-1,p 3*q+q-1-R*t,1]]

theorem diagonal_dyadic (c delta : ℕ) (hc : 3 ≤ c) :
    8 ≤ (2 : ℕ) ^ c ∧ 8 ∣ (2 : ℕ) ^ c ∧ 4 ∣ diagonalH c delta := by
  have hz : 8 ≤ (2 : ℕ) ^ c := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hc
  have hz8 : 8 ∣ (2 : ℕ) ^ c := by
    refine ⟨2 ^ (c-3), ?_⟩
    rw [show c = (c-3)+3 by omega, pow_add]
    norm_num <;> ring
  have hh4 : 4 ∣ diagonalH c delta := by
    refine ⟨2 ^ (diagonalExponent c delta-2), ?_⟩
    dsimp only [diagonalH]
    rw [show diagonalExponent c delta = (diagonalExponent c delta-2)+2 by
      dsimp only [diagonalExponent]; omega, pow_add]
    norm_num <;> ring
  exact ⟨hz, hz8, hh4⟩

theorem diagonal_tail_scale (c delta : ℕ) (hc : 3 ≤ c) (hd : 4 ≤ delta) :
    8 * 2 ^ c ≤ diagonalH c delta := by
  have he : c+3 ≤ diagonalExponent c delta := by dsimp only [diagonalExponent]; omega
  calc
    8 * 2 ^ c = (2 : ℕ) ^ (c+3) := by rw [pow_add]; norm_num <;> ring
    _ ≤ diagonalH c delta := Nat.pow_le_pow_right (by decide) he

theorem diagonal_boundary_scales (c : ℕ) (hc : 3 ≤ c) :
    diagonalH c 0 = 2 ^ c / 2 ∧ diagonalH c 1 = 2 ^ c ∧
    diagonalH c 2 = 2 * 2 ^ c ∧ diagonalH c 3 = 4 * 2 ^ c := by
  have hz : (2 : ℕ) ^ c = 2 * 2 ^ (c-1) := by
    calc
      (2 : ℕ)^c = 2^((c-1)+1) := by congr 1; omega
      _ = 2*2^(c-1) := by rw [pow_succ]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [diagonalH, diagonalExponent, Nat.add_zero]
    omega
  · simp [diagonalH, diagonalExponent]
  · rw [diagonalH, show diagonalExponent c 2 = c+1 by dsimp [diagonalExponent] <;> omega]
    rw [pow_succ]; ring
  · rw [diagonalH, show diagonalExponent c 3 = c+2 by dsimp [diagonalExponent] <;> omega]
    rw [pow_add]; norm_num <;> ring

/-- The exact divisibilities in the boundary formulas are consumed before
natural subtraction.  No truncated negative expression defines a selector. -/
theorem diagonal_boundary_capacities (z : ℕ) (hz : 8 ≤ z) (hz8 : 8 ∣ z) :
    z*z/4+3*z/8-1 < z*(z/2) ∧ z < z*z ∧
    z*z-5*z/2 < z*(2*z) ∧ 17*z/4+4 < z*(4*z) ∧
    z-3 < z ∧ 7*z/2-16 < 4*z := by
  obtain ⟨Z, hZ⟩ := hz8
  have hz2 : 2*(z/2) = z := by omega
  have hz3 : 8*(3*z/8) = 3*z := by omega
  have hz5 : 2*(5*z/2) = 5*z := by omega
  have hz17 : 4*(17*z/4) = 17*z := by omega
  have hz7 : 2*(7*z/2) = 7*z := by omega
  have hz4 : 4*(z*z/4) = z*z := by
    apply Nat.mul_div_cancel'
    refine ⟨16*Z*Z, ?_⟩
    rw [hZ]
    ring
  have hsq : 8*z ≤ z*z := by nlinarith [Nat.mul_le_mul_left z hz]
  have hhalf0 : 1 ≤ z*z/4+3*z/8 := by omega
  have hhalf : (z*z/4+3*z/8-1)+1 = z*z/4+3*z/8 := by omega
  have hhalfprod : 2*(z*(z/2)) = z*z := by nlinarith only [hz2]
  have htwodiv : 5*z/2 ≤ z*z := by nlinarith only [hz5, hsq]
  have htwo : (z*z-5*z/2)+5*z/2 = z*z := by omega
  have hfour : (7*z/2-16)+16 = 7*z/2 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hz, hz3, hz4, hhalf, hhalfprod, hsq]
  · nlinarith only [hz, hsq]
  · have hsub : z*z-5*z/2 ≤ z*z := Nat.sub_le _ _
    have hpos : 0 < z*z := by positivity
    nlinarith only [hsub, hpos]
  · nlinarith only [hz, hz17, hsq]
  · omega
  · omega

theorem diagonal_capacities (c delta : ℕ) (hc : 3 ≤ c) :
    diagonalAlpha c delta < 2 ^ c * diagonalH c delta ∧
    diagonalR c delta < diagonalH c delta := by
  have hd := diagonal_dyadic c delta hc
  have hb := diagonal_boundary_capacities (2 ^ c) hd.1 hd.2.1
  have hs := diagonal_boundary_scales c hc
  by_cases h0 : delta = 0
  · subst delta
    simpa [diagonalAlpha, diagonalR, hs.1] using
      (show 2^c*2^c/4+3*2^c/8-1 < 2^c*(2^c/2) ∧ 0 < 2^c/2 from
        ⟨hb.1, by omega⟩)
  · by_cases h1 : delta = 1
    · subst delta
      simpa [diagonalAlpha, diagonalR, hs.2.1] using
        (show 2^c < 2^c*2^c ∧ 2^c-3 < 2^c from ⟨hb.2.1, hb.2.2.2.2.1⟩)
    · by_cases h2 : delta = 2
      · subst delta
        simpa [diagonalAlpha, diagonalR, hs.2.2.1] using
          (show 2^c*2^c-5*2^c/2 < 2^c*(2*2^c) ∧ 0 < 2*2^c from
            ⟨hb.2.2.1, by positivity⟩)
      · by_cases h3 : delta = 3
        · subst delta
          simpa [diagonalAlpha, diagonalR, hs.2.2.2] using
            ⟨hb.2.2.2.1, hb.2.2.2.2.2⟩
        · have ht : 4 ≤ delta := by omega
          have hh := diagonal_tail_scale c delta hc ht
          have hcvt := diagonal_tail_transport (2 ^ c) (diagonalH c delta)
            hd.1 hh hd.2.1 hd.2.2
          simpa [diagonalAlpha, diagonalR, h0, h1, h2, h3] using ⟨hcvt.1, hcvt.2.1⟩

theorem diagonal_normal_high_inventory (c : ℕ) (hc : 3 ≤ c) :
    MaskInventory (c+1) ![2*2^c-4,2,0,1] := by
  have hz : (2 : ℕ) ^ c = 2 * 2 ^ (c-1) := by
    calc
      (2 : ℕ)^c = 2^((c-1)+1) := by congr 1; omega
      _ = 2*2^(c-1) := by rw [pow_succ]; ring
  have hp := Nat.two_pow_pos (c-1)
  have hi : MaskInventory (c-1) ![2^(c-1)-1,0,0,0] := by
    exact inventory_02 (c-1) (2^(c-1)-1) 0 (by omega)
  have hl : MaskInventory 2 ![0,2,0,1] := by apply inventory_of_finite_bits <;> decide
  have hb := inventory_blocks 2 (c-1) ![0,2,0,1] ![2^(c-1)-1,0,0,0] hl hi
  convert hb using 1
  · omega
  · ext bank
    fin_cases bank <;> simp
    omega

theorem diagonal_half_high_inventory (c : ℕ) (hc : 3 ≤ c) :
    MaskInventory (c+1) ![2^c-3,2,2^c,0] := by
  have hz := (diagonal_dyadic c 0 hc).1
  have hl : MaskInventory c ![2^c-3,2,0,0] :=
    inventory_01 c (2^c-3) 2 (by omega)
  have hh : MaskInventory 1 ![0,0,1,0] := by apply inventory_of_finite_bits <;> decide
  have hb := inventory_blocks c 1 ![2^c-3,2,0,0] ![0,0,1,0] hl hh
  convert hb using 1 <;> ext bank <;> fin_cases bank <;> simp

theorem diagonal_two_high_inventory (c : ℕ) (hc : 3 ≤ c) :
    MaskInventory (c+1) ![2^c+1,2,2^c-4,0] := by
  have hz : (2 : ℕ) ^ c = 4 * 2 ^ (c-2) := by
    rw [show c = (c-2)+2 by omega, pow_add]; norm_num <;> ring
  have hp := Nat.two_pow_pos (c-2)
  have hh : MaskInventory (c-2) ![0,0,2^(c-2)-1,0] :=
    inventory_02 (c-2) 0 (2^(c-2)-1) (by omega)
  have hl : MaskInventory 2 ![1,2,0,0] := by apply inventory_of_finite_bits <;> decide
  have hb := inventory_blocks 2 (c-2) ![1,2,0,0] ![0,0,2^(c-2)-1,0] hl hh
  have hlo : MaskInventory c ![1,2,2^c-4,0] := by
    convert hb using 1
    · omega
    · ext bank
      fin_cases bank <;> simp
      omega
  have hhi : MaskInventory 1 ![1,0,0,0] := by apply inventory_of_finite_bits <;> decide
  have hfull := inventory_blocks c 1 ![1,2,2^c-4,0] ![1,0,0,0] hlo hhi
  convert hfull using 1 <;> ext bank <;> fin_cases bank <;> simp

theorem diagonal_high_inventory (c delta : ℕ) (hc : 3 ≤ c) :
    MaskInventory (c+1) (diagonalHigh c delta) := by
  by_cases h0 : delta = 0
  · simpa [diagonalHigh, h0] using diagonal_half_high_inventory c hc
  · by_cases h2 : delta = 2
    · simpa [diagonalHigh, h0, h2] using diagonal_two_high_inventory c hc
    · simpa [diagonalHigh, h0, h2] using diagonal_normal_high_inventory c hc

theorem diagonal_inventory (c delta ell : ℕ) (hc : 3 ≤ c) :
    ∀ chain : Fin 4, MaskInventory
      ((![c+diagonalExponent c delta, c-1,
          diagonalExponent c delta+ell+(c+1), c] : Fin 4 → ℕ) chain)
      (fun bank => diagonalBanks c delta ell bank chain) := by
  have hd := diagonal_dyadic c delta hc
  have hcapa := diagonal_capacities c delta hc
  have hU : MaskInventory (c+diagonalExponent c delta)
      ![diagonalAlpha c delta,0,2^c*diagonalH c delta-1-diagonalAlpha c delta,0] := by
    apply inventory_02
    have hh : (2 : ℕ) ^ (c+diagonalExponent c delta) = 2^c*diagonalH c delta := by
      rw [pow_add, diagonalH]
    rw [hh]
    omega
  have hV : MaskInventory (c-1) ![0,0,0,2^c/2-1] := by
    apply inventory_03
    have hh : (2 : ℕ) ^ c = 2 * 2^(c-1) := by
      calc
      (2 : ℕ)^c = 2^((c-1)+1) := by congr 1; omega
      _ = 2*2^(c-1) := by rw [pow_succ]; ring
    omega
  have hX : MaskInventory c ![0,2^c-2,0,1] := by
    apply inventory_13
    omega
  have hW := w_inventory (diagonalExponent c delta) ell (diagonalR c delta)
    (c+1) (diagonalHigh c delta) hcapa.2 (diagonal_high_inventory c delta hc)
  intro chain
  fin_cases chain
  · convert hU using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [diagonalBanks])
  · convert hV using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [diagonalBanks])
  · convert hW using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [diagonalBanks, wMasks, diagonalH])
  · convert hX using 1 <;> first | rfl | (ext bank; fin_cases bank <;> simp [diagonalBanks])

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

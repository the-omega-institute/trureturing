/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pOddNeighbor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pOddNeighbor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The catalogue P48p odd neighbor is the scaled integral preimage of the ternary frame kernel. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Tactic.Linarith
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# The catalogue P48p odd neighbor

The catalogue frame rows form the matrix `F`, and `P = G * Fᵀ` is the
pairing matrix. Half-frame pairings give integral coordinates on the
neighbor obtained by adjoining half of row zero to the even-pairing
kernel. These coordinates describe the preimage of the kernel of
`Fᵀ` modulo three, with the dot product divided by three.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pOddNeighbor

open scoped BigOperators Matrix
open P48pSyndromeFrame
open NormTwoTernarySyndrome (ternarySyndrome)

abbrev IntRow := Fin 48 → ℤ
abbrev RatRow := Fin 48 → ℚ

local notation "F" => p48pFrameRows
local notation "G" => p48pGram
local notation "P" => p48pPairingFrame

/-- Embed an integral row in the rational coordinate space. -/
def ratRow (y : IntRow) : RatRow := fun j => (y j : ℚ)

private abbrev castMatrix :
    Matrix (Fin 48) (Fin 48) ℤ →+* Matrix (Fin 48) (Fin 48) ℚ :=
  (Int.castRingHom ℚ).mapMatrix

private theorem castMatrix_twelve_smul (A : Matrix (Fin 48) (Fin 48) ℤ) :
    castMatrix ((12 : ℤ) • A) = (12 : ℚ) • castMatrix A := by
  ext i j
  change (↑((12 : ℤ) • A i j) : ℚ) = (12 : ℚ) • (A i j : ℚ)
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, smul_eq_mul]

private theorem castMatrix_transpose (A : Matrix (Fin 48) (Fin 48) ℤ) :
    castMatrix Aᵀ = (castMatrix A)ᵀ := rfl

/-- Pairing with each half-frame vector in the catalogue basis. -/
def halfFramePairings (x : RatRow) : RatRow :=
  x ᵥ* ((1 / 2 : ℚ) • castMatrix P)

/-- Reconstruct a catalogue row from its half-frame pairings. -/
def fromHalfFrame (y : RatRow) : RatRow :=
  y ᵥ* ((1 / 6 : ℚ) • castMatrix F)

private theorem scaled_frame_mul_pairing :
    ((1 / 6 : ℚ) • castMatrix F) * ((1 / 2 : ℚ) • castMatrix P) = 1 := by
  have h : F * P = (12 : ℤ) • 1 := by
    rw [p48pPairingFrame_eq, ← Matrix.mul_assoc, p48pFrameRows_orthogonal]
  have hQ : castMatrix F * castMatrix P = (12 : ℚ) • 1 := by
    simpa only [map_mul, castMatrix_twelve_smul, map_one] using congrArg castMatrix h
  simp only [Matrix.smul_mul, Matrix.mul_smul, hQ, smul_smul]
  norm_num

@[simp] theorem halfFramePairings_fromHalfFrame (y : RatRow) :
    halfFramePairings (fromHalfFrame y) = y := by
  simp only [halfFramePairings, fromHalfFrame, Matrix.vecMul_vecMul,
    scaled_frame_mul_pairing, Matrix.vecMul_one]

@[simp] theorem fromHalfFrame_halfFramePairings (x : RatRow) :
    fromHalfFrame (halfFramePairings x) = x := by
  have h : ((1 / 2 : ℚ) • castMatrix P) * ((1 / 6 : ℚ) • castMatrix F) = 1 :=
    mul_eq_one_comm.mp scaled_frame_mul_pairing
  simp only [fromHalfFrame, halfFramePairings, Matrix.vecMul_vecMul,
    h, Matrix.vecMul_one]

private theorem cast_vecMul (A : Matrix (Fin 48) (Fin 48) ℤ) (y : IntRow) (j : Fin 48) :
    (ratRow y ᵥ* castMatrix A) j = ((y ᵥ* A) j : ℚ) :=
  ((Int.castRingHom ℚ).map_vecMul A y j).symm

private theorem halfFramePairings_ratRow_apply (a : IntRow) (j : Fin 48) :
    halfFramePairings (ratRow a) j = ((a ᵥ* P) j : ℚ) / 2 := by
  rw [halfFramePairings, Matrix.vecMul_smul]
  change (1 / 2 : ℚ) * (ratRow a ᵥ* castMatrix P) j = _
  rw [cast_vecMul] <;> ring

private theorem fromHalfFrame_ratRow_apply (y : IntRow) (j : Fin 48) :
    fromHalfFrame (ratRow y) j = ((y ᵥ* F) j : ℚ) / 6 := by
  rw [fromHalfFrame, Matrix.vecMul_smul]
  change (1 / 6 : ℚ) * (ratRow y ᵥ* castMatrix F) j = _
  rw [cast_vecMul] <;> ring

/-- The integral catalogue rows pairing evenly with the first frame vector. -/
def evenKernel : Set IntRow := {a | (2 : ℤ) ∣ (a ᵥ* P) 0}

/-- The pairing columns have common parity, so a single column tests the kernel. -/
theorem mem_evenKernel_iff (a : IntRow) :
    a ∈ evenKernel ↔ ∀ j, (2 : ℤ) ∣ (a ᵥ* P) j := by
  constructor
  · intro ha j
    have hParity : ((a ᵥ* P) j : ZMod 2) = ((a ᵥ* P) 0 : ZMod 2) := by
      simp only [Matrix.vecMul_apply_eq_sum, Int.cast_sum, Int.cast_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [p48pPairingFrame_columns_same_parity i j 0]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
      (hParity.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 ha))
  · intro ha
    exact ha 0

/-- Half of a catalogue frame row. -/
def halfFrameVector (i : Fin 48) : RatRow :=
  (1 / 2 : ℚ) • castMatrix F i

/-- The even-pairing kernel with the half of row zero adjoined. -/
def oddNeighbor : Set RatRow :=
  {x | ∃ a ∈ evenKernel, ∃ n : ℤ, x = ratRow a + (n : ℚ) • halfFrameVector 0}

private theorem frame_rows_same_parity (i j : Fin 48) :
    (F i j : ZMod 2) = (F 0 j : ZMod 2) := by
  have h : List.ofFn (fun k : Fin 48 => F i k % 2) =
      List.ofFn (fun k : Fin 48 => F 0 k % 2) := by
    fin_cases i <;> decide +kernel
  exact (ZMod.intCast_eq_intCast_iff' _ _ 2).2 (congrFun (List.ofFn_injective h) j)

private theorem frame_zero_zero_mod_two : (F 0 0 : ZMod 2) = 1 := by decide +kernel

private theorem vecMul_frame_parity (y : IntRow) (j : Fin 48) :
    ((y ᵥ* F) j : ZMod 2) = ((∑ i, y i : ℤ) : ZMod 2) * (F 0 j : ZMod 2) := by
  simp only [Matrix.vecMul_apply_eq_sum, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [frame_rows_same_parity i j]

/-- The frame product is even in every coordinate exactly when the coordinate sum is even. -/
theorem frame_even_iff (y : IntRow) :
    (∀ j, (2 : ℤ) ∣ (y ᵥ* F) j) ↔ (2 : ℤ) ∣ ∑ i, y i := by
  constructor
  · intro h
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (h 0)
    rw [vecMul_frame_parity, frame_zero_zero_mod_two, mul_one] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h0
  · intro h j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
    rw [vecMul_frame_parity, (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 h, zero_mul]

private theorem shift_vecMul (y : IntRow) (n : ℤ) (j : Fin 48) :
    ((y + Pi.single (0 : Fin 48) (3 * n)) ᵥ* F) j =
      (y ᵥ* F) j + 3 * (n * F 0 j) := by
  rw [Matrix.add_vecMul, Matrix.single_vecMul]
  change (y ᵥ* F) j + (3 * n) * F 0 j = _
  rw [mul_assoc]

private theorem fromHalfFrame_shift (y : IntRow) (n : ℤ) :
    fromHalfFrame (ratRow (y + Pi.single (0 : Fin 48) (3 * n))) =
      fromHalfFrame (ratRow y) + (n : ℚ) • halfFrameVector 0 := by
  funext j
  rw [fromHalfFrame_ratRow_apply, shift_vecMul]
  change (↑((y ᵥ* F) j + 3 * (n * F 0 j)) : ℚ) / 6 =
    fromHalfFrame (ratRow y) j + (n : ℚ) * ((1 / 2 : ℚ) * (F 0 j : ℚ))
  rw [fromHalfFrame_ratRow_apply]
  push_cast <;> ring

private theorem evenKernel_lift (y : IntRow) (h : ∀ j, (6 : ℤ) ∣ (y ᵥ* F) j) :
    ∃ a ∈ evenKernel, fromHalfFrame (ratRow y) = ratRow a := by
  choose a ha using h
  have hLift : fromHalfFrame (ratRow y) = ratRow a := by
    funext j
    rw [fromHalfFrame_ratRow_apply, ha j]
    change (↑(6 * a j) : ℚ) / 6 = (a j : ℚ)
    push_cast <;> ring
  refine ⟨a, (mem_evenKernel_iff a).2 ?_, hLift⟩
  intro j
  have hPair := congrFun (halfFramePairings_fromHalfFrame (ratRow y)) j
  rw [hLift, halfFramePairings_ratRow_apply] at hPair
  change ((a ᵥ* P) j : ℚ) / 2 = (y j : ℚ) at hPair
  have hEq : ((a ᵥ* P) j : ℚ) = 2 * (y j : ℚ) := by linarith only [hPair]
  exact ⟨y j, by exact_mod_cast hEq⟩

/-- Exact membership in the concrete odd neighbor in half-frame coordinates. -/
theorem mem_oddNeighbor_iff (x : RatRow) :
    x ∈ oddNeighbor ↔
      ∃ y : IntRow, halfFramePairings x = ratRow y ∧ ∀ j, (3 : ℤ) ∣ (y ᵥ* F) j := by
  constructor
  · rintro ⟨a, ha, n, rfl⟩
    choose w hw using (mem_evenKernel_iff a).1 ha
    have hPair : halfFramePairings (ratRow a) = ratRow w := by
      funext j
      rw [halfFramePairings_ratRow_apply, hw j]
      change (↑(2 * w j) : ℚ) / 2 = (w j : ℚ)
      push_cast <;> ring
    have hLift : fromHalfFrame (ratRow w) = ratRow a := by
      rw [← hPair, fromHalfFrame_halfFramePairings]
    refine ⟨w + Pi.single (0 : Fin 48) (3 * n), ?_, ?_⟩
    · rw [← hLift, ← fromHalfFrame_shift, halfFramePairings_fromHalfFrame]
    · intro j
      have hj := (fromHalfFrame_ratRow_apply w j).symm.trans (congrFun hLift j)
      change ((w ᵥ* F) j : ℚ) / 6 = (a j : ℚ) at hj
      have hQ : ((w ᵥ* F) j : ℚ) = 6 * (a j : ℚ) := by linarith only [hj]
      have hZ : (w ᵥ* F) j = 6 * a j := by exact_mod_cast hQ
      refine ⟨2 * a j + n * F 0 j, ?_⟩
      rw [shift_vecMul, hZ]
      ring
  · rintro ⟨y, hPair, hy⟩
    let n : ℤ := (∑ i, y i) % 2
    let z : IntRow := y - Pi.single (0 : Fin 48) (3 * n)
    have hRestore : z + Pi.single (0 : Fin 48) (3 * n) = y := sub_add_cancel _ _
    have hSum : (∑ i, z i) = (∑ i, y i) - 3 * n := by
      simp only [z, Pi.sub_apply, Finset.sum_sub_distrib, Fintype.sum_pi_single']
    have hEven : (2 : ℤ) ∣ ∑ i, z i := by
      rw [hSum]
      dsimp only [n]
      omega
    have hSix (j : Fin 48) : (6 : ℤ) ∣ (z ᵥ* F) j := by
      obtain ⟨a, ha⟩ := (frame_even_iff z).2 hEven j
      obtain ⟨b, hb⟩ := hy j
      have hj := shift_vecMul z n j
      rw [hRestore, hb] at hj
      exact ⟨a - b + n * F 0 j, by omega⟩
    obtain ⟨a, ha, hLift⟩ := evenKernel_lift z hSix
    refine ⟨a, ha, n, ?_⟩
    calc
      x = fromHalfFrame (ratRow y) := by rw [← hPair, fromHalfFrame_halfFramePairings]
      _ = fromHalfFrame (ratRow z) + (n : ℚ) • halfFrameVector 0 := by
        rw [← fromHalfFrame_shift, hRestore]
      _ = _ := by rw [hLift]

/-- The column syndrome defined by the transpose of the actual frame rows. -/
abbrev frameSyndrome : (Fin 48 → ZMod 3) → (Fin 48 → ZMod 3) :=
  ternarySyndrome Fᵀ

/-- Reduce the integral half-frame coordinates modulo three. -/
def ternaryResidue (y : IntRow) : Fin 48 → ZMod 3 := fun j => (y j : ZMod 3)

theorem frameSyndrome_residue_eq_zero_iff (y : IntRow) :
    frameSyndrome (ternaryResidue y) = 0 ↔ ∀ j, (3 : ℤ) ∣ (y ᵥ* F) j := by
  have hCast (j : Fin 48) :
      frameSyndrome (ternaryResidue y) j = ((y ᵥ* F) j : ZMod 3) := by
    rw [← Matrix.mulVec_transpose F y]
    exact ((Int.castRingHom (ZMod 3)).map_mulVec Fᵀ y j).symm
  constructor
  · intro h j
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 ((hCast j).symm.trans (congrFun h j))
  · intro h
    funext j
    exact (hCast j).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (h j))

/-- Construction A for the kernel of the actual frame transpose modulo three. -/
theorem mem_oddNeighbor_iff_ternary (x : RatRow) :
    x ∈ oddNeighbor ↔
      ∃ y : IntRow, halfFramePairings x = ratRow y ∧ frameSyndrome (ternaryResidue y) = 0 := by
  simp only [mem_oddNeighbor_iff, frameSyndrome_residue_eq_zero_iff]

/-- The rational extension of the catalogue Gram pairing. -/
def cataloguePairing (x z : RatRow) : ℚ := (x ᵥ* castMatrix G) ⬝ᵥ z

/-- The pairings give the Construction A normalization of the dot product. -/
theorem cataloguePairing_eq (x z : RatRow) :
    cataloguePairing x z = (halfFramePairings x ⬝ᵥ halfFramePairings z) / 3 := by
  have hGram : castMatrix P * (castMatrix P)ᵀ = (12 : ℚ) • castMatrix G := by
    simpa only [map_mul, castMatrix_transpose, castMatrix_twelve_smul] using
      congrArg castMatrix p48pPairingFrame_mul_transpose
  have hDot : (x ᵥ* castMatrix P) ⬝ᵥ (z ᵥ* castMatrix P) = 12 * cataloguePairing x z := by
    rw [← Matrix.mulVec_transpose (castMatrix P) z, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hGram, Matrix.vecMul_smul, smul_dotProduct] <;> rfl
  simp only [halfFramePairings, Matrix.vecMul_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hDot] <;> ring

/-- A kernel distance above nine forces every positive norm at most three
in the neighbor onto a signed half-frame vector. -/
theorem short_norm_halfFramePairings
    (hKernel : ∀ u : Fin 48 → ZMod 3, hammingNorm u ≤ 9 → frameSyndrome u = 0 → u = 0)
    (x : RatRow) (hx : x ∈ oddNeighbor)
    (hPos : 0 < cataloguePairing x x) (hUpper : cataloguePairing x x ≤ 3) :
    ∃ i : Fin 48, halfFramePairings x = ratRow (Pi.single i 3) ∨
      halfFramePairings x = ratRow (Pi.single i (-3)) := by
  obtain ⟨y, hPair, hSyndrome⟩ := (mem_oddNeighbor_iff_ternary x).1 hx
  have hNorm : cataloguePairing x x = ((∑ j, y j ^ 2 : ℤ) : ℚ) / 3 := by
    rw [cataloguePairing_eq, hPair]
    simp only [dotProduct, ratRow, Int.cast_sum, pow_two, Int.cast_mul]
  have hSquares : (∑ j, y j ^ 2) ≤ 9 := by
    have hQ : ((∑ j, y j ^ 2 : ℤ) : ℚ) ≤ 9 := by linarith only [hNorm, hUpper]
    exact_mod_cast hQ
  have hWeight : hammingNorm (ternaryResidue y) ≤ 9 := by
    let support := Finset.univ.filter (fun j => ternaryResidue y j ≠ 0)
    have hBound : (hammingNorm (ternaryResidue y) : ℤ) ≤ ∑ j, y j ^ 2 := by
      calc
        _ = ∑ j ∈ support, (1 : ℤ) := by simp [hammingNorm, support]
        _ ≤ ∑ j ∈ support, y j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : ternaryResidue y j ≠ 0 := (Finset.mem_filter.mp hj).2
          have hne : y j ≠ 0 := fun hz => hj' (by simp [ternaryResidue, hz])
          have hSquare := sq_pos_of_ne_zero hne
          omega
        _ ≤ ∑ j, y j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => sq_nonneg (y j))
    have hBoundNine : (hammingNorm (ternaryResidue y) : ℤ) ≤ 9 := hBound.trans hSquares
    exact_mod_cast hBoundNine
  have hZero := hKernel (ternaryResidue y) hWeight hSyndrome
  have hDiv (j : Fin 48) : (3 : ℤ) ∣ y j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 (congrFun hZero j)
  choose w hw using hDiv
  have hScale : (∑ j, y j ^ 2) = 9 * ∑ j, w j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hw j] <;> ring
  have hSmall : (∑ j, w j ^ 2) ≤ 1 := by omega
  have hNonzero : ∃ i, w i ≠ 0 := by
    by_contra! h
    have hAll (j : Fin 48) : y j = 0 := by rw [hw j, h j, mul_zero]
    simp only [hAll, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
      Int.cast_zero, zero_div] at hNorm
    exact (ne_of_gt hPos) hNorm
  obtain ⟨i, hi⟩ := hNonzero
  have hErase := Finset.sum_erase_add (s := Finset.univ) (fun j => w j ^ 2) (Finset.mem_univ i)
  have hRest : 0 ≤ ∑ j ∈ (Finset.univ.erase i), w j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (w j)
  have hiSquare : w i ^ 2 = 1 := by
    have hiPos := sq_pos_of_ne_zero hi
    omega
  have hOff (j : Fin 48) (hji : j ≠ i) : w j = 0 := by
    by_contra hne
    have hLower : w j ^ 2 ≤ ∑ k ∈ (Finset.univ.erase i), w k ^ 2 :=
      Finset.single_le_sum (f := fun k => w k ^ 2) (fun k _ => sq_nonneg (w k))
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have hjPos := sq_pos_of_ne_zero hne
    omega
  have hSingle (c : ℤ) (hc : w i = c) : y = Pi.single i (3 * c) := by
    funext j
    by_cases hji : j = i
    · subst j
      rw [Pi.single_eq_same, hw i, hc]
    · have hAhead : i ≠ j := fun he => hji he.symm
      rw [Pi.single_eq_of_ne' (M := fun _ : Fin 48 => ℤ) hAhead (3 * c),
        hw j, hOff j hji, mul_zero]
  have hFactor : (w i - 1) * (w i + 1) = 0 := calc
    _ = w i ^ 2 - 1 := by ring
    _ = 0 := by rw [hiSquare, sub_self]
  refine ⟨i, ?_⟩
  rcases mul_eq_zero.mp hFactor with hPlus | hMinus
  · left
    have h := hSingle 1 (by omega)
    simpa only [mul_one, h] using hPair
  · right
    have h := hSingle (-1) (by omega)
    simpa only [mul_neg, mul_one, h] using hPair

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pOddNeighbor

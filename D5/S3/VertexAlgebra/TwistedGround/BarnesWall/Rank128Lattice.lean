/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank128Lattice
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/Rank128Lattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: The Barnes–Wall tensor Gram is even unimodular with the stated half-Gram cocycle. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8TraceSign
import Mathlib.Combinatorics.Colex
import Mathlib.LinearAlgebra.Matrix.Block
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The rank-128 Barnes–Wall tensor basis of Keller, Roberts and Roberts
(arXiv:2411.13646v2, Appendix A.1) in the word order of `Q8TraceSign`.
The normalized tensor rows use the two factors `(1, 0)` and `(1, 1)`.
Their integral Gram and its lower-triangular cocycle give the input to
the reflection-quotient ground representation. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank128Lattice

open Q8TraceSign (Word gramExponent gramMod8 halfGram halfGram_from_mod8)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeTwistedGroundRealization (Ground actual_twisted_ground_representation)
open LatticeTwistedGroundRealization.SignQuotient
open scoped BigOperators

open private weight from D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Q8TraceSign

/-- The integral Gram in increasing binary word order. -/
def gram : Matrix Word Word ℤ := fun u v => 2 ^ gramExponent u v

private def rowExponent (u : Word) : ℕ := (8 - weight u.val) / 2

private def rowFactor (u : Word) : ℚ := 2 ^ rowExponent u / 4

/-- The normalized tensor row for `u` is supported on the submasks of `u`. -/
def B : Matrix Word Word ℚ := fun u k =>
  if k.val &&& u.val = k.val then rowFactor u else 0

private abbrev bits (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

private theorem bits_and (a b : ℕ) : bits (a &&& b) = bits a ∩ bits b := by
  ext i
  simp only [bits, Finset.mem_inter, List.mem_toFinset, Nat.mem_bitIndices,
    Nat.testBit_and, Bool.and_eq_true]

private theorem submask_iff {a b : ℕ} : a &&& b = a ↔ bits a ⊆ bits b := by
  constructor
  · intro h
    have hbits := congrArg bits h
    rw [bits_and] at hbits
    exact Finset.inter_eq_left.mp hbits
  · intro h
    apply Finset.equivBitIndices.injective
    exact (bits_and a b).trans (Finset.inter_eq_left.mpr h)

private theorem bits_subset_range (u : Word) : bits u.val ⊆ Finset.range 7 := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra! h
  have hpow : 128 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h
  have hi' := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  exact (not_le_of_gt u.isLt) (hpow.trans hi')

-- This single-word check matches the finite trace file's seven-term weight formula.
set_option maxRecDepth 4096 in
private theorem weight_eq_filter_card : ∀ u : Word,
    ((Finset.range 7).filter fun i => u.val.testBit i).card = weight u.val := by
  decide +kernel

private theorem bits_card (u : Word) : (bits u.val).card = weight u.val := by
  rw [← weight_eq_filter_card u]
  apply congrArg Finset.card
  ext i
  constructor
  · intro hi
    exact Finset.mem_filter.mpr
      ⟨bits_subset_range u hi, Nat.mem_bitIndices.mp (List.mem_toFinset.mp hi)⟩
  · intro hi
    exact List.mem_toFinset.mpr (Nat.mem_bitIndices.mpr (Finset.mem_filter.mp hi).2)

private theorem weight_le_seven (u : Word) : weight u.val ≤ 7 := by
  simpa only [bits_card, Finset.card_range] using Finset.card_le_card (bits_subset_range u)

private theorem card_submasks (m : Word) :
    (Finset.univ.filter fun k : Word => k.val &&& m.val = k.val).card =
      2 ^ weight m.val := by
  rw [← bits_card m, ← Finset.card_powerset]
  refine Finset.card_bij (fun k _ => bits k.val) ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_powerset.mpr (submask_iff.mp (Finset.mem_filter.mp hk).2)
  · intro k _ l _ h
    exact Fin.ext (Finset.equivBitIndices.injective h)
  · intro s hs
    let k := Finset.equivBitIndices.symm s
    have hk : bits k = s := Finset.equivBitIndices.apply_symm_apply s
    have hkm : k &&& m.val = k := submask_iff.mpr (by
      rw [hk]
      exact Finset.mem_powerset.mp hs)
    have hle : k ≤ m.val := calc
      k = k &&& m.val := hkm.symm
      _ ≤ m.val := Nat.and_le_right
    exact ⟨⟨k, lt_of_le_of_lt hle m.isLt⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkm⟩, hk⟩

private def meetWord (u v : Word) : Word :=
  ⟨u.val &&& v.val, lt_of_le_of_lt Nat.and_le_left u.isLt⟩

private theorem submask_meet (k u v : Word) :
    k.val &&& (meetWord u v).val = k.val ↔
      k.val &&& u.val = k.val ∧ k.val &&& v.val = k.val := by
  simp only [submask_iff, meetWord, bits_and, Finset.subset_inter_iff]

-- The size of the word union bounds the numerator exponent from below.
private theorem exponent_add_four (u v : Word) :
    gramExponent u v + 4 = rowExponent u + rowExponent v + weight (u.val &&& v.val) := by
  have hinter := bits_card (meetWord u v)
  change (bits (u.val &&& v.val)).card = weight (u.val &&& v.val) at hinter
  rw [bits_and] at hinter
  have hunion : (bits u.val ∪ bits v.val).card ≤ 7 := by
    simpa only [Finset.card_range] using
      Finset.card_le_card (Finset.union_subset (bits_subset_range u) (bits_subset_range v))
  have hcard := Finset.card_union_add_card_inter (bits u.val) (bits v.val)
  rw [hinter, bits_card u, bits_card v] at hcard
  have hu := weight_le_seven u
  have hv := weight_le_seven v
  unfold gramExponent rowExponent
  omega

/-- The rational dot products of the normalized tensor rows give the integral Gram. -/
theorem gram_factorization : gram.map (Int.castRingHom ℚ) = B * B.transpose := by
  ext u v
  change (gram u v : ℚ) = (B * B.transpose) u v
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  let submasks := Finset.univ.filter (fun k : Word => k.val &&& (meetWord u v).val = k.val)
  have hsum : (∑ k : Word, B u k * B v k) = (submasks.card : ℚ) *
      (rowFactor u * rowFactor v) := by
    calc
      _ = ∑ k : Word, if k.val &&& (meetWord u v).val = k.val then
          rowFactor u * rowFactor v else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hu : k.val &&& u.val = k.val <;> by_cases hv : k.val &&& v.val = k.val <;>
          simp [B, submask_meet, hu, hv]
      _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcount : submasks.card = 2 ^ weight (u.val &&& v.val) := card_submasks (meetWord u v)
  rw [hsum, hcount]
  simp only [gram, rowFactor, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℚ) ^ gramExponent u v = 2 ^ (gramExponent u v + 4) / 16 := by
      rw [pow_add]
      ring
    _ = _ := by
      rw [exponent_add_four]
      simp only [pow_add]
      ring

private theorem B_lowerTriangular : B.IsLowerTriangular := by
  intro u v huv
  change u.val < v.val at huv
  have hn : v.val &&& u.val ≠ v.val := by
    intro h
    have hle : v.val &&& u.val ≤ u.val := Nat.and_le_right
    rw [h] at hle
    exact (not_le_of_gt huv) hle
  simp [B, hn]

-- On seven bits, `Fin.rev` sends `u` to `127 - u`, its bitwise complement.
set_option maxRecDepth 4096 in
private theorem complementary_exponents : ∀ u : Word,
    rowExponent u + rowExponent u.rev = 4 := by
  decide +kernel

private theorem B_det : B.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular B B_lowerTriangular]
  simp only [B, Nat.and_self, ite_true]
  refine Finset.prod_ninvolution Fin.rev ?_ ?_ (fun u => Finset.mem_univ u.rev) Fin.rev_rev
  · intro u
    calc
      rowFactor u * rowFactor u.rev = (2 : ℚ) ^ (rowExponent u + rowExponent u.rev) / 16 := by
        rw [pow_add]
        unfold rowFactor
        ring
      _ = 1 := by rw [complementary_exponents]; norm_num
  · intro u _ h
    have hval := congrArg Fin.val h
    simp only [Fin.val_rev] at hval
    have hu := u.isLt
    omega

theorem gram_det : gram.det = 1 := by
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_one, Int.cast_det]
  change (gram.map (Int.castRingHom ℚ)).det = 1
  rw [gram_factorization, Matrix.det_mul, Matrix.det_transpose, B_det, mul_one]

private theorem gram_symmetric (u v : Word) : gram u v = gram v u := by
  unfold gram gramExponent
  rw [Nat.and_comm v.val u.val,
    add_comm ((8 - weight v.val) / 2) ((8 - weight u.val) / 2)]

private theorem gram_diagonal_factor (u : Word) :
    gram u u = (2 : ℤ) ^ (gramExponent u u - 1) * 2 := by
  have h : gramExponent u u - 1 + 1 = gramExponent u u := by
    have hu := weight_le_seven u
    simp only [gramExponent, Nat.and_self]
    omega
  change (2 : ℤ) ^ gramExponent u u = _
  rw [← pow_succ, h]

/-- The rank-128 Barnes–Wall datum for the actual lattice fields. -/
def latticeData : LatticeData where
  rank := 128
  G := gram
  symmetric := gram_symmetric
  even_diagonal u := ⟨2 ^ (gramExponent u u - 1), by rw [gram_diagonal_factor, mul_two]⟩

private theorem residue_power (n : ℕ) :
    BinaryGauss.residue ((2 : ZMod 8) ^ n) = ((2 : ℤ) ^ n : F₂) := by
  rw [map_pow]
  rw [show BinaryGauss.residue (2 : ZMod 8) = ((2 : ℤ) : F₂) by decide]

/-- Reduce the strict lower Gram entries and the already halved diagonal. -/
theorem lowerMatrix_mod_two :
    (lowerMatrix latticeData).map (Int.castRingHom F₂) = Matrix.of halfGram := by
  have entry (u v : Word) : (lowerMatrix latticeData u v : F₂) = halfGram u v := by
    change (((if v < u then gram u v else 0) +
      (if v = u then gram u u / 2 else 0) : ℤ) : F₂) = halfGram u v
    rw [halfGram_from_mod8 u v]
    by_cases huv : u = v
    · subst v
      simp only [lt_irrefl, ite_false, ite_true, zero_add]
      rw [gram_diagonal_factor, Int.mul_ediv_cancel _ (by decide : (2 : ℤ) ≠ 0), residue_power]
      exact Int.cast_pow _ _
    · by_cases hvu : v < u
      · simp [huv, Ne.symm huv, hvu, gramMod8, residue_power, gram]
      · simp [huv, Ne.symm huv, hvu]
  exact Matrix.ext entry

/-- The actual reflection-quotient cocycle is the finite trace model's bilinear form. -/
theorem modTwoCocycle_eq_halfGram (a b : ModTwoCharge latticeData) :
    modTwoCocycle latticeData a b = (Matrix.of halfGram).toBilin' a b := by
  exact congrArg (fun M : Matrix Word Word F₂ => M.toBilin' a b) lowerMatrix_mod_two

/-- The same lattice datum supplies the irreducible negative-sign ground
representation of dimension `2 ^ 64`. -/
theorem actual_rank128_ground :
    ∃ ρ : Representation ℂ (Extension latticeData ⧸ K latticeData) (Ground 64),
      Representation.IsIrreducible ρ ∧
      ρ (QuotientGroup.mk (⟨1, 0⟩ : Extension latticeData)) =
        -(1 : Module.End ℂ (Ground 64)) ∧
      Module.finrank ℂ (Ground 64) = 2 ^ 64 := by
  have hu : IsUnit latticeData.G.det := by
    change IsUnit gram.det
    rw [gram_det]
    exact isUnit_one
  obtain ⟨n, ρ, hn, hirr, hsign, hdim, _⟩ := actual_twisted_ground_representation latticeData hu
  have hn' : n = 64 := by
    change 128 = n + n at hn
    omega
  subst n
  exact ⟨ρ, hirr, hsign, hdim⟩

#print axioms gram_det
#print axioms modTwoCocycle_eq_halfGram

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.Rank128Lattice

/- GID: D5/S3/Arith/Lattices/Golay/GolayEncoder
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Golay/GolayEncoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Lattices/Golay/IntegerLeech.minimum_norm; premises=D5/S3/Arith/Lattices/Golay/GolayEncoder.weight_spectrum
   digest: Explicit polynomial Golay encoder and kernel-checked weight reduction. -/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

open scoped BigOperators
open Matrix
namespace D5.S3.Arith.Lattices.Golay.GolayEncoder

abbrev F2 := ZMod 2
abbrev Message := Fin 12 → F2
abbrev Word := Fin 24 → F2

/-- Coefficients of X^11 + X^9 + X^7 + X^6 + X^5 + X + 1. -/
def generatorCoeff (k : ℕ) : F2 :=
  if k ∈ ({0, 1, 5, 6, 7, 9, 11} : Finset ℕ) then 1 else 0

/-- Columns are the twelve shifted generator words, followed by their parity bit.
The shifts have degree at most 22, so there is no cyclic wraparound. -/
def generator : Matrix (Fin 24) (Fin 12) F2 := fun i j =>
  if i.val < 23 then
    if j.val ≤ i.val then generatorCoeff (i.val - j.val) else 0
  else 1

/-- Elkies, Math 256x, Cyclic codes (2013), last page, uses the reciprocal
polynomial X^11+X^10+X^6+X^5+X^4+X^2+1. The parity coordinate is fixed. -/
def referenceGenerator : Matrix (Fin 24) (Fin 12) F2 := fun i j =>
  if i.val < 23 then
    if j.val ≤ i.val ∧ i.val-j.val ∈ ({0,2,4,5,6,10,11} : Finset ℕ) then 1 else 0
  else 1

def reverseCoordinate (i : Fin 24) : Fin 24 :=
  if h : i.val < 23 then ⟨22-i.val, by omega⟩ else i

private theorem reverseCoordinate_involutive : Function.Involutive reverseCoordinate := by
  intro i
  apply Fin.ext
  simp only [reverseCoordinate]
  split_ifs <;> simp_all only <;> omega

/-- Reverse the twenty-three cyclic coordinates and fix the extension coordinate. -/
def reverseCoordinateEquiv : Fin 24 ≃ Fin 24 where
  toFun := reverseCoordinate
  invFun := reverseCoordinate
  left_inv := reverseCoordinate_involutive
  right_inv := reverseCoordinate_involutive

private theorem reference_generator_reverse :
    referenceGenerator = generator.submatrix reverseCoordinateEquiv Fin.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Carryless multiplication by the given polynomial, then parity extension. -/
def encode : Message →ₗ[F2] Word := generator.mulVecLin

/-- This is an exact encoder identification, including the message and coordinate
permutations; it does not replace the approved generator by a code hypothesis. -/
theorem reference_encoder_identification :
    referenceGenerator.mulVecLin =
      (LinearMap.funLeft F2 F2 reverseCoordinateEquiv).comp
        (encode.comp (LinearMap.funLeft F2 F2 (Fin.rev : Fin 12 → Fin 12))) := by
  rw [reference_generator_reverse]
  have h := Matrix.mulVecLin_submatrix reverseCoordinateEquiv
    (⟨Fin.rev, Fin.rev, Fin.rev_involutive, Fin.rev_involutive⟩ : Fin 12 ≃ Fin 12) generator
  change (generator.submatrix reverseCoordinateEquiv Fin.rev).mulVecLin =
    (LinearMap.funLeft F2 F2 reverseCoordinateEquiv).comp
      (generator.mulVecLin.comp (LinearMap.funLeft F2 F2 (Fin.rev : Fin 12 → Fin 12))) at h
  exact h

/-- The 24th coordinate is precisely the parity extension of the first 23. -/
theorem parity_extension (m : Message) :
    encode m 23 = ∑ i : Fin 23, encode m i.castSucc := by
  have hc : ∀ j : Fin 12, (∑ i : Fin 23, generator i.castSucc j) = 1 := by
    intro j
    fin_cases j <;> decide +kernel
  have hp : ∀ j : Fin 12, generator 23 j = 1 := by intro j; simp [generator]
  change (∑ j, generator 23 j * m j) = ∑ i : Fin 23, ∑ j, generator i.castSucc j * m j
  simp_rw [hp, one_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hc, one_mul]

def code : Submodule F2 Word := LinearMap.range encode

/-- The truncated inverse power series has coefficient mask 0x49f. -/
private def decoder : Matrix (Fin 12) (Fin 24) F2 := fun i j =>
  if j.val ≤ i.val ∧ i.val - j.val ∈ ({0,1,2,3,4,7,10} : Finset ℕ) then 1 else 0

private theorem decoder_generator : decoder * generator = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem encode_injective : Function.Injective encode := by
  have h : Function.LeftInverse decoder.mulVecLin encode := by
    intro m
    change decoder *ᵥ (generator *ᵥ m) = m
    rw [Matrix.mulVec_mulVec, decoder_generator, Matrix.one_mulVec]
  exact h.injective

theorem code_finrank : Module.finrank F2 code = 12 := by
  unfold code
  rw [LinearMap.finrank_range_of_inj encode_injective]
  simp

theorem code_card : Nat.card code = 4096 := by
  unfold code
  have e := LinearEquiv.ofInjective encode encode_injective
  rw [Nat.card_congr e.toEquiv.symm]
  simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

/-- All 4096 ordinary twelve-bit messages, without discarding leading zeroes. -/
def message (n : ℕ) : Message := fun i => if n.testBit i.val then 1 else 0

private theorem message_injective : Function.Injective (fun n : Fin 4096 => message n.val) := by
  intro n m h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have h' := congrFun h ⟨i, hi⟩
    change (if n.val.testBit i then (1 : F2) else 0) =
      (if m.val.testBit i then 1 else 0) at h'
    cases hn : n.val.testBit i <;> cases hm : m.val.testBit i <;> simp_all
  · have hp : 4096 ≤ 2^i := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 12 ≤ i)
      norm_num at this ⊢
      exact this
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le n.isLt hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le m.isLt hp)]

private theorem message_surjective : Function.Surjective (fun n : Fin 4096 => message n.val) := by
  apply ((Fintype.bijective_iff_injective_and_card _).2 ⟨message_injective, ?_⟩).2
  simp [Fintype.card_pi, ZMod.card]

/-- Actual Hamming weight on all 24 coordinates. -/
def weight (v : Word) : ℕ := ∑ i, if v i = 0 then 0 else 1

private theorem weight_zero_iff (v : Word) : weight v = 0 ↔ v = 0 := by
  simp only [weight, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _),
    Finset.mem_univ, forall_const]
  constructor
  · intro h; ext i; have := h i; split_ifs at this with hi <;> simp_all
  · intro h; subst v; simp

private abbrev WeightSpectrum (n : ℕ) : Prop :=
  let w := weight (encode (message n))
  w = 0 ∨ w = 8 ∨ w = 12 ∨ w = 16 ∨ w = 24

private theorem block_0 : ∀ lo : Fin 64, WeightSpectrum (0 * 64 + lo.val) := by decide +kernel
private theorem block_1 : ∀ lo : Fin 64, WeightSpectrum (1 * 64 + lo.val) := by decide +kernel
private theorem block_2 : ∀ lo : Fin 64, WeightSpectrum (2 * 64 + lo.val) := by decide +kernel
private theorem block_3 : ∀ lo : Fin 64, WeightSpectrum (3 * 64 + lo.val) := by decide +kernel
private theorem block_4 : ∀ lo : Fin 64, WeightSpectrum (4 * 64 + lo.val) := by decide +kernel
private theorem block_5 : ∀ lo : Fin 64, WeightSpectrum (5 * 64 + lo.val) := by decide +kernel
private theorem block_6 : ∀ lo : Fin 64, WeightSpectrum (6 * 64 + lo.val) := by decide +kernel
private theorem block_7 : ∀ lo : Fin 64, WeightSpectrum (7 * 64 + lo.val) := by decide +kernel
private theorem block_8 : ∀ lo : Fin 64, WeightSpectrum (8 * 64 + lo.val) := by decide +kernel
private theorem block_9 : ∀ lo : Fin 64, WeightSpectrum (9 * 64 + lo.val) := by decide +kernel
private theorem block_10 : ∀ lo : Fin 64, WeightSpectrum (10 * 64 + lo.val) := by decide +kernel
private theorem block_11 : ∀ lo : Fin 64, WeightSpectrum (11 * 64 + lo.val) := by decide +kernel
private theorem block_12 : ∀ lo : Fin 64, WeightSpectrum (12 * 64 + lo.val) := by decide +kernel
private theorem block_13 : ∀ lo : Fin 64, WeightSpectrum (13 * 64 + lo.val) := by decide +kernel
private theorem block_14 : ∀ lo : Fin 64, WeightSpectrum (14 * 64 + lo.val) := by decide +kernel
private theorem block_15 : ∀ lo : Fin 64, WeightSpectrum (15 * 64 + lo.val) := by decide +kernel
private theorem block_16 : ∀ lo : Fin 64, WeightSpectrum (16 * 64 + lo.val) := by decide +kernel
private theorem block_17 : ∀ lo : Fin 64, WeightSpectrum (17 * 64 + lo.val) := by decide +kernel
private theorem block_18 : ∀ lo : Fin 64, WeightSpectrum (18 * 64 + lo.val) := by decide +kernel
private theorem block_19 : ∀ lo : Fin 64, WeightSpectrum (19 * 64 + lo.val) := by decide +kernel
private theorem block_20 : ∀ lo : Fin 64, WeightSpectrum (20 * 64 + lo.val) := by decide +kernel
private theorem block_21 : ∀ lo : Fin 64, WeightSpectrum (21 * 64 + lo.val) := by decide +kernel
private theorem block_22 : ∀ lo : Fin 64, WeightSpectrum (22 * 64 + lo.val) := by decide +kernel
private theorem block_23 : ∀ lo : Fin 64, WeightSpectrum (23 * 64 + lo.val) := by decide +kernel
private theorem block_24 : ∀ lo : Fin 64, WeightSpectrum (24 * 64 + lo.val) := by decide +kernel
private theorem block_25 : ∀ lo : Fin 64, WeightSpectrum (25 * 64 + lo.val) := by decide +kernel
private theorem block_26 : ∀ lo : Fin 64, WeightSpectrum (26 * 64 + lo.val) := by decide +kernel
private theorem block_27 : ∀ lo : Fin 64, WeightSpectrum (27 * 64 + lo.val) := by decide +kernel
private theorem block_28 : ∀ lo : Fin 64, WeightSpectrum (28 * 64 + lo.val) := by decide +kernel
private theorem block_29 : ∀ lo : Fin 64, WeightSpectrum (29 * 64 + lo.val) := by decide +kernel
private theorem block_30 : ∀ lo : Fin 64, WeightSpectrum (30 * 64 + lo.val) := by decide +kernel
private theorem block_31 : ∀ lo : Fin 64, WeightSpectrum (31 * 64 + lo.val) := by decide +kernel
private theorem block_32 : ∀ lo : Fin 64, WeightSpectrum (32 * 64 + lo.val) := by decide +kernel
private theorem block_33 : ∀ lo : Fin 64, WeightSpectrum (33 * 64 + lo.val) := by decide +kernel
private theorem block_34 : ∀ lo : Fin 64, WeightSpectrum (34 * 64 + lo.val) := by decide +kernel
private theorem block_35 : ∀ lo : Fin 64, WeightSpectrum (35 * 64 + lo.val) := by decide +kernel
private theorem block_36 : ∀ lo : Fin 64, WeightSpectrum (36 * 64 + lo.val) := by decide +kernel
private theorem block_37 : ∀ lo : Fin 64, WeightSpectrum (37 * 64 + lo.val) := by decide +kernel
private theorem block_38 : ∀ lo : Fin 64, WeightSpectrum (38 * 64 + lo.val) := by decide +kernel
private theorem block_39 : ∀ lo : Fin 64, WeightSpectrum (39 * 64 + lo.val) := by decide +kernel
private theorem block_40 : ∀ lo : Fin 64, WeightSpectrum (40 * 64 + lo.val) := by decide +kernel
private theorem block_41 : ∀ lo : Fin 64, WeightSpectrum (41 * 64 + lo.val) := by decide +kernel
private theorem block_42 : ∀ lo : Fin 64, WeightSpectrum (42 * 64 + lo.val) := by decide +kernel
private theorem block_43 : ∀ lo : Fin 64, WeightSpectrum (43 * 64 + lo.val) := by decide +kernel
private theorem block_44 : ∀ lo : Fin 64, WeightSpectrum (44 * 64 + lo.val) := by decide +kernel
private theorem block_45 : ∀ lo : Fin 64, WeightSpectrum (45 * 64 + lo.val) := by decide +kernel
private theorem block_46 : ∀ lo : Fin 64, WeightSpectrum (46 * 64 + lo.val) := by decide +kernel
private theorem block_47 : ∀ lo : Fin 64, WeightSpectrum (47 * 64 + lo.val) := by decide +kernel
private theorem block_48 : ∀ lo : Fin 64, WeightSpectrum (48 * 64 + lo.val) := by decide +kernel
private theorem block_49 : ∀ lo : Fin 64, WeightSpectrum (49 * 64 + lo.val) := by decide +kernel
private theorem block_50 : ∀ lo : Fin 64, WeightSpectrum (50 * 64 + lo.val) := by decide +kernel
private theorem block_51 : ∀ lo : Fin 64, WeightSpectrum (51 * 64 + lo.val) := by decide +kernel
private theorem block_52 : ∀ lo : Fin 64, WeightSpectrum (52 * 64 + lo.val) := by decide +kernel
private theorem block_53 : ∀ lo : Fin 64, WeightSpectrum (53 * 64 + lo.val) := by decide +kernel
private theorem block_54 : ∀ lo : Fin 64, WeightSpectrum (54 * 64 + lo.val) := by decide +kernel
private theorem block_55 : ∀ lo : Fin 64, WeightSpectrum (55 * 64 + lo.val) := by decide +kernel
private theorem block_56 : ∀ lo : Fin 64, WeightSpectrum (56 * 64 + lo.val) := by decide +kernel
private theorem block_57 : ∀ lo : Fin 64, WeightSpectrum (57 * 64 + lo.val) := by decide +kernel
private theorem block_58 : ∀ lo : Fin 64, WeightSpectrum (58 * 64 + lo.val) := by decide +kernel
private theorem block_59 : ∀ lo : Fin 64, WeightSpectrum (59 * 64 + lo.val) := by decide +kernel
private theorem block_60 : ∀ lo : Fin 64, WeightSpectrum (60 * 64 + lo.val) := by decide +kernel
private theorem block_61 : ∀ lo : Fin 64, WeightSpectrum (61 * 64 + lo.val) := by decide +kernel
private theorem block_62 : ∀ lo : Fin 64, WeightSpectrum (62 * 64 + lo.val) := by decide +kernel
private theorem block_63 : ∀ lo : Fin 64, WeightSpectrum (63 * 64 + lo.val) := by decide +kernel

private theorem blocks_spectrum (b l : Fin 64) :
    WeightSpectrum (b.val * 64 + l.val) := by
  fin_cases b
  · exact block_0 l
  · exact block_1 l
  · exact block_2 l
  · exact block_3 l
  · exact block_4 l
  · exact block_5 l
  · exact block_6 l
  · exact block_7 l
  · exact block_8 l
  · exact block_9 l
  · exact block_10 l
  · exact block_11 l
  · exact block_12 l
  · exact block_13 l
  · exact block_14 l
  · exact block_15 l
  · exact block_16 l
  · exact block_17 l
  · exact block_18 l
  · exact block_19 l
  · exact block_20 l
  · exact block_21 l
  · exact block_22 l
  · exact block_23 l
  · exact block_24 l
  · exact block_25 l
  · exact block_26 l
  · exact block_27 l
  · exact block_28 l
  · exact block_29 l
  · exact block_30 l
  · exact block_31 l
  · exact block_32 l
  · exact block_33 l
  · exact block_34 l
  · exact block_35 l
  · exact block_36 l
  · exact block_37 l
  · exact block_38 l
  · exact block_39 l
  · exact block_40 l
  · exact block_41 l
  · exact block_42 l
  · exact block_43 l
  · exact block_44 l
  · exact block_45 l
  · exact block_46 l
  · exact block_47 l
  · exact block_48 l
  · exact block_49 l
  · exact block_50 l
  · exact block_51 l
  · exact block_52 l
  · exact block_53 l
  · exact block_54 l
  · exact block_55 l
  · exact block_56 l
  · exact block_57 l
  · exact block_58 l
  · exact block_59 l
  · exact block_60 l
  · exact block_61 l
  · exact block_62 l
  · exact block_63 l

private theorem all_messages_spectrum (n : Fin 4096) : WeightSpectrum n.val := by
  have hi : n.val / 64 < 64 := by omega
  have lo : n.val % 64 < 64 := Nat.mod_lt _ (by decide)
  let b : Fin 64 := ⟨n.val / 64, hi⟩
  let l : Fin 64 := ⟨n.val % 64, lo⟩
  have hn : b.val * 64 + l.val = n.val := by
    dsimp [b, l]
    omega
  exact hn ▸ blocks_spectrum b l


theorem weight_spectrum (v : Word) (hv : v ∈ code) :
    weight v = 0 ∨ weight v = 8 ∨ weight v = 12 ∨ weight v = 16 ∨ weight v = 24 := by
  obtain ⟨m, rfl⟩ := hv
  obtain ⟨n, rfl⟩ := message_surjective m
  exact all_messages_spectrum n

theorem doubly_even (v : Word) (hv : v ∈ code) : 4 ∣ weight v := by
  rcases weight_spectrum v hv with h | h | h | h | h <;> rw [h] <;> norm_num

theorem minimum_weight (v : Word) (hv : v ∈ code) (hn : v ≠ 0) : 8 ≤ weight v := by
  have hn' : weight v ≠ 0 := mt (weight_zero_iff v).mp hn
  rcases weight_spectrum v hv with h | h | h | h | h <;> omega

theorem all_ones_mem : (fun _ : Fin 24 => (1 : F2)) ∈ code := by
  refine ⟨message 3189, ?_⟩
  ext i
  fin_cases i <;> decide +kernel

def octad : Word := encode (message 1)

theorem octad_mem : octad ∈ code := ⟨message 1, rfl⟩

theorem octad_weight : weight octad = 8 := by decide +kernel

private theorem gram_zero : generator.transpose * generator = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem self_orthogonal (v w : Word) (hv : v ∈ code) (hw : w ∈ code) :
    dotProduct v w = 0 := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨b, rfl⟩ := hw
  change dotProduct (generator *ᵥ a) (generator *ᵥ b) = 0
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, gram_zero,
    Matrix.vecMul_zero, zero_dotProduct]

def coordinatePairing : LinearMap.BilinForm F2 Word :=
  dotProductBilin F2 F2

/-- Auxiliary splitting matrix. Its row masks were obtained from (I + GD)Dᵀ.
Only the following kernel-checked matrix identity is used in the proof. -/
private def complement : Matrix (Fin 24) (Fin 12) F2 := fun i j =>
  if (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 10, 20, 40, 83, 165, 329, 658, 1319, 2638, 1] : Fin 24 → ℕ) i |>.testBit j.val then 1 else 0
private theorem decomposition : generator * decoder + complement * generator.transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Self-duality for the actual binary coordinate pairing, by exact matrix reconstruction. -/
theorem self_dual : coordinatePairing.orthogonal code = code := by
  apply le_antisymm
  · intro v hv
    have ht : generator.transpose *ᵥ v = 0 := by
      apply dotProduct_eq_zero
      intro a
      rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) (encode a) ⟨a, rfl⟩
    refine ⟨decoder *ᵥ v, ?_⟩
    change generator *ᵥ (decoder *ᵥ v) = v
    have h := congrArg (fun A : Matrix (Fin 24) (Fin 24) F2 => A *ᵥ v) decomposition
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ht, Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
    exact h
  · intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    change dotProduct w v = 0
    exact self_orthogonal w v hw hv

#print axioms encode_injective
#print axioms weight_spectrum
#print axioms self_dual
end D5.S3.Arith.Lattices.Golay.GolayEncoder

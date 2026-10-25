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

private theorem reference_generator_reverse :
    referenceGenerator = generator.submatrix reverseCoordinate Fin.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Carryless multiplication by the given polynomial, then parity extension. -/
def encode : Message →ₗ[F2] Word := generator.mulVecLin

/-- This is an exact encoder identification, including the message and coordinate
permutations; it does not replace the approved generator by a code hypothesis. -/
theorem reference_encoder_identification :
    referenceGenerator.mulVecLin =
      (LinearMap.funLeft F2 F2 reverseCoordinate).comp
        (encode.comp (LinearMap.funLeft F2 F2 (Fin.rev : Fin 12 → Fin 12))) := by
  rw [reference_generator_reverse]
  have h := Matrix.mulVecLin_submatrix reverseCoordinate
    (⟨Fin.rev, Fin.rev, Fin.rev_involutive, Fin.rev_involutive⟩ : Fin 12 ≃ Fin 12) generator
  change (generator.submatrix reverseCoordinate Fin.rev).mulVecLin =
    (LinearMap.funLeft F2 F2 reverseCoordinate).comp
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

private theorem coordinatePairing_symm : coordinatePairing.IsSymm := by
  constructor
  intro v w
  change dotProduct v w = dotProduct w v
  exact dotProduct_comm v w

private theorem coordinatePairing_nondegenerate : coordinatePairing.Nondegenerate := by
  apply coordinatePairing_symm.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro v h
  exact dotProduct_eq_zero v h

/-- Self-duality for the standard nondegenerate binary coordinate pairing. -/
set_option diagnostics true in
theorem self_dual : LinearMap.BilinForm.orthogonal (R := F2) (M := Word)
    coordinatePairing code = code := by
  have hc : code ≤ coordinatePairing.orthogonal code := by
    intro v hv w hw
    exact self_orthogonal w v hw hv
  have hr := LinearMap.BilinForm.finrank_orthogonal coordinatePairing_nondegenerate code
  have hdim : Module.finrank F2 Word = 24 := by simp
  rw [code_finrank, hdim] at hr
  exact (Submodule.eq_of_le_of_finrank_le hc (by rw [code_finrank, hr])).symm

#print axioms encode_injective
#print axioms self_dual
end D5.S3.Arith.Lattices.Golay.GolayEncoder

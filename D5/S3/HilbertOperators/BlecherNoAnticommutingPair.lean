/- GID: D5/S3/HilbertOperators/BlecherNoAnticommutingPair
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/BlecherNoAnticommutingPair
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim; result=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.result; claim=D5/S3/HilbertOperators/BlecherNoAnticommutingPair.claim
   digest: A finite symmetric operator algebra excludes nonzero anticommuting products. -/

import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.LinearCombination

/-! A symmetric operator algebra answering the question in Blecher, Example 5.5
(arXiv:2509.17673v2). Its multiplication is the unconjugated outer product of
the row coordinates, with the product in a two-sided annihilator. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.longLine false

noncomputable section
namespace D5.S3.HilbertOperators.BlecherNoAnticommutingPair

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

/-- The necessity of a nonzero anticommuting product in a noncommutative symmetric
matrix algebra, at ambient size sixteen. -/
def claim : Prop :=
  ∀ A : Submodule ℂ (Matrix (Fin 16) (Fin 16) ℂ),
    (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) →
    (∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) →
    (∀ k (x : Matrix (Fin k) (Fin k) (Matrix (Fin 16) (Fin 16) ℂ)),
      (∀ i j, x i j ∈ A) →
      ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖) →
    ∃ x ∈ A, ∃ y ∈ A, x * y = -(y * x) ∧ x * y ≠ 0

variable {m : ℕ}

private abbrev Row (m : ℕ) := Fin (m + 1) → ℂ
private abbrev Coord (m : ℕ) := Row m × Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ
private abbrev Probe (m : ℕ) := Fin (m + 1) × Fin (m + 1)
private abbrev Slot (m : ℕ) := Option (Option (Fin (m + 1)))

-- The middle slot has size m + 1. Probe (i,j) uses the swap of i and j.
-- The sign selects a diagonal reflection or distinguishes the two orders of a swap.
private def probeSwap (t : Probe m) : Equiv.Perm (Fin (m + 1)) := Equiv.swap t.1 t.2

private def probeSign (t : Probe m) (i : Fin (m + 1)) : ℂ :=
  if (t.1 = t.2 ∧ t.1 ≠ Fin.last m ∧ i = t.1) ∨ (t.2 < t.1 ∧ i = t.2)
  then -1 else 1

private lemma probeSign_sq (t : Probe m) (i : Fin (m + 1)) :
    probeSign t i * probeSign t i = 1 := by
  unfold probeSign
  split_ifs <;> norm_num

private lemma probeSign_star (t : Probe m) (i : Fin (m + 1)) :
    star (probeSign t i) = probeSign t i := by
  unfold probeSign
  split_ifs <;> simp

private def readout (t : Probe m) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : ℂ :=
  ∑ i, probeSign t i * Z i (probeSwap t i)

-- On the outer slots, none is the first coordinate and some none is the last.
private def block (t : Probe m) (x : Coord m) : Matrix (Slot m) (Slot m) ℂ :=
  Matrix.of fun
  | none, some (some j) => x.1 j
  | none, some none => readout t x.2
  | some (some i), some none => probeSign t i * x.1 (probeSwap t i)
  | _, _ => 0

private def blockLinear (t : Probe m) : Coord m →ₗ[ℂ] Matrix (Slot m) (Slot m) ℂ where
  toFun := block t
  map_add' x y := by
    apply Matrix.ext
    rintro (_ | (_ | i)) (_ | (_ | j)) <;>
      simp [block, readout, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Matrix.ext
    rintro (_ | (_ | i)) (_ | (_ | j)) <;>
      simp [block, readout, Matrix.smul_apply, ← Finset.mul_sum, mul_left_comm]

private lemma block_mul (t : Probe m) (x y : Coord m) :
    block t x * block t y = block t (0, vecMulVec x.1 y.1) := by
  apply Matrix.ext
  rintro (_ | (_ | i)) (_ | (_ | j)) <;>
    simp [Matrix.mul_apply, Fintype.sum_option, block, readout, vecMulVec_apply, mul_left_comm]

private def slotSwap (t : Probe m) : Equiv.Perm (Slot m) :=
  (Equiv.optionCongr (Equiv.optionCongr (probeSwap t))).trans (Equiv.swap none (some none))

private lemma slotSwap_top (t : Probe m) : slotSwap t none = some none := rfl
private lemma slotSwap_bottom (t : Probe m) : slotSwap t (some none) = none := rfl
private lemma slotSwap_middle (t : Probe m) (i : Fin (m + 1)) :
    slotSwap t (some (some i)) = some (some (probeSwap t i)) := rfl

private lemma slotSwap_involutive (t : Probe m) (i : Slot m) :
    slotSwap t (slotSwap t i) = i := by
  rcases i with _ | (i | i) <;>
    simp [slotSwap_top, slotSwap_bottom, slotSwap_middle, probeSwap, Equiv.swap_apply_self]

private def slotSign (t : Probe m) : Slot m → ℂ
  | some (some i) => probeSign t i
  | _ => 1

private lemma slotSign_sq (t : Probe m) (i : Slot m) : slotSign t i * slotSign t i = 1 := by
  rcases i with _ | (i | i) <;> simp [slotSign, probeSign_sq]

private lemma slotSign_star (t : Probe m) (i : Slot m) : star (slotSign t i) = slotSign t i := by
  rcases i with _ | (i | i) <;> simp [slotSign, probeSign_star]

private def flipBlock (t : Probe m) : Matrix (Slot m) (Slot m) ℂ :=
  Matrix.of fun i j => if j = slotSwap t i then slotSign t i else 0

private lemma flip_mul (t : Probe m) (X : Matrix (Slot m) (Slot m) ℂ) (i j : Slot m) :
    (flipBlock t * X) i j = slotSign t i * X (slotSwap t i) j := by
  simp [Matrix.mul_apply, flipBlock, ite_mul, Finset.sum_ite_eq']

private lemma mul_flip (t : Probe m) (X : Matrix (Slot m) (Slot m) ℂ) (i j : Slot m) :
    (X * flipBlock t) i j = X i (slotSwap t j) * slotSign t (slotSwap t j) := by
  have h (a : Slot m) : j = slotSwap t a ↔ a = slotSwap t j := by
    constructor
    · intro h
      rw [h, slotSwap_involutive]
    · intro h
      rw [h, slotSwap_involutive]
  simp [Matrix.mul_apply, flipBlock, h, mul_ite, Finset.sum_ite_eq']

private lemma flipBlock_unitary (t : Probe m) : flipBlock t ∈ unitary (Matrix (Slot m) (Slot m) ℂ) := by
  constructor
  · apply Matrix.ext
    intro i j
    rw [mul_flip, Matrix.star_apply]
    simp only [flipBlock, Matrix.of_apply, apply_ite star, star_zero, slotSign_star, Matrix.one_apply]
    by_cases h : i = j
    · simp [h, slotSign_sq, slotSwap_involutive]
    · simp [h, slotSwap_involutive]
  · apply Matrix.ext
    intro i j
    rw [flip_mul, Matrix.star_apply]
    simp only [flipBlock, Matrix.of_apply, apply_ite star, star_zero, slotSign_star, Matrix.one_apply]
    by_cases h : i = j <;> simp [h, slotSign_sq]

private lemma flipBlock_transpose (t : Probe m) (x : Coord m) :
    flipBlock t * (block t x)ᵀ * flipBlock t = block t x := by
  apply Matrix.ext
  rintro (_ | (_ | i)) (_ | (_ | j)) <;>
    simp [mul_flip, flip_mul, transpose_apply, slotSwap_top, slotSwap_bottom,
      slotSwap_middle, block, slotSign, probeSwap, Equiv.swap_apply_self,
      mul_assoc]
  rw [mul_comm (x.1 j), ← mul_assoc, probeSign_sq, one_mul]

private def baseProbe (m : ℕ) : Probe m := (Fin.last m, Fin.last m)

private lemma probe_diagonal (i : Fin (m + 1)) (a : Fin (m + 1)) :
    probeSign (i, i) a = if i ≠ Fin.last m ∧ a = i then -1 else 1 := by simp [probeSign]

private lemma probe_positive {i j : Fin (m + 1)} (h : i < j) (a : Fin (m + 1)) :
    probeSign (i, j) a = 1 := by simp [probeSign, h.ne, not_lt_of_ge h.le]

private lemma probe_negative {i j : Fin (m + 1)} (h : i < j) (a : Fin (m + 1)) :
    probeSign (j, i) a = if a = i then -1 else 1 := by simp [probeSign, h.ne.symm, h]

private lemma readout_base (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    readout (baseProbe m) Z = ∑ a, Z a a := by
  simp [readout, baseProbe, probe_diagonal, probeSwap]

private lemma readout_diagonal (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (i : Fin (m + 1)) (hi : i ≠ Fin.last m) :
    readout (baseProbe m) Z - readout (i, i) Z = 2 * Z i i := by
  rw [readout_base]
  simp only [readout, probe_diagonal, probeSwap, Equiv.swap_self,
    Equiv.refl_apply, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ a, if a = i then 2 * Z i i else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a = i
      · subst a
        simp [hi]
        ring
      · simp [h]
    _ = _ := by simp

private lemma readout_signed_swap (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    {i j : Fin (m + 1)} (hij : i < j) :
    readout (i, j) Z - readout (j, i) Z = 2 * Z i j := by
  simp only [readout, probe_positive hij, probe_negative hij, probeSwap,
    one_mul, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ a, if a = i then 2 * Z i j else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a = i
      · subst a
        simp
        ring
      · simp [h, Equiv.swap_comm j i]
    _ = _ := by simp

private lemma readout_swap (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    {i j : Fin (m + 1)} (hij : i < j) :
    readout (i, j) Z - readout (baseProbe m) Z =
      (Z i j - Z i i) + (Z j i - Z j j) := by
  rw [readout_base]
  simp only [readout, probe_positive hij, probeSwap, one_mul, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ a, ((if a = i then Z i j - Z i i else 0) + (if a = j then Z j i - Z j j else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hi : a = i
      · subst a; simp [hij.ne]
      by_cases hj : a = j
      · subst a; simp [hij.ne.symm]
      simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]
    _ = _ := by simp [Finset.sum_add_distrib]

private lemma readout_injective (Z W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (h : ∀ t, readout t Z = readout t W) : Z = W := by
  have diag (i : Fin (m + 1)) (hi : i ≠ Fin.last m) : Z i i = W i i := by
    have hz := readout_diagonal Z i hi
    have hw := readout_diagonal W i hi
    rw [h, h, hw] at hz
    linear_combination -hz / 2
  have last : Z (Fin.last m) (Fin.last m) = W (Fin.last m) (Fin.last m) := by
    have hb := h (baseProbe m)
    rw [readout_base, readout_base] at hb
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (Fin.last m)),
        ← Finset.sum_erase_add Finset.univ (fun a => W a a) (Finset.mem_univ (Fin.last m))] at hb
    have hs : ∑ a ∈ Finset.univ.erase (Fin.last m), Z a a =
        ∑ a ∈ Finset.univ.erase (Fin.last m), W a a :=
      Finset.sum_congr rfl fun a ha => diag a (Finset.ne_of_mem_erase ha)
    exact add_left_cancel (hs ▸ hb)
  have diag' (i : Fin (m + 1)) : Z i i = W i i := by
    by_cases hi : i = Fin.last m
    · simpa only [hi] using last
    · exact diag i hi
  have off {i j : Fin (m + 1)} (hij : i < j) : Z i j = W i j ∧ Z j i = W j i := by
    have hz := readout_signed_swap Z hij
    rw [h, h, readout_signed_swap W hij] at hz
    have hp : Z i j = W i j := by linear_combination -hz / 2
    have hs := readout_swap Z hij
    rw [h, h, readout_swap W hij, hp, diag', diag'] at hs
    exact ⟨hp, by linear_combination -hs⟩
  apply Matrix.ext
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (off hij).1
  · exact diag' i
  · exact (off hji).2

private abbrev Ambient (m : ℕ) := Fin ((m + 1) * (m + 1) * (m + 1 + 2))

private def slotIndex (m : ℕ) : Slot m ≃ Fin (m + 1 + 2) :=
  (Equiv.optionCongr (finSuccEquiv (m + 1)).symm).trans (finSuccEquiv (m + 1 + 1)).symm

private def index (m : ℕ) : Slot m × Probe m ≃ Ambient m :=
  (Equiv.prodComm _ _).trans ((finProdFinEquiv.prodCongr (slotIndex m)).trans finProdFinEquiv)

private def assembled : Coord m →ₗ[ℂ] Matrix (Slot m × Probe m) (Slot m × Probe m) ℂ where
  toFun x := blockDiagonal fun t => blockLinear t x
  map_add' x y := by
    rw [← blockDiagonal_add]
    congr
    funext t
    exact map_add (blockLinear t) x y
  map_smul' c x := by
    ext i j
    by_cases h : i.2 = j.2
    · simp [blockDiagonal_apply, h, Matrix.smul_apply]
    · simp [blockDiagonal_apply, h, Matrix.smul_apply]

private def representation : Coord m →ₗ[ℂ] Matrix (Ambient m) (Ambient m) ℂ :=
  (reindexAlgEquiv ℂ ℂ (index m)).toLinearMap.comp assembled

private lemma representation_mul (x y : Coord m) :
    representation x * representation y = representation (0, vecMulVec x.1 y.1) := by
  change reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal fun t => block t x) *
    reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal fun t => block t y) = _
  rw [← map_mul, ← blockDiagonal_mul]
  simp only [block_mul]
  rfl

private lemma representation_injective : Function.Injective (representation (m := m)) := by
  intro x y h
  have blocks (t : Probe m) (i j : Slot m) : block t x i j = block t y i j := by
    have h' : (blockDiagonal fun t => block t x) = (blockDiagonal fun t => block t y) :=
      (reindexAlgEquiv ℂ ℂ (index m)).injective h
    simpa only [blockDiagonal_apply_eq] using
      congrArg (fun a : Matrix (Slot m × Probe m) (Slot m × Probe m) ℂ => a (i, t) (j, t)) h'
  apply Prod.ext
  · funext i
    exact blocks (baseProbe m) none (some (some i))
  · apply readout_injective
    intro t
    exact blocks t none (some none)

private def flip (m : ℕ) : Matrix (Ambient m) (Ambient m) ℂ :=
  reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal (flipBlock (m := m)))

private lemma flip_unitary (m : ℕ) : flip m ∈ unitary (Matrix (Ambient m) (Ambient m) ℂ) := by
  have hstar (M : Matrix (Slot m × Probe m) (Slot m × Probe m) ℂ) :
      star (reindexAlgEquiv ℂ ℂ (index m) M) = reindexAlgEquiv ℂ ℂ (index m) (star M) := rfl
  constructor <;>
    simp only [flip, hstar, ← map_mul, ← map_one (reindexAlgEquiv ℂ ℂ (index m))]
  all_goals
    apply congrArg (reindexAlgEquiv ℂ ℂ (index m))
    simp only [Matrix.star_eq_conjTranspose, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    rw [← blockDiagonal_one]
    congr
    funext t
    first | exact (flipBlock_unitary t).1 | exact (flipBlock_unitary t).2

private lemma flip_transpose (x : Coord m) :
    flip m * (representation x)ᵀ * flip m = representation x := by
  have htranspose (M : Matrix (Slot m × Probe m) (Slot m × Probe m) ℂ) :
      (reindexAlgEquiv ℂ ℂ (index m) M)ᵀ = reindexAlgEquiv ℂ ℂ (index m) (Mᵀ) := rfl
  change reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal (flipBlock (m := m))) *
    (reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal fun t => block t x))ᵀ *
    reindexAlgEquiv ℂ ℂ (index m) (blockDiagonal (flipBlock (m := m))) = _
  rw [htranspose, ← map_mul, ← map_mul, blockDiagonal_transpose,
    ← blockDiagonal_mul, ← blockDiagonal_mul]
  simp only [flipBlock_transpose]
  rfl

private lemma amplified_norm (k : ℕ)
    (x : Matrix (Fin k) (Fin k) (Matrix (Ambient m) (Ambient m) ℂ))
    (hx : ∀ i j, x i j ∈ LinearMap.range representation) :
    ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖ := by
  let W := compRingEquiv (Fin k) (Ambient m) ℂ
  let D : Matrix (Fin k) (Fin k) (Matrix (Ambient m) (Ambient m) ℂ) := diagonal fun _ => flip m
  have hD : W D ∈ unitary (Matrix (Fin k × Ambient m) (Fin k × Ambient m) ℂ) := by
    have hstar : star (W D) = W (diagonal fun _ => star (flip m)) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      by_cases h : i = j
      · subst j
        simp [W, D, Matrix.star_apply, comp_apply]
      · simp [W, D, Matrix.star_apply, comp_apply, h, Ne.symm h]
    constructor <;> rw [hstar, ← map_mul, ← map_one W] <;> congr 1 <;>
      simp [D, diagonal_mul_diagonal, (flip_unitary m).1, (flip_unitary m).2, ← Matrix.diagonal_one]
  have hflip : W D * W (of (fun i j => (x i j)ᵀ)) * W D = W x := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Matrix.ext
    intro i j
    rw [mul_diagonal, diagonal_mul]
    obtain ⟨z, hz⟩ := hx i j
    change flip m * (x i j)ᵀ * flip m = x i j
    rw [← hz, flip_transpose]
  change ‖W (of (fun i j => (x i j)ᵀ))‖ = ‖W x‖
  rw [← hflip, CStarRing.norm_mul_mem_unitary _ hD, CStarRing.norm_mem_unitary_mul _ hD]

private lemma outer_eq_neg_swapped {r s : Row m}
    (h : vecMulVec r s = -(vecMulVec s r)) : vecMulVec r s = 0 := by
  by_cases hr : r = 0
  · simp [hr]
  have ⟨i, hi⟩ : ∃ i, r i ≠ 0 := Function.ne_iff.mp hr
  have entry (i j : Fin (m + 1)) : r i * s j = -(s i * r j) :=
    congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ => M i j) h
  have hdiag : (2 : ℂ) * (r i * s i) = 0 := by
    linear_combination entry i i
  have hsi : s i = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hdiag).resolve_left (by norm_num))).resolve_left hi
  have hs : s = 0 := by
    funext j
    exact (mul_eq_zero.mp (by simpa [hsi] using entry i j)).resolve_left hi
  simp [hs]

private lemma faithfulCounterexampleSucc (hm : 0 < m) :
    ∃ ρ : Coord m →ₗ[ℂ] Matrix (Ambient m) (Ambient m) ℂ,
      Function.Injective ρ ∧
      (∀ x y, ρ x * ρ y = ρ (0, vecMulVec x.1 y.1)) ∧
      (∃ x ∈ LinearMap.range ρ, ∃ y ∈ LinearMap.range ρ, x * y ≠ y * x) ∧
      (∀ x ∈ LinearMap.range ρ, ∀ y ∈ LinearMap.range ρ, x * y = -(y * x) → x * y = 0) ∧
      (∀ k (x : Matrix (Fin k) (Fin k) (Matrix (Ambient m) (Ambient m) ℂ)),
        (∀ i j, x i j ∈ LinearMap.range ρ) →
        ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖) := by
  refine ⟨representation, representation_injective, representation_mul, ?_, ?_, amplified_norm⟩
  · let i : Fin (m + 1) := ⟨0, by omega⟩
    let j : Fin (m + 1) := ⟨1, Nat.succ_lt_succ hm⟩
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      contradiction
    let x : Coord m := (Pi.single i 1, 0)
    let y : Coord m := (Pi.single j 1, 0)
    refine ⟨representation x, ⟨x, rfl⟩, representation y, ⟨y, rfl⟩, ?_⟩
    intro h
    rw [representation_mul, representation_mul] at h
    have h' := congrArg (fun z : Coord m => z.2 i j) (representation_injective h)
    simp [x, y, vecMulVec_apply, hij, hij.symm] at h'
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    rw [representation_mul, representation_mul, ← map_neg] at h
    have h' := congrArg Prod.snd (representation_injective h)
    rw [representation_mul, outer_eq_neg_swapped h']
    exact map_zero representation

-- Here m is the row length, rather than its predecessor.
private lemma faithfulCounterexample (m : ℕ) (hm : 2 ≤ m) :
    ∃ ρ : ((Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ) →ₗ[ℂ] Matrix (Fin (m * m * (m + 2))) (Fin (m * m * (m + 2))) ℂ,
      Function.Injective ρ ∧
      (∀ x y, ρ x * ρ y = ρ (0, vecMulVec x.1 y.1)) ∧
      (∃ x ∈ LinearMap.range ρ, ∃ y ∈ LinearMap.range ρ, x * y ≠ y * x) ∧
      (∀ x ∈ LinearMap.range ρ, ∀ y ∈ LinearMap.range ρ, x * y = -(y * x) → x * y = 0) ∧
      (∀ k (x : Matrix (Fin k) (Fin k) (Matrix (Fin (m * m * (m + 2))) (Fin (m * m * (m + 2))) ℂ)),
        (∀ i j, x i j ∈ LinearMap.range ρ) →
        ‖comp _ _ _ _ ℂ (fun i j => (x i j)ᵀ)‖ = ‖comp _ _ _ _ ℂ x‖) := by
  cases m with
  | zero => omega
  | succ m => exact faithfulCounterexampleSucc (by omega : 0 < m)

/-- A noncommutative symmetric operator algebra in sixteen dimensions whose
anticommuting pairs all have zero product. -/
theorem result : ¬ claim := by
  intro necessity
  obtain ⟨ρ, _, hmul, hnc, hzero, hnorm⟩ := faithfulCounterexample 2 (by decide)
  have hclosed : ∀ x ∈ LinearMap.range ρ, ∀ y ∈ LinearMap.range ρ,
      x * y ∈ LinearMap.range ρ := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨_, (hmul x y).symm⟩
  obtain ⟨x, hx, y, hy, hxy, hnonzero⟩ := necessity _ hclosed hnc hnorm
  exact hnonzero (hzero x hx y hy hxy)

end D5.S3.HilbertOperators.BlecherNoAnticommutingPair

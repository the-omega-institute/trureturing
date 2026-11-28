import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! Omega original.

A doubled integral presentation of the six-dimensional exceptional root system
and its realization in Euclidean space. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace Matrix
open WithLp

namespace OmegaMath.ExceptionalSix

abbrev Lattice := Fin 8 → ℤ

private def pairs : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
    (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

private def sign (b : Bool) : ℤ := if b then -1 else 1

private def orthogonalCode (k : Fin 40) : Lattice :=
  let p := pairs (Fin.ofNat 10 (k.val / 4))
  fun j =>
    if j.val = p.1.val then 2 * sign (k.val.testBit 1)
    else if j.val = p.2.val then 2 * sign (k.val.testBit 0)
    else 0

private def spinCode (k : Fin 32) : Lattice :=
  let negatives := (List.range 5 |>.filter k.val.testBit).length
  let tail : ℤ := if negatives % 2 = 0 then -1 else 1
  fun j =>
    if j.val < 5 then sign (k.val.testBit j.val)
    else if j.val = 7 then -tail else tail

def code (k : Fin 72) : Lattice :=
  if hk : k.val < 40 then orthogonalCode ⟨k.val, hk⟩
  else spinCode (Fin.ofNat 32 (k.val - 40))

def indexOf (z : Lattice) : Fin 72 :=
  if z 5 = 0 then
    let p := (List.range 10).findIdx fun k =>
      let ij := pairs (Fin.ofNat 10 k)
      z (Fin.ofNat 8 ij.1.val) != 0 && z (Fin.ofNat 8 ij.2.val) != 0
    let ij := pairs (Fin.ofNat 10 p)
    let first := if z (Fin.ofNat 8 ij.1.val) < 0 then 2 else 0
    let second := if z (Fin.ofNat 8 ij.2.val) < 0 then 1 else 0
    Fin.ofNat 72 (4 * p + first + second)
  else
    Fin.ofNat 72 (40 + ((List.range 5).map fun j =>
      if z (Fin.ofNat 8 j) < 0 then 2 ^ j else 0).sum)

private theorem indexOf_code (k : Fin 72) : indexOf (code k) = k := by
  fin_cases k <;> decide

def dot (x y : Lattice) : ℤ :=
  ((List.finRange 8).map fun j => x j * y j).sum

private theorem dot_eq_sum (x y : Lattice) : dot x y = ∑ j, x j * y j := by
  simp [dot, Fin.sum_univ_succ, List.finRange_succ]

private def reflected (k l : Fin 72) : Lattice :=
  fun j => code l j - (dot (code k) (code l) / 4) * code k j

private def productCondition (k l : Fin 72) : Prop :=
  let d := dot (code k) (code l)
  (d = -8 ∨ d = -4 ∨ d = 0 ∨ d = 4 ∨ d = 8) ∧
    (d = 8 ↔ k = l) ∧
    (d = -8 ↔ code k = -code l) ∧
    code (indexOf (reflected k l)) = reflected k l

private instance (k l : Fin 72) : Decidable (productCondition k l) := by
  unfold productCondition
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The certificate checks every ordered pair of the seventy-two roots.
private theorem products (k l : Fin 72) : productCondition k l := by
  revert l
  fin_cases k <;> decide +kernel

private theorem code_geometry (k : Fin 72) :
    code k 5 = code k 6 ∧ code k 6 = -code k 7 ∧ dot (code k) (code k) = 8 ∧
      code (indexOf (-code k)) = -code k := by
  fin_cases k <;> decide

abbrev Ambient := EuclideanSpace ℝ (Fin 8)

noncomputable def realize (z : Fin 8 → ℤ) : Ambient :=
  toLp 2 fun j => (z j : ℝ) / 2

noncomputable def root (k : Fin 72) : Ambient := realize (code k)

theorem realize_injective : Function.Injective realize := by
  intro x y h
  funext j
  have hj := congrArg (fun v : Ambient => v j) h
  change (x j : ℝ) / 2 = (y j : ℝ) / 2 at hj
  have he : (x j : ℝ) = (y j : ℝ) := (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp hj
  exact_mod_cast he

theorem inner_realize (x y : Lattice) :
    ⟪realize x, realize y⟫_ℝ = (dot x y : ℝ) / 4 := by
  rw [dot_eq_sum, Int.cast_sum, Finset.sum_div]
  simp only [PiLp.inner_apply, Real.inner_apply, realize, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realize_neg (x : Lattice) : realize (-x) = -realize x := by
  ext i
  change ((-x i : ℤ) : ℝ) / 2 = -((x i : ℝ) / 2)
  push_cast
  ring

noncomputable def roots : Finset Ambient := by
  classical
  exact Finset.univ.image root

private theorem mem_roots {v : Ambient} : v ∈ roots ↔ ∃ k, root k = v := by
  classical
  simp [roots]

theorem card_roots : roots.card = 72 := by
  classical
  unfold roots
  rw [Finset.card_image_of_injective]
  · simp
  · intro k l h
    simpa only [indexOf_code] using congrArg indexOf (realize_injective h)

def rankSix : Submodule ℝ Ambient where
  carrier := {v | v 5 = v 6 ∧ v 6 = -v 7}
  zero_mem' := by simp
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    change v 5 + w 5 = v 6 + w 6 ∧ v 6 + w 6 = -(v 7 + w 7)
    constructor <;> linarith
  smul_mem' := by
    rintro c v ⟨h, h'⟩
    change c * v 5 = c * v 6 ∧ c * v 6 = -(c * v 7)
    exact ⟨congrArg (c * ·) h, by rw [h']; ring⟩

private def extension (f : Fin 6 → ℝ) : Ambient :=
  toLp 2 ![f 0, f 1, f 2, f 3, f 4, f 5, f 5, -f 5]

private def rankEquiv : (Fin 6 → ℝ) ≃ₗ[ℝ] rankSix where
  toFun f := ⟨extension f, by
    change extension f 5 = extension f 6 ∧ extension f 6 = -extension f 7
    simp [extension]⟩
  invFun v i := v.1 (Fin.castLE (by decide : 6 ≤ 8) i)
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    ext i
    obtain ⟨h, h'⟩ := v.2
    fin_cases i <;> first | rfl | exact h | (change -(v.1 5) = v.1 7; linarith only [h, h'])
  map_add' f g := by
    apply Subtype.ext
    ext i
    fin_cases i <;> first | rfl | exact neg_add _ _
  map_smul' c f := by
    apply Subtype.ext
    ext i
    fin_cases i <;> first | rfl | exact (mul_neg _ _).symm

theorem roots_rank_six : (∀ v ∈ roots, v ∈ rankSix) ∧ Module.finrank ℝ rankSix = 6 := by
  constructor
  · intro v hv
    obtain ⟨k, rfl⟩ := mem_roots.mp hv
    obtain ⟨h, h', _, _⟩ := code_geometry k
    change ((code k 5 : ℤ) : ℝ) / 2 = (code k 6 : ℝ) / 2 ∧
      (code k 6 : ℝ) / 2 = -((code k 7 : ℝ) / 2)
    rw [h, h']
    push_cast
    constructor <;> ring
  · rw [← rankEquiv.finrank_eq, Module.finrank_pi, Fintype.card_fin]

theorem root_norm {v : Ambient} (hv : v ∈ roots) : ⟪v, v⟫_ℝ = 2 := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  rw [root, inner_realize, (code_geometry k).2.2.1]
  norm_num

theorem root_products {v w : Ambient} (hv : v ∈ roots) (hw : w ∈ roots) :
    ⟪v, w⟫_ℝ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪v, w⟫_ℝ = 2 ↔ v = w) ∧ (⟪v, w⟫_ℝ = -2 ↔ v = -w) := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  obtain ⟨l, rfl⟩ := mem_roots.mp hw
  obtain ⟨values, pos, neg, _⟩ := products k l
  simp only [root, inner_realize]
  refine ⟨?_, ?_, ?_⟩
  · rcases values with h | h | h | h | h <;> rw [h] <;> norm_num
  · have h : (dot (code k) (code l) : ℝ) / 4 = 2 ↔ dot (code k) (code l) = 8 := by
      rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0)]
      norm_num <;> exact_mod_cast (Iff.rfl : dot (code k) (code l) = 8 ↔ _)
    rw [h, pos]
    exact ⟨congrArg (realize ∘ code), fun he =>
      by simpa only [indexOf_code] using congrArg indexOf (realize_injective he)⟩
  · have h : (dot (code k) (code l) : ℝ) / 4 = -2 ↔ dot (code k) (code l) = -8 := by
      rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0)]
      norm_num <;> exact_mod_cast (Iff.rfl : dot (code k) (code l) = -8 ↔ _)
    rw [h, neg, ← realize_neg]
    exact ⟨congrArg realize, fun h => realize_injective h⟩

theorem root_neg {v : Ambient} (hv : v ∈ roots) : -v ∈ roots := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  exact mem_roots.mpr ⟨indexOf (-code k), by
    rw [root, (code_geometry k).2.2.2, realize_neg, root]⟩

theorem root_reflection {v w : Ambient} (hv : v ∈ roots) (hw : w ∈ roots) :
    w - ⟪v, w⟫_ℝ • v ∈ roots := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  obtain ⟨l, rfl⟩ := mem_roots.mp hw
  obtain ⟨values, _, _, h⟩ := products k l
  refine mem_roots.mpr ⟨indexOf (reflected k l), ?_⟩
  rw [root, h]
  simp only [root, inner_realize]
  have hcast : ((dot (code k) (code l) / 4 : ℤ) : ℝ) =
      (dot (code k) (code l) : ℝ) / 4 := by
    rcases values with h | h | h | h | h <;> rw [h] <;> norm_num
  ext j
  change ((code l j - (dot (code k) (code l) / 4) * code k j : ℤ) : ℝ) / 2 =
    (code l j : ℝ) / 2 - ((dot (code k) (code l) : ℝ) / 4) * ((code k j : ℝ) / 2)
  push_cast
  rw [hcast]
  ring

def simpleCode : Fin 6 → Lattice :=
  ![![1, -1, -1, -1, -1, -1, -1, 1],
    ![2, 2, 0, 0, 0, 0, 0, 0], ![-2, 2, 0, 0, 0, 0, 0, 0],
    ![0, -2, 2, 0, 0, 0, 0, 0], ![0, 0, -2, 2, 0, 0, 0, 0],
    ![0, 0, 0, -2, 2, 0, 0, 0]]

noncomputable def simple (i : Fin 6) : Ambient := realize (simpleCode i)

def cartan : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0; -1, 0, 2, -1, 0, 0;
    0, -1, -1, 2, -1, 0; 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2]

private def coefficients (z : Lattice) : Fin 6 → ℤ :=
  let a₁ := -z 5
  let a₆ := (z 4 + a₁) / 2
  let a₅ := (z 3 + a₁) / 2 + a₆
  let a₄ := (z 2 + a₁) / 2 + a₅
  let a₂ := (z 0 + z 1 + 2 * a₄) / 4
  let a₃ := (z 1 + a₁) / 2 + a₄ - a₂
  ![a₁, a₂, a₃, a₄, a₅, a₆]

private theorem coordinates (k : Fin 72) :
    (∀ j, code k j =
      ((List.finRange 6).map fun i => coefficients (code k) i * simpleCode i j).sum) ∧
    ((∀ i, 0 ≤ coefficients (code k) i) ∨ (∀ i, coefficients (code k) i ≤ 0)) := by
  fin_cases k <;> decide

private theorem independent_simple : LinearIndependent ℝ simple := by
  rw [Fintype.linearIndependent_iff]
  intro c he i
  have coord (j : Fin 8) : (∑ i, c i * simple i j) = 0 := by
    let ev := PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : Fin 8 => ℝ) j
    simpa [ev, map_sum, map_smul, PiLp.projₗ_apply, smul_eq_mul] using congrArg ev he
  have h₀ := coord 0
  have h₁ := coord 1
  have h₂ := coord 2
  have h₃ := coord 3
  have h₄ := coord 4
  have h₅ := coord 5
  norm_num [Fin.sum_univ_succ, simple, realize, simpleCode, PiLp.toLp_apply]
    at h₀ h₁ h₂ h₃ h₄ h₅
  fin_cases i
  all_goals
    first | change c 0 = 0 | change c 1 = 0 | change c 2 = 0 |
      change c 3 = 0 | change c 4 = 0 | change c 5 = 0
    linarith only [h₀, h₁, h₂, h₃, h₄, h₅]

theorem simple_system :
    (∀ i, simple i ∈ roots) ∧
    (∀ i j, ⟪simple i, simple j⟫_ℝ = (cartan i j : ℝ)) ∧
    cartan.det = 3 ∧
    LinearIndependent ℝ simple ∧
    (∀ v ∈ roots, ∃ c : Fin 6 → ℤ, v = ∑ i, (c i : ℝ) • simple i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0))) := by
  refine ⟨?_, ?_, ?_, independent_simple, ?_⟩
  · intro i
    have h : code (indexOf (simpleCode i)) = simpleCode i := by
      fin_cases i <;> decide
    exact mem_roots.mpr ⟨indexOf (simpleCode i), congrArg realize h⟩
  · intro i j
    have h : dot (simpleCode i) (simpleCode j) = 4 * cartan i j := by
      fin_cases i <;> fin_cases j <;> decide
    simp only [simple, inner_realize, h, Int.cast_mul, Int.cast_ofNat]
    ring
  · norm_num [cartan, Matrix.det_succ_row_zero, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]
  · intro v hv
    obtain ⟨k, rfl⟩ := mem_roots.mp hv
    obtain ⟨h, hs⟩ := coordinates k
    refine ⟨coefficients (code k), ?_, hs⟩
    ext j
    have hsums : code k j = ∑ i, coefficients (code k) i * simpleCode i j := by
      simpa [List.finRange_succ, Fin.sum_univ_succ] using h j
    change (code k j : ℝ) / 2 =
      PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : Fin 8 => ℝ) j (∑ i, (coefficients (code k) i : ℝ) • simple i)
    rw [map_sum]
    simp only [map_smul, PiLp.projₗ_apply, simple, realize, smul_eq_mul]
    rw [hsums, Int.cast_sum, Finset.sum_div]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    ring

end OmegaMath.ExceptionalSix

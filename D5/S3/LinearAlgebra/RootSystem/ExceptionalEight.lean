/- GID: D5/S3/LinearAlgebra/RootSystem/ExceptionalEight
   generality: G
   mirror-B: none(waiver:covered-by-e8-root-system-unification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The doubled integral coordinates of the exceptional root system, with a base whose first six vectors are the base of the embedded rank-six subsystem. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.Set.Finite.Range
import D5.S3.LinearAlgebra.RootSystem.ExceptionalSix

/-! Omega original.

The doubled integral coordinates of the exceptional root system, with a base
whose first six vectors are the base of the embedded rank-six subsystem. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace Matrix
open WithLp

namespace OmegaMath.ExceptionalEight

abbrev Lattice := ExceptionalSix.Lattice
abbrev Ambient := ExceptionalSix.Ambient
noncomputable abbrev realize := ExceptionalSix.realize

private def pairs : Fin 28 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
    (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7),
    (5, 6), (5, 7), (6, 7)]

private def sign (b : Bool) : ℤ := if b then -1 else 1

/-- A vector supported on an unordered coordinate pair, with two independent signs. -/
def orthogonalCode (k : Fin 112) : Lattice :=
  let ij := pairs (Fin.ofNat 28 (k.val / 4))
  fun j =>
    if j = ij.1 then 2 * sign (k.val.testBit 1)
    else if j = ij.2 then 2 * sign (k.val.testBit 0)
    else 0

/-- The eighth sign makes the number of negative signs even. -/
def spinCode (k : Fin 128) : Lattice :=
  fun j =>
    if j.val < 7 then sign (k.val.testBit j.val)
    else sign (((List.range 7 |>.filter k.val.testBit).length % 2) == 1)

/-- Enumeration of the two families of doubled roots. -/
def code (k : Fin 240) : Lattice :=
  if hk : k.val < 112 then orthogonalCode ⟨k.val, hk⟩
  else spinCode (Fin.ofNat 128 (k.val - 112))

/-- Recover the index of a doubled root using its support or its first seven signs. -/
def indexOf (z : Lattice) : Fin 240 :=
  if z 0 % 2 = 0 then
    let support := (List.range 8).filter fun j => z (Fin.ofNat 8 j) != 0
    let i := support[0]?.getD 0
    let j := support[1]?.getD 0
    let p := i * (15 - i) / 2 + j - (i + 1)
    let first := if z (Fin.ofNat 8 i) < 0 then 2 else 0
    let second := if z (Fin.ofNat 8 j) < 0 then 1 else 0
    Fin.ofNat 240 (4 * p + first + second)
  else
    Fin.ofNat 240 (112 + ((List.range 7).map fun j =>
      if z (Fin.ofNat 8 j) < 0 then 2 ^ j else 0).sum)

theorem indexOf_code (k : Fin 240) : indexOf (code k) = k := by
  fin_cases k <;> decide

abbrev dot := ExceptionalSix.dot

private theorem code_geometry (k : Fin 240) :
    dot (code k) (code k) = 8 ∧ code (indexOf (-code k)) = -code k := by
  fin_cases k <;> decide

abbrev realize_injective := ExceptionalSix.realize_injective
abbrev realize_inner := ExceptionalSix.inner_realize
abbrev realize_neg := ExceptionalSix.realize_neg

theorem realize_sub (x y : Lattice) : realize (x - y) = realize x - realize y := by
  ext i
  change ((x i - y i : ℤ) : ℝ) / 2 = (x i : ℝ) / 2 - (y i : ℝ) / 2
  push_cast
  ring

noncomputable def root (k : Fin 240) : Ambient := realize (code k)

theorem root_injective : Function.Injective root := by
  intro k l h
  simpa only [indexOf_code] using congrArg indexOf (realize_injective h)

/-- The finite range of the realized doubled roots. -/
noncomputable def roots : Finset Ambient := (Set.finite_range root).toFinset

theorem mem_roots {v : Ambient} : v ∈ roots ↔ ∃ k, root k = v := by
  simp [roots]

theorem mem_roots_iff_code (z : Lattice) : realize z ∈ roots ↔ code (indexOf z) = z := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_roots.mp h
    rw [← realize_injective hk, indexOf_code]
  · intro h
    exact mem_roots.mpr ⟨indexOf z, congrArg realize h⟩

noncomputable def orthogonalRoots : Finset Ambient := by
  classical
  exact Finset.univ.image (realize ∘ orthogonalCode)

noncomputable def spinRoots : Finset Ambient := by
  classical
  exact Finset.univ.image (realize ∘ spinCode)

private def orthogonalIndex (k : Fin 112) : Fin 240 := k.castLE (by decide)
private def spinIndex (k : Fin 128) : Fin 240 := k.natAdd 112

private theorem code_orthogonalIndex (k : Fin 112) : code (orthogonalIndex k) = orthogonalCode k := by
  fin_cases k <;> decide

private theorem code_spinIndex (k : Fin 128) : code (spinIndex k) = spinCode k := by
  fin_cases k <;> decide

theorem card_root_families :
    orthogonalRoots.card = 112 ∧ spinRoots.card = 128 ∧
    Disjoint orthogonalRoots spinRoots ∧ orthogonalRoots ∪ spinRoots = roots := by
  classical
  have orthogonalRoot (k : Fin 112) : (realize ∘ orthogonalCode) k = root (orthogonalIndex k) := by
    rw [Function.comp_apply, root, code_orthogonalIndex]
  have spinRoot (k : Fin 128) : (realize ∘ spinCode) k = root (spinIndex k) := by
    rw [Function.comp_apply, root, code_spinIndex]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold orthogonalRoots
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      rw [orthogonalRoot, orthogonalRoot] at h
      exact Fin.ext (congrArg (fun k : Fin 240 => k.val) (root_injective h))
  · unfold spinRoots
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      rw [spinRoot, spinRoot] at h
      have he := congrArg Fin.val (root_injective h)
      change 112 + a.val = 112 + b.val at he
      exact Fin.ext (Nat.add_left_cancel he)
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [orthogonalRoots, spinRoots, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    have he := congrArg Fin.val (root_injective ((orthogonalRoot a).symm.trans
      (ha.trans (hb.symm.trans (spinRoot b)))))
    change a.val = 112 + b.val at he
    omega
  · ext x
    simp only [Finset.mem_union, orthogonalRoots, spinRoots, Finset.mem_image,
      Finset.mem_univ, true_and, mem_roots, orthogonalRoot, spinRoot]
    constructor
    · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
      · exact ⟨orthogonalIndex k, hk⟩
      · exact ⟨spinIndex k, hk⟩
    · rintro ⟨k, rfl⟩
      by_cases hk : k.val < 112
      · exact Or.inl ⟨⟨k.val, hk⟩, rfl⟩
      · refine Or.inr ⟨⟨k.val - 112, by omega⟩, ?_⟩
        congr 1
        apply Fin.ext
        change 112 + (k.val - 112) = k.val
        omega

theorem card_roots : roots.card = 240 := by
  obtain ⟨ha, hb, hd, hu⟩ := card_root_families
  classical
  rw [← hu, Finset.card_union_of_disjoint hd, ha, hb]

theorem root_norm {v : Ambient} (hv : v ∈ roots) : ⟪v, v⟫_ℝ = 2 := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  rw [root, realize_inner]
  change (dot (code k) (code k) : ℝ) / 4 = 2
  rw [(code_geometry k).1]
  norm_num

theorem root_neg {v : Ambient} (hv : v ∈ roots) : -v ∈ roots := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  rw [root, ← realize_neg]
  exact (mem_roots_iff_code _).mpr (code_geometry k).2

private theorem six_code_mem (k : Fin 72) :
    ExceptionalEight.code (ExceptionalEight.indexOf (ExceptionalSix.code k)) =
      ExceptionalSix.code k := by
  fin_cases k <;> decide

theorem six_subset : ExceptionalSix.roots ⊆ roots := by
  intro v hv
  obtain ⟨k, rfl⟩ : ∃ k, ExceptionalSix.root k = v := by
    classical
    simpa [ExceptionalSix.roots] using hv
  exact (mem_roots_iff_code _).mpr (six_code_mem k)

private theorem code_in_six (k : Fin 240) :
    ExceptionalEight.code k 5 = ExceptionalEight.code k 6 →
    ExceptionalEight.code k 6 = -ExceptionalEight.code k 7 →
    ExceptionalSix.code (ExceptionalSix.indexOf (ExceptionalEight.code k)) =
      ExceptionalEight.code k := by
  fin_cases k <;> decide

theorem roots_inter_rankSix (v : Ambient) (hv : v ∈ roots) :
    v ∈ ExceptionalSix.rankSix ↔ v ∈ ExceptionalSix.roots := by
  refine ⟨?_, ExceptionalSix.roots_rank_six.1 v⟩
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  rintro ⟨h₅, h₆⟩
  change (ExceptionalEight.code k 5 : ℝ) / 2 = (ExceptionalEight.code k 6 : ℝ) / 2 at h₅
  change (ExceptionalEight.code k 6 : ℝ) / 2 = -((ExceptionalEight.code k 7 : ℝ) / 2) at h₆
  have h₅' : (ExceptionalEight.code k 5 : ℝ) = (ExceptionalEight.code k 6 : ℝ) := by linarith
  have h₆' : (ExceptionalEight.code k 6 : ℝ) = -((ExceptionalEight.code k 7 : ℝ)) := by linarith
  classical
  unfold ExceptionalSix.roots
  exact Finset.mem_image.mpr ⟨ExceptionalSix.indexOf (ExceptionalEight.code k), Finset.mem_univ _,
    congrArg realize (code_in_six k (by exact_mod_cast h₅') (by exact_mod_cast h₆'))⟩

private def simpleCode (i : Fin 8) : Lattice :=
  if hi : i.val < 6 then ExceptionalSix.simpleCode ⟨i.val, hi⟩
  else if i.val = 6 then ![0, 0, 0, 0, -2, 2, 0, 0]
  else ![0, 0, 0, 0, 0, -2, 2, 0]

noncomputable def simple (i : Fin 8) : Ambient := realize (ExceptionalEight.simpleCode i)

def cartan : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, 0, -1, 0, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0, 0, 0;
    -1, 0, 2, -1, 0, 0, 0, 0; 0, -1, -1, 2, -1, 0, 0, 0;
    0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, 0, 0, -1, 2]

private def coefficients (z : Lattice) : Fin 8 → ℤ :=
  let a₁ := z 7
  let a₈ := (z 6 + a₁) / 2
  let a₇ := (z 5 + a₁) / 2 + a₈
  let a₆ := (z 4 + a₁) / 2 + a₇
  let a₅ := (z 3 + a₁) / 2 + a₆
  let a₄ := (z 2 + a₁) / 2 + a₅
  let a₂ := (z 0 + z 1 + 2 * a₄) / 4
  let a₃ := (z 1 + a₁) / 2 + a₄ - a₂
  ![a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈]

private theorem coordinates (k : Fin 240) :
    (∀ j, ExceptionalEight.code k j =
      ((List.finRange 8).map fun i => coefficients (ExceptionalEight.code k) i *
        ExceptionalEight.simpleCode i j).sum) ∧
    ((∀ i, 0 ≤ coefficients (ExceptionalEight.code k) i) ∨
      (∀ i, coefficients (ExceptionalEight.code k) i ≤ 0)) := by
  fin_cases k <;> decide

private theorem simple_inner (i j : Fin 8) : ⟪simple i, simple j⟫_ℝ = (cartan i j : ℝ) := by
  have h : dot (ExceptionalEight.simpleCode i) (ExceptionalEight.simpleCode j) = 4 * cartan i j := by
    fin_cases i <;> fin_cases j <;> decide
  simp only [simple, realize_inner, h, Int.cast_mul, Int.cast_ofNat]
  ring

set_option maxHeartbeats 20000000 in
private theorem cartan_det : cartan.det = 1 := by
  norm_num [cartan, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]

private theorem independent_simple : LinearIndependent ℝ simple := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero (𝕜 := ℝ)
  have h : Matrix.gram ℝ simple = (Int.castRingHom ℝ).mapMatrix cartan := by
    ext i j
    exact simple_inner i j
  rw [h, ← RingHom.map_det, cartan_det, map_one]
  norm_num

theorem simple_system :
    (∀ i, simple i ∈ roots) ∧
    (∀ i j, ⟪simple i, simple j⟫_ℝ = (cartan i j : ℝ)) ∧
    cartan.det = 1 ∧
    LinearIndependent ℝ simple ∧
    (∀ v ∈ roots, ∃ c : Fin 8 → ℤ, v = ∑ i, (c i : ℝ) • simple i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0))) ∧
    (∀ i : Fin 6, simple (i.castLE (by decide)) = ExceptionalSix.simple i) := by
  refine ⟨?_, simple_inner, cartan_det, independent_simple, ?_, ?_⟩
  · intro i
    apply (mem_roots_iff_code _).mpr
    fin_cases i <;> decide
  · intro v hv
    obtain ⟨k, rfl⟩ := mem_roots.mp hv
    obtain ⟨h, hs⟩ := coordinates k
    refine ⟨coefficients (ExceptionalEight.code k), ?_, hs⟩
    ext j
    have hsums : ExceptionalEight.code k j =
        ∑ i, coefficients (ExceptionalEight.code k) i * ExceptionalEight.simpleCode i j := by
      simpa [List.finRange_succ, Fin.sum_univ_succ] using h j
    change (ExceptionalEight.code k j : ℝ) / 2 =
      PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : Fin 8 => ℝ) j
        (∑ i, (coefficients (ExceptionalEight.code k) i : ℝ) • simple i)
    rw [map_sum]
    simp only [map_smul, PiLp.projₗ_apply, simple, realize, smul_eq_mul]
    rw [hsums, Int.cast_sum, Finset.sum_div]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    change _ = (coefficients (code k) i : ℝ) * ((simpleCode i j : ℝ) / 2)
    ring
  · intro i
    simp only [simple, ExceptionalSix.simple, ExceptionalEight.simpleCode, Fin.val_castLE,
      i.isLt, dite_true, realize]

private theorem inner_integral {v w : Ambient} (hv : v ∈ roots) (hw : w ∈ roots) :
    ∃ d : ℤ, ⟪v, w⟫_ℝ = d := by
  obtain ⟨c, rfl, _⟩ := simple_system.2.2.2.2.1 v hv
  obtain ⟨b, rfl, _⟩ := simple_system.2.2.2.2.1 w hw
  refine ⟨∑ j, ∑ i, b j * (c i * cartan i j), ?_⟩
  push_cast
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, simple_inner]

theorem root_products {v w : Ambient} (hv : v ∈ roots) (hw : w ∈ roots) :
    ⟪v, w⟫_ℝ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪v, w⟫_ℝ = 2 ↔ v = w) ∧ (⟪v, w⟫_ℝ = -2 ↔ v = -w) := by
  have hm : ⟪v - w, v - w⟫_ℝ = 4 - 2 * ⟪v, w⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm w v, root_norm hv, root_norm hw]
    ring
  have hp : ⟪v + w, v + w⟫_ℝ = 4 + 2 * ⟪v, w⟫_ℝ := by
    simp only [inner_add_left, inner_add_right, real_inner_comm w v, root_norm hv, root_norm hw]
    ring
  have hl : -2 ≤ ⟪v, w⟫_ℝ := by linarith [real_inner_self_nonneg (x := v + w)]
  have hu : ⟪v, w⟫_ℝ ≤ 2 := by linarith [real_inner_self_nonneg (x := v - w)]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨d, h⟩ := inner_integral hv hw
    rw [h] at hl hu ⊢
    have hdl : -2 ≤ d := by exact_mod_cast hl
    have hdu : d ≤ 2 := by exact_mod_cast hu
    have : d = -2 ∨ d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · have hz : v = w ↔ ⟪v - w, v - w⟫_ℝ = 0 :=
      sub_eq_zero.symm.trans inner_self_eq_zero.symm
    rw [hz, hm]
    constructor <;> intro h <;> linarith
  · have hz : v = -w ↔ v + w = 0 := by
      rw [← sub_neg_eq_add, sub_eq_zero]
    rw [hz, ← inner_self_eq_zero (𝕜 := ℝ) (x := v + w), hp]
    constructor <;> intro h <;> linarith

private noncomputable def reflect (v w : Ambient) : Ambient := w - ⟪v, w⟫_ℝ • v

private theorem reflect_twice (u x : Ambient) (hu : ⟪u, u⟫_ℝ = 2) :
    reflect u (reflect u x) = x := by
  simp only [reflect, inner_sub_right, real_inner_smul_right, hu]
  ext j
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem reflect_inner (u x y : Ambient) (hu : ⟪u, u⟫_ℝ = 2) :
    ⟪reflect u x, reflect u y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [reflect, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm x u, hu]
  ring

private theorem reflect_conjugate (u x y : Ambient) (hu : ⟪u, u⟫_ℝ = 2) :
    reflect u (reflect x y) = reflect (reflect u x) (reflect u y) := by
  calc
    reflect u (reflect x y) = reflect u y - ⟪x, y⟫_ℝ • reflect u x := by
      simp only [reflect, inner_sub_right, real_inner_smul_right]
      ext j
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      change _ = reflect u y - ⟪reflect u x, reflect u y⟫_ℝ • reflect u x
      rw [reflect_inner u x y hu]

private def reflectedCode (z w : Lattice) : Lattice :=
  fun j => w j - (dot z w / 4) * z j

private def simpleReflectionIndex (i : Fin 8) (k : Fin 240) : Fin 240 :=
  indexOf (reflectedCode (simpleCode i) (code k))

private def simpleReflectionCondition (i : Fin 8) (k : Fin 240) : Prop :=
  code (simpleReflectionIndex i k) = reflectedCode (simpleCode i) (code k)

private instance (i : Fin 8) (k : Fin 240) : Decidable (simpleReflectionCondition i k) := by
  unfold simpleReflectionCondition
  infer_instance

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem simpleReflection_code (i : Fin 8) (k : Fin 240) :
    simpleReflectionCondition i k := by
  revert k
  fin_cases i <;> decide +kernel

private theorem simpleReflection_root (i : Fin 8) (k : Fin 240) :
    root (simpleReflectionIndex i k) = reflect (simple i) (root k) := by
  obtain ⟨d, hd⟩ := inner_integral (simple_system.1 i) (mem_roots.mpr ⟨k, rfl⟩)
  rw [simple, root, realize_inner] at hd
  have hdot : dot (simpleCode i) (code k) = 4 * d := by
    have hcast : (dot (simpleCode i) (code k) : ℝ) = 4 * (d : ℝ) := by linarith
    exact_mod_cast hcast
  have hdiv : dot (simpleCode i) (code k) / 4 = d := by omega
  have h := simpleReflection_code i k
  unfold simpleReflectionCondition at h
  rw [root, h]
  unfold reflect
  rw [simple, root, realize_inner, hd]
  ext j
  change ((code k j - (dot (simpleCode i) (code k) / 4) * simpleCode i j : ℤ) : ℝ) / 2 =
    (code k j : ℝ) / 2 - (d : ℝ) * ((simpleCode i j : ℝ) / 2)
  rw [hdiv]
  push_cast
  ring

private theorem simpleReflection_closed (i : Fin 8) {w : Ambient} (hw : w ∈ roots) :
    reflect (simple i) w ∈ roots := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hw
  exact mem_roots.mpr ⟨simpleReflectionIndex i k, simpleReflection_root i k⟩

private def height (k : Fin 240) : ℕ :=
  ((List.finRange 8).map fun i => (coefficients (code k) i).natAbs).sum

private def descentIndex (k : Fin 240) : Fin 8 :=
  ((List.finRange 8).find? fun i => decide
    (height (simpleReflectionIndex i k) < height k)).getD 0

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem simple_or_descent (k : Fin 240) :
    (∃ i : Fin 8, code k = simpleCode i ∨ code k = -simpleCode i) ∨
      height (simpleReflectionIndex (descentIndex k) k) < height k := by
  fin_cases k <;> decide +kernel

theorem root_reflection {v w : Ambient} (hv : v ∈ roots) (hw : w ∈ roots) :
    w - ⟪v, w⟫_ℝ • v ∈ roots := by
  obtain ⟨k, rfl⟩ := mem_roots.mp hv
  have closed (k : Fin 240) : ∀ w ∈ roots, reflect (root k) w ∈ roots := by
    induction k using (measure height).wf.induction with
    | h k ih =>
      intro w hw
      rcases simple_or_descent k with ⟨i, h | h⟩ | h
      · rw [show root k = simple i from congrArg realize h]
        exact simpleReflection_closed i hw
      · rw [show root k = -simple i from (congrArg realize h).trans (realize_neg _)]
        simpa only [reflect, inner_neg_left, neg_smul, smul_neg, neg_neg]
          using simpleReflection_closed i hw
      · let i := descentIndex k
        have hm := root_norm (simple_system.1 i)
        have hnext := ih (simpleReflectionIndex i k) h
          (reflect (simple i) w) (simpleReflection_closed i hw)
        rw [simpleReflection_root, ← reflect_conjugate _ _ _ hm] at hnext
        have hback := simpleReflection_closed i hnext
        rwa [reflect_twice _ _ hm] at hback
  exact closed k w hw

end OmegaMath.ExceptionalEight

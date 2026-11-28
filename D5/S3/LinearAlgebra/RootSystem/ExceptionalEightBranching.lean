/- GID: D5/S3/LinearAlgebra/RootSystem/ExceptionalEightBranching
   generality: G
   mirror-B: none(waiver:covered-by-e8-root-system-unification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonal subsystem and the two families of minuscule weight fibers in the doubled integral presentation of the eight-dimensional exceptional root system. -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.RootSystem.ExceptionalEight
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Omega original.

Orthogonal subsystem and the two families of minuscule weight fibers in the
doubled integral presentation of the eight-dimensional exceptional root system. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace Matrix
open WithLp

namespace OmegaMath.ExceptionalEightBranching

open ExceptionalEight (Ambient Lattice code root roots indexOf realize_injective realize_inner
  realize_sub mem_roots root_neg)
open ExceptionalSix (realize rankSix)

def firstIndex (j : Fin 5) : Fin 8 := Fin.castLE (by decide : 5 ≤ 8) j

private def familySimpleCode : Fin 2 → Lattice :=
  ![![0, 0, 0, 0, 0, 2, -2, 0], ![0, 0, 0, 0, 0, 0, 2, 2]]

noncomputable def familySimple (i : Fin 2) : Ambient := realize (familySimpleCode i)

def a2Cartan : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]

private def a2Code : Fin 6 → Lattice :=
  ![familySimpleCode 0, familySimpleCode 1, familySimpleCode 0 + familySimpleCode 1,
    -familySimpleCode 0, -familySimpleCode 1, -(familySimpleCode 0 + familySimpleCode 1)]

noncomputable def a2Roots : Finset Ambient :=
  Finset.univ.image (realize ∘ a2Code)

def familyWeight (v : Ambient) : ℝ × ℝ := (v 5 - v 6, v 6 + v 7)

def fundamentalWeight (i : Fin 3) : ℝ × ℝ := ![(1, 0), (-1, 1), (0, -1)] i

/-- The component along the rank-six direction, normalized to integral charge. -/
def psiCharge (v : Ambient) : ℝ := -2 * (v 5 + v 6 - v 7)

private def spinMask (i : Fin 16) : ℕ :=
  ![31, 22, 14, 21, 13, 19, 11, 28, 26, 25, 1, 2, 4, 16, 8, 7] i

/-- The highest family fiber uses sixteen spin weights, ten vector weights and one scalar. -/
def highestCode (i : Fin 27) : Lattice :=
  if hi : i.val < 16 then
    fun j =>
      if j.val < 5 then
        if (spinMask ⟨i.val, hi⟩).testBit j.val then -1 else 1
      else ![0, 0, 0, 0, 0, 1, -1, 1] j
  else if i.val < 26 then
    let k := (i.val - 16) % 5
    let s : ℤ := if i.val < 21 then 2 else -2
    fun j => if j.val = k then s else if j.val = 5 then 2 else 0
  else ![0, 0, 0, 0, 0, 0, -2, 2]

private def loweringOffset (f : Fin 3) : Lattice :=
  ![0, familySimpleCode 0, familySimpleCode 0 + familySimpleCode 1] f

def generationCode (f : Fin 3) (i : Fin 27) : Lattice := highestCode i - loweringOffset f

noncomputable def generationRoot (f : Fin 3) (i : Fin 27) : Ambient :=
  realize (generationCode f i)

noncomputable def generationFiber (f : Fin 3) : Finset Ambient :=
  Finset.univ.image (generationRoot f)

noncomputable def conjugateFiber (f : Fin 3) : Finset Ambient :=
  Finset.univ.image (fun i => -generationRoot f i)

noncomputable def rep27x3Roots : Finset Ambient :=
  Finset.univ.image (fun p : Fin 3 × Fin 27 => generationRoot p.1 p.2)

noncomputable def rep27barx3barRoots : Finset Ambient :=
  Finset.univ.image (fun p : Fin 3 × Fin 27 => -generationRoot p.1 p.2)

noncomputable def branchPart (i : Fin 4) : Finset Ambient :=
  ![ExceptionalSix.roots, a2Roots, rep27x3Roots, rep27barx3barRoots] i

private theorem a2_code_injective : Function.Injective a2Code := by decide

private theorem a2_code_in_roots (i : Fin 6) : code (indexOf (a2Code i)) = a2Code i := by
  fin_cases i <;> decide

private theorem family_code_in_roots (f : Fin 3) (i : Fin 27) :
    code (indexOf (generationCode f i)) = generationCode f i := by
  fin_cases f <;> fin_cases i <;> decide

private theorem realized_mem {z : Lattice} (h : code (indexOf z) = z) :
    realize z ∈ roots :=
  mem_roots.mpr ⟨indexOf z, congrArg realize h⟩

private theorem a2_subset : a2Roots ⊆ roots := by
  classical
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact realized_mem (a2_code_in_roots i)

theorem generationRoot_mem (f : Fin 3) (i : Fin 27) : generationRoot f i ∈ roots :=
  realized_mem (family_code_in_roots f i)

theorem a2_card : a2Roots.card = 6 := by
  classical
  rw [a2Roots, Finset.card_image_of_injective _ (realize_injective.comp a2_code_injective)]
  simp

theorem a2_cartan :
    (∀ i j, ⟪familySimple i, familySimple j⟫_ℝ = (a2Cartan i j : ℝ)) ∧
      a2Cartan.det = 3 := by
  constructor
  · intro i j
    have h : ExceptionalEight.dot (familySimpleCode i) (familySimpleCode j) =
        4 * a2Cartan i j := by
      fin_cases i <;> fin_cases j <;> decide
    simp only [familySimple, realize_inner, h, Int.cast_mul, Int.cast_ofNat]
    ring
  · norm_num [a2Cartan, Matrix.det_fin_two]

private theorem tail_coordinates (v : Ambient) :
    v ∈ rankSixᗮ ↔ (∀ i : Fin 5, v (firstIndex i) = 0) ∧ v 5 + v 6 - v 7 = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    constructor
    · intro i
      let z : Ambient := toLp 2 (fun j => if j = firstIndex i then 1 else 0)
      have hz : z ∈ rankSix := by
        change (if (5 : Fin 8) = firstIndex i then (1 : ℝ) else 0) =
          (if (6 : Fin 8) = firstIndex i then (1 : ℝ) else 0) ∧
          (if (6 : Fin 8) = firstIndex i then (1 : ℝ) else 0) =
            -(if (7 : Fin 8) = firstIndex i then (1 : ℝ) else 0)
        fin_cases i <;> norm_num [firstIndex, Fin.castLE, Fin.reduceFinMk]
      have hzv := h z hz
      simpa [z, PiLp.inner_apply, Real.inner_apply, mul_ite, ite_mul] using hzv
    · let z : Ambient := toLp 2 ![0, 0, 0, 0, 0, 1, 1, -1]
      have hz : z ∈ rankSix := by
        change (1 : ℝ) = 1 ∧ (1 : ℝ) = -(-1)
        norm_num
      have hzv := h z hz
      norm_num [z, PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_succ] at hzv
      linarith
  · rintro ⟨h, ht⟩ u hu
    obtain ⟨hu₅, hu₆⟩ : u 5 = u 6 ∧ u 6 = -u 7 := hu
    have h₀ : v 0 = 0 := h 0
    have h₁ : v 1 = 0 := h 1
    have h₂ : v 2 = 0 := h 2
    have h₃ : v 3 = 0 := h 3
    have h₄ : v 4 = 0 := h 4
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    change u 0 * v 0 + (u 1 * v 1 + (u 2 * v 2 + (u 3 * v 3 + (u 4 * v 4 +
      (u 5 * v 5 + (u 6 * v 6 + (u 7 * v 7 + 0))))))) = 0
    simp only [h₀, h₁, h₂, h₃, h₄, mul_zero, zero_add, add_zero, hu₅, hu₆]
    linear_combination -u 7 * ht

theorem family_span : Submodule.span ℝ (Set.range familySimple) = rankSixᗮ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change familySimple i ∈ rankSixᗮ
    rw [tail_coordinates]
    constructor
    · intro j
      fin_cases i <;> fin_cases j <;>
        norm_num [familySimple, familySimpleCode, realize, firstIndex, Fin.castLE]
    · fin_cases i <;> norm_num [familySimple, familySimpleCode, realize]
  · intro v hv
    obtain ⟨hv, ht⟩ := (tail_coordinates v).mp hv
    have he : v = v 5 • familySimple 0 + v 7 • familySimple 1 := by
      ext j
      fin_cases j
      · simpa [familySimple, familySimpleCode, realize] using (show v 0 = 0 from hv 0)
      · simpa [familySimple, familySimpleCode, realize] using (show v 1 = 0 from hv 1)
      · simpa [familySimple, familySimpleCode, realize] using (show v 2 = 0 from hv 2)
      · simpa [familySimple, familySimpleCode, realize] using (show v 3 = 0 from hv 3)
      · simpa [familySimple, familySimpleCode, realize] using (show v 4 = 0 from hv 4)
      · simp [familySimple, familySimpleCode, realize]
      · simpa [familySimple, familySimpleCode, realize, neg_add_eq_sub] using (show v 6 = v 7 - v 5 by linarith)
      · simp [familySimple, familySimpleCode, realize]
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

private def inOrthogonalTail (z : Lattice) : Prop :=
  (∀ i : Fin 5, z (firstIndex i) = 0) ∧ z 5 + z 6 - z 7 = 0

private instance (z : Lattice) : Decidable (inOrthogonalTail z) := by
  unfold inOrthogonalTail
  infer_instance

private theorem code_perp (k : Fin 240) :
    inOrthogonalTail (code k) ↔ ∃ i, a2Code i = code k := by
  fin_cases k <;> decide

private theorem a2_in_tail (i : Fin 6) : inOrthogonalTail (a2Code i) := by
  fin_cases i <;> decide

private theorem realize_perp (z : Lattice) : realize z ∈ rankSixᗮ ↔ inOrthogonalTail z := by
  rw [tail_coordinates]
  change ((∀ i : Fin 5, (z (firstIndex i) : ℝ) / 2 = 0) ∧
    (z 5 : ℝ) / 2 + (z 6 : ℝ) / 2 - (z 7 : ℝ) / 2 = 0) ↔
    (∀ i : Fin 5, z (firstIndex i) = 0) ∧ z 5 + z 6 - z 7 = 0
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => ?_, ?_⟩
    · exact_mod_cast (show (z (firstIndex i) : ℝ) = 0 by linarith [h₁ i])
    · exact_mod_cast (show (z 5 : ℝ) + (z 6 : ℝ) - (z 7 : ℝ) = 0 by linarith)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun i => by simp [h₁ i], ?_⟩
    have h : (z 5 : ℝ) + (z 6 : ℝ) - (z 7 : ℝ) = 0 := by exact_mod_cast h₂
    linarith

theorem a2_exact (v : Ambient) :
    v ∈ a2Roots ↔ v ∈ roots ∧ v ∈ rankSixᗮ := by
  classical
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨realized_mem (a2_code_in_roots i), (realize_perp _).mpr (a2_in_tail i)⟩
  · rintro ⟨hv, ho⟩
    obtain ⟨k, rfl⟩ := mem_roots.mp hv
    obtain ⟨i, hi⟩ := (code_perp k).mp ((realize_perp _).mp ho)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg realize hi⟩

private def doubledWeight (z : Lattice) : ℤ × ℤ := (z 5 - z 6, z 6 + z 7)

private def fundamentalCode (f : Fin 3) : ℤ × ℤ := ![(2, 0), (-2, 2), (0, -2)] f

private theorem generation_code_weight (f : Fin 3) (i : Fin 27) :
    doubledWeight (generationCode f i) = fundamentalCode f := by
  fin_cases f <;> fin_cases i <;> decide

theorem generation_weight (f : Fin 3) (i : Fin 27) :
    familyWeight (generationRoot f i) = fundamentalWeight f := by
  have h := generation_code_weight f i
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext
  · change (generationCode f i 5 : ℝ) / 2 - (generationCode f i 6 : ℝ) / 2 = _
    change generationCode f i 5 - generationCode f i 6 = _ at h₁
    have he : (generationCode f i 5 : ℝ) - (generationCode f i 6 : ℝ) =
        ((fundamentalCode f).1 : ℝ) := by exact_mod_cast h₁
    fin_cases f <;> norm_num [fundamentalCode, fundamentalWeight] at he ⊢ <;> linarith
  · change (generationCode f i 6 : ℝ) / 2 + (generationCode f i 7 : ℝ) / 2 = _
    change generationCode f i 6 + generationCode f i 7 = _ at h₂
    have he : (generationCode f i 6 : ℝ) + (generationCode f i 7 : ℝ) =
        ((fundamentalCode f).2 : ℝ) := by exact_mod_cast h₂
    fin_cases f <;> norm_num [fundamentalCode, fundamentalWeight] at he ⊢ <;> linarith

theorem generation_steps (i : Fin 27) :
    generationRoot 1 i = generationRoot 0 i - familySimple 0 ∧
      generationRoot 2 i = generationRoot 1 i - familySimple 1 := by
  simp only [generationRoot, familySimple, generationCode, realize_sub]
  change realize (highestCode i) - realize (familySimpleCode 0) =
      realize (highestCode i) - realize (0 : Lattice) - realize (familySimpleCode 0) ∧
    realize (highestCode i) - realize (familySimpleCode 0 + familySimpleCode 1) =
      realize (highestCode i) - realize (familySimpleCode 0) - realize (familySimpleCode 1)
  have hz : realize (0 : Lattice) = 0 := by ext j; simp [realize]
  have ha : realize (familySimpleCode 0 + familySimpleCode 1) =
      realize (familySimpleCode 0) + realize (familySimpleCode 1) := by
    ext j
    change ((familySimpleCode 0 j + familySimpleCode 1 j : ℤ) : ℝ) / 2 = _
    push_cast
    change ((familySimpleCode 0 j : ℝ) + (familySimpleCode 1 j : ℝ)) / 2 =
      (familySimpleCode 0 j : ℝ) / 2 + (familySimpleCode 1 j : ℝ) / 2
    ring
  simp [hz, ha, sub_sub]

theorem generation_head (f : Fin 3) (i : Fin 27) (j : Fin 5) :
    generationRoot f i (firstIndex j) = (highestCode i (firstIndex j) : ℝ) / 2 := by
  have h : loweringOffset f (firstIndex j) = 0 := by
    fin_cases f <;> fin_cases j <;> decide
  change ((highestCode i (firstIndex j) - loweringOffset f (firstIndex j) : ℤ) : ℝ) / 2 = _
  simp [h]

def chargeCode (i : Fin 27) : ℤ := if i.val < 16 then 1 else if i.val < 26 then -2 else 4

theorem generation_charge (f : Fin 3) (i : Fin 27) :
    psiCharge (generationRoot f i) = (chargeCode i : ℝ) := by
  have hc : -(generationCode f i 5 + generationCode f i 6 - generationCode f i 7) =
      chargeCode i := by
    fin_cases f <;> fin_cases i <;> decide
  have he : -((generationCode f i 5 : ℝ) + (generationCode f i 6 : ℝ) -
      (generationCode f i 7 : ℝ)) = (chargeCode i : ℝ) := by exact_mod_cast hc
  change -2 * ((generationCode f i 5 : ℝ) / 2 + (generationCode f i 6 : ℝ) / 2 -
      (generationCode f i 7 : ℝ) / 2) = _
  linarith

set_option maxRecDepth 4096 in
private theorem highest_readout_injective :
    Function.Injective fun i : Fin 27 => fun j : Fin 5 => highestCode i (firstIndex j) := by
  intro i j
  have h : ∀ i j : Fin 27,
      (∀ k : Fin 5, highestCode i (firstIndex k) = highestCode j (firstIndex k)) → i = j := by
    intro i
    fin_cases i <;> decide
  intro hij
  exact h i j (congrFun hij)

private theorem fundamentalWeight_injective : Function.Injective fundamentalWeight := by
  intro f g h
  fin_cases f <;> fin_cases g <;> first
  | rfl
  | have hh := congrArg Prod.fst h
    norm_num [fundamentalWeight] at hh

private theorem family_injective :
    Function.Injective fun p : Fin 3 × Fin 27 => generationRoot p.1 p.2 := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  change generationRoot f i = generationRoot g j at h
  have hfg : f = g := fundamentalWeight_injective
    (by simpa only [generation_weight] using congrArg familyWeight h)
  subst g
  congr
  apply highest_readout_injective
  funext k
  have he := congrArg (fun v : Ambient => v (firstIndex k)) h
  simp only [generation_head] at he
  exact_mod_cast (show (highestCode i (firstIndex k) : ℝ) =
      (highestCode j (firstIndex k) : ℝ) by linarith)

theorem generation_injective (f : Fin 3) : Function.Injective (generationRoot f) := by
  intro i j h
  have he : (f, i) = (f, j) := family_injective h
  exact congrArg Prod.snd he

private theorem conjugate_injective :
    Function.Injective fun p : Fin 3 × Fin 27 => -generationRoot p.1 p.2 := by
  intro i j hij
  exact family_injective (neg_injective hij)

private theorem fiber_cards (f : Fin 3) :
    (generationFiber f).card = 27 ∧ (conjugateFiber f).card = 27 := by
  classical
  constructor
  · rw [generationFiber, Finset.card_image_of_injective _ (generation_injective f)]
    simp
  · have hi : Function.Injective (fun i => -generationRoot f i) :=
      neg_injective.comp (generation_injective f)
    rw [conjugateFiber, Finset.card_image_of_injective _ hi]
    simp

private theorem card_generation_charge (f : Fin 3) (q : ℤ) :
    ((generationFiber f).filter fun v => psiCharge v = (q : ℝ)).card =
      ((Finset.univ : Finset (Fin 27)).filter fun i => chargeCode i = q).card := by
  classical
  rw [generationFiber, Finset.filter_image,
    Finset.card_image_of_injective _ (generation_injective f)]
  congr 1
  ext i
  simp [generation_charge]

theorem generation_charge_cards (f : Fin 3) :
    ((generationFiber f).filter fun v => psiCharge v = 1).card = 16 ∧
    ((generationFiber f).filter fun v => psiCharge v = -2).card = 10 ∧
    ((generationFiber f).filter fun v => psiCharge v = 4).card = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (card_generation_charge f 1).trans (by decide : _ = 16)
  · simpa using (card_generation_charge f (-2)).trans (by decide : _ = 10)
  · simpa using (card_generation_charge f 4).trans (by decide : _ = 1)

private theorem rep_cards : rep27x3Roots.card = 81 ∧ rep27barx3barRoots.card = 81 := by
  classical
  constructor
  · rw [rep27x3Roots, Finset.card_image_of_injective _ family_injective]
    norm_num
  · rw [rep27barx3barRoots, Finset.card_image_of_injective _ conjugate_injective]
    norm_num

private theorem neg_weight (f : Fin 3) (i : Fin 27) :
    familyWeight (-generationRoot f i) = -(fundamentalWeight f) := by
  rw [← generation_weight f i]
  apply Prod.ext <;> simp [familyWeight] <;> ring

private def a2Weight (i : Fin 6) : ℝ × ℝ :=
  ![(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)] i

private theorem a2_weight (i : Fin 6) :
    familyWeight (realize (a2Code i)) = a2Weight i := by
  fin_cases i <;> apply Prod.ext <;>
    norm_num [familyWeight, a2Weight, realize, a2Code, familySimpleCode]

private theorem e6_weight {v : Ambient} (h : v ∈ ExceptionalSix.roots) :
    familyWeight v = (0, 0) := by
  obtain ⟨h₁, h₂⟩ : v 5 = v 6 ∧ v 6 = -v 7 :=
    ExceptionalSix.roots_rank_six.1 v h
  exact Prod.ext (sub_eq_zero.mpr h₁) (by change v 6 + v 7 = 0; linarith)

private def weightCode (p : Fin 4) (i : Fin 6) : ℤ × ℤ :=
  ![(0, 0), ![(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)] i,
    ![(1, 0), (-1, 1), (0, -1)] (Fin.ofNat 3 i.val),
    ![(-1, 0), (1, -1), (0, 1)] (Fin.ofNat 3 i.val)] p

private theorem weightCode_unique (p q : Fin 4) (i j : Fin 6) (h : p ≠ q) :
    weightCode p i ≠ weightCode q j := by
  have he : ∀ p q : Fin 4, ∀ i j : Fin 6, p ≠ q → weightCode p i ≠ weightCode q j := by decide
  exact he p q i j h

private def castWeight (w : ℤ × ℤ) : ℝ × ℝ := ((w.1 : ℝ), (w.2 : ℝ))

private theorem castWeight_injective : Function.Injective castWeight := by
  intro a b h
  have hf : (a.1 : ℝ) = (b.1 : ℝ) := congrArg Prod.fst h
  have hs : (a.2 : ℝ) = (b.2 : ℝ) := congrArg Prod.snd h
  exact Prod.ext (by exact_mod_cast hf) (by exact_mod_cast hs)

private theorem part_weight {p : Fin 4} {v : Ambient} (hv : v ∈ branchPart p) :
    ∃ i, familyWeight v = castWeight (weightCode p i) := by
  classical
  fin_cases p
  · exact ⟨0, by simpa [weightCode, castWeight] using e6_weight hv⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show v ∈ a2Roots from hv)
    exact ⟨i, by fin_cases i <;> norm_num [a2_weight, a2Weight, weightCode, castWeight]⟩
  · obtain ⟨⟨f, i⟩, _, rfl⟩ := Finset.mem_image.mp (show v ∈ rep27x3Roots from hv)
    have hf := generation_weight f i
    exact ⟨Fin.castLE (by decide : 3 ≤ 6) f,
      by fin_cases f <;> norm_num [fundamentalWeight, weightCode, castWeight, Fin.ofNat, Fin.castLE] at hf ⊢ <;> exact hf⟩
  · obtain ⟨⟨f, i⟩, _, rfl⟩ := Finset.mem_image.mp (show v ∈ rep27barx3barRoots from hv)
    have hf := neg_weight f i
    exact ⟨Fin.castLE (by decide : 3 ≤ 6) f,
      by fin_cases f <;> norm_num [fundamentalWeight, weightCode, castWeight, Fin.ofNat, Fin.castLE] at hf ⊢ <;> exact hf⟩

private theorem parts_disjoint : Pairwise (fun p q : Fin 4 => Disjoint (branchPart p) (branchPart q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨i, hi⟩ := part_weight hv
  obtain ⟨j, hj⟩ := part_weight hw
  exact weightCode_unique p q i j hpq (castWeight_injective (hi.symm.trans hj))

theorem partition :
    ExceptionalSix.roots ∪ a2Roots ∪ rep27x3Roots ∪ rep27barx3barRoots = roots ∧
    Pairwise (fun p q : Fin 4 => Disjoint (branchPart p) (branchPart q)) ∧
    ExceptionalSix.roots.card = 72 ∧ a2Roots.card = 6 ∧
    rep27x3Roots.card = 81 ∧ rep27barx3barRoots.card = 81 := by
  classical
  have d01 : Disjoint ExceptionalSix.roots a2Roots := parts_disjoint (by decide : (0 : Fin 4) ≠ 1)
  have d02 : Disjoint ExceptionalSix.roots rep27x3Roots := parts_disjoint (by decide : (0 : Fin 4) ≠ 2)
  have d03 : Disjoint ExceptionalSix.roots rep27barx3barRoots := parts_disjoint (by decide : (0 : Fin 4) ≠ 3)
  have d12 : Disjoint a2Roots rep27x3Roots := parts_disjoint (by decide : (1 : Fin 4) ≠ 2)
  have d13 : Disjoint a2Roots rep27barx3barRoots := parts_disjoint (by decide : (1 : Fin 4) ≠ 3)
  have d23 : Disjoint rep27x3Roots rep27barx3barRoots := parts_disjoint (by decide : (2 : Fin 4) ≠ 3)
  have du2 : Disjoint (ExceptionalSix.roots ∪ a2Roots) rep27x3Roots :=
    Finset.disjoint_union_left.mpr ⟨d02, d12⟩
  have du3 : Disjoint (ExceptionalSix.roots ∪ a2Roots ∪ rep27x3Roots) rep27barx3barRoots :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d03, d13⟩, d23⟩
  obtain ⟨h₁, h₂⟩ := rep_cards
  refine ⟨?_, parts_disjoint, ExceptionalSix.card_roots, a2_card, h₁, h₂⟩
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with ((hv | hv) | hv) | hv
    · exact ExceptionalEight.six_subset hv
    · exact a2_subset hv
    · obtain ⟨⟨f, i⟩, _, rfl⟩ := Finset.mem_image.mp hv
      exact generationRoot_mem f i
    · obtain ⟨⟨f, i⟩, _, rfl⟩ := Finset.mem_image.mp hv
      exact root_neg (generationRoot_mem f i)
  · rw [Finset.card_union_of_disjoint du3, Finset.card_union_of_disjoint du2,
      Finset.card_union_of_disjoint d01, ExceptionalEight.card_roots,
      ExceptionalSix.card_roots, a2_card, h₁, h₂]

theorem weight_fibers (f : Fin 3) :
    (∀ v, v ∈ generationFiber f ↔ v ∈ roots ∧ familyWeight v = fundamentalWeight f) ∧
    (∀ v, v ∈ conjugateFiber f ↔ v ∈ roots ∧ familyWeight v = -(fundamentalWeight f)) ∧
    (generationFiber f).card = 27 ∧ (conjugateFiber f).card = 27 := by
  classical
  have hp (p : Fin 4) {v : Ambient} (hv : v ∈ branchPart p)
      (h : familyWeight v = fundamentalWeight f) : p = 2 := by
    by_contra hp
    obtain ⟨j, hj⟩ := part_weight hv
    have hk : fundamentalWeight f =
        castWeight (weightCode 2 (Fin.castLE (by decide : 3 ≤ 6) f)) := by
      fin_cases f <;> norm_num [fundamentalWeight, weightCode, castWeight, Fin.ofNat, Fin.castLE]
    exact weightCode_unique p 2 j _ hp (castWeight_injective (hj.symm.trans (h.trans hk)))
  have hn (p : Fin 4) {v : Ambient} (hv : v ∈ branchPart p)
      (h : familyWeight v = -(fundamentalWeight f)) : p = 3 := by
    by_contra hp
    obtain ⟨j, hj⟩ := part_weight hv
    have hk : -(fundamentalWeight f) =
        castWeight (weightCode 3 (Fin.castLE (by decide : 3 ≤ 6) f)) := by
      fin_cases f <;> norm_num [fundamentalWeight, weightCode, castWeight, Fin.ofNat, Fin.castLE]
    exact weightCode_unique p 3 j _ hp (castWeight_injective (hj.symm.trans (h.trans hk)))
  have hex {v : Ambient} (hv : v ∈ roots) : ∃ p, v ∈ branchPart p := by
    rw [← partition.1] at hv
    simp only [Finset.mem_union] at hv
    rcases hv with ((h | h) | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  refine ⟨?_, ?_, fiber_cards f⟩
  · intro v
    constructor
    · intro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨generationRoot_mem f i, generation_weight f i⟩
    · rintro ⟨hv, hw⟩
      obtain ⟨p, h⟩ := hex hv
      obtain rfl := hp p h hw
      obtain ⟨⟨g, i⟩, _, rfl⟩ := Finset.mem_image.mp (show v ∈ rep27x3Roots from h)
      rw [generation_weight] at hw
      obtain rfl := fundamentalWeight_injective hw
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro v
    constructor
    · intro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨root_neg (generationRoot_mem f i), neg_weight f i⟩
    · rintro ⟨hv, hw⟩
      obtain ⟨p, h⟩ := hex hv
      obtain rfl := hn p h hw
      obtain ⟨⟨g, i⟩, _, rfl⟩ := Finset.mem_image.mp (show v ∈ rep27barx3barRoots from h)
      rw [neg_weight] at hw
      obtain rfl := fundamentalWeight_injective (neg_injective hw)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end OmegaMath.ExceptionalEightBranching

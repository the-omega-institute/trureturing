/- GID: D5/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/MajoranaFourteenModeDistanceFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Parity Majorana codes with a logical qubit need sixteen modes for distance four. -/

import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Hastings, arXiv:1703.00612v1, `c.tex` lines 86–117 and 272–273.
The source identifies stabilizers with self-orthogonal binary subspaces, requires
the all-ones parity stabilizer, and defines distance by the least weight in the
commutant outside the stabilizer subspace. Preregistration: issue #23984.
The inequality `2 * finrank C < n` is the source's positive logical-qubit count.
Admission basis: open-problem-resolution. This file is the mathematical source;
publication and freezing belong to the caller.
-/

open scoped BigOperators
open Matrix

noncomputable section

namespace D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour

/-- The weight of the Majorana product is the Hamming weight of its bit string
(Hastings, source line 113). This directly reuses Mathlib's Hamming norm. -/
def weight {ι : Type*} [Fintype ι] (v : ι → ZMod 2) : ℕ := hammingNorm v

/-- Stabilizer subspaces are pairwise orthogonal, including each vector with
itself (Hastings, source lines 94–97). -/
def IsSelfOrthogonal {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) : Prop :=
  ∀ x ∈ c, ∀ y ∈ c, x ⬝ᵥ y = 0

/-- Products commuting with every stabilizer (source lines 107–108).
Mathlib's orthogonal complement uses the other dot-product argument, which is
equal by commutativity over the binary field. -/
def commutant {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  LinearMap.BilinForm.orthogonal
    (dotProductBilin (ZMod 2) (ZMod 2) : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) c

/-- Hastings's belief for at most fourteen modes: under the parity convention
(lines 115–117), a positive logical-qubit count (lines 99–104) forces a logical
operator outside the stabilizers of weight below four (lines 107–113).
The fourteen-mode assertion is the belief at source lines 272–273. -/
def claim : Prop :=
  ∀ n : ℕ, n ≤ 14 → ∀ c : Submodule (ZMod 2) (Fin n → ZMod 2),
    IsSelfOrthogonal c → (fun _ => 1) ∈ c →
    2 * Module.finrank (ZMod 2) c < n →
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4

private lemma mem_commutant {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (v : ι → ZMod 2) :
    v ∈ commutant c ↔ ∀ x ∈ c, v ⬝ᵥ x = 0 := by
  change (∀ x ∈ c, x ⬝ᵥ v = 0) ↔ _
  simp only [dotProduct_comm]

private lemma binary_value (x : ZMod 2) : x = 0 ∨ x = 1 := by
  change (x : Fin 2) = 0 ∨ x = 1
  omega

private lemma parity_card {ι : Type*} [Fintype ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) : Even (Fintype.card ι) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := hc _ hp _ hp
  change (1 : ι → ZMod 2) ⬝ᵥ 1 = 0 at h
  rwa [one_dotProduct_one] at h

private lemma pair_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) : weight (Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) = 2 := by
  classical
  change (Finset.univ.filter fun a : ι =>
    (Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) a ≠ 0).card = 2
  have hs : (Finset.univ.filter fun a : ι =>
      (Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) a ≠ 0) = {i, j} := by
    ext a
    by_cases hai : a = i
    · subst a
      simp only [Finset.mem_filter, Finset.mem_univ, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, add_zero, one_ne_zero, and_self, Finset.mem_insert,
        true_or]
    · by_cases haj : a = j
      · subst a
        simp only [Finset.mem_filter, Finset.mem_univ, Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hij.symm, zero_add, one_ne_zero, and_self,
          Finset.mem_insert, Finset.mem_singleton, or_true]
      · simp only [Finset.mem_filter, Finset.mem_univ, Pi.add_apply,
          Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj, zero_add, ne_eq,
          not_true_eq_false, and_false, Finset.mem_insert, Finset.mem_singleton,
          hai, haj, or_self]
  rw [hs, Finset.card_pair hij]

private lemma pair_agreement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (i j : ι) (hp : Pi.single i 1 + Pi.single j 1 ∈ c) :
    ∀ x ∈ c, x i = x j := by
  intro x hx
  have h := hc x hx _ hp
  rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one] at h
  exact CharTwo.add_eq_zero.mp h

private lemma sum_remove_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (g : ι → ZMod 2) (hi : g i = 0) (hj : g j = 0) :
    ∑ a, g a = ∑ a : {a : ι // a ≠ i ∧ a ≠ j}, g a.val := by
  classical
  let t := Finset.univ.filter (fun a : ι => a ≠ i ∧ a ≠ j)
  have hs : ∑ a ∈ t, g a = ∑ a, g a := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    have h : a = i ∨ a = j := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or,
        not_not] using hnot
    rcases h with rfl | rfl <;> assumption
  exact hs.symm.trans (Finset.sum_subtype t (by intro x; simp only [t, Finset.mem_filter,
    Finset.mem_univ, true_and]) g)

private lemma remove_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (i j : ι) (hij : i ≠ j)
    (hv : Pi.single i 1 + Pi.single j 1 ∈ c) :
    ∃ d : Submodule (ZMod 2) ({a : ι // a ≠ i ∧ a ≠ j} → ZMod 2),
      IsSelfOrthogonal d ∧ (fun _ => 1) ∈ d ∧
      Module.finrank (ZMod 2) d + 1 = Module.finrank (ZMod 2) c ∧
      Fintype.card {a : ι // a ≠ i ∧ a ≠ j} + 2 = Fintype.card ι ∧
      (∀ v ∈ commutant d, v ∉ d → weight v < 4 →
        ∃ w ∈ commutant c, w ∉ c ∧ weight w < 4) := by
  classical
  let ev : c →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i).comp c.subtype
  let res : LinearMap.ker ev →ₗ[ZMod 2] ({a : ι // a ≠ i ∧ a ≠ j} → ZMod 2) :=
    { toFun := fun x a => x.val.val a.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have zero_i (x : LinearMap.ker ev) : x.val.val i = 0 := x.property
  have zero_j (x : LinearMap.ker ev) : x.val.val j = 0 :=
    (pair_agreement c hc i j hv _ x.val.property).symm.trans (zero_i x)
  have res_inj : Function.Injective res := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext a
    by_cases hai : a = i
    · subst a
      rw [zero_i, zero_i]
    · by_cases haj : a = j
      · subst a
        rw [zero_j, zero_j]
      · exact congrFun h ⟨a, hai, haj⟩
  refine ⟨LinearMap.range res, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    have hh := hc _ a.val.property _ b.val.property
    change (∑ t, a.val.val t * b.val.val t) = 0 at hh
    change (∑ t : {a : ι // a ≠ i ∧ a ≠ j}, a.val.val t.val * b.val.val t.val) = 0
    rw [← sum_remove_pair i j (fun t => a.val.val t * b.val.val t)
      (by rw [zero_i, zero_mul]) (by rw [zero_j, zero_mul])]
    exact hh
  · let y : c := ⟨(fun _ => 1) + (Pi.single i 1 + Pi.single j 1), c.add_mem hp hv⟩
    have hy : y ∈ LinearMap.ker ev := by
      change 1 + ((Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) i) = 0
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
        add_zero, CharTwo.add_self_eq_zero]
    refine ⟨⟨y, hy⟩, ?_⟩
    funext a
    change 1 + ((Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) a.val) = 1
    simp only [Pi.add_apply, Pi.single_eq_of_ne a.property.1,
      Pi.single_eq_of_ne a.property.2, zero_add, add_zero]
  · have hev : Function.Surjective ev := by
      intro z
      refine ⟨z • ⟨(fun _ => 1), hp⟩, ?_⟩
      change z * 1 = z
      exact mul_one z
    have hdim := ev.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hev, finrank_top, Module.finrank_self] at hdim
    rw [LinearMap.finrank_range_of_inj res_inj]
    omega
  · rw [Fintype.card_subtype]
    have ht : (Finset.univ.filter fun a : ι => a ≠ i ∧ a ≠ j) =
        Finset.univ \ {i, j} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton, not_or]
    rw [ht, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hij,
      Finset.card_univ]
    have hh := Finset.card_le_card (Finset.subset_univ ({i, j} : Finset ι))
    rw [Finset.card_pair hij, Finset.card_univ] at hh
    omega
  · intro v hvc hvd hvw
    let w : ι → ZMod 2 := fun a => if h : a ≠ i ∧ a ≠ j then v ⟨a, h⟩ else 0
    have wi : w i = 0 := dite_eq_right (by simp only [ne_eq, not_true_eq_false, false_and, not_false_eq_true])
    have wj : w j = 0 := dite_eq_right (by simp only [ne_eq, not_true_eq_false, and_false, not_false_eq_true])
    have wrest (a : {a : ι // a ≠ i ∧ a ≠ j}) : w a.val = v a := dite_eq_left a.property
    refine ⟨w, ?_, ?_, ?_⟩
    · rw [mem_commutant] at hvc ⊢
      intro x hx
      let y : c := ⟨x + x i • (Pi.single i 1 + Pi.single j 1),
        c.add_mem hx (c.smul_mem _ hv)⟩
      have hy : y ∈ LinearMap.ker ev := by
        change x i + x i * ((Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) i) = 0
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
          add_zero, mul_one, CharTwo.add_self_eq_zero]
      have hh := hvc (res ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
      change (∑ a, v a * (res ⟨y, hy⟩) a) = 0 at hh
      change (∑ a, w a * x a) = 0
      rw [sum_remove_pair i j _ (by rw [wi, zero_mul]) (by rw [wj, zero_mul])]
      convert hh using 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [wrest]
      change v a * x a.val = v a *
        (x a.val + x i * ((Pi.single i 1 + Pi.single j 1 : ι → ZMod 2) a.val))
      simp only [Pi.add_apply, Pi.single_eq_of_ne a.property.1,
        Pi.single_eq_of_ne a.property.2, zero_add, mul_zero, add_zero]
    · intro hwc
      have hwker : (⟨w, hwc⟩ : c) ∈ LinearMap.ker ev := wi
      apply hvd
      refine ⟨⟨⟨w, hwc⟩, hwker⟩, ?_⟩
      exact funext wrest
    · have hw : weight w = weight v := by
        change (Finset.univ.filter fun a => w a ≠ 0).card =
          (Finset.univ.filter fun a => v a ≠ 0).card
        symm
        apply Finset.card_bij (fun a _ => a.val)
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          rwa [wrest]
        · intro a ha b hb hab
          exact Subtype.ext hab
        · intro a ha
          have hwa : w a ≠ 0 := (Finset.mem_filter.mp ha).2
          have hp : a ≠ i ∧ a ≠ j := by
            by_contra h
            exact hwa (dite_eq_right h)
          refine ⟨⟨a, hp⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rwa [← wrest ⟨a, hp⟩]
      rwa [hw]

private lemma column_encoding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hp : (fun _ => 1) ∈ c)
    (hn : 0 < Fintype.card ι)
    (hs : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ commutant c) :
    ∃ k : ℕ, k + 1 = Module.finrank (ZMod 2) c ∧
      ∃ r : Fin k → c, Function.Injective (fun i : ι => fun a : Fin k => (r a).val i) := by
  classical
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp hn
  let ev : c →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i₀).comp c.subtype
  have hev : Function.Surjective ev := by
    intro z
    refine ⟨z • ⟨(fun _ => 1), hp⟩, ?_⟩
    change z * 1 = z
    exact mul_one z
  have hdim := ev.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hev, finrank_top, Module.finrank_self] at hdim
  let k := Module.finrank (ZMod 2) (LinearMap.ker ev)
  let b := Module.finBasis (ZMod 2) (LinearMap.ker ev)
  refine ⟨k, by omega, (fun a => (b a).val), ?_⟩
  intro i j heq
  by_contra hij
  apply hs i j hij
  rw [mem_commutant]
  intro x hx
  rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct]
  apply CharTwo.add_eq_zero.mpr
  let y : c := ⟨x + x i₀ • (fun _ => 1), c.add_mem hx (c.smul_mem _ hp)⟩
  have hy : y ∈ LinearMap.ker ev := by
    change x i₀ + x i₀ * 1 = 0
    rw [mul_one, CharTwo.add_self_eq_zero]
  have hlinear :
      (LinearMap.proj i).comp (c.subtype.comp (LinearMap.ker ev).subtype) =
        (LinearMap.proj j).comp (c.subtype.comp (LinearMap.ker ev).subtype) := by
    apply b.ext
    intro a
    exact congrFun heq a
  have hxy := DFunLike.congr_fun hlinear ⟨y, hy⟩
  change x i + x i₀ * 1 = x j + x i₀ * 1 at hxy
  exact add_right_cancel hxy

private lemma column_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (k : ℕ) (r : Fin k → c)
    (hi : Function.Injective (fun i : ι => fun a : Fin k => (r a).val i)) :
    let s := Finset.univ.image (fun i : ι => fun a : Fin k => (r a).val i)
    s.card = Fintype.card ι ∧
      ∀ a : Finset (Fin k), a.card ≤ 2 →
        ∑ x : Fin k → ZMod 2, (if x ∈ s then (1 : ZMod 2) else 0) *
          ∏ b ∈ a, x b = 0 := by
  classical
  dsimp only
  refine ⟨Finset.card_image_of_injective _ hi, ?_⟩
  intro a ha
  have transfer :
      (∑ x : Fin k → ZMod 2,
        (if x ∈ Finset.univ.image (fun i : ι => fun b : Fin k => (r b).val i)
          then (1 : ZMod 2) else 0) * ∏ b ∈ a, x b) =
        ∑ i : ι, ∏ b ∈ a, (r b).val i := by
    rw [show (∑ x : Fin k → ZMod 2,
      (if x ∈ Finset.univ.image (fun i : ι => fun b : Fin k => (r b).val i)
        then (1 : ZMod 2) else 0) * ∏ b ∈ a, x b) =
      ∑ x ∈ Finset.univ.image (fun i : ι => fun b : Fin k => (r b).val i),
        ∏ b ∈ a, x b from by
          simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
            Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]]
    exact Finset.sum_image (fun i _ j _ h => hi h)
  rw [transfer]
  by_cases hz : a.card = 0
  · have he := Finset.card_eq_zero.mp hz
    subst a
    have hh := hc _ hp _ hp
    change (∑ i : ι, (1 : ZMod 2) * 1) = 0 at hh
    simpa only [Finset.prod_empty, mul_one] using hh
  · by_cases ho : a.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp ho
      have hh := hc _ (r b).property _ hp
      change (∑ i : ι, (r b).val i * 1) = 0 at hh
      simpa only [Finset.prod_singleton, mul_one] using hh
    · obtain ⟨b, d, hbd, rfl⟩ := Finset.card_eq_two.mp (show a.card = 2 by omega)
      have hh := hc _ (r b).property _ (r d).property
      change (∑ i : ι, (r b).val i * (r d).val i) = 0 at hh
      simpa only [Finset.prod_pair hbd] using hh

private lemma boolean_expansion (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (x : Fin k → ZMod 2) :
    f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∑ y : Fin k → ZMod 2, f y * ∏ i ∈ Finset.univ \ a, y i) *
        ∏ i ∈ a, (x i + 1) := by
  classical
  have delta (y : Fin k → ZMod 2) :
      (∏ i, (x i + 1 + y i)) = if y = x then 1 else 0 := by
    by_cases hy : y = x
    · subst y
      have he (i : Fin k) : x i + 1 + x i = 1 := by
        rcases binary_value (x i) with h | h <;> rw [h] <;> decide
      simp only [he, Finset.prod_const_one, ite_true]
    · rw [ite_eq_right hy]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rcases binary_value (x i) with hx | hx <;>
        rcases binary_value (y i) with hyi | hyi
      all_goals rw [hx, hyi] at hi ⊢
      all_goals first | exact (hi rfl).elim | decide
  calc
    f x = ∑ y : Fin k → ZMod 2, f y * ∏ i, (x i + 1 + y i) := by
      simp only [delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
    _ = ∑ y : Fin k → ZMod 2,
        ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
          f y * ((∏ i ∈ a, (x i + 1)) * ∏ i ∈ Finset.univ \ a, y i) := by
      simp only [Finset.prod_add, Finset.mul_sum]
    _ = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
        (∑ y : Fin k → ZMod 2, f y * ∏ i ∈ Finset.univ \ a, y i) *
          ∏ i ∈ a, (x i + 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      ring

private lemma moment_degree (k : ℕ) (hk : 3 ≤ k)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (hm : ∀ a : Finset (Fin k), a.card ≤ 2 → ∑ x, f x * ∏ i ∈ a, x i = 0) :
    ∃ q : Finset (Fin k) → ZMod 2,
      (∀ a, k - 3 < a.card → q a = 0) ∧
      ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
        q a * ∏ i ∈ a, (x i + 1) := by
  classical
  refine ⟨(fun a => ∑ y : Fin k → ZMod 2, f y * ∏ i ∈ Finset.univ \ a, y i), ?_, ?_⟩
  · intro a ha
    apply hm
    have hc : (Finset.univ \ a).card = k - a.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ a), Finset.card_univ,
        Fintype.card_fin]
    rw [hc]
    omega
  · intro x
    exact boolean_expansion k f x

private lemma affine_weight (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 1 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) :
    weight f = 0 ∨ 2 * weight f = 2 ^ k ∨ weight f = 2 ^ k := by
  classical
  have derivative (x u : Fin k → ZMod 2) : f (x + u) + f x = f u + f 0 := by
    rw [hf (x + u), hf x, hf u, hf 0, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hz : a.card = 0
    · rw [Finset.card_eq_zero.mp hz]
      simp only [Finset.prod_empty, mul_one, CharTwo.add_self_eq_zero]
    · by_cases ho : a.card = 1
      · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp ho
        simp only [Finset.prod_singleton, Pi.add_apply, Pi.zero_apply]
        ring_nf
        simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]
      · rw [hq a (by omega)]
        simp only [zero_mul, zero_add]
  by_cases hc : ∀ x, f x = f 0
  · rcases binary_value (f 0) with hz | ho
    · left
      have he : f = 0 := funext fun x => (hc x).trans hz
      change hammingNorm f = 0
      rw [he, hammingNorm_zero]
    · right; right
      have he : f = fun _ => 1 := funext fun x => (hc x).trans ho
      rw [he]
      change (Finset.univ.filter fun _ : Fin k → ZMod 2 => (1 : ZMod 2) ≠ 0).card = _
      simp only [ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true, Finset.card_univ, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
  · obtain ⟨u, hu⟩ := not_forall.mp hc
    have huone : f u + f 0 = 1 := by
      rcases binary_value (f u) with h | h <;>
        rcases binary_value (f 0) with hzero | hzero
      all_goals rw [h, hzero] at hu ⊢
      all_goals first | exact (hu rfl).elim | decide
    have flip (x : Fin k → ZMod 2) : f (x + u) = f x + 1 := by
      have hh := derivative x u
      rw [huone] at hh
      exact (CharTwo.add_eq_iff_eq_add.mp hh).trans (add_comm _ _)
    have count : (∑ x, if f x = 0 then (0 : ℕ) else 1) = weight f := by
      change (∑ x, if f x = 0 then (0 : ℕ) else 1) =
        (Finset.univ.filter fun x => f x ≠ 0).card
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, ite_not]
    have bij : (∑ x, if f (x + u) = 0 then (0 : ℕ) else 1) =
        ∑ x, if f x = 0 then (0 : ℕ) else 1 :=
      Equiv.sum_comp (Equiv.addRight u) _
    have each (x : Fin k → ZMod 2) :
        (if f x = 0 then (0 : ℕ) else 1) +
          (if f (x + u) = 0 then (0 : ℕ) else 1) = 1 := by
      rw [flip]
      rcases binary_value (f x) with h | h <;> rw [h] <;> decide
    have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun x _ => each x)
    rw [Finset.sum_add_distrib, bij, count] at total
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, smul_eq_mul, mul_one] at total
    exact Or.inr (Or.inl (by omega))

private lemma quadratic_polarization (k : ℕ)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 2 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) :
    ∀ u x y, f (x + y + u) + f (x + y) + f u + f 0 =
      (f (x + u) + f x + f u + f 0) + (f (y + u) + f y + f u + f 0) := by
  intro u x y
  simp only [hf, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : a.card = 0
  · rw [Finset.card_eq_zero.mp hz]
    simp only [Finset.prod_empty, mul_one, CharTwo.add_self_eq_zero, zero_add]
  · by_cases ho : a.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp ho
      simp only [Finset.prod_singleton, Pi.add_apply, Pi.zero_apply]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
        show (8 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]
    · by_cases ht : a.card = 2
      · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp ht
        simp only [Finset.prod_pair hij, Pi.add_apply, Pi.zero_apply]
        ring_nf
        simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide,
          show (8 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]
      · rw [hq a (by omega)]
        simp only [zero_mul, zero_add]

private lemma walsh_square (k : ℕ) (f : (Fin k → ZMod 2) → ZMod 2)
    (hb : ∀ u x y, f (x + y + u) + f (x + y) + f u + f 0 =
      (f (x + u) + f x + f u + f 0) + (f (y + u) + f y + f u + f 0)) :
    (2 ^ k : ℤ) ∣ (∑ x, if f x = 0 then (1 : ℤ) else -1) ^ 2 := by
  classical
  let χ : ZMod 2 → ℤ := fun a => if a = 0 then 1 else -1
  have χadd (a b : ZMod 2) : χ (a + b) = χ a * χ b := by
    rcases binary_value a with ha | ha <;>
      rcases binary_value b with hb | hb <;>
        subst a <;> subst b <;> decide
  have χzero : χ 0 = 1 := rfl
  let b := fun u x : Fin k → ZMod 2 => f (x + u) + f x + f u + f 0
  have badd (u x y : Fin k → ZMod 2) : b u (x + y) = b u x + b u y := hb u x y
  have linear_sum (u : Fin k → ZMod 2) :
      (∑ x, χ (b u x)) = 0 ∨ (∑ x, χ (b u x)) = 2 ^ k := by
    let ψ : AddChar (Fin k → ZMod 2) ℤ :=
      { toFun := fun x => χ (b u x)
        map_zero_eq_one' := by
          have hz : b u 0 = 0 := by
            change f (0 + u) + f 0 + f u + f 0 = 0
            rw [zero_add]
            ring_nf
            simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add]
          rw [hz, χzero]
        map_add_eq_mul' := fun x y => by rw [badd, χadd] }
    have hs := AddChar.sum_eq_ite ψ
    change (∑ x, χ (b u x)) = if ψ = 0 then (Fintype.card (Fin k → ZMod 2) : ℤ) else 0 at hs
    by_cases hz : ψ = 0
    · right
      simpa only [ite_eq_left hz, Fintype.card_fun, ZMod.card, Fintype.card_fin,
        Nat.cast_pow, Nat.cast_ofNat] using hs
    · exact Or.inl (by simpa only [ite_eq_right hz] using hs)
  have square : (∑ x, χ (f x)) ^ 2 = ∑ u, ∑ x, χ (f (x + u) + f x) := by
    rw [pow_two, Finset.sum_mul_sum]
    rw [Finset.sum_comm (f := fun u x => χ (f (x + u) + f x))]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (∑ y, χ (f x) * χ (f y)) = ∑ y, χ (f y + f x) := by
        simp only [χadd, mul_comm]
      _ = ∑ u, χ (f (x + u) + f x) :=
        (Equiv.sum_comp (Equiv.addLeft x) (fun y => χ (f y + f x))).symm
  change (2 ^ k : ℤ) ∣ (∑ x, χ (f x)) ^ 2
  rw [square]
  apply Finset.dvd_sum
  intro u hu
  have inner : (∑ x, χ (f (x + u) + f x)) =
      χ (f u + f 0) * ∑ x, χ (b u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have he : f (x + u) + f x = (f u + f 0) + b u x := by
      change f (x + u) + f x = (f u + f 0) + (f (x + u) + f x + f u + f 0)
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
    rw [he, χadd]
  rw [inner]
  rcases linear_sum u with hz | ht
  · rw [hz, mul_zero]
    exact dvd_zero _
  · rw [ht]
    exact dvd_mul_left _ _

private lemma quadratic_weight (k : ℕ) (hk : k = 5)
    (f : (Fin k → ZMod 2) → ZMod 2)
    (q : Finset (Fin k) → ZMod 2) (hq : ∀ a, 2 < a.card → q a = 0)
    (hf : ∀ x, f x = ∑ a ∈ (Finset.univ : Finset (Fin k)).powerset,
      q a * ∏ i ∈ a, (x i + 1)) : 4 ∣ weight f := by
  have hb := quadratic_polarization k f q hq hf
  have hw := walsh_square k f hb
  classical
  let w : ℤ := ∑ x, if f x = 0 then 1 else -1
  have hw32 : (32 : ℤ) ∣ w ^ 2 := by simpa only [hk, show (2 : ℤ) ^ 5 = 32 by decide] using hw
  have hw8 : (8 : ℤ) ∣ w := by
    have hmod := Int.emod_eq_zero_of_dvd hw32
    rw [pow_two, Int.mul_emod] at hmod
    have hlo := Int.emod_nonneg w (by decide : (32 : ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos w (by decide : (0 : ℤ) < 32)
    have hdiv := Int.emod_add_mul_ediv w 32
    apply Int.dvd_of_emod_eq_zero
    interval_cases h : w % 32 <;> norm_num [h] at hmod <;> omega
  have count : (∑ x, if f x = 0 then (0 : ℤ) else 1) = (weight f : ℤ) := by
    change (∑ x, if f x = 0 then (0 : ℤ) else 1) =
      ((Finset.univ.filter fun x => f x ≠ 0).card : ℤ)
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      Finset.sum_filter, ite_not, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  have relation : w = 2 ^ k - 2 * (weight f : ℤ) := by
    have each (x : Fin k → ZMod 2) :
        (if f x = 0 then (1 : ℤ) else -1) =
          1 - 2 * (if f x = 0 then (0 : ℤ) else 1) := by
      split_ifs <;> decide
    change (∑ x, if f x = 0 then (1 : ℤ) else -1) = _
    simp only [each, Finset.sum_sub_distrib, ← Finset.mul_sum, count,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  obtain ⟨t, ht⟩ := hw8
  have powk : (2 : ℤ) ^ k = 32 := by rw [hk]; decide
  rw [powk] at relation
  have hz : (4 : ℤ) ∣ (weight f : ℤ) := ⟨4 - t, by omega⟩
  exact_mod_cast hz

private lemma moments_obstruction (k : ℕ) (s : Finset (Fin k → ZMod 2))
    (hk : k ≤ 5) (hn : s.card ≤ 14) (hd : 2 * (k + 1) < s.card)
    (he : Even s.card)
    (hm : ∀ a : Finset (Fin k), a.card ≤ 2 →
      ∑ x, (if x ∈ s then (1 : ZMod 2) else 0) * ∏ i ∈ a, x i = 0) : False := by
  classical
  have hcard : weight (fun x => if x ∈ s then (1 : ZMod 2) else 0) = s.card := by
    change (Finset.univ.filter fun x => (if x ∈ s then (1 : ZMod 2) else 0) ≠ 0).card = _
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp only [Finset.mem_filter, Finset.mem_univ, hx,
      ite_true, ite_false, one_ne_zero, ne_eq, not_true_eq_false, not_false_eq_true,
      and_self, and_false]
  have cases : k = 4 ∨ k = 5 := by
    have hs := Finset.card_le_univ s
    have hu : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hu] at hs
    interval_cases k <;> norm_num at hs <;> omega
  obtain ⟨q, hq, hf⟩ := moment_degree k (by omega) _ hm
  rcases cases with hfour | hfive
  · have hw := affine_weight k _ q (by simpa only [hfour] using hq) hf
    rw [hcard] at hw
    have powk : 2 ^ k = 16 := by rw [hfour]
    rw [powk] at hw
    rcases hw with hw | hw | hw <;> omega
  · have hw := quadratic_weight k hfive _ q (by simpa only [hfive] using hq) hf
    rw [hcard] at hw
    obtain ⟨m, hm⟩ := he
    have hs : s.card = 14 := by omega
    rw [hs] at hw
    norm_num at hw

private lemma nondegenerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (hn : Fintype.card ι ≤ 14)
    (hd : 2 * Module.finrank (ZMod 2) c < Fintype.card ι)
    (hs : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ c) :
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4 := by
  classical
  by_contra h
  have hscomm : ∀ i j : ι, i ≠ j → Pi.single i 1 + Pi.single j 1 ∉ commutant c := by
    intro i j hij hv
    exact h ⟨_, hv, hs i j hij, by rw [pair_weight i j hij]; decide⟩
  obtain ⟨k, hk, r, hi⟩ := column_encoding c hp (by omega) hscomm
  obtain ⟨hcard, hm⟩ := column_moments c hc hp k r hi
  exact moments_obstruction k _ (by omega) (by omega) (by omega)
    (by rw [hcard]; exact parity_card c hc hp) hm

private lemma general_result {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Submodule (ZMod 2) (ι → ZMod 2)) (hc : IsSelfOrthogonal c)
    (hp : (fun _ => 1) ∈ c) (hn : Fintype.card ι ≤ 14)
    (hd : 2 * Module.finrank (ZMod 2) c < Fintype.card ι) :
    ∃ v ∈ commutant c, v ∉ c ∧ weight v < 4 := by
  classical
  induction hncard : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h m ih =>
    by_cases hs : ∃ i j : ι, i ≠ j ∧ Pi.single i 1 + Pi.single j 1 ∈ c
    · obtain ⟨i, j, hij, hv⟩ := hs
      obtain ⟨d, hdc, hdp, hdim, hsize, hlift⟩ := remove_pair c hc hp i j hij hv
      have smaller : Fintype.card {a : ι // a ≠ i ∧ a ≠ j} < m := by omega
      have short : ∃ v ∈ commutant d, v ∉ d ∧ weight v < 4 := by
        exact ih _ smaller d hdc hdp (by omega) (by omega) rfl
      obtain ⟨v, hvc, hvd, hvw⟩ := short
      exact hlift v hvc hvd hvw
    · apply nondegenerate c hc hp hn hd
      intro i j hij hv
      exact hs ⟨i, j, hij, hv⟩

/-- The preregistered bound, with the source's stabilizer, parity and distance
definitions and without any additional nondegeneracy assumption. -/
theorem result : claim := by
  intro n hn c hc hp hd
  exact general_result c hc hp (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin] using hd)

end D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour

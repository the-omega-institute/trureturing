/- GID: D5/S3/Quantum/StationaryPreparation/PaddingResidualGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingResidualGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact residual-coordinate overlap and normalized Gram. -/

import D5.S3.Quantum.StationaryPreparation.PaddingTransition
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PaddingResidualGram

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v w

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def occ (a : Multiset σ) (r : PaddingTransition.Box a) : Multiset σ :=
  ∑ i : σ, Multiset.replicate (r i).val i

def tailOcc (head : σ) (r : Multiset σ) : Multiset σ :=
  r.filter (fun i => i ≠ head)

def tailIndex (a : Multiset σ) (head : σ) (r : PaddingTransition.Box a) : PaddingTransition.Tail a head :=
  fun i => r i.val

def tailWord (a : Multiset σ) (head : σ) (b : PaddingTransition.Tail a head) : Multiset σ :=
  ∑ i : PaddingTransition.TailAlphabet head, Multiset.replicate (b i).val i.val

def slice (a : Multiset σ) (head : σ) (b : PaddingTransition.Tail a head) (j : ℕ) : Multiset σ :=
  Multiset.replicate j head + tailWord a head b

def M (r : Multiset σ) : ℕ := multiplicity r.card r

def m (a : Multiset σ) (head : σ) (b : PaddingTransition.Tail a head) (j : ℕ) : ℝ :=
  (M (slice a head b j) : ℝ)

def delta (a : Multiset σ) (head : σ) (b : PaddingTransition.Tail a head) (j : ℕ) : ℝ :=
  if j = 0 then m a head b 0 else m a head b j - m a head b (j - 1)

def lastTail (head : σ) (r : Multiset σ) : ℝ :=
  ((tailOcc head r).card : ℝ) * (M r : ℝ) / (r.card : ℝ)

def z (head : σ) (r : Multiset σ) : ℂ := if tailOcc head r = 0 then 1 else 0

def G (a : Multiset σ) (head : σ) : Matrix (PaddingTransition.Box a) (PaddingTransition.Box a) ℂ := fun r s =>
  if occ a s ≤ occ a r then
    (Real.sqrt (((M (occ a s) : ℝ) * (M (occ a r - occ a s) : ℝ)) /
      (M (occ a r) : ℝ)) : ℂ) * z head (occ a r - occ a s)
  else if occ a r ≤ occ a s then
    star ((Real.sqrt (((M (occ a r) : ℝ) * (M (occ a s - occ a r) : ℝ)) /
      (M (occ a s) : ℝ)) : ℂ) * z head (occ a s - occ a r))
  else 0

def D (a : Multiset σ) : Matrix (PaddingTransition.Box a) (PaddingTransition.Box a) ℂ :=
  Matrix.diagonal (fun r => (Real.sqrt (M (occ a r) : ℝ) : ℂ))

def block (a : Multiset σ) (head : σ) (b : PaddingTransition.Tail a head) :
    Matrix (Fin (a.count head + 1)) (Fin (a.count head + 1)) ℂ :=
  fun j k => (m a head b (min j.val k.val) : ℂ)

end

def L (A : ℕ) : Matrix (Fin (A + 1)) (Fin (A + 1)) ℂ :=
  fun j k => if k ≤ j then 1 else 0

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def B (a : Multiset σ) (head : σ) : Matrix (PaddingTransition.Box a) (PaddingTransition.Box a) ℂ := fun r s =>
  if tailIndex a head r = tailIndex a head s then
    block a head (tailIndex a head r) (r head) (s head) else 0

def padding (a : Multiset σ) (head : σ) (r : Multiset σ) : Space (PaddingTransition.K a head) :=
  WithLp.toLp 2 (fun q => match q with
    | none => if r ≤ a ∧ tailOcc head r = 0 then 1 else 0
    | some (b, j) =>
        if r ≤ a ∧ tailOcc head r = tailWord a head b.val ∧ j.val ≤ r.count head then
          (Real.sqrt (lastTail head (slice a head b.val j.val)) : ℂ) else 0)

def phi (a : Multiset σ) (head : σ) (r : Multiset σ) : Space (PaddingTransition.K a head) :=
  (Real.sqrt (M r : ℝ) : ℂ)⁻¹ • padding a head r

end

section
variable {A : Type u} [Fintype A] [DecidableEq A]

def tailCount (head : A) (b : Multiset A) : ℕ :=
  ∑ i : {i : A // i ≠ head}, b.count i.val

def lastTailMass (head : A) (b : Multiset A) : ℝ :=
  (tailCount head b : ℝ) * (multiplicity b.card b : ℝ) / (b.card : ℝ)

def headSlice (head : A) (b : Multiset A) (h : ℕ) : Multiset A :=
  Multiset.replicate h head + b.filter (fun i => i ≠ head)

def residualTail (head : A) (a b : Multiset A) (hb : b ≤ a) :
    TailBox (fun i : PaddingTransition.TailAlphabet head => a.count i.val) :=
  fun i => ⟨b.count i.val, Nat.lt_succ_of_le (Multiset.le_iff_count.mp hb i.val)⟩

def residualPaddingTail (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount head b) : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val) := by
  have tail_sum_eq_zero_iff {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) :
      tailSum b = 0 ↔ b = PaddingTransition.zeroTail c := by
    constructor
    · intro h
      have hz : ∀ i, (b i).val = 0 := by
        simpa only [tailSum, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
          using h
      funext i
      exact Fin.ext (hz i)
    · rintro rfl
      simp [tailSum, PaddingTransition.zeroTail]

  exact ⟨residualTail head a b hb, by
      intro hz
      have hh := (tail_sum_eq_zero_iff _ _).mpr hz
      change tailCount head b = 0 at hh
      omega⟩

def residualHeadIndex (head : A) (a b : Multiset A) (hb : b ≤ a)
    (h : Fin (b.count head + 1)) : Fin (a.count head + 1) :=
  ⟨h.val, lt_of_lt_of_le h.isLt (Nat.add_le_add_right (Multiset.le_iff_count.mp hb head) 1)⟩

def paddingResidual (head : A) (a b : Multiset A) : Space (PaddingTransition.K a head) := by
  exact if hb : b ≤ a then
      if hr : 0 < tailCount head b then
        ∑ h : Fin (b.count head + 1),
          (Real.sqrt (lastTailMass head (headSlice head b h.val)) : ℂ) •
            basis (some (residualPaddingTail head a b hb hr, residualHeadIndex head a b hb h))
      else basis none
    else 0

end

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def residualScale (r : Multiset σ) : ℝ := Real.sqrt (multiplicity r.card r : ℝ)

end

section
variable {A : Type u} [Fintype A] [DecidableEq A]

private theorem padding_residual_inner_positive (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
    inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  have head_add_tail_count {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      b.count head + tailCount head b = b.card := by
    unfold tailCount
    rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
    exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)
  have last_tail_mass_pos {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (hR : 0 < tailCount head b) :
      0 < lastTailMass head b := by
    have hn : 0 < b.card := by have := head_add_tail_count head b; omega
    unfold lastTailMass
    exact div_pos (mul_pos (by exact_mod_cast hR)
      (by exact_mod_cast multiplicity_pos b rfl)) (by exact_mod_cast hn)
  have head_slice_count_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (headSlice head b h).count head = h := by
    simp [headSlice, Multiset.count_filter]
  have head_slice_count_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (i : A) (hi : i ≠ head) : (headSlice head b h).count i = b.count i := by
    simp [head_slice_count_head, headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]
  have head_slice_tail_count {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      tailCount head (headSlice head b h) = tailCount head b := by
    apply Finset.sum_congr rfl
    intro i _
    exact head_slice_count_tail head b h i.val i.property
  have residual_tail_eq_iff {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b c : Multiset A)
      (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
      residualPaddingTail head a b hb hr = residualPaddingTail head a c hc hs ↔
        b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
    constructor
    · intro h
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp []
      · have he := congrArg (fun t : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val) =>
          (t.val ⟨i, hi⟩).val) h
        simpa [residualPaddingTail, residualTail, Multiset.count_filter, hi] using he
    · intro h
      apply Subtype.ext
      funext i
      apply Fin.ext
      have he := congrArg (Multiset.count i.val) h
      simpa [residualPaddingTail, residualTail, Multiset.count_filter, i.property] using he
  have padding_residual_none {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < tailCount head b) : paddingResidual head a b none = 0 := by
    simp [head_slice_count_head, paddingResidual, hb, hr, WithLp.ofLp_sum, Finset.sum_apply,
      basis_apply]
  have padding_residual_coordinates {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < tailCount head b)
      (t : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val))
      (k : Fin (a.count head + 1)) :
      paddingResidual head a b (some (t, k)) =
        if t = residualPaddingTail head a b hb hr ∧ k.val ≤ b.count head then
          (Real.sqrt (lastTailMass head (headSlice head b k.val)) : ℂ) else 0 := by
    classical
    rw [paddingResidual, dif_pos hb, dif_pos hr]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      basis_apply, Option.some.injEq, Prod.mk.injEq]
    by_cases ht : t = residualPaddingTail head a b hb hr
    · subst t
      by_cases hk : k.val ≤ b.count head
      · rw [if_pos ⟨rfl, hk⟩]
        let j : Fin (b.count head + 1) := ⟨k.val, Nat.lt_succ_of_le hk⟩
        rw [Finset.sum_eq_single j]
        · simp [head_slice_count_head, j, residualHeadIndex]
        · intro i _ hij
          have hi : k ≠ residualHeadIndex head a b hb i := by
            intro he
            apply hij
            exact Fin.ext (congrArg Fin.val he).symm
          simp [head_slice_count_head, hi]
        · simp [head_slice_count_head]
      · rw [if_neg (by simp [head_slice_count_head, hk])]
        apply Finset.sum_eq_zero
        intro i _
        have hi : k ≠ residualHeadIndex head a b hb i := by
          intro he
          have := congrArg Fin.val he
          have := i.isLt
          simp only [residualHeadIndex] at *
          omega
        simp [head_slice_count_head, hi]
    · simp [head_slice_count_head, ht]
  have erase_multiplicity_real {A : Type u} [Fintype A] [DecidableEq A] (b : Multiset A) (i : A) (hi : i ∈ b) :
      (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
        (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
    have hn : (b.erase i).card + 1 = b.card := by
      simpa using congrArg Multiset.card (Multiset.cons_erase hi)
    have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
    rw [hn] at hm
    exact_mod_cast hm
  have head_slice_card {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (headSlice head b h).card = h + tailCount head b := by
    rw [← head_add_tail_count head, head_slice_count_head, head_slice_tail_count]
  have head_slice_erase_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (headSlice head b h).erase head = headSlice head b (h - 1) := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [head_slice_count_head]
    · rw [Multiset.count_erase_of_ne hi,
        head_slice_count_tail head b h i hi, head_slice_count_tail head b (h - 1) i hi]
  have last_tail_mass_head_slice {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hr : 0 < tailCount head b) (j : ℕ) :
      lastTailMass head (headSlice head b j) =
        if j = 0 then
          (multiplicity (headSlice head b 0).card (headSlice head b 0) : ℝ)
        else
          (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ) -
          (multiplicity (headSlice head b (j - 1)).card (headSlice head b (j - 1)) : ℝ) := by
    have hn : (0 : ℝ) < (headSlice head b j).card := by
      exact_mod_cast (show 0 < (headSlice head b j).card by rw [head_slice_card]; omega)
    by_cases hj : j = 0
    · subst j
      simp only [ite_true, lastTailMass, head_slice_tail_count, head_slice_card, zero_add]
      exact mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')
    · rw [if_neg hj]
      have hm := erase_multiplicity_real (headSlice head b j) head
        (Multiset.count_pos.mp (by simpa [head_slice_count_head] using Nat.pos_of_ne_zero hj))
      rw [head_slice_erase_head, head_slice_count_head] at hm
      have hs : ((headSlice head b j).card : ℝ) = j + (tailCount head b : ℝ) := by
        exact_mod_cast head_slice_card head b j
      unfold lastTailMass
      rw [head_slice_tail_count, div_eq_iff hn.ne']
      nlinarith [congrArg (fun x : ℝ =>
        x * (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ)) hs]
  have sum_last_tail_mass {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hr : 0 < tailCount head b) (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1), lastTailMass head (headSlice head b j)) =
        (multiplicity (headSlice head b n).card (headSlice head b n) : ℝ) := by
    simp_rw [last_tail_mass_head_slice head b hr]
    exact (Finset.eq_sum_range_sub' _ n).symm
  have sum_bounded_mass {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hr : 0 < tailCount head b) (n : ℕ) (hn : n ≤ a.count head) :
      (∑ k : Fin (a.count head + 1),
        if k.val ≤ n then (lastTailMass head (headSlice head b k.val) : ℂ) else 0) =
        (multiplicity (headSlice head b n).card (headSlice head b n) : ℂ) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0)]
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
        intro k _ hk
        have : ¬ k ≤ n := by simpa [head_slice_count_head, Finset.mem_range, Nat.lt_succ_iff] using hk
        simp [head_slice_count_head, this]
      _ = ∑ k ∈ Finset.range (n + 1),
          (lastTailMass head (headSlice head b k) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      _ = _ := by exact_mod_cast sum_last_tail_mass head b hr n
  have hg : inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      ∑ x, star (paddingResidual head a b x) * paddingResidual head a c x := by
    calc
      _ = inner ℂ (∑ x, paddingResidual head a b x • basis x)
          (∑ x, paddingResidual head a c x • basis x) :=
        congrArg₂ (inner ℂ) (basis_expansion _) (basis_expansion _)
      _ = _ := (EuclideanSpace.basisFun (PaddingTransition.K a head) ℂ).orthonormal.inner_sum
        (paddingResidual head a b) (paddingResidual head a c) Finset.univ

  classical
  rw [hg, Fintype.sum_option, padding_residual_none head a b hb hr, star_zero,
    zero_mul, zero_add, Fintype.sum_prod_type]
  by_cases ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head)
  · rw [if_pos ht]
    have htt := (residual_tail_eq_iff head a b c hb hc hr hs).mpr ht
    have hslice (j : ℕ) : headSlice head c j = headSlice head b j := by
      simp only [headSlice, ht]
    have hterm (t : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val))
        (k : Fin (a.count head + 1)) :
        star (paddingResidual head a b (some (t, k))) *
          paddingResidual head a c (some (t, k)) =
        if t = residualPaddingTail head a b hb hr ∧
            k.val ≤ min (b.count head) (c.count head) then
          (lastTailMass head (headSlice head b k.val) : ℂ) else 0 := by
      rw [padding_residual_coordinates head a b hb hr,
        padding_residual_coordinates head a c hc hs, ← htt, hslice]
      have hm := (last_tail_mass_pos head (headSlice head b k.val)
        (by simpa only [head_slice_tail_count] using hr)).le
      by_cases htb : t = residualPaddingTail head a b hb hr <;>
        by_cases hkb : k.val ≤ b.count head <;> by_cases hkc : k.val ≤ c.count head <;>
        simp [htb, hkb, hkc, ← Complex.ofReal_mul,
          Real.mul_self_sqrt hm]
    simp_rw [hterm]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sum_bounded_mass head a b hr _
      (le_trans (min_le_left _ _) (Multiset.le_iff_count.mp hb head))
  · rw [if_neg ht]
    have htt : residualPaddingTail head a b hb hr ≠ residualPaddingTail head a c hc hs :=
      fun h => ht ((residual_tail_eq_iff head a b c hb hc hr hs).mp h)
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro k _
    rw [padding_residual_coordinates head a b hb hr,
      padding_residual_coordinates head a c hc hs]
    by_cases htb : t = residualPaddingTail head a b hb hr
    · have htc : t ≠ residualPaddingTail head a c hc hs := by simpa [htb] using htt
      simp [htc]
    · simp [htb]

theorem padding_inner (a : Multiset A) (head : A) (b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) :
    inner ℂ (padding a head b) (padding a head c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  have head_slice_count_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (headSlice head b h).count head = h := by
    simp [headSlice, Multiset.count_filter]
  have capacities_multiset_echo {σ : Type u} [Fintype σ] [DecidableEq σ] (c : σ → ℕ) :
      (∀ i : σ, (∑ j : σ, Multiset.replicate (c j) j).count i = c i) ∧
        (∑ j : σ, Multiset.replicate (c j) j).card = ∑ j : σ, c j := by
    have hc (i : σ) : (∑ j : σ, Multiset.replicate (c j) j).count i = c i := by
      simp [Multiset.count_sum', Multiset.count_replicate]
    refine ⟨hc, ?_⟩
    rw [← Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)]
    simp_rw [hc]
  have occ_count {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (r : PaddingTransition.Box a) (i : σ) :
      (occ a r).count i = (r i).val :=
    (capacities_multiset_echo (fun j => (r j).val)).1 i
  have padding_residual_tail_free {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : tailCount head b = 0) : paddingResidual head a b = basis none := by
    simp [paddingResidual, hb, hr]
  have tail_count_zero_iff {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      tailCount head b = 0 ↔ ∀ i, i ≠ head → b.count i = 0 := by
    simp only [tailCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩
    · intro h i
      exact h i.val i.property
  have tail_filter_eq_zero {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      b.filter (fun i => i ≠ head) = 0 ↔ tailCount head b = 0 := by
    rw [tail_count_zero_iff]
    constructor
    · intro h i hi
      have := congrArg (Multiset.count i) h
      simpa [Multiset.count_filter, hi] using this
    · intro h
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp []
      · simp [hi, h i hi]
  have tail_free_multiplicity {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hr : tailCount head b = 0) (n : ℕ) :
      multiplicity (headSlice head b n).card (headSlice head b n) = 1 := by
    have hf := (tail_filter_eq_zero head b).mpr hr
    simp only [headSlice, hf, add_zero, Multiset.card_replicate]
    rw [multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
    simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
    simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
    exact Nat.div_self (Nat.factorial_pos n)
  have padding_residual_none {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < tailCount head b) : paddingResidual head a b none = 0 := by
    simp [occ_count, head_slice_count_head, paddingResidual, hb, hr, WithLp.ofLp_sum, Finset.sum_apply,
      basis_apply]
  have padding_residual_coordinates {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < tailCount head b)
      (t : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val))
      (k : Fin (a.count head + 1)) :
      paddingResidual head a b (some (t, k)) =
        if t = residualPaddingTail head a b hb hr ∧ k.val ≤ b.count head then
          (Real.sqrt (lastTailMass head (headSlice head b k.val)) : ℂ) else 0 := by
    classical
    rw [paddingResidual, dif_pos hb, dif_pos hr]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      basis_apply, Option.some.injEq, Prod.mk.injEq]
    by_cases ht : t = residualPaddingTail head a b hb hr
    · subst t
      by_cases hk : k.val ≤ b.count head
      · rw [if_pos ⟨rfl, hk⟩]
        let j : Fin (b.count head + 1) := ⟨k.val, Nat.lt_succ_of_le hk⟩
        rw [Finset.sum_eq_single j]
        · simp [head_slice_count_head, j, residualHeadIndex]
        · intro i _ hij
          have hi : k ≠ residualHeadIndex head a b hb i := by
            intro he
            apply hij
            exact Fin.ext (congrArg Fin.val he).symm
          simp [head_slice_count_head, hi]
        · simp [head_slice_count_head]
      · rw [if_neg (by simp [head_slice_count_head, hk])]
        apply Finset.sum_eq_zero
        intro i _
        have hi : k ≠ residualHeadIndex head a b hb i := by
          intro he
          have := congrArg Fin.val he
          have := i.isLt
          simp only [residualHeadIndex] at *
          omega
        simp [head_slice_count_head, hi]
    · simp [head_slice_count_head, ht]
  have tail_word_count_head {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.Tail a head) : (tailWord a head b).count head = 0 := by
    simp only [tailWord, Multiset.count_sum', Multiset.count_replicate]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg i.property
  have tail_word_count {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.Tail a head) (i : PaddingTransition.TailAlphabet head) :
      (tailWord a head b).count i.val = (b i).val := by
    simp only [tailWord, Multiset.count_sum', Multiset.count_replicate, Subtype.val_inj]
    simpa only [Finset.mem_univ, if_true] using
      Finset.sum_ite_eq' Finset.univ i (fun j => (b j).val)
  have tail_word_injective {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) :
      Function.Injective (tailWord a head) := by
    intro b c h
    funext i
    apply Fin.ext
    simpa only [tail_word_count] using congrArg (Multiset.count i.val) h
  have tail_word_zero {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) :
      tailWord a head 0 = 0 := by
    simp [tail_word_count_head, tail_word_count, tailWord]
  have tail_word_ne_zero {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.PositiveTail a head) : tailWord a head b.val ≠ 0 := by
    intro h
    apply b.property
    apply tail_word_injective a head
    simpa only [tail_word_zero] using h
  have tail_word_residual {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) :
      tailWord a head (residualTail head a r hr) = tailOcc head r := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [tail_word_count_head, tail_word_count, tail_word_zero, tailOcc]
    · rw [show i = (⟨i, hi⟩ : PaddingTransition.TailAlphabet head).val from rfl, tail_word_count]
      simp [tail_word_count_head, tail_word_count, tail_word_zero, residualTail, tailOcc, hi]
  have head_add_tail_count {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      b.count head + tailCount head b = b.card := by
    unfold tailCount
    rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
    exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)
  have tail_occ_card {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r : Multiset σ) :
      (tailOcc head r).card = tailCount head r := by
    have h := head_add_tail_count head (tailOcc head r)
    have ht : tailCount head (tailOcc head r) = tailCount head r := by
      apply Finset.sum_congr rfl
      intro i _
      simp [tailOcc, Multiset.count_filter, i.property]
    rw [ht] at h
    simpa [tailOcc] using h.symm
  have last_tail_eq_mass {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r : Multiset σ) :
      lastTail head r = lastTailMass head r := by
    rw [lastTail, tail_occ_card]
    rfl
  have slice_eq_head_slice {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) (j : ℕ) :
      slice a head (residualTail head a r hr) j = headSlice head r j := by
    rw [slice, tail_word_residual]
    rfl
  have padding_eq_residual {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) (r : Multiset σ) :
      padding a head r = paddingResidual head a r := by
    by_cases hr : r ≤ a
    · by_cases ht : 0 < tailCount head r
      · have hf : tailOcc head r ≠ 0 := by
          intro h
          have := (tail_filter_eq_zero head r).mp h
          omega
        ext q
        cases q with
        | none => simp [tail_word_count_head, tail_word_count, tail_word_zero, padding, hr, hf, padding_residual_none head a r hr ht]
        | some q =>
          rcases q with ⟨b, j⟩
          rw [padding_residual_coordinates head a r hr ht]
          have he : tailOcc head r = tailWord a head b.val ↔
              b = residualPaddingTail head a r hr ht := by
            rw [← tail_word_residual a head r hr]
            constructor
            · intro h
              exact Subtype.ext ((tail_word_injective a head h).symm)
            · rintro rfl
              rfl
          change (if r ≤ a ∧ tailOcc head r = tailWord a head b.val ∧ j.val ≤ r.count head
            then (Real.sqrt (lastTail head (slice a head b.val j.val)) : ℂ) else 0) = _
          simp only [hr, true_and, he]
          by_cases hb : b = residualPaddingTail head a r hr ht
          · subst b
            simp only [true_and, residualPaddingTail, slice_eq_head_slice, last_tail_eq_mass]
          · simp only [hb, false_and, if_false]
      · have hz : tailCount head r = 0 := by omega
        have hf : tailOcc head r = 0 := (tail_filter_eq_zero head r).mpr hz
        rw [padding_residual_tail_free head a r hr hz]
        ext q
        cases q with
        | none => simp [tail_word_count_head, tail_word_count, tail_word_zero, padding, hr, hf]
        | some q =>
          rcases q with ⟨b, j⟩
          have hn := tail_word_ne_zero a head b
          simp [tail_word_count_head, tail_word_count, tail_word_zero, padding, hr, hf, Ne.symm hn, basis_apply]
    · ext q
      cases q <;> simp [tail_word_count_head, tail_word_count, tail_word_zero, padding, paddingResidual, hr]
  have padding_residual_inner {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b c : Multiset A)
      (hb : b ≤ a) (hc : c ≤ a) :
      inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
        if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
          let q := headSlice head b (min (b.count head) (c.count head))
          (multiplicity q.card q : ℂ)
        else 0 := by
    classical
    by_cases hr : tailCount head b = 0
    · rw [padding_residual_tail_free head a b hb hr]
      by_cases hs : tailCount head c = 0
      · have ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
          rw [(tail_filter_eq_zero head b).mpr hr, (tail_filter_eq_zero head c).mpr hs]
        rw [padding_residual_tail_free head a c hc hs, if_pos ht]
        dsimp only
        rw [tail_free_multiplicity head b hr]
        simp [basis]
      · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
          intro h
          apply hs
          apply (tail_filter_eq_zero head c).mp
          rw [← h, (tail_filter_eq_zero head b).mpr hr]
        rw [if_neg ht]
        simpa only [basis, EuclideanSpace.basisFun_inner] using
          padding_residual_none head a c hc (Nat.pos_of_ne_zero hs)
    · by_cases hs : tailCount head c = 0
      · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
          intro h
          apply hr
          apply (tail_filter_eq_zero head b).mp
          rw [h, (tail_filter_eq_zero head c).mpr hs]
        rw [padding_residual_tail_free head a c hc hs, if_neg ht]
        apply inner_eq_zero_symm.mp
        simpa only [basis, EuclideanSpace.basisFun_inner] using
          padding_residual_none head a b hb (Nat.pos_of_ne_zero hr)
      · exact padding_residual_inner_positive head a b c hb hc
          (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hs)

  rw [padding_eq_residual, padding_eq_residual]
  exact padding_residual_inner head a b c hb hc

end

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

theorem phi_gram (a : Multiset σ) (head : σ) :
    Matrix.gram ℂ (fun r : PaddingTransition.Box a => phi a head (occ a r)) = G a head := by
  have capacities_multiset_echo {σ : Type u} [Fintype σ] [DecidableEq σ] (c : σ → ℕ) :
      (∀ i : σ, (∑ j : σ, Multiset.replicate (c j) j).count i = c i) ∧
        (∑ j : σ, Multiset.replicate (c j) j).card = ∑ j : σ, c j := by
    have hc (i : σ) : (∑ j : σ, Multiset.replicate (c j) j).count i = c i := by
      simp [Multiset.count_sum', Multiset.count_replicate]
    refine ⟨hc, ?_⟩
    rw [← Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)]
    simp_rw [hc]
  have occ_count {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (r : PaddingTransition.Box a) (i : σ) :
      (occ a r).count i = (r i).val :=
    (capacities_multiset_echo (fun j => (r j).val)).1 i
  have box_occupation_le {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (r : PaddingTransition.Box a) : occ a r ≤ a := by
    apply Multiset.le_iff_count.mpr
    intro i
    rw [occ_count]
    exact Nat.le_of_lt_succ (r i).isLt
  have head_slice_count_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (headSlice head b h).count head = h := by
    simp [headSlice, Multiset.count_filter]
  have head_slice_count_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (i : A) (hi : i ≠ head) : (headSlice head b h).count i = b.count i := by
    simp [head_slice_count_head, headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]
  have head_slice_self {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      headSlice head b (b.count head) = b := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; exact head_slice_count_head head b _
    · exact head_slice_count_tail head b _ i hi
  have tail_count_zero_iff {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      tailCount head b = 0 ↔ ∀ i, i ≠ head → b.count i = 0 := by
    simp only [tailCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩
    · intro h i
      exact h i.val i.property
  have tail_filter_eq_zero {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      b.filter (fun i => i ≠ head) = 0 ↔ tailCount head b = 0 := by
    rw [tail_count_zero_iff]
    constructor
    · intro h i hi
      have := congrArg (Multiset.count i) h
      simpa [Multiset.count_filter, hi] using this
    · intro h
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp []
      · simp [hi, h i hi]
  have tail_free_multiplicity {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hr : tailCount head b = 0) (n : ℕ) :
      multiplicity (headSlice head b n).card (headSlice head b n) = 1 := by
    have hf := (tail_filter_eq_zero head b).mpr hr
    simp only [headSlice, hf, add_zero, Multiset.card_replicate]
    rw [multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
    simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
    simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
    exact Nat.div_self (Nat.factorial_pos n)
  have phi_eq_normalized {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) (r : Multiset σ) :
      phi a head r = phi a head r := by
    rfl
  have same_tail_count {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r s : Multiset σ)
      (h : tailOcc head r = tailOcc head s) (i : σ) (hi : i ≠ head) :
      r.count i = s.count i := by
    simpa [tailOcc, Multiset.count_filter, hi] using congrArg (Multiset.count i) h
  have same_tail_le {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r s : Multiset σ)
      (h : tailOcc head r = tailOcc head s) : r ≤ s ↔ r.count head ≤ s.count head := by
    constructor
    · intro hrs
      exact Multiset.le_iff_count.mp hrs head
    · intro hh
      apply Multiset.le_iff_count.mpr
      intro i
      by_cases hi : i = head
      · simpa only [hi] using hh
      · exact (same_tail_count head r s h i hi).le
  have tail_sub_zero_iff {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r s : Multiset σ) (h : s ≤ r) :
      tailOcc head (r - s) = 0 ↔ tailOcc head r = tailOcc head s := by
    have hle : tailOcc head s ≤ tailOcc head r := Multiset.filter_le_filter _ h
    rw [tailOcc, Multiset.filter_sub, tsub_eq_zero_iff_le]
    exact ⟨fun h' => le_antisymm h' hle, fun h' => h'.le⟩
  have head_only_M {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r : Multiset σ) (h : tailOcc head r = 0) :
      M r = 1 := by
    have hz := (tail_filter_eq_zero head r).mp h
    simpa only [head_slice_self, M] using tail_free_multiplicity head r hz (r.count head)
  have scale_pos {σ : Type u} [Fintype σ] [DecidableEq σ] (r : Multiset σ) : 0 < residualScale r := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)
  have scale_sq {σ : Type u} [Fintype σ] [DecidableEq σ] (r : Multiset σ) : residualScale r ^ 2 = (multiplicity r.card r : ℝ) := by
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have normalized_scalar {σ : Type u} [Fintype σ] [DecidableEq σ] (r s : Multiset σ) :
      (residualScale r : ℂ)⁻¹ * ((residualScale s : ℂ)⁻¹ * (M s : ℂ)) =
        (Real.sqrt ((M s : ℝ) / (M r : ℝ)) : ℂ) := by
    have h : (residualScale r)⁻¹ * ((residualScale s)⁻¹ * (M s : ℝ)) =
        Real.sqrt ((M s : ℝ) / (M r : ℝ)) := by
      rw [Real.sqrt_div (Nat.cast_nonneg _)]
      change (residualScale r)⁻¹ * ((residualScale s)⁻¹ * (M s : ℝ)) =
        residualScale s / residualScale r
      field_simp [(scale_pos r).ne', (scale_pos s).ne']
      simpa only [pow_two, M] using (scale_sq s).symm
    exact_mod_cast h
  have phi_inner_of_le {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) (r s : Multiset σ)
      (hr : r ≤ a) (hs : s ≤ a) (hle : s ≤ r) :
      inner ℂ (phi a head r) (phi a head s) =
        (Real.sqrt (((M s : ℝ) * (M (r - s) : ℝ)) / (M r : ℝ)) : ℂ) * z head (r - s) := by
    rw [phi_eq_normalized, phi_eq_normalized]
    simp only [phi, inner_smul_left, inner_smul_right, map_inv₀,
      Complex.conj_ofReal]
    rw [padding_inner a head r s hr hs]
    change (residualScale s : ℂ)⁻¹ * ((residualScale r : ℂ)⁻¹ *
      (if tailOcc head r = tailOcc head s then
        (M (headSlice head r (min (r.count head) (s.count head))) : ℂ) else 0)) = _
    by_cases ht : tailOcc head r = tailOcc head s
    · rw [if_pos ht]
      have hz := (tail_sub_zero_iff head r s hle).mpr ht
      have hm := head_only_M head (r - s) hz
      have hh := Multiset.le_iff_count.mp hle head
      have hslice : headSlice head r (s.count head) = s := by
        apply Multiset.ext.mpr
        intro i
        by_cases hi : i = head
        · subst i
          exact head_slice_count_head head r _
        · rw [head_slice_count_tail head r _ i hi]
          exact same_tail_count head r s ht i hi
      simp only [min_eq_right hh, hslice, z, hz, if_true, hm, Nat.cast_one,
        mul_one]
      simpa only [mul_left_comm] using normalized_scalar r s
    · have hz : tailOcc head (r - s) ≠ 0 := fun h => ht ((tail_sub_zero_iff head r s hle).mp h)
      simp only [if_neg ht, z, if_neg hz, mul_zero]

  ext r s
  change inner ℂ (phi a head (occ a r)) (phi a head (occ a s)) = G a head r s
  rw [G]
  by_cases hsr : occ a s ≤ occ a r
  · rw [if_pos hsr]
    exact phi_inner_of_le a head _ _ (box_occupation_le a r) (box_occupation_le a s) hsr
  · rw [if_neg hsr]
    by_cases hrs : occ a r ≤ occ a s
    · rw [if_pos hrs]
      have h := congrArg star (phi_inner_of_le a head _ _
        (box_occupation_le a s) (box_occupation_le a r) hrs)
      simpa only [← starRingEnd_apply, inner_conj_symm] using h
    · rw [if_neg hrs, phi_eq_normalized, phi_eq_normalized]
      have ht : tailOcc head (occ a r) ≠ tailOcc head (occ a s) := by
        intro he
        rcases le_total ((occ a r).count head) ((occ a s).count head) with h | h
        · exact hrs ((same_tail_le head _ _ he).mpr h)
        · exact hsr ((same_tail_le head _ _ he.symm).mpr h)
      dsimp only [tailOcc] at ht
      simp only [phi, inner_smul_left, inner_smul_right,
        padding_inner a head _ _ (box_occupation_le a r) (box_occupation_le a s),
        if_neg ht, mul_zero]

/-- The concrete coordinate overlap gives unit norm for every legal residual. -/
theorem phi_norm (a : Multiset σ) (head : σ) (r : Multiset σ) (hr : r ≤ a) :
    ‖phi a head r‖ = 1 := by
  have hs : headSlice head r (r.count head) = r := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp [headSlice, Multiset.count_filter]
    · simp [headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]
  have hp : 0 < residualScale r :=
    Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)
  have hi := padding_inner a head r r hr hr
  simp only [ite_true, min_self, hs] at hi
  have hn : ‖padding a head r‖ = residualScale r := by
    have hh : ‖padding a head r‖ ^ 2 = (multiplicity r.card r : ℝ) := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hi]
      rfl
    have hsq : residualScale r ^ 2 = (multiplicity r.card r : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith [norm_nonneg (padding a head r)]
  change ‖(residualScale r : ℂ)⁻¹ • padding a head r‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, hn, inv_mul_cancel₀ hp.ne']

end

end D5.S3.Quantum.StationaryPreparation.PaddingResidualGram

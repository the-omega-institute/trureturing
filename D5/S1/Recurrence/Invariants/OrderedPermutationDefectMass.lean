/- GID: D5/S1/Recurrence/Invariants/OrderedPermutationDefectMass
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/OrderedPermutationDefectMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered permutation capacity and the complete floor defect mass bound. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.OrderedPermutationDefectMass

open scoped BigOperators

/-- Rank i here is the source's rank i+1; Fin.rev gives its opposite rank p-i.
The two integer floor sums and both real lower bounds retain every link of the chain. -/
theorem result (t c : ℝ) (r : ℤ) (A : Finset ℤ) (f : ℤ → ℤ)
    (ht : 0 < t) (ht1 : t < 1) (hp : 1 ≤ A.card)
    (hf : ∀ z ∈ A, ⌊t * (z : ℝ) + c⌋ ≤ f z)
    (hperm : Set.BijOn (fun z => r - f z) (A : Set ℤ) (A : Set ℤ)) :
    let z := A.orderEmbOfFin rfl
    let lo := Fin.castLEEmb (Nat.div_le_self A.card 2)
    (∀ i : Fin A.card, z i.rev + ⌊t * (z i : ℝ) + c⌋ ≤ r) ∧
    (∑ i : Fin (A.card / 2), ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋) ≤
      (∑ a ∈ A, (f a - ⌊t * (a : ℝ) + c⌋)) ∧
    (∑ i : Fin (A.card / 2), ⌊(1 - t) * ((A.card : ℝ) - 1 - 2 * (i.val : ℝ))⌋) ≤
      (∑ i : Fin (A.card / 2), ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋) ∧
    (1 - t) * (⌊(A.card : ℝ)^2 / 4⌋ : ℝ) - ((A.card / 2 : ℕ) : ℝ) ≤
      ((∑ i : Fin (A.card / 2), ⌊(1 - t) * ((A.card : ℝ) - 1 - 2 * (i.val : ℝ))⌋ : ℤ) : ℝ) ∧
    (1 - t) * (A.card : ℝ)^2 / 4 - (A.card : ℝ) / 2 ≤
      (1 - t) * (⌊(A.card : ℝ)^2 / 4⌋ : ℝ) - ((A.card / 2 : ℕ) : ℝ) := by
  classical
  let p := A.card
  let m := p / 2
  let z := A.orderEmbOfFin rfl
  let lo := Fin.castLEEmb (Nat.div_le_self p 2)
  let g : ℤ → ℤ := fun a => ⌊t * (a : ℝ) + c⌋
  let e := A.orderIsoOfFin rfl
  let q : Fin p → Fin p := fun i =>
    e.symm ⟨r - f (z i), hperm.mapsTo (A.orderEmbOfFin_mem rfl i)⟩
  have q_value (i : Fin p) : z (q i) = r - f (z i) := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have q_inj : Function.Injective q := by
    intro i j hij
    apply z.injective
    apply hperm.injOn (A.orderEmbOfFin_mem rfl i) (A.orderEmbOfFin_mem rfl j)
    change r - f (z i) = r - f (z j)
    rw [← q_value, ← q_value, hij]
  have g_mono : Monotone g := by
    intro a b hab
    change ⌊t * (a : ℝ) + c⌋ ≤ ⌊t * (b : ℝ) + c⌋
    apply Int.floor_mono
    have hc := mul_le_mul_of_nonneg_left
      (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab) ht.le
    linarith
  have rank_capacity (i : Fin p) : z i.rev + g (z i) ≤ r := by
    by_contra hn
    have hlt : r - g (z i) < z i.rev := by omega
    have hmaps : Set.MapsTo q (Finset.Ici i : Set (Fin p)) (Finset.Iio i.rev : Set (Fin p)) := by
      intro k hk
      have hik : i ≤ k := Finset.mem_Ici.mp hk
      apply Finset.mem_Iio.mpr
      apply z.lt_iff_lt.mp
      rw [q_value]
      have hfg := hf (z k) (A.orderEmbOfFin_mem rfl k)
      have hgg := g_mono (z.monotone hik)
      change g (z k) ≤ f (z k) at hfg
      omega
    have hcard := Finset.card_le_card_of_injOn q hmaps q_inj.injOn
    rw [Fin.card_Ici, Fin.card_Iio] at hcard
    have hi := i.isLt
    have hr := Fin.val_rev i
    omega
  let s : Fin p → ℤ := fun i => r - g (z i) - z i.rev
  have s_nonneg (i : Fin p) : 0 ≤ s i := by
    have h := rank_capacity i
    dsimp [s]
    omega
  have permutation_sum : (∑ a ∈ A, (r - f a)) = ∑ a ∈ A, a := by
    exact Finset.sum_nbij (fun a => r - f a) hperm.mapsTo hperm.injOn hperm.surjOn
      (fun _ _ => rfl)
  have enumeration_sum (F : ℤ → ℤ) : (∑ i : Fin p, F (z i)) = ∑ a ∈ A, F a := by
    calc
      _ = ∑ a ∈ Finset.univ.map z.toEmbedding, F a := (Finset.sum_map _ _ _).symm
      _ = _ := congrArg (fun B : Finset ℤ => ∑ a ∈ B, F a) (A.map_orderEmbOfFin_univ rfl)
  have reversed_sum : (∑ i : Fin p, z i.rev) = ∑ i : Fin p, z i := by
    exact Equiv.sum_comp Fin.revPerm z
  have mass_identity : (∑ a ∈ A, (f a - g a)) = ∑ i : Fin p, s i := by
    have hσ := permutation_sum
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hσ
    simp only [s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, reversed_sum, enumeration_sum]
    have hz := enumeration_sum (fun a => a)
    change (∑ i : Fin p, z i) = ∑ a ∈ A, a at hz
    change (∑ a ∈ A, f a) - (∑ a ∈ A, g a) =
      (A.card : ℤ) * r - (∑ a ∈ A, g a) - (∑ i : Fin p, z i)
    omega
  have pair_bound (i : Fin m) :
      ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋ ≤ s (lo i) + s (lo i).rev := by
    let a := z (lo i)
    let b := z (lo i).rev
    let D : ℤ := b - a
    have hround : ⌊(1 - t) * (D : ℝ)⌋ ≤ D - (g b - g a) := by
      have h := Int.le_floor_add ((1 - t) * (D : ℝ)) (t * (b : ℝ) + c)
      have harg : (1 - t) * (D : ℝ) + (t * (b : ℝ) + c) =
          (t * (a : ℝ) + c) + (D : ℝ) := by
        dsimp [D]
        push_cast
        ring
      rw [harg, Int.floor_add_intCast] at h
      change ⌊(1 - t) * (D : ℝ)⌋ + g b ≤ g a + D at h
      omega
    have hs := s_nonneg (lo i)
    change ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋ ≤
      (z (lo i).rev - z (lo i)) - (g (z (lo i).rev) - g (z (lo i))) at hround
    dsimp only [s] at hs ⊢
    rw [Fin.rev_rev]
    omega
  let L : Finset (Fin p) := Finset.univ.map lo
  let R : Finset (Fin p) := L.map Fin.revPerm.toEmbedding
  have disjoint_pairs : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro k hk hkR
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hk
    obtain ⟨j, hj, hjk⟩ := Finset.mem_map.mp hkR
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hj
    have hi' := i.isLt
    have ha' := a.isLt
    have hr := Fin.val_rev (lo a)
    have hh : (lo a).rev = lo i := by simpa [← ha, ← hi, Fin.revPerm] using hjk
    have hv := congrArg Fin.val hh
    simp [Fin.val_rev, lo, Fin.castLEEmb] at hv
    omega
  have pair_sum_le : (∑ i : Fin m, (s (lo i) + s (lo i).rev)) ≤ ∑ i : Fin p, s i := by
    calc
      _ = (∑ k ∈ L, s k) + ∑ k ∈ R, s k := by
        simp [L, R, Finset.sum_map, Finset.sum_add_distrib, Fin.revPerm]
        rfl
      _ = ∑ k ∈ L ∪ R, s k := (Finset.sum_union disjoint_pairs).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => s_nonneg i)
  have first_bound : (∑ i : Fin m, ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋) ≤
      ∑ a ∈ A, (f a - g a) := by
    rw [mass_identity]
    exact (Finset.sum_le_sum (fun i _ => pair_bound i)).trans pair_sum_le
  have integer_spacing (i j : Fin p) (hij : i ≤ j) :
      (j.val : ℤ) - i.val ≤ z j - z i := by
    have hcard := Finset.card_le_card_of_injOn z
      (s := Finset.Icc i j) (t := Finset.Icc (z i) (z j))
      (fun k hk => Finset.mem_Icc.mpr
        ⟨z.monotone (Finset.mem_Icc.mp hk).1, z.monotone (Finset.mem_Icc.mp hk).2⟩)
      z.injective.injOn
    rw [Fin.card_Icc] at hcard
    have hz := z.monotone hij
    have hInt := Int.card_Icc_of_le (z i) (z j) (show z i ≤ z j + 1 by omega)
    have hnat : i.val ≤ j.val + 1 := by omega
    have hcast := (Nat.cast_le (α := ℤ)).mpr hcard
    rw [hInt, Nat.cast_sub hnat] at hcast
    push_cast at hcast
    omega
  have rank_spacing (i : Fin m) :
      (p : ℝ) - 1 - 2 * (i.val : ℝ) ≤ ((z (lo i).rev - z (lo i) : ℤ) : ℝ) := by
    have hi := i.isLt
    have hrev := Fin.val_rev (lo i)
    have hle : lo i ≤ (lo i).rev := by
      apply Fin.le_iff_val_le_val.mpr
      simp [Fin.val_rev, lo, Fin.castLEEmb]
      dsimp [m] at hi
      omega
    have hh := integer_spacing (lo i) (lo i).rev hle
    have hni : i.val + 1 ≤ p := by dsimp [m] at hi; omega
    have hcast := (Int.cast_le (R := ℝ)).mpr hh
    simp only [Fin.val_rev] at hcast
    change ((((p - (i.val + 1) : ℕ) : ℤ) - (i.val : ℤ) : ℤ) : ℝ) ≤
      ((z (lo i).rev - z (lo i) : ℤ) : ℝ) at hcast
    push_cast [Nat.cast_sub hni] at hcast
    push_cast
    linarith
  have second_bound : (∑ i : Fin m, ⌊(1 - t) * ((p : ℝ) - 1 - 2 * (i.val : ℝ))⌋) ≤
      ∑ i : Fin m, ⌊(1 - t) * ((z (lo i).rev - z (lo i) : ℤ) : ℝ)⌋ := by
    apply Finset.sum_le_sum
    intro i _
    exact Int.floor_mono (mul_le_mul_of_nonneg_left (rank_spacing i) (by linarith))
  have sum_indices : 2 * (∑ i : Fin m, (i.val : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) := by
    have h := Finset.sum_range_id_mul_two m
    by_cases hm : m = 0
    · rw [Fin.sum_univ_eq_sum_range]
      simp [hm]
    · have hn : 1 ≤ m := by omega
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast [Nat.cast_sub hn] at hc
      rw [Fin.sum_univ_eq_sum_range]
      nlinarith
  have rank_sum : (∑ i : Fin m, ((p : ℝ) - 1 - 2 * (i.val : ℝ))) = (m : ℝ) * ((p : ℝ) - m) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    nlinarith [sum_indices]
  have parity : p = 2 * m ∨ p = 2 * m + 1 := by dsimp [m]; omega
  have square_floor : (⌊(p : ℝ)^2 / 4⌋ : ℝ) = (m : ℝ) * ((p : ℝ) - m) := by
    rcases parity with h | h
    · have heq : (p : ℝ)^2 / 4 = ((m * m : ℕ) : ℝ) := by
        have hc := congrArg (fun n : ℕ => (n : ℝ)) h
        push_cast at *
        nlinarith
      rw [heq, Int.floor_natCast]
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at hc ⊢
      rw [hc]
      ring
    · have heq : ⌊(p : ℝ)^2 / 4⌋ = (m * (m + 1) : ℕ) := by
        apply Int.floor_eq_iff.mpr
        have hc := congrArg (fun n : ℕ => (n : ℝ)) h
        push_cast at *
        constructor <;> nlinarith
      rw [heq]
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at *
      nlinarith
  have third_bound : (1 - t) * (⌊(p : ℝ)^2 / 4⌋ : ℝ) - (m : ℝ) ≤
      ((∑ i : Fin m, ⌊(1 - t) * ((p : ℝ) - 1 - 2 * (i.val : ℝ))⌋ : ℤ) : ℝ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) _ =>
      (Int.sub_one_lt_floor ((1 - t) * ((p : ℝ) - 1 - 2 * (i.val : ℝ)))).le)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum, rank_sum] at hs
    rw [square_floor]
    exact_mod_cast hs
  have fourth_bound : (1 - t) * (p : ℝ)^2 / 4 - (p : ℝ) / 2 ≤
      (1 - t) * (⌊(p : ℝ)^2 / 4⌋ : ℝ) - (m : ℝ) := by
    rw [square_floor]
    rcases parity with h | h <;>
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h <;>
      push_cast at hc <;> rw [hc] <;> ring_nf <;> linarith
  exact ⟨rank_capacity, first_bound, second_bound, third_bound, fourth_bound⟩

end D5.S1.Recurrence.Invariants.OrderedPermutationDefectMass

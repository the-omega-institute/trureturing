/- GID: D5/S0/Tower/Tribonacci/Values
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Values
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tribonacci name values have an exact three-gap spectrum from level three. -/

import D5.S0.Tower.Tribonacci.Names
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Order.IntermediateValue

namespace D5.S0.Tower.Tribonacci.Values

open D5.S0.Tower.Tribonacci.Names

/-- A real root of the Tribonacci polynomial lies strictly between one and two. -/
theorem exists_tribonacci_root :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧ t ^ 3 = t ^ 2 + t + 1 := by
  let f : ℝ → ℝ := fun x ↦ x ^ 3 - x ^ 2 - x - 1
  have hcontinuous : Continuous f := by fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (f 1) (f 2) := by norm_num [f]
  have himage := intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num)
    hcontinuous.continuousOn hzero
  obtain ⟨t, ht, hft⟩ := (Set.mem_image f (Set.Icc (1 : ℝ) 2) 0).mp himage
  have htroot : t ^ 3 = t ^ 2 + t + 1 := by
    dsimp [f] at hft
    nlinarith
  refine ⟨t, ?_, ?_, htroot⟩
  · exact lt_of_le_of_ne ht.1 (by
      intro heq
      rw [← heq] at htroot
      norm_num at htroot)
  · exact lt_of_le_of_ne ht.2 (by
      intro heq
      rw [heq] at htroot
      norm_num at htroot)

/-- The Tribonacci constant: the real root in `(1, 2)` of `x^3 = x^2 + x + 1`. -/
noncomputable def tribonacciConstant : ℝ := Classical.choose exists_tribonacci_root

local notation "t" => tribonacciConstant

theorem one_lt_tribonacciConstant : 1 < t :=
  (Classical.choose_spec exists_tribonacci_root).1

theorem tribonacciConstant_lt_two : t < 2 :=
  (Classical.choose_spec exists_tribonacci_root).2.1

theorem tribonacciConstant_cubic : t ^ 3 = t ^ 2 + t + 1 :=
  (Classical.choose_spec exists_tribonacci_root).2.2

theorem tribonacciConstant_pos : 0 < t := lt_trans (by norm_num) one_lt_tribonacciConstant

theorem tribonacciConstant_ne_zero : t ≠ 0 := ne_of_gt tribonacciConstant_pos

/-- The reciprocal powers of the Tribonacci constant partition one. -/
theorem tribonacci_inverse_sum :
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) + t ^ (-3 : ℤ) = 1 := by
  rw [zpow_neg, zpow_neg, zpow_neg]
  norm_num only [zpow_ofNat, pow_one]
  field_simp [tribonacciConstant_ne_zero]
  nlinarith [tribonacciConstant_cubic]

theorem tribonacci_zpow_mul (a b : ℤ) : t ^ a * t ^ b = t ^ (a + b) := by
  rw [zpow_add₀ tribonacciConstant_ne_zero]

theorem tribonacci_zpow_recurrence (Q : Nat) :
    t ^ (-(Q : ℤ)) =
      t ^ (-((Q + 1 : Nat) : ℤ)) + t ^ (-((Q + 2 : Nat) : ℤ)) +
        t ^ (-((Q + 3 : Nat) : ℤ)) := by
  calc
    t ^ (-(Q : ℤ)) = t ^ (-(Q : ℤ)) * 1 := by ring
    _ = t ^ (-(Q : ℤ)) *
        (t ^ (-1 : ℤ) + t ^ (-2 : ℤ) + t ^ (-3 : ℤ)) := by
      rw [tribonacci_inverse_sum]
    _ = t ^ (-(Q : ℤ)) * t ^ (-1 : ℤ) +
          t ^ (-(Q : ℤ)) * t ^ (-2 : ℤ) +
            t ^ (-(Q : ℤ)) * t ^ (-3 : ℤ) := by ring
    _ = _ := by
      rw [tribonacci_zpow_mul, tribonacci_zpow_mul, tribonacci_zpow_mul]
      congr 1 <;> push_cast <;> ring_nf

/-- The canonical prefix order identifies Tribonacci names with their counting interval. -/
def tribonacciIndexEquiv :
    (Q : Nat) → Fin (tribonacci (Q + 2)) ≃ TribonacciName Q
  | 0 =>
      { toFun := fun _ => ⟨fun i => Fin.elim0 i, trivial⟩
        invFun := fun _ => ⟨0, by norm_num [tribonacci]⟩
        left_inv := by intro i; fin_cases i; simp
        right_inv := by intro name; apply Subtype.ext; funext i; exact Fin.elim0 i }
  | 1 =>
      { toFun := fun i => ⟨fun _ => i.1 == 1, trivial⟩
        invFun := fun name => if name.1 0 then ⟨1, by norm_num [tribonacci]⟩
          else ⟨0, by norm_num [tribonacci]⟩
        left_inv := by intro i; apply Fin.ext; fin_cases i <;> decide
        right_inv := by
          intro name
          apply Subtype.ext
          funext i
          fin_cases i
          cases h : name.1 0 <;> simp [h] }
  | 2 =>
      { toFun := fun i => ⟨fun j =>
          if j.1 = 0 then decide (2 ≤ i.1) else decide (i.1 % 2 = 1), trivial⟩
        invFun := fun name => ⟨2 * (name.1 0).toNat + (name.1 1).toNat, by
          cases h0 : name.1 0 <;> cases h1 : name.1 1 <;>
            simp [tribonacci]⟩
        left_inv := by intro i; apply Fin.ext; fin_cases i <;> decide
        right_inv := by
          intro name
          apply Subtype.ext
          funext i
          fin_cases i <;>
            cases h0 : name.1 0 <;> cases h1 : name.1 1 <;> simp [h0, h1] }
  | n + 3 =>
      have hcount : tribonacci ((n + 3) + 2) =
          tribonacci (n + 4) + (tribonacci (n + 3) + tribonacci (n + 2)) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          tribonacci_add_three (n + 2)
      (finCongr hcount).trans
        ((finSumFinEquiv (m := tribonacci (n + 4))
          (n := tribonacci (n + 3) + tribonacci (n + 2))).symm.trans
          ((Equiv.sumCongr (tribonacciIndexEquiv (n + 2))
            ((finSumFinEquiv (m := tribonacci (n + 3))
              (n := tribonacci (n + 2))).symm.trans
                (Equiv.sumCongr (tribonacciIndexEquiv (n + 1))
                  (tribonacciIndexEquiv n)))).trans
            (tribonacciNameSplitEquiv n).symm))

/-- The real value of an arbitrary binary word, with its first digit weighted by `t^-1`. -/
noncomputable def tribonacciWordValue (Q : Nat) (word : Fin Q → Bool) : ℝ :=
  ∑ i, if word i then t ^ (-((i.1 + 1 : Nat) : ℤ)) else 0

/-- Read a Tribonacci-admissible word as a real base-`t` expansion. -/
noncomputable def tribonacciNameValue (Q : Nat) (name : TribonacciName Q) : ℝ :=
  tribonacciWordValue Q name.1

theorem tribonacciWordValue_cons (Q : Nat) (head : Bool) (tail : Fin Q → Bool) :
    tribonacciWordValue (Q + 1) (Fin.cons head tail) =
      (if head then t ^ (-1 : ℤ) else 0) +
        t ^ (-1 : ℤ) * tribonacciWordValue Q tail := by
  unfold tribonacciWordValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by simp)
  intro i _
  by_cases hi : tail i
  · simp only [hi, ↓reduceIte]
    rw [← zpow_add₀ tribonacciConstant_ne_zero]
    congr 1
    rw [Fin.val_succ]
    push_cast
    omega
  · simp [hi]

theorem tribonacciNameValue_zero_prefix (n : Nat) (name : TribonacciName (n + 2)) :
    tribonacciNameValue (n + 3)
        ((tribonacciNameSplitEquiv n).symm (Sum.inl name)) =
      t ^ (-1 : ℤ) * tribonacciNameValue (n + 2) name := by
  rw [tribonacciNameValue, tribonacciNameValue]
  change tribonacciWordValue (n + 3) (Fin.cons false name.1) = _
  rw [tribonacciWordValue_cons]
  simp

theorem tribonacciNameValue_one_zero_prefix (n : Nat) (name : TribonacciName (n + 1)) :
    tribonacciNameValue (n + 3)
        ((tribonacciNameSplitEquiv n).symm (Sum.inr (Sum.inl name))) =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * tribonacciNameValue (n + 1) name := by
  rw [tribonacciNameValue, tribonacciNameValue]
  change tribonacciWordValue (n + 3) (Fin.cons true (Fin.cons false name.1)) = _
  rw [tribonacciWordValue_cons, tribonacciWordValue_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have hsq : t ^ (-1 : ℤ) * t ^ (-1 : ℤ) = t ^ (-2 : ℤ) := by
    rw [← zpow_add₀ tribonacciConstant_ne_zero]
    norm_num
  rw [← mul_assoc, hsq]

theorem tribonacciNameValue_one_one_zero_prefix (n : Nat) (name : TribonacciName n) :
    tribonacciNameValue (n + 3)
        ((tribonacciNameSplitEquiv n).symm (Sum.inr (Sum.inr name))) =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) +
        t ^ (-3 : ℤ) * tribonacciNameValue n name := by
  rw [tribonacciNameValue, tribonacciNameValue]
  change tribonacciWordValue (n + 3)
    (Fin.cons true (Fin.cons true (Fin.cons false name.1))) = _
  rw [tribonacciWordValue_cons, tribonacciWordValue_cons, tribonacciWordValue_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have hne := tribonacciConstant_ne_zero
  have hsq : t ^ (-1 : ℤ) * t ^ (-1 : ℤ) = t ^ (-2 : ℤ) := by
    rw [← zpow_add₀ hne]
    norm_num
  have hnext : t ^ (-2 : ℤ) * t ^ (-1 : ℤ) = t ^ (-3 : ℤ) := by
    rw [← zpow_add₀ hne]
    norm_num
  calc
    t ^ (-1 : ℤ) + t ^ (-1 : ℤ) *
        (t ^ (-1 : ℤ) + t ^ (-1 : ℤ) *
          (t ^ (-1 : ℤ) * tribonacciWordValue n name.1)) =
        t ^ (-1 : ℤ) + (t ^ (-1 : ℤ) * t ^ (-1 : ℤ)) +
          (t ^ (-1 : ℤ) * t ^ (-1 : ℤ) * t ^ (-1 : ℤ)) *
            tribonacciWordValue n name.1 := by ring
    _ = t ^ (-1 : ℤ) + t ^ (-2 : ℤ) +
        t ^ (-3 : ℤ) * tribonacciWordValue n name.1 := by rw [hsq, hnext]

/-- The value of the `i`th Tribonacci name in canonical prefix order. -/
noncomputable def indexedNameValue (Q : Nat) (i : Fin (tribonacci (Q + 2))) : ℝ :=
  tribonacciNameValue Q (tribonacciIndexEquiv Q i)

theorem admissible_all_false (Q : Nat) :
    TribonacciAdmissible Q (fun _ => false) := by
  induction Q with
  | zero => trivial
  | succ Q ih =>
      rw [show (fun _ : Fin (Q + 1) => false) =
          Fin.cons false (fun _ : Fin Q => false) by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp]
      exact (admissible_cons_false Q (fun _ => false)).2 ih

theorem tribonacci_level_pos (Q : Nat) : 0 < tribonacci (Q + 2) := by
  rw [← tribonacci_name_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => false, admissible_all_false Q⟩⟩

theorem tribonacci_count_split (n : Nat) :
    tribonacci ((n + 3) + 2) =
      tribonacci (n + 4) + (tribonacci (n + 3) + tribonacci (n + 2)) := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    tribonacci_add_three (n + 2)

theorem tribonacciIndexEquiv_add_three (n : Nat) :
    tribonacciIndexEquiv (n + 3) =
      (finCongr (tribonacci_count_split n)).trans
        ((finSumFinEquiv (m := tribonacci (n + 4))
          (n := tribonacci (n + 3) + tribonacci (n + 2))).symm.trans
          ((Equiv.sumCongr (tribonacciIndexEquiv (n + 2))
            ((finSumFinEquiv (m := tribonacci (n + 3))
              (n := tribonacci (n + 2))).symm.trans
                (Equiv.sumCongr (tribonacciIndexEquiv (n + 1))
                  (tribonacciIndexEquiv n)))).trans
            (tribonacciNameSplitEquiv n).symm)) := by
  simp [tribonacciIndexEquiv]

theorem indexedNameValue_lower (n : Nat) (i : Fin (tribonacci (n + 5)))
    (hi : i.1 < tribonacci (n + 4)) :
    indexedNameValue (n + 3) i =
      t ^ (-1 : ℤ) * indexedNameValue (n + 2) ⟨i.1, hi⟩ := by
  have hindex : Fin.cast (tribonacci_count_split n) i =
      Fin.castAdd (tribonacci (n + 3) + tribonacci (n + 2)) ⟨i.1, hi⟩ := by
    apply Fin.ext
    simp
  have hname : tribonacciIndexEquiv (n + 3) i =
      (tribonacciNameSplitEquiv n).symm
        (Sum.inl (tribonacciIndexEquiv (n + 2) ⟨i.1, hi⟩)) := by
    rw [tribonacciIndexEquiv_add_three]
    simp only [Equiv.trans_apply, finCongr_apply]
    rw [hindex, finSumFinEquiv_symm_apply_castAdd]
    simp only [Equiv.sumCongr_apply, Sum.map_inl]
  rw [indexedNameValue, indexedNameValue, hname,
    tribonacciNameValue_zero_prefix]

theorem indexedNameValue_middle (n : Nat) (i : Fin (tribonacci (n + 5)))
    (hlower : tribonacci (n + 4) ≤ i.1)
    (hupper : i.1 < tribonacci (n + 4) + tribonacci (n + 3)) :
    indexedNameValue (n + 3) i =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) *
        indexedNameValue (n + 1)
          ⟨i.1 - tribonacci (n + 4), by
            rw [show (n + 1) + 2 = n + 3 by omega]
            omega⟩ := by
  let j : Fin (tribonacci ((n + 1) + 2)) :=
    ⟨i.1 - tribonacci (n + 4), by
      rw [show (n + 1) + 2 = n + 3 by omega]
      omega⟩
  have hindex : Fin.cast (tribonacci_count_split n) i =
      Fin.natAdd (tribonacci (n + 4))
        (Fin.castAdd (tribonacci (n + 2)) j) := by
    apply Fin.ext
    simp [j]
    omega
  have hname : tribonacciIndexEquiv (n + 3) i =
      (tribonacciNameSplitEquiv n).symm
        (Sum.inr (Sum.inl (tribonacciIndexEquiv (n + 1) j))) := by
    rw [tribonacciIndexEquiv_add_three]
    simp only [Equiv.trans_apply, finCongr_apply]
    rw [hindex, finSumFinEquiv_symm_apply_natAdd]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply]
    rw [finSumFinEquiv_symm_apply_castAdd]
    simp only [Sum.map_inl]
  rw [indexedNameValue, indexedNameValue, hname,
    tribonacciNameValue_one_zero_prefix]

theorem indexedNameValue_upper (n : Nat) (i : Fin (tribonacci (n + 5)))
    (hlower : tribonacci (n + 4) + tribonacci (n + 3) ≤ i.1) :
    indexedNameValue (n + 3) i =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) + t ^ (-3 : ℤ) *
        indexedNameValue n
          ⟨i.1 - (tribonacci (n + 4) + tribonacci (n + 3)), by
            have hi : i.1 < tribonacci (n + 4) +
                (tribonacci (n + 3) + tribonacci (n + 2)) := by
              calc
                i.1 < tribonacci (n + 5) := i.2
                _ = _ := tribonacci_count_split n
            omega⟩ := by
  let j : Fin (tribonacci (n + 2)) :=
    ⟨i.1 - (tribonacci (n + 4) + tribonacci (n + 3)), by
      have hi : i.1 < tribonacci (n + 4) +
          (tribonacci (n + 3) + tribonacci (n + 2)) := by
        calc
          i.1 < tribonacci (n + 5) := i.2
          _ = _ := tribonacci_count_split n
      omega⟩
  have hindex : Fin.cast (tribonacci_count_split n) i =
      Fin.natAdd (tribonacci (n + 4))
        (Fin.natAdd (tribonacci (n + 3)) j) := by
    apply Fin.ext
    simp [j]
    omega
  have hname : tribonacciIndexEquiv (n + 3) i =
      (tribonacciNameSplitEquiv n).symm
        (Sum.inr (Sum.inr (tribonacciIndexEquiv n j))) := by
    rw [tribonacciIndexEquiv_add_three]
    simp only [Equiv.trans_apply, finCongr_apply]
    rw [hindex, finSumFinEquiv_symm_apply_natAdd]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply]
    rw [finSumFinEquiv_symm_apply_natAdd]
    simp only [Sum.map_inr]
  rw [indexedNameValue, indexedNameValue, hname,
    tribonacciNameValue_one_one_zero_prefix]

/-- Adjacent differences in the canonical prefix enumeration, with multiplicity and order. -/
noncomputable def adjacentNameValueGaps (Q : Nat) : List ℝ :=
  List.ofFn fun i : Fin (tribonacci (Q + 2) - 1) ↦
    indexedNameValue Q
          ⟨i.1 + 1, by have := i.2; have := tribonacci_level_pos Q; omega⟩ -
      indexedNameValue Q
        ⟨i.1, by have := i.2; have := tribonacci_level_pos Q; omega⟩

@[simp] theorem indexedNameValue_level_zero :
    indexedNameValue 0 ⟨0, by decide⟩ = 0 := by
  norm_num [indexedNameValue, tribonacciNameValue, tribonacciWordValue,
    tribonacciIndexEquiv, tribonacci]

@[simp] theorem indexedNameValue_level_one_zero :
    indexedNameValue 1 ⟨0, by decide⟩ = 0 := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 1 ⟨0, by decide⟩).1 =
      Fin.cons false (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_one_one :
    indexedNameValue 1 ⟨1, by decide⟩ = t ^ (-1 : ℤ) := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 1 ⟨1, by decide⟩).1 =
      Fin.cons true (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_two_zero :
    indexedNameValue 2 ⟨0, by decide⟩ = 0 := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 2 ⟨0, by decide⟩).1 =
      Fin.cons false (Fin.cons false (fun i : Fin 0 => Fin.elim0 i)) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_two_one :
    indexedNameValue 2 ⟨1, by decide⟩ = t ^ (-2 : ℤ) := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 2 ⟨1, by decide⟩).1 =
      Fin.cons false (Fin.cons true (fun i : Fin 0 => Fin.elim0 i)) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_two_two :
    indexedNameValue 2 ⟨2, by decide⟩ = t ^ (-1 : ℤ) := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 2 ⟨2, by decide⟩).1 =
      Fin.cons true (Fin.cons false (fun i : Fin 0 => Fin.elim0 i)) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_two_three :
    indexedNameValue 2 ⟨3, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-2 : ℤ) := by
  unfold indexedNameValue tribonacciNameValue
  have hword : (tribonacciIndexEquiv 2 ⟨3, by decide⟩).1 =
      Fin.cons true (Fin.cons true (fun i : Fin 0 => Fin.elim0 i)) := by
    funext i
    fin_cases i <;> decide
  rw [hword]
  norm_num [tribonacciWordValue, tribonacci_zpow_mul]

@[simp] theorem indexedNameValue_level_three_zero :
    indexedNameValue 3 ⟨0, by decide⟩ = 0 := by
  rw [indexedNameValue_lower 0 ⟨0, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci])]
  have hindex : (⟨0, by norm_num [tribonacci]⟩ : Fin (tribonacci (0 + 4))) =
      ⟨0, by decide⟩ := by apply Fin.ext; norm_num
  rw [hindex, indexedNameValue_level_two_zero]
  ring

@[simp] theorem indexedNameValue_level_three_one :
    indexedNameValue 3 ⟨1, by decide⟩ = t ^ (-3 : ℤ) := by
  rw [indexedNameValue_lower 0 ⟨1, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci])]
  have hindex : (⟨1, by norm_num [tribonacci]⟩ : Fin (tribonacci (0 + 4))) =
      ⟨1, by decide⟩ := by apply Fin.ext; norm_num
  rw [hindex, indexedNameValue_level_two_one, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_three_two :
    indexedNameValue 3 ⟨2, by decide⟩ = t ^ (-2 : ℤ) := by
  rw [indexedNameValue_lower 0 ⟨2, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci])]
  have hindex : (⟨2, by norm_num [tribonacci]⟩ : Fin (tribonacci (0 + 4))) =
      ⟨2, by decide⟩ := by apply Fin.ext; norm_num
  rw [hindex, indexedNameValue_level_two_two, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_three_three :
    indexedNameValue 3 ⟨3, by decide⟩ = t ^ (-2 : ℤ) + t ^ (-3 : ℤ) := by
  rw [indexedNameValue_lower 0 ⟨3, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci])]
  have hindex : (⟨3, by norm_num [tribonacci]⟩ : Fin (tribonacci (0 + 4))) =
      ⟨3, by decide⟩ := by apply Fin.ext; norm_num
  rw [hindex, indexedNameValue_level_two_three, mul_add,
    tribonacci_zpow_mul, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_three_four :
    indexedNameValue 3 ⟨4, by decide⟩ = t ^ (-1 : ℤ) := by
  rw [indexedNameValue_middle 0 ⟨4, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci]) (by norm_num [tribonacci])]
  have hindex :
      (⟨(4 : Nat) - tribonacci (0 + 4), by norm_num [tribonacci]⟩ :
          Fin (tribonacci ((0 + 1) + 2))) = ⟨0, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacci]
  rw [hindex, indexedNameValue_level_one_zero]
  ring

@[simp] theorem indexedNameValue_level_three_five :
    indexedNameValue 3 ⟨5, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-3 : ℤ) := by
  rw [indexedNameValue_middle 0 ⟨5, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci]) (by norm_num [tribonacci])]
  have hindex :
      (⟨(5 : Nat) - tribonacci (0 + 4), by norm_num [tribonacci]⟩ :
          Fin (tribonacci ((0 + 1) + 2))) = ⟨1, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacci]
  rw [hindex, indexedNameValue_level_one_one, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_three_six :
    indexedNameValue 3 ⟨6, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-2 : ℤ) := by
  rw [indexedNameValue_upper 0 ⟨6, by norm_num [tribonacci]⟩
    (by norm_num [tribonacci])]
  have hindex :
      (⟨(6 : Nat) - (tribonacci (0 + 4) + tribonacci (0 + 3)),
          by norm_num [tribonacci]⟩ : Fin (tribonacci (0 + 2))) =
        ⟨0, by decide⟩ := by
    apply Fin.ext
    norm_num [tribonacci]
  rw [hindex, indexedNameValue_level_zero]
  ring

example : adjacentNameValueGaps 2 =
    [t ^ (-2 : ℤ), t ^ (-3 : ℤ) + t ^ (-4 : ℤ), t ^ (-2 : ℤ)] := by
  change [indexedNameValue 2 ⟨1, by decide⟩ - indexedNameValue 2 ⟨0, by decide⟩,
    indexedNameValue 2 ⟨2, by decide⟩ - indexedNameValue 2 ⟨1, by decide⟩,
    indexedNameValue 2 ⟨3, by decide⟩ - indexedNameValue 2 ⟨2, by decide⟩] = _
  rw [indexedNameValue_level_two_zero, indexedNameValue_level_two_one,
    indexedNameValue_level_two_two, indexedNameValue_level_two_three]
  simp only [List.cons.injEq, sub_zero, add_sub_cancel_left, true_and, and_true]
  have hrec : t ^ (-1 : ℤ) =
      t ^ (-2 : ℤ) + t ^ (-3 : ℤ) + t ^ (-4 : ℤ) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  linarith

example : adjacentNameValueGaps 3 =
    [t ^ (-3 : ℤ), t ^ (-4 : ℤ) + t ^ (-5 : ℤ), t ^ (-3 : ℤ),
      t ^ (-4 : ℤ), t ^ (-3 : ℤ), t ^ (-4 : ℤ) + t ^ (-5 : ℤ)] := by
  change [indexedNameValue 3 ⟨1, by decide⟩ - indexedNameValue 3 ⟨0, by decide⟩,
    indexedNameValue 3 ⟨2, by decide⟩ - indexedNameValue 3 ⟨1, by decide⟩,
    indexedNameValue 3 ⟨3, by decide⟩ - indexedNameValue 3 ⟨2, by decide⟩,
    indexedNameValue 3 ⟨4, by decide⟩ - indexedNameValue 3 ⟨3, by decide⟩,
    indexedNameValue 3 ⟨5, by decide⟩ - indexedNameValue 3 ⟨4, by decide⟩,
    indexedNameValue 3 ⟨6, by decide⟩ - indexedNameValue 3 ⟨5, by decide⟩] = _
  rw [indexedNameValue_level_three_zero, indexedNameValue_level_three_one,
    indexedNameValue_level_three_two, indexedNameValue_level_three_three,
    indexedNameValue_level_three_four, indexedNameValue_level_three_five,
    indexedNameValue_level_three_six]
  simp only [List.cons.injEq, sub_zero, add_sub_cancel_left, true_and, and_true]
  have hrec1 : t ^ (-1 : ℤ) =
      t ^ (-2 : ℤ) + t ^ (-3 : ℤ) + t ^ (-4 : ℤ) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  have hrec2 : t ^ (-2 : ℤ) =
      t ^ (-3 : ℤ) + t ^ (-4 : ℤ) + t ^ (-5 : ℤ) := by
    convert tribonacci_zpow_recurrence 2 using 1 <;> norm_num
  constructor
  · linarith
  · constructor <;> linarith

theorem indexedNameValue_level_four_lower (i : Fin 7) :
    indexedNameValue 4 ⟨i.1, by norm_num [tribonacci]; omega⟩ =
      t ^ (-1 : ℤ) * indexedNameValue 3 i := by
  have hi : i.1 < tribonacci (1 + 4) := by
    norm_num [tribonacci]
  have h := indexedNameValue_lower 1
    ⟨i.1, by norm_num [tribonacci]; omega⟩ hi
  simpa [tribonacci] using h

theorem indexedNameValue_level_four_middle (i : Fin 4) :
    indexedNameValue 4 ⟨7 + i.1, by norm_num [tribonacci]; omega⟩ =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * indexedNameValue 2 i := by
  have hlower : tribonacci (1 + 4) ≤ 7 + i.1 := by norm_num [tribonacci]
  have hupper : 7 + i.1 < tribonacci (1 + 4) + tribonacci (1 + 3) := by
    norm_num [tribonacci]
    omega
  have h := indexedNameValue_middle 1
    ⟨7 + i.1, by norm_num [tribonacci]; omega⟩ hlower hupper
  simpa [tribonacci] using h

theorem indexedNameValue_level_four_upper (i : Fin 2) :
    indexedNameValue 4 ⟨11 + i.1, by norm_num [tribonacci]; omega⟩ =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) + t ^ (-3 : ℤ) * indexedNameValue 1 i := by
  have hlower : tribonacci (1 + 4) + tribonacci (1 + 3) ≤ 11 + i.1 := by
    norm_num [tribonacci]
  have h := indexedNameValue_upper 1
    ⟨11 + i.1, by norm_num [tribonacci]; omega⟩ hlower
  simpa [tribonacci] using h

@[simp] theorem indexedNameValue_level_four_zero :
    indexedNameValue 4 ⟨0, by decide⟩ = 0 := by
  rw [indexedNameValue_level_four_lower ⟨0, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨0, by decide⟩ = 0
  rw [indexedNameValue_level_three_zero]
  ring

@[simp] theorem indexedNameValue_level_four_one :
    indexedNameValue 4 ⟨1, by decide⟩ = t ^ (-4 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨1, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨1, by decide⟩ = _
  rw [indexedNameValue_level_three_one, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_two :
    indexedNameValue 4 ⟨2, by decide⟩ = t ^ (-3 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨2, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨2, by decide⟩ = _
  rw [indexedNameValue_level_three_two, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_three :
    indexedNameValue 4 ⟨3, by decide⟩ = t ^ (-3 : ℤ) + t ^ (-4 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨3, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨3, by decide⟩ = _
  rw [indexedNameValue_level_three_three, mul_add,
    tribonacci_zpow_mul, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_four :
    indexedNameValue 4 ⟨4, by decide⟩ = t ^ (-2 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨4, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨4, by decide⟩ = _
  rw [indexedNameValue_level_three_four, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_five :
    indexedNameValue 4 ⟨5, by decide⟩ = t ^ (-2 : ℤ) + t ^ (-4 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨5, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨5, by decide⟩ = _
  rw [indexedNameValue_level_three_five, mul_add,
    tribonacci_zpow_mul, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_six :
    indexedNameValue 4 ⟨6, by decide⟩ = t ^ (-2 : ℤ) + t ^ (-3 : ℤ) := by
  rw [indexedNameValue_level_four_lower ⟨6, by decide⟩]
  change t ^ (-1 : ℤ) * indexedNameValue 3 ⟨6, by decide⟩ = _
  rw [indexedNameValue_level_three_six, mul_add,
    tribonacci_zpow_mul, tribonacci_zpow_mul]
  norm_num

@[simp] theorem indexedNameValue_level_four_seven :
    indexedNameValue 4 ⟨7, by decide⟩ = t ^ (-1 : ℤ) := by
  have h := indexedNameValue_level_four_middle ⟨0, by decide⟩
  change indexedNameValue 4 ⟨7, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * indexedNameValue 2 ⟨0, by decide⟩ at h
  rw [indexedNameValue_level_two_zero] at h
  simpa using h

@[simp] theorem indexedNameValue_level_four_eight :
    indexedNameValue 4 ⟨8, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-4 : ℤ) := by
  have h := indexedNameValue_level_four_middle ⟨1, by decide⟩
  change indexedNameValue 4 ⟨8, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * indexedNameValue 2 ⟨1, by decide⟩ at h
  rw [indexedNameValue_level_two_one, tribonacci_zpow_mul] at h
  norm_num at h
  simpa using h

@[simp] theorem indexedNameValue_level_four_nine :
    indexedNameValue 4 ⟨9, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-3 : ℤ) := by
  have h := indexedNameValue_level_four_middle ⟨2, by decide⟩
  change indexedNameValue 4 ⟨9, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * indexedNameValue 2 ⟨2, by decide⟩ at h
  rw [indexedNameValue_level_two_two, tribonacci_zpow_mul] at h
  norm_num at h
  simpa using h

@[simp] theorem indexedNameValue_level_four_ten :
    indexedNameValue 4 ⟨10, by decide⟩ =
      t ^ (-1 : ℤ) + t ^ (-3 : ℤ) + t ^ (-4 : ℤ) := by
  have h := indexedNameValue_level_four_middle ⟨3, by decide⟩
  change indexedNameValue 4 ⟨10, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) * indexedNameValue 2 ⟨3, by decide⟩ at h
  rw [indexedNameValue_level_two_three, mul_add,
    tribonacci_zpow_mul, tribonacci_zpow_mul] at h
  norm_num at h
  simpa [add_assoc] using h

@[simp] theorem indexedNameValue_level_four_eleven :
    indexedNameValue 4 ⟨11, by decide⟩ = t ^ (-1 : ℤ) + t ^ (-2 : ℤ) := by
  have h := indexedNameValue_level_four_upper ⟨0, by decide⟩
  change indexedNameValue 4 ⟨11, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) +
      t ^ (-3 : ℤ) * indexedNameValue 1 ⟨0, by decide⟩ at h
  rw [indexedNameValue_level_one_zero] at h
  simpa using h

@[simp] theorem indexedNameValue_level_four_twelve :
    indexedNameValue 4 ⟨12, by decide⟩ =
      t ^ (-1 : ℤ) + t ^ (-2 : ℤ) + t ^ (-4 : ℤ) := by
  have h := indexedNameValue_level_four_upper ⟨1, by decide⟩
  change indexedNameValue 4 ⟨12, by decide⟩ =
    t ^ (-1 : ℤ) + t ^ (-2 : ℤ) +
      t ^ (-3 : ℤ) * indexedNameValue 1 ⟨1, by decide⟩ at h
  rw [indexedNameValue_level_one_one, tribonacci_zpow_mul] at h
  norm_num at h
  simpa using h

example : adjacentNameValueGaps 4 =
    [t ^ (-4 : ℤ), t ^ (-5 : ℤ) + t ^ (-6 : ℤ), t ^ (-4 : ℤ),
      t ^ (-5 : ℤ), t ^ (-4 : ℤ), t ^ (-5 : ℤ) + t ^ (-6 : ℤ),
      t ^ (-4 : ℤ), t ^ (-4 : ℤ), t ^ (-5 : ℤ) + t ^ (-6 : ℤ),
      t ^ (-4 : ℤ), t ^ (-5 : ℤ), t ^ (-4 : ℤ)] := by
  change [indexedNameValue 4 ⟨1, by decide⟩ - indexedNameValue 4 ⟨0, by decide⟩,
    indexedNameValue 4 ⟨2, by decide⟩ - indexedNameValue 4 ⟨1, by decide⟩,
    indexedNameValue 4 ⟨3, by decide⟩ - indexedNameValue 4 ⟨2, by decide⟩,
    indexedNameValue 4 ⟨4, by decide⟩ - indexedNameValue 4 ⟨3, by decide⟩,
    indexedNameValue 4 ⟨5, by decide⟩ - indexedNameValue 4 ⟨4, by decide⟩,
    indexedNameValue 4 ⟨6, by decide⟩ - indexedNameValue 4 ⟨5, by decide⟩,
    indexedNameValue 4 ⟨7, by decide⟩ - indexedNameValue 4 ⟨6, by decide⟩,
    indexedNameValue 4 ⟨8, by decide⟩ - indexedNameValue 4 ⟨7, by decide⟩,
    indexedNameValue 4 ⟨9, by decide⟩ - indexedNameValue 4 ⟨8, by decide⟩,
    indexedNameValue 4 ⟨10, by decide⟩ - indexedNameValue 4 ⟨9, by decide⟩,
    indexedNameValue 4 ⟨11, by decide⟩ - indexedNameValue 4 ⟨10, by decide⟩,
    indexedNameValue 4 ⟨12, by decide⟩ - indexedNameValue 4 ⟨11, by decide⟩] = _
  rw [indexedNameValue_level_four_zero, indexedNameValue_level_four_one,
    indexedNameValue_level_four_two, indexedNameValue_level_four_three,
    indexedNameValue_level_four_four, indexedNameValue_level_four_five,
    indexedNameValue_level_four_six, indexedNameValue_level_four_seven,
    indexedNameValue_level_four_eight, indexedNameValue_level_four_nine,
    indexedNameValue_level_four_ten, indexedNameValue_level_four_eleven,
    indexedNameValue_level_four_twelve]
  simp only [List.cons.injEq, sub_zero, true_and, and_true]
  have hrec1 : t ^ (-1 : ℤ) =
      t ^ (-2 : ℤ) + t ^ (-3 : ℤ) + t ^ (-4 : ℤ) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  have hrec2 : t ^ (-2 : ℤ) =
      t ^ (-3 : ℤ) + t ^ (-4 : ℤ) + t ^ (-5 : ℤ) := by
    convert tribonacci_zpow_recurrence 2 using 1 <;> norm_num
  have hrec3 : t ^ (-3 : ℤ) =
      t ^ (-4 : ℤ) + t ^ (-5 : ℤ) + t ^ (-6 : ℤ) := by
    convert tribonacci_zpow_recurrence 3 using 1 <;> norm_num
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · constructor
                · linarith
                · constructor
                  · linarith
                  · constructor <;> linarith

end D5.S0.Tower.Tribonacci.Values

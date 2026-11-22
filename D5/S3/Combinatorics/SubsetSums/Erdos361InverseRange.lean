/- GID: D5/S3/Combinatorics/SubsetSums/Erdos361InverseRange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSums/Erdos361InverseRange
   mirror-E: none(waiver:integer-counterexample)
   anchors: []
   utility: none
   digest: Sharp range obstruction for the least-nondivisor-four subset-sum inverse theorem. -/

module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-! Modulo-five obstructions for the inverse theorem with the fixed factor six. -/

namespace D5.S3.Combinatorics.SubsetSums.Erdos361InverseRange

public section

open scoped BigOperators

private def base (k m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (4 * (k + 1) * m)).image (fun j => 5 * j)

private def top (k m : ℕ) : Finset ℕ :=
  (Finset.Ico ((3 * k + 2) * m) (4 * (k + 1) * m)).image (fun j => 5 * j + 1)

/-- These interval sets have excess m over one quarter of the ambient interval. -/
def avoidingSet (k m : ℕ) : Finset ℕ :=
  base k m ∪ top k m

private theorem mem_base_mod {k m x : ℕ} (hx : x ∈ base k m) : x % 5 = 0 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  omega

private theorem mem_top_mod {k m x : ℕ} (hx : x ∈ top k m) : x % 5 = 1 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  omega

theorem avoidingSet_subset (k m : ℕ) : avoidingSet k m ⊆ Finset.Icc 1 (20 * (k + 1) * m) := by
  have hscale : 20 * (k+1) * m = 5 * (4 * (k+1) * m) := by ring
  rw [hscale]
  intro x hx
  rcases Finset.mem_union.mp hx with hb | ht
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rcases Finset.mem_Icc.mp hj with ⟨hlo, hhi⟩
    rw [Finset.mem_Icc]
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hhi := (Finset.mem_Ico.mp hj).2
    rw [Finset.mem_Icc]
    omega

theorem avoidingSet_card (k m : ℕ) : (avoidingSet k m).card = (5 * k + 6) * m := by
  have hd : Disjoint (base k m) (top k m) := Finset.disjoint_left.mpr fun _ hb ht =>
    by simpa [mem_base_mod hb] using mem_top_mod ht
  unfold avoidingSet
  rw [Finset.card_union_of_disjoint hd]
  unfold base top
  rw [Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_image_of_injective _ (fun a b h => by omega), Nat.card_Icc, Nat.card_Ico]
  have h (a b : ℕ) : 4 * (a+1) * b = (3*a+2)*b + (a+2)*b := by ring
  rw [h k m]
  have htotal : (5*k+6)*m = (3*k+2)*m + 2*((k+2)*m) := by ring
  omega

/-- For all m at least three this particular target is absent among the
distinct-element sums, even though the set exceeds quarter density. -/
theorem avoidingSet_sum_ne (k m : ℕ) (hm : 3 ≤ m) (B : Finset ℕ)
    (hB : B ⊆ avoidingSet k m) :
    (∑ x ∈ B, x) ≠ 6 * (5 * (2 * k + 1) * m + 4) := by
  intro he
  let C := B.filter (fun x => x ∈ top k m)
  have hmod : (∑ x ∈ B, x) ≡ ∑ x ∈ B, if x ∈ top k m then 1 else 0 [MOD 5] := by
    apply Nat.ModEq.sum
    intro x hx
    rcases Finset.mem_union.mp (hB hx) with hl | hu
    · have hnot : x ∉ top k m := fun h => by
        simpa [mem_base_mod hl] using mem_top_mod h
      simpa only [ite_eq_right hnot, Nat.ModEq] using mem_base_mod hl
    · simpa only [ite_eq_left hu, Nat.ModEq] using mem_top_mod hu
  have hcount : (∑ x ∈ B, if x ∈ top k m then 1 else 0) = C.card := by
    simp [C, Finset.filter_mem_eq_inter]
  rw [he, hcount] at hmod
  change (6 * (5 * (2 * k + 1) * m + 4)) % 5 = C.card % 5 at hmod
  have hres : 6 * (5 * (2*k+1)*m + 4) = 5 * (6 * ((2*k+1)*m)) + 24 := by ring
  rw [hres] at hmod
  have hf : 4 ≤ C.card := by omega
  have hterms : C.card * (5 * ((3 * k + 2) * m) + 1) ≤ ∑ x ∈ C, x := by
    calc
      _ = ∑ _ ∈ C, (5 * ((3 * k + 2) * m) + 1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).2
        have hj' := (Finset.mem_Ico.mp hj).1
        omega
  have hsub : (∑ x ∈ C, x) ≤ ∑ x ∈ B, x :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hlo := Nat.mul_le_mul_right (5 * ((3 * k + 2) * m) + 1) hf
  have hstrict : 6 * (5 * (2 * k + 1) * m + 4) < 4 * (5 * ((3 * k + 2) * m) + 1) := by
    have hbal : 4 * (5 * ((3*k+2)*m) + 1) + 20 =
      6 * (5 * (2*k+1)*m + 4) + 10*m := by ring
    omega
  exact (not_le_of_gt hstrict) (hlo.trans (hterms.trans (hsub.trans_eq he)))


/-- For the fixed factor six, whose least nondivisor is four, every range
constant below three fails at a fixed positive density excess and
arbitrarily large multipliers. -/
theorem every_range_below_three_fails (theta : ℝ) (htheta : theta < 3) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ cutoff : ℕ,
      ∃ E T : ℕ, ∃ A : Finset ℕ,
        cutoff ≤ T ∧ 1 ≤ E ∧ A ⊆ Finset.Icc 1 E ∧
        theta * (E : ℝ) ≤ 6 * (T : ℝ) ∧
        (E : ℝ) / 4 + epsilon * (T : ℝ) ≤ (A.card : ℝ) ∧
        ∀ B : Finset ℕ, B ⊆ A → (∑ x ∈ B, x) ≠ 6 * T := by
  have hgap0 : 0 < 3 - theta := sub_pos.mpr htheta
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / (3 - theta))
  have hgap : 3 < (3 - theta) * (k : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hgap0).mp hk
  let denominator : ℝ := 5 * (2 * (k : ℝ) + 1) + 4
  have hd : 0 < denominator := by
    dsimp [denominator]
    positivity
  refine ⟨denominator⁻¹, inv_pos.mpr hd, ?_⟩
  intro cutoff
  let m := cutoff + 3
  let E := 20 * (k + 1) * m
  let T := 5 * (2 * k + 1) * m + 4
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hmN : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hcutoff : cutoff ≤ T := by
    have hmT : m ≤ 5 * (2 * k + 1) * m := by
      simpa only [one_mul] using
        Nat.mul_le_mul_right m (show 1 ≤ 5 * (2 * k + 1) by omega)
    calc
      cutoff ≤ m := by dsimp [m]; omega
      _ ≤ 5 * (2*k+1) * m := hmT
      _ ≤ T := Nat.le_add_right _ _
  have hE : 1 ≤ E := by
    apply Nat.succ_le_of_lt
    dsimp [E]
    have hmpos : 0 < m := by omega
    positivity
  refine ⟨E, T, avoidingSet k m, hcutoff, hE, avoidingSet_subset k m, ?_, ?_, ?_⟩
  · have hsingle : theta * (20 * ((k : ℝ) + 1)) ≤ 6 * (5 * (2 * (k : ℝ) + 1)) := by
      nlinarith
    dsimp [E, T]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hsingle hmN]
  · have hT : (T : ℝ) ≤ denominator * (m : ℝ) := by
      dsimp [T, denominator]
      push_cast
      nlinarith only [hmR]
    have hexcess : denominator⁻¹ * (T : ℝ) ≤ (m : ℝ) := by
      have hdiv := (div_le_iff₀ hd).mpr (show (T : ℝ) ≤ (m : ℝ) * denominator by
        simpa only [mul_comm] using hT)
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    rw [avoidingSet_card]
    dsimp [E]
    push_cast
    nlinarith only [hexcess]
  · intro B hB
    exact avoidingSet_sum_ne k m hm B hB

#print axioms every_range_below_three_fails

end

end D5.S3.Combinatorics.SubsetSums.Erdos361InverseRange

/- GID: D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.claim; result=D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.result; claim=D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutation.claim
   digest: A staged set refutes the beta-three quarter-density conjecture. -/

import D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationDensity
import D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationOrder
import D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationEnumeration

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutation

open D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationDensity

/-- An infinite set admits a bijective enumeration with no three-term arithmetic
progression as a subsequence, in either numerical direction. -/
def ThreeFree (T : Set ℕ) : Prop :=
  ∃ π : ℕ → ℕ, Function.Injective π ∧ Set.range π = T ∧
    ∀ i j k : ℕ, i < j → j < k → π i + π k ≠ 2 * π j

/-- The source's lower density: liminf of the number of elements in [1,n]
divided by n, with real-valued ratios. -/
noncomputable def lowerDensity (T : Set ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => ((T ∩ Set.Icc 1 n).ncard : ℝ) / n) Filter.atTop

/-- LeSaulnier--Vijay's conjectured upper bound for beta(3). -/
def claim : Prop :=
  ∀ T : Set ℕ, 0 ∉ T → ThreeFree T → lowerDensity T ≤ 1 / 4

private lemma stage_before {i j x y : ℕ} (hi : x ∈ stage i) (hj : y ∈ stage j)
    (hij : i < j) : x < y := by
  have hx := stage_bounds hi
  have hy := stage_bounds hj
  have hm := M_strictMono.monotone (show i + 1 ≤ j by omega)
  have hp := M_pos j
  omega

private lemma stage_unique {i j x : ℕ} (hi : x ∈ stage i) (hj : x ∈ stage j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := stage_before hi hj h; omega
  · exact h
  · have := stage_before hj hi h; omega

private lemma one_not_stage (k : ℕ) : 1 ∉ stage k := by
  intro h
  have := stage_bounds h
  have := M_pos k
  omega

private lemma earlier_bound {k x y : ℕ} (hx : x ∈ S) (hy : y ∈ stage k)
    (hxy : x < y) : x ≤ M k ∨ x ∈ stage k := by
  rcases hx with hx | ⟨i, hi⟩
  · have := M_pos k
    simp only [Set.mem_singleton_iff] at hx
    omega
  · rcases lt_trichotomy i k with h | h | h
    · have := (stage_bounds hi).2
      have := M_strictMono.monotone (show i + 1 ≤ k by omega)
      exact Or.inl (by omega)
    · subst i; exact Or.inr hi
    · have := stage_before hy hi h; omega

private lemma separated {a b c : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbc : b < c) (hap : a + c = 2 * b) :
    ∃ k, a ∈ stage k ∧ b ∈ stage k ∧ c ∈ stage k := by
  have hapos := S_pos ha
  rcases hc with hc | ⟨k, hk⟩
  · simp only [Set.mem_singleton_iff] at hc; omega
  · have hcBounds := stage_bounds hk
    rcases earlier_bound hb hk hbc with hbold | hbcur
    · omega
    · refine ⟨k, ?_, hbcur, hk⟩
      rcases earlier_bound ha hbcur hab with haold | hacur
      · have hp := M_pos k
        rw [M_step] at hcBounds
        rcases hbcur with hbcur | hbcur <;>
          simp only [Set.mem_Icc] at hbcur
        · rcases hk with hk | hk <;> simp only [Set.mem_Icc] at hk <;> omega
        · omega
      · exact hacur

private noncomputable def stageIndex (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, x ∈ stage k then Nat.find h else 0

private lemma stageIndex_eq {k x : ℕ} (hx : x ∈ stage k) : stageIndex x = k := by
  classical
  have h : ∃ k, x ∈ stage k := ⟨k, hx⟩
  unfold stageIndex
  rw [dif_pos h]
  exact stage_unique (Nat.find_spec h) hx

private noncomputable def globalRank (x : ℕ) : ℕ :=
  if x = 1 then 0 else
    2 ^ M (stageIndex x + 1) +
      LeSaulnierVijayLowerDensityRefutationOrder.rank (M (stageIndex x + 1)) x

private lemma globalRank_stage {k x : ℕ} (hx : x ∈ stage k) :
    globalRank x = 2 ^ M (k + 1) +
      LeSaulnierVijayLowerDensityRefutationOrder.rank (M (k + 1)) x := by
  have hne : x ≠ 1 := by intro h; subst x; exact one_not_stage k hx
  simp only [globalRank, if_neg hne, stageIndex_eq hx]

private lemma globalRank_positive {k x : ℕ} (hx : x ∈ stage k) : 0 < globalRank x := by
  rw [globalRank_stage hx]
  have : 0 < (2 : ℕ) ^ M (k + 1) := pow_pos (by omega) _
  omega

private lemma globalRank_before {i j x y : ℕ} (hx : x ∈ stage i)
    (hy : y ∈ stage j) (hij : i < j) : globalRank x < globalRank y := by
  rw [globalRank_stage hx, globalRank_stage hy]
  have hr := LeSaulnierVijayLowerDensityRefutationOrder.rank_lt (M (i + 1)) x
  have hm := M_strictMono (show i + 1 < j + 1 by omega)
  have hp : (2 : ℕ) ^ (M (i + 1) + 1) ≤ 2 ^ M (j + 1) :=
    pow_le_pow_right' (by omega) (by omega)
  rw [pow_succ] at hp
  omega

private lemma globalRank_injective : Set.InjOn globalRank S := by
  intro x hx y hy heq
  rcases hx with hx | ⟨i, hi⟩ <;> rcases hy with hy | ⟨j, hj⟩
  · simp only [Set.mem_singleton_iff] at hx hy
    exact hx.trans hy.symm
  · simp only [Set.mem_singleton_iff] at hx
    subst x
    have := globalRank_positive hj
    have hz : globalRank 1 = 0 := by simp [globalRank]
    rw [hz] at heq
    omega
  · simp only [Set.mem_singleton_iff] at hy
    subst y
    have := globalRank_positive hi
    have hz : globalRank 1 = 0 := by simp [globalRank]
    rw [hz] at heq
    omega
  · have hij : i = j := by
      rcases lt_trichotomy i j with h | h | h
      · have := globalRank_before hi hj h; omega
      · exact h
      · have := globalRank_before hj hi h; omega
    subst j
    rw [globalRank_stage hi, globalRank_stage hj] at heq
    have hxBound : x < 2 ^ M (i + 1) :=
      lt_of_le_of_lt (stage_bounds hi).2 (Nat.lt_two_pow_self)
    have hyBound : y < 2 ^ M (i + 1) :=
      lt_of_le_of_lt (stage_bounds hj).2 (Nat.lt_two_pow_self)
    exact LeSaulnierVijayLowerDensityRefutationOrder.rank_injective hxBound hyBound
      (by omega)

private lemma S_infinite : S.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => 2 * M k)
  · intro i j h
    change 2 * M i = 2 * M j at h
    apply M_strictMono.injective
    omega
  · intro k
    apply Or.inr
    refine ⟨k, Or.inl ?_⟩
    have := M_pos k
    simp only [Set.mem_Icc]
    omega

private lemma S_threeFree : ThreeFree S := by
  obtain ⟨π, hinj, hrange, hmono⟩ :=
    LeSaulnierVijayLowerDensityRefutationEnumeration.enumerateRank S_infinite
      globalRank globalRank_injective
  refine ⟨π, hinj, hrange, ?_⟩
  intro i j k hij hjk hap
  have hmem : ∀ n, π n ∈ S := by intro n; rw [← hrange]; exact ⟨n, rfl⟩
  have hab : π i ≠ π j := fun h => (by omega : i ≠ j) (hinj h)
  have hbc : π j ≠ π k := fun h => (by omega : j ≠ k) (hinj h)
  have hrab := hmono i j hij
  have hrbc := hmono j k hjk
  have hsame : ∃ t, π i ∈ stage t ∧ π j ∈ stage t ∧ π k ∈ stage t := by
    rcases lt_trichotomy (π i) (π j) with h | h | h
    · exact separated (hmem i) (hmem j) (hmem k) h (by omega) hap
    · exact False.elim (hab h)
    · obtain ⟨t, ht⟩ := separated (hmem k) (hmem j) (hmem i) (by omega) h (by omega)
      exact ⟨t, ht.2.2, ht.2.1, ht.1⟩
  obtain ⟨t, ha, hb, hc⟩ := hsame
  rw [globalRank_stage ha, globalRank_stage hb] at hrab
  rw [globalRank_stage hb, globalRank_stage hc] at hrbc
  apply LeSaulnierVijayLowerDensityRefutationOrder.rank_no_ap
    (lt_of_le_of_lt (stage_bounds ha).2 Nat.lt_two_pow_self)
    (lt_of_le_of_lt (stage_bounds hb).2 Nat.lt_two_pow_self)
    (lt_of_le_of_lt (stage_bounds hc).2 Nat.lt_two_pow_self) hap
  constructor <;> omega

/-- The intervals in the conjecture refutation, with the literal power endpoints. -/
private def witness : Set ℕ :=
  {1} ∪ {x | ∃ k : ℕ,
    x ∈ Set.Icc (11 ^ k + 1) ((3 * 11 ^ k + 1) / 2) ∪
      Set.Icc (3 * 11 ^ k + 1) ((11 ^ (k + 1) + 1) / 2)}

private lemma witness_eq : witness = S := by
  ext x
  simp only [witness, S, Set.mem_union, Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  apply exists_congr
  intro k
  have ht := twice_M k
  have hp := M_pos k
  have hleft : 11 ^ k + 1 = 2 * M k := by omega
  have hmiddle : (3 * 11 ^ k + 1) / 2 = 3 * M k - 1 := by omega
  have hright : 3 * 11 ^ k + 1 = 6 * M k - 2 := by omega
  rw [hleft, hmiddle, hright]
  change x ∈ Set.Icc (2 * M k) (3 * M k - 1) ∪
    Set.Icc (6 * M k - 2) (M (k + 1)) ↔ x ∈ stage k
  rw [M_step]
  rfl

/-- The explicit staged set has lower density at least 4/15, exceeding 1/4. -/
theorem result : ¬ claim := by
  intro h
  have hpositive : 0 ∉ witness := by
    rw [witness_eq]
    intro hzero
    have := S_pos hzero
    omega
  have hfree : ThreeFree witness := by rw [witness_eq]; exact S_threeFree
  have hupper := h witness hpositive hfree
  rw [witness_eq] at hupper
  have hlower := lowerDensityBound
  change (4 / 15 : ℝ) ≤ lowerDensity S at hlower
  norm_num at hupper hlower ⊢
  linarith

end D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutation

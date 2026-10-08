/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdSynchronization
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdSynchronization
   mirror-E: none(waiver:palette-phase-synchronization)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Data.Nat.Count]
   utility: none
   digest: Equal coloured windows determine both palette phases once both cycles are seen. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Count
import D5.S1.Words.BalancedThreshold.BalancedThresholdPalettes
import D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

open D5.S1.Words.Mechanical D5.S1.Words.Complexity

/-- Physical-window induction extracts the consecutive palette ranks. Two majority ranks
determine both cycle residues, and coprimality recovers the complete majority phase. -/
theorem palette_factor_synchronization (alpha rho : ℝ) (t : ℕ) (ht : 0 < t)
    (n i j : ℕ)
    (heq : wordFactor (colouredMechanicalWord alpha rho t ht) n i =
      wordFactor (colouredMechanicalWord alpha rho t ht) n j)
    (ha : 0 < lowerMechanicalWindowTrueCount alpha rho i n)
    (hb : 2 ≤ n - lowerMechanicalWindowTrueCount alpha rho i n) :
    wordFactor (lowerMechanicalWord alpha rho) n i =
      wordFactor (lowerMechanicalWord alpha rho) n j ∧
    lowerMechanicalWindowTrueCount alpha rho 0 i % 2 =
      lowerMechanicalWindowTrueCount alpha rho 0 j % 2 ∧
    (i - lowerMechanicalWindowTrueCount alpha rho 0 i) % (2 * t * (t + 1)) =
      (j - lowerMechanicalWindowTrueCount alpha rho 0 j) % (2 * t * (t + 1)) := by
  classical
  let u := lowerMechanicalWord alpha rho
  let x := colouredMechanicalWord alpha rho t ht
  let c := lowerMechanicalWindowTrueCount alpha rho 0
  let a := fun s k => lowerMechanicalWindowTrueCount alpha rho s k
  let b := fun s => s - c s
  let paint := fun r : ℕ =>
    if r % 2 = 0 then 2 + (r / 2) % t else 2 + t + (r / 2) % (t + 1)
  have cle : ∀ k, c k ≤ k := by
    intro k
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range k)
  have ale : ∀ s k, a s k ≤ k := by
    intro s k
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range k)
  have telescope : ∀ s k, c (s + k) = c s + a s k := by
    intro s k
    simpa only [Nat.count_eq_card_filter_range, u, c, a, lowerMechanicalWindowTrueCount,
      Nat.zero_add] using Nat.count_add (fun r => u r = true) s k
  have bs : ∀ s k, b (s + k) = b s + (k - a s k) := by
    intro s k
    have hc := telescope s k
    have hcs := cle s
    have hak := ale s k
    dsimp [b]
    omega
  have astep : ∀ s k, a s (k + 1) = a s k + if u (s + k) = true then 1 else 0 := by
    intro s k
    simp only [a, lowerMechanicalWindowTrueCount, Finset.range_add_one,
      Finset.filter_insert]
    split_ifs <;> simp_all
  have label : ∀ k, (x k).val = if u k = true then c k % 2 else paint (b k) := by
    intro k
    simp only [x, colouredMechanicalWord, u, c, b, paint]
    split_ifs <;> rfl
  have project : ∀ k, u k = true ↔ (x k).val < 2 := by
    intro k
    rw [label]
    have hm := Nat.mod_lt (c k) (by omega : 0 < 2)
    by_cases hu : u k = true
    · simp [hu, hm]
    · constructor
      · exact fun h => (hu h).elim
      · intro hz
        rw [if_neg hu] at hz
        dsimp [paint] at hz
        split_ifs at hz <;> omega
  have extract : ∀ k,
      (∀ r, r < k → x (i + r) = x (j + r)) →
      (∀ r, r < k → u (i + r) = u (j + r)) ∧
      a i k = a j k ∧
      (∀ q, q < a i k → (c i + q) % 2 = (c j + q) % 2) ∧
      (∀ q, q < k - a i k → paint (b i + q) = paint (b j + q)) := by
    intro k
    induction k with
    | zero => simp [a, lowerMechanicalWindowTrueCount]
    | succ k ih =>
      intro he
      obtain ⟨hproj, hac, htrue, hfalse⟩ := ih (fun r hr => he r (by omega))
      have hx := he k (by omega)
      have hv := congrArg Fin.val hx
      have hu : u (i + k) = u (j + k) := by
        have hi := project (i + k)
        have hj := project (j + k)
        have hh : (u (i + k) = true) ↔ u (j + k) = true := by
          rw [hi, hj, hv]
        exact Bool.eq_iff_iff.mpr hh
      have hai := astep i k
      have haj := astep j k
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr
        by_cases hk : r < k
        · exact hproj r hk
        · have : r = k := by omega
          simpa [this] using hu
      · rw [hai, haj, hac, hu]
      · intro q hq
        by_cases hqk : q < a i k
        · exact htrue q hqk
        · have hui : u (i + k) = true := by split_ifs at hai <;> omega
          have hqeq : q = a i k := by rw [hui, if_pos rfl] at hai; omega
          rw [label, label, if_pos hui, if_pos (hu.symm.trans hui),
            telescope i k, telescope j k, ← hac] at hv
          simpa [hqeq] using hv
      · intro q hq
        by_cases hqk : q < k - a i k
        · exact hfalse q hqk
        · have hui : u (i + k) ≠ true := by split_ifs at hai <;> omega
          have huj : u (j + k) ≠ true := by simpa [← hu] using hui
          have hqeq : q = k - a i k := by rw [if_neg hui] at hai; omega
          rw [label, label, if_neg hui, if_neg huj, bs i k, bs j k, ← hac] at hv
          simpa [hqeq] using hv
  obtain ⟨hproj, _, htrue, hfalse⟩ := extract n (fun r hr => congrFun heq ⟨r, hr⟩)
  change 0 < a i n at ha
  change 2 ≤ n - a i n at hb
  have hminor := htrue 0 ha
  have hfirst := hfalse 0 (by omega)
  have hsecond := hfalse 1 (by omega)
  simp only [Nat.add_zero] at hminor hfirst
  have parity : b i % 2 = b j % 2 := by
    have hti := Nat.mod_lt (b i / 2) ht
    have htj := Nat.mod_lt (b j / 2) ht
    dsimp [paint] at hfirst
    split_ifs at hfirst <;> omega
  have halves : b i / 2 ≡ b j / 2 [MOD t * (t + 1)] := by
    apply (Nat.modEq_and_modEq_iff_modEq_mul
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right t))).mp
    have hi := Nat.mod_lt (b i) (by omega : 0 < 2)
    have hj := Nat.mod_lt (b j) (by omega : 0 < 2)
    by_cases he : b i % 2 = 0
    · have hej : b j % 2 = 0 := by omega
      have hei : (b i + 1) % 2 ≠ 0 := by omega
      have hej' : (b j + 1) % 2 ≠ 0 := by omega
      have hdi : (b i + 1) / 2 = b i / 2 := by omega
      have hdj : (b j + 1) / 2 = b j / 2 := by omega
      simp only [paint, if_pos he, if_pos hej] at hfirst
      simp only [paint, if_neg hei, if_neg hej', hdi, hdj] at hsecond
      constructor <;> change _ % _ = _ % _ <;> omega
    · have hej : b j % 2 ≠ 0 := by omega
      have hei : (b i + 1) % 2 = 0 := by omega
      have hej' : (b j + 1) % 2 = 0 := by omega
      have hdi : (b i + 1) / 2 = b i / 2 + 1 := by omega
      have hdj : (b j + 1) / 2 = b j / 2 + 1 := by omega
      simp only [paint, if_neg he, if_neg hej] at hfirst
      simp only [paint, if_pos hei, if_pos hej', hdi, hdj] at hsecond
      have hnext : b i / 2 + 1 ≡ b j / 2 + 1 [MOD t] := by
        change _ % _ = _ % _
        omega
      exact ⟨hnext.add_right_cancel' 1, by
        change _ % _ = _ % _
        omega⟩
  have hmajor : b i ≡ b j [MOD 2 * t * (t + 1)] := by
    have hmul := halves.mul_left' 2
    have hadd := hmul.add (Nat.ModEq.refl (b i % 2))
    have hi := Nat.mod_add_div (b i) 2
    have hj := Nat.mod_add_div (b j) 2
    rw [← parity] at hj
    simpa only [Nat.mul_assoc, Nat.add_comm, hi, hj] using hadd
  refine ⟨?_, hminor, hmajor⟩
  funext r
  exact hproj r r.isLt

end D5.S1.Words.BalancedThreshold

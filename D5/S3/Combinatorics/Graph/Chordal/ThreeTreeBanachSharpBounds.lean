/- GID: D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An invariant polygon bounds clique-four reconstruction and a hexagonal witness bounds finite width-three path coefficients. -/

import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import OmegaMath.Combinatorics.Graph.ThreeTreePolygon
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Module
import Mathlib.Tactic.IntervalCases

/-! # Banach reconstruction on clique-four chordal graphs and third powers of paths -/

namespace SimpleGraph

open scoped BigOperators

/-- The third power of a finite path. -/
abbrev pathPowerThree (n : ℕ) : SimpleGraph (Fin n) := BanachPathPower.pathPower n 3

section PathUpper

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private def integrate (d : ℕ → E) : ℕ → E
  | 0 => 0
  | i+1 => integrate d i + d i

private def clamp {n : ℕ} (hn : 0 < n) (i : ℕ) : Fin n := ⟨min (i-2) (n-1), by omega⟩

private theorem clamp_between {n : ℕ} (hn : 0 < n) {i j : ℕ} (hij : i ≤ j)
    (hji : j ≤ i + 3) : clamp hn i = clamp hn j ∨
      (pathPowerThree n).Adj (clamp hn i) (clamp hn j) := by
  by_cases h : clamp hn i = clamp hn j
  · exact Or.inl h
  · right
    refine ⟨h, ?_, ?_⟩ <;> dsimp [clamp] <;> omega

/-- Integrate the adjacent gains, then add the sum of the local corrections on the prefix. -/
noncomputable def pathPowerThree_causal_potential (n : ℕ) (g : Fin n → Fin n → E) (i : Fin n) : E :=
  let c := clamp (Nat.zero_lt_of_lt i.isLt)
  let I := integrate fun j => g (c j) (c (j+1))
  let f (j k : ℕ) := g (c j) (c k) - (I k - I j)
  let a (j : ℕ) := f j (j+2)
  let b (j : ℕ) := f j (j+3)
  let ψ (j : ℕ) := (1/3 : ℝ) • (b j - a j + a (j+1))
  I (i.val+2) + integrate ψ i.val

/-- The explicitly integrated causal potential controls the error on all three edge lengths. -/
theorem pathPowerThree_causal_potential_error (n : ℕ) (g : Fin n → Fin n → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ i j, g j i = -g i j)
    (ht : ∀ i j k, (pathPowerThree n).Adj i j → (pathPowerThree n).Adj j k →
      (pathPowerThree n).Adj i k → ‖g i j + g j k - g i k‖ ≤ ε) :
    ∀ i j, (pathPowerThree n).Adj i j →
      ‖g i j - (pathPowerThree_causal_potential n g j - pathPowerThree_causal_potential n g i)‖ ≤
        (4/3 : ℝ) * ε := by
  by_cases hn : 0 < n
  · let c := clamp hn
    let I := integrate fun i => g (c i) (c (i+1))
    let f (i j : ℕ) := g (c i) (c j) - (I j - I i)
    have hstep (i : ℕ) : f i (i+1) = 0 := by simp [f, I, integrate]
    have hdiag (i : Fin n) : g i i = 0 := by
      have hz := eq_neg_iff_add_eq_zero.mp (hg i i)
      exact (smul_eq_zero.mp (by simpa only [two_smul] using hz : (2 : ℝ) • g i i = 0)).resolve_left
        (by norm_num)
    have hflat {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hik : k ≤ i+3) :
        ‖f i j + f j k - f i k‖ ≤ ε := by
      rw [show f i j + f j k - f i k = g (c i) (c j) + g (c j) (c k) - g (c i) (c k) by
        dsimp only [f]; abel]
      rcases clamp_between hn hij (by omega) with h | h₁
      · change c i = c j at h
        simpa [h, hdiag] using hε
      rcases clamp_between hn hjk (by omega) with h | h₂
      · change c j = c k at h
        simpa [h, hdiag] using hε
      rcases clamp_between hn (hij.trans hjk) hik with h | h₃
      · change c i = c k at h
        simpa [← h, hg (c i) (c j), hdiag] using hε
      exact ht _ _ _ h₁ h₂ h₃
    let a (i : ℕ) := f i (i+2)
    let b (i : ℕ) := f i (i+3)
    have ha (i : ℕ) : ‖a i‖ ≤ ε := by
      simpa [a, hstep] using hflat (i := i) (j := i+1) (k := i+2) (by omega) (by omega) (by omega)
    have hab (i : ℕ) : ‖a i - b i‖ ≤ ε := by
      simpa [a, b, hstep] using hflat (i := i) (j := i+2) (k := i+3) (by omega) (by omega) (by omega)
    have hab' (i : ℕ) : ‖a (i+1) - b i‖ ≤ ε := by
      simpa [a, b, hstep, Nat.add_assoc] using hflat (i := i) (j := i+1) (k := i+3)
        (by omega) (by omega) (by omega)
    let ψ (i : ℕ) := (1/3 : ℝ) • (b i - a i + a (i+1))
    let P := integrate ψ
    let φ (i : Fin n) := I (i.val+2) + P i.val
    have hclamp (i : Fin n) : c (i.val+2) = i := by
      apply Fin.ext
      dsimp [c, clamp]
      omega
    have forward {i j : Fin n} (hij : i.val < j.val) (hji : j.val ≤ i.val+3) :
        ‖g i j - (φ j - φ i)‖ ≤ (4/3 : ℝ) * ε := by
      have he : g i j - (φ j - φ i) = f (i.val+2) (j.val+2) - (P j.val - P i.val) := by
        dsimp only [φ, f]
        rw [hclamp i, hclamp j]
        abel
      rw [he]
      let x := i.val
      change ‖f (x+2) (j.val+2) - (P j.val - P x)‖ ≤ _
      have hspan : j.val = x+1 ∨ j.val = x+2 ∨ j.val = x+3 := by dsimp [x]; omega
      rcases hspan with h | h | h
      · rw [h]
        have eq : f (x+2) (x+1+2) - (P (x+1) - P x) =
            (1/3 : ℝ) • ((a x - b x) - a (x+1)) := by
          rw [show x+1+2 = x+2+1 by omega, hstep]
          dsimp [P, integrate, ψ]
          module
        rw [eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)]
        have hn := (norm_sub_le (a x-b x) (a (x+1))).trans (add_le_add (hab x) (ha (x+1)))
        linarith
      · rw [h]
        have eq : f (x+2) (x+2+2) - (P (x+2) - P x) =
            (1/3 : ℝ) • (a (x+2) + (a (x+2) - b (x+1)) + (a x - b x)) := by
          change a (x+2) - (P (x+2) - P x) = _
          dsimp [P, integrate, ψ]
          module
        rw [eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)]
        have hn := (norm_add_le (a (x+2) + (a (x+2) - b (x+1))) (a x-b x)).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add (ha (x+2)) (hab' (x+1)))) (hab x))
        linarith
      · rw [h]
        have eq : f (x+2) (x+3+2) - (P (x+3) - P x) =
            (1/3 : ℝ) • ((b (x+2) - a (x+2)) + (b (x+2) - a (x+3)) +
              (a (x+2) - b (x+1)) + (a x - b x)) := by
          rw [show x+3+2 = x+2+3 by omega]
          change b (x+2) - (P (x+3) - P x) = _
          dsimp [P, integrate, ψ]
          module
        rw [eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3)]
        have hb₁ : ‖b (x+2) - a (x+2)‖ ≤ ε := by rw [norm_sub_rev]; exact hab (x+2)
        have hb₂ : ‖b (x+2) - a (x+3)‖ ≤ ε := by rw [norm_sub_rev]; exact hab' (x+2)
        have hn := (norm_add_le ((b (x+2) - a (x+2)) + (b (x+2) - a (x+3)) +
          (a (x+2) - b (x+1))) (a x - b x)).trans
          (add_le_add ((norm_add_le _ _).trans
            (add_le_add ((norm_add_le _ _).trans (add_le_add hb₁ hb₂)) (hab' (x+1)))) (hab x))
        linarith
    change ∀ i j, (pathPowerThree n).Adj i j → ‖g i j - (φ j - φ i)‖ ≤ _
    intro i j hij
    rcases lt_or_gt_of_ne (fun e => hij.ne (Fin.ext e)) with h | h
    · exact forward h hij.2.2
    · rw [show g i j - (φ j - φ i) = -(g j i - (φ i - φ j)) by rw [hg j i]; abel, norm_neg]
      exact forward h hij.2.1
  · intro i _ _
    exact False.elim (hn (Nat.zero_lt_of_lt i.isLt))

/-- The explicit causal potential gives an existential reconstruction bound. -/
theorem pathPowerThree_banach_upper_four_thirds (n : ℕ) (g : Fin n → Fin n → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ i j, g j i = -g i j)
    (ht : ∀ i j k, (pathPowerThree n).Adj i j → (pathPowerThree n).Adj j k →
      (pathPowerThree n).Adj i k → ‖g i j + g j k - g i k‖ ≤ ε) :
    ∃ φ : Fin n → E, ∀ i j, (pathPowerThree n).Adj i j →
      ‖g i j - (φ j - φ i)‖ ≤ (4/3 : ℝ) * ε :=
  ⟨pathPowerThree_causal_potential n g, pathPowerThree_causal_potential_error n g ε hε hg ht⟩

end PathUpper


section PathLower

/-- The zero-sum plane with the supremum norm inherited from three real coordinates. -/
def pathHexagon : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {x | ∑ r, x r = 0}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change ∑ r, (x r + y r) = 0
    rw [Finset.sum_add_distrib, Set.mem_ofPred_eq.mp hx, Set.mem_ofPred_eq.mp hy, add_zero]
  smul_mem' c x hx := by
    change ∑ r, c * x r = 0
    rw [← Finset.mul_sum, Set.mem_ofPred_eq.mp hx, mul_zero]

noncomputable section

private def hexMark (i : ℕ) (r : Fin 3) : ℝ := if i % 3 = r.val then 1 else 0

private def hexLong (i : ℕ) : pathHexagon :=
  ⟨fun r => 2/3 - 2 * hexMark i r, by
    change ∑ r, (2/3 - 2 * hexMark i r) = 0
    have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
    rw [Fin.sum_univ_three]
    interval_cases h : i % 3 <;> norm_num [hexMark, h]⟩

private def hexShort (i : ℕ) : pathHexagon :=
  (1/2 : ℝ) • (hexLong (i+2) + hexLong i)

private theorem hex_long_coord (i : ℕ) (r : Fin 3) :
    (hexLong i).val r = 2/3 - 2 * hexMark i r := rfl

private theorem hex_short_coord (i : ℕ) (r : Fin 3) :
    (hexShort i).val r = 2/3 - hexMark (i+2) r - hexMark i r := by
  change (1/2 : ℝ) * ((hexLong (i+2)).val r + (hexLong i).val r) = _
  simp only [hex_long_coord]
  ring

private theorem hex_norm {z : pathHexagon} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ r, |z.val r| ≤ M) : ‖z‖ ≤ M := by
  change ‖z.val‖ ≤ M
  exact (pi_norm_le_iff_of_nonneg hM).mpr h

private theorem hex_coord (z : pathHexagon) (r : Fin 3) : |z.val r| ≤ ‖z‖ := by
  change ‖z.val r‖ ≤ ‖z.val‖
  exact norm_le_pi_norm z.val r

private theorem hex_short_norm (i : ℕ) : ‖hexShort i‖ ≤ 1 := by
  apply hex_norm zero_le_one
  intro r
  rw [hex_short_coord, abs_le]
  unfold hexMark
  split_ifs with h₁ h₂
  · omega
  all_goals norm_num

private theorem hex_short_sub_long (i : ℕ) : ‖hexShort i - hexLong i‖ ≤ 1 := by
  apply hex_norm zero_le_one
  intro r
  change |(hexShort i).val r - (hexLong i).val r| ≤ 1
  rw [hex_short_coord, hex_long_coord, abs_le]
  unfold hexMark
  split_ifs <;> norm_num

private theorem hex_next_sub_long (i : ℕ) : ‖hexShort (i+1) - hexLong i‖ ≤ 1 := by
  apply hex_norm zero_le_one
  intro r
  change |(hexShort (i+1)).val r - (hexLong i).val r| ≤ 1
  rw [hex_short_coord, hex_long_coord, abs_le]
  unfold hexMark
  rw [show (i+1+2)%3 = i%3 by omega]
  split_ifs <;> norm_num

private def hexForward (i j : ℕ) : pathHexagon :=
  if j = i+2 then hexShort i else if j = i+3 then hexLong i else 0

private def hexGain {n : ℕ} (i j : Fin n) : pathHexagon :=
  if i.val < j.val then hexForward i.val j.val
  else if j.val < i.val then -hexForward j.val i.val else 0

private theorem hex_skew {n : ℕ} (i j : Fin n) : hexGain j i = -hexGain i j := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · simp [hexGain, h, not_lt_of_ge h.le]
  · simp [hexGain, h]
  · simp [hexGain, h, not_lt_of_ge h.le]

private theorem hex_sorted {n : ℕ} {i j k : Fin n} (hij : i.val < j.val)
    (hjk : j.val < k.val) (hik : k.val ≤ i.val+3) :
    ‖hexGain i j + hexGain j k - hexGain i k‖ ≤ 1 := by
  have h (a b : Fin n) (hab : a.val < b.val) : hexGain a b = hexForward a.val b.val := by
    simp [hexGain, hab]
  rw [h i j hij, h j k hjk, h i k (hij.trans hjk)]
  rcases (show (j.val = i.val+1 ∧ k.val = i.val+2) ∨
    (j.val = i.val+2 ∧ k.val = i.val+3) ∨ (j.val = i.val+1 ∧ k.val = i.val+3) by omega)
    with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · simpa [hexForward, h₁, h₂, Nat.add_assoc] using hex_short_norm i.val
  · simpa [hexForward, h₁, h₂, Nat.add_assoc] using hex_short_sub_long i.val
  · simpa [hexForward, h₁, h₂, Nat.add_assoc] using hex_next_sub_long i.val

private theorem hex_flat {n : ℕ} (i j k : Fin n) (hij : (pathPowerThree n).Adj i j)
    (hjk : (pathPowerThree n).Adj j k) (hik : (pathPowerThree n).Adj i k) :
    ‖hexGain i j + hexGain j k - hexGain i k‖ ≤ 1 := by
  let D (a b c : Fin n) := ‖(hexGain a b + hexGain b c - hexGain a c : pathHexagon)‖
  have swap (a b c : Fin n) : D a b c = D b a c := by
    change ‖(hexGain a b + hexGain b c - hexGain a c : pathHexagon)‖ =
      ‖(hexGain b a + hexGain a c - hexGain b c : pathHexagon)‖
    rw [show hexGain b a + hexGain a c - hexGain b c =
        -(hexGain a b + hexGain b c - hexGain a c) by rw [hex_skew a b]; abel, norm_neg]
  have cycle (a b c : Fin n) : D a b c = D b c a := by
    change ‖(hexGain a b + hexGain b c - hexGain a c : pathHexagon)‖ =
      ‖(hexGain b c + hexGain c a - hexGain b a : pathHexagon)‖
    rw [show hexGain b c + hexGain c a - hexGain b a =
        hexGain a b + hexGain b c - hexGain a c by rw [hex_skew a c, hex_skew a b]; abel]
  change D i j k ≤ 1
  rcases lt_or_gt_of_ne (fun e => hij.ne (Fin.ext e)) with h₁ | h₁
  · rcases lt_or_gt_of_ne (fun e => hjk.ne (Fin.ext e)) with h₂ | h₂
    · exact hex_sorted h₁ h₂ hik.2.2
    · rcases lt_or_gt_of_ne (fun e => hik.ne (Fin.ext e)) with h₃ | h₃
      · rw [← cycle k i j, swap k i j]
        exact hex_sorted h₃ h₂ hij.2.2
      · rw [← cycle k i j]
        exact hex_sorted h₃ h₁ hjk.2.1
  · rcases lt_or_gt_of_ne (fun e => hik.ne (Fin.ext e)) with h₂ | h₂
    · rw [swap i j k]
      exact hex_sorted h₁ h₂ hjk.2.2
    · rcases lt_or_gt_of_ne (fun e => hjk.ne (Fin.ext e)) with h₃ | h₃
      · rw [cycle i j k]
        exact hex_sorted h₃ h₂ hij.2.1
      · rw [swap i j k, ← cycle k j i]
        exact hex_sorted h₃ h₁ hik.2.1

private def laneVertex (m l : ℕ) (hl : l ≤ m) (r : Fin 3) : Fin (3*m+3) :=
  ⟨3*l+r.val, by have := r.isLt; omega⟩

private theorem hex_lower_bound (m : ℕ) {φ : Fin (3*m+3) → pathHexagon} {M : ℝ}
    (hM : ∀ i j, (pathPowerThree (3*m+3)).Adj i j →
      ‖hexGain i j - (φ j - φ i)‖ ≤ M) : (4*m : ℝ) ≤ (3*m+4) * M := by
  let value (r : Fin 3) (l : ℕ) : ℝ :=
    if h : l ≤ m then (φ (laneVertex m l h r)).val r else 0
  have lane (r : Fin 3) (l : ℕ) (hl : l < m) :
      value r (l+1) - value r l ≤ -4/3 + M := by
    let i := laneVertex m l hl.le r
    let j := laneVertex m (l+1) (by omega) r
    have hij : j.val = i.val+3 := by dsimp [i, j, laneVertex]; omega
    have adj : (pathPowerThree (3*m+3)).Adj i j :=
      ⟨fun h => by have := congrArg Fin.val h; omega, by omega, by omega⟩
    have gain : hexGain i j = hexLong i.val := by
      simp [hexGain, hexForward, hij]
    have hh := (hex_coord (hexGain i j - (φ j - φ i)) r).trans (hM i j adj)
    rw [gain] at hh
    change |(hexLong i.val).val r - ((φ j).val r - (φ i).val r)| ≤ M at hh
    have hmod : i.val % 3 = r.val := by dsimp [i, laneVertex]; have := r.isLt; omega
    rw [hex_long_coord, hexMark, ite_eq_left hmod, abs_le] at hh
    dsimp only [value]
    rw [dite_eq_left (by omega : l+1 ≤ m), dite_eq_left hl.le]
    change (φ j).val r - (φ i).val r ≤ _
    linarith only [hh.1]
  have lanes (r : Fin 3) : value r m - value r 0 ≤ (m : ℝ) * (-4/3 + M) := by
    have h (l : ℕ) (hl : l ≤ m) : value r l - value r 0 ≤ (l : ℝ) * (-4/3 + M) := by
      induction l with
      | zero => simp
      | succ l ih =>
        rw [Nat.cast_succ]
        linarith only [lane r l (by omega), ih (by omega)]
    exact h m le_rfl
  let e (l : ℕ) (hl : l ≤ m) (r : Fin 3) := φ (laneVertex m l hl r)
  have boundary (l : ℕ) (hl : l ≤ m) (r s t : Fin 3) (hst : s.val = t.val + 1) :
      |(e l hl s).val r - (e l hl t).val r| ≤ M := by
    let i := laneVertex m l hl t
    let j := laneVertex m l hl s
    have h : j.val = i.val+1 := by dsimp [i, j, laneVertex]; omega
    have adj : (pathPowerThree (3*m+3)).Adj i j :=
      ⟨fun e => by have := congrArg Fin.val e; omega, by omega, by omega⟩
    have gain : hexGain i j = 0 := by
      have hlt : i.val < j.val := by omega
      have h₂ : j.val ≠ i.val+2 := by omega
      have h₃ : j.val ≠ i.val+3 := by omega
      simp [hexGain, hexForward, hlt, h₂, h₃]
    have hh := (hex_coord (hexGain i j - (φ j - φ i)) r).trans (hM i j adj)
    rw [gain] at hh
    change |(0:ℝ) - ((φ j).val r - (φ i).val r)| ≤ M at hh
    simpa only [zero_sub, abs_neg] using hh
  have zeros (l : ℕ) (hl : l ≤ m) :
      (e l hl 1).val 0 + (e l hl 1).val 1 + (e l hl 1).val 2 = 0 := by
    have h : ∑ r, (e l hl 1).val r = 0 := (e l hl 1).property
    simpa only [Fin.sum_univ_three] using h
  have head (r : Fin 3) : value r 0 = (e 0 (Nat.zero_le _) r).val r := by simp [value, e]
  have tail (r : Fin 3) : value r m = (e m le_rfl r).val r := by simp [value, e]
  have h₀ := abs_le.mp (boundary 0 (Nat.zero_le _) 0 1 0 (by decide))
  have h₂ := abs_le.mp (boundary 0 (Nat.zero_le _) 2 2 1 (by decide))
  have h₀' := abs_le.mp (boundary m le_rfl 0 1 0 (by decide))
  have h₂' := abs_le.mp (boundary m le_rfl 2 2 1 (by decide))
  have l₀ := lanes 0
  have l₁ := lanes 1
  have l₂ := lanes 2
  simp only [head, tail] at l₀ l₁ l₂
  nlinarith only [l₀, l₁, l₂, h₀.1, h₂.2, h₀'.2, h₂'.1,
    zeros 0 (Nat.zero_le _), zeros m le_rfl]

/-- Periodic gains in the hexagonal plane force the rational lower bound on a path power. -/
theorem pathPowerThree_banach_lower_four_thirds (m : ℕ) (hm : 1 ≤ m) :
    ∃ g : Fin (3*m+3) → Fin (3*m+3) → pathHexagon,
      (∀ i j, g j i = -g i j) ∧
      (∀ i j k, (pathPowerThree (3*m+3)).Adj i j → (pathPowerThree (3*m+3)).Adj j k →
        (pathPowerThree (3*m+3)).Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) ∧
      (∀ φ : Fin (3*m+3) → pathHexagon, ∃ i j, (pathPowerThree (3*m+3)).Adj i j ∧
        (4*m : ℝ)/(3*m+4) ≤ ‖g i j - (φ j - φ i)‖) := by
  classical
  refine ⟨hexGain, hex_skew, hex_flat, fun φ => ?_⟩
  let e := Finset.univ.filter fun ij : Fin (3*m+3) × Fin (3*m+3) =>
    (pathPowerThree (3*m+3)).Adj ij.1 ij.2
  let R (ij : Fin (3*m+3) × Fin (3*m+3)) := ‖hexGain ij.1 ij.2 - (φ ij.2 - φ ij.1)‖
  have he : e.Nonempty := by
    refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨fun h => by have := congrArg Fin.val h; contradiction,
      show 0 ≤ 1 + 3 by decide, show 1 ≤ 0 + 3 by decide⟩
  obtain ⟨ij, hij, hmax⟩ := Finset.exists_max_image e R he
  refine ⟨ij.1, ij.2, (Finset.mem_filter.mp hij).2, ?_⟩
  have h := hex_lower_bound m (φ := φ) (M := R ij) fun i j h =>
    hmax (i,j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  change (4*m : ℝ)/(3*m+4) ≤ R ij
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 3*m+4)).mpr (by simpa [mul_comm] using h)

end
end PathLower

section ChordalUpper

open Omega.ThreeTreePolygon

variable {E V : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

private def defect (g : V → V → E) (a b c : V) : E := g a b + g b c - g a c

private def residual (g : V → V → E) (p : V → E) (a b : V) : E := g a b - (p b - p a)

private def faceState (ε : ℝ) (A C t : E) : Prop :=
  ∀ δ : ℝ, ε ≤ δ → 0 < δ → ∀ f : StrongDual ℝ E, ‖f‖ ≤ 1 →
    InPolytope (f A / δ) (f C / δ) (f t / δ)

private theorem dual_le (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) (x : E) : |f x| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  calc
    ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖x‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (norm_nonneg x)

private theorem scaled_dual_le {x : E} {ε δ : ℝ} (hx : ‖x‖ ≤ ε) (hδ : ε ≤ δ)
    (hδp : 0 < δ) (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) : |f x / δ| ≤ 1 := by
  rw [abs_div, abs_of_pos hδp, div_le_one hδp]
  exact ((dual_le f hf x).trans hx).trans hδ

private theorem norm_of_scaled {x : E} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ δ : ℝ, ε ≤ δ → 0 < δ → ∀ f : StrongDual ℝ E, ‖f‖ ≤ 1 →
      |f x / δ| ≤ 72537/50000) : ‖x‖ ≤ (72537/50000 : ℝ)*ε := by
  obtain ⟨f, hf, he⟩ := exists_dual_vector'' ℝ x
  by_contra! hh
  let δ := (ε + ‖x‖ / (72537/50000 : ℝ)) / 2
  have hlo : ε < δ := by dsimp [δ]; linarith
  have hhi : (72537/50000 : ℝ)*δ < ‖x‖ := by dsimp [δ]; linarith
  have hd := hε.trans_lt hlo
  have hb := h δ hlo.le hd f hf
  rw [he] at hb
  change |‖x‖ / δ| ≤ 72537/50000 at hb
  rw [abs_of_nonneg (div_nonneg (norm_nonneg x) hd.le)] at hb
  exact hhi.not_ge ((div_le_iff₀ hd).mp hb)

private theorem step_face {ε : ℝ} {A C t u v : E} (h : faceState ε A C t)
    (ht : ‖t‖ ≤ ε) (hu : ‖u‖ ≤ ε) (hv : ‖v‖ ≤ ε) (hw : ‖u+v-t‖ ≤ ε) :
    let B := middle A C t u v
    faceState ε A B u ∧ faceState ε (A+C-t) (B-C+v) (u+v-t) ∧ faceState ε C (B-C+v) v := by
  let B := middle A C t u v
  let F (δ : ℝ) (f : StrongDual ℝ E) (z : E) := f z / δ
  have add (δ : ℝ) (f : StrongDual ℝ E) (x y : E) :
      F δ f (x+y) = F δ f x + F δ f y := by simp [F, add_div]
  have sub (δ : ℝ) (f : StrongDual ℝ E) (x y : E) :
      F δ f (x-y) = F δ f x - F δ f y := by simp [F, sub_div]
  have mid (δ : ℝ) (f : StrongDual ℝ E) :
      F δ f B = middle (F δ f A) (F δ f C) (F δ f t) (F δ f u) (F δ f v) := by
    simp only [B, middle, F, map_add, map_sub, map_smul, smul_eq_mul]
    ring
  have H (δ : ℝ) (hδ : ε ≤ δ) (hδp : 0 < δ) (f : StrongDual ℝ E) (hf : ‖f‖ ≤ 1) :
      InPolytope (F δ f A) (F δ f B) (F δ f u) ∧
      InPolytope (F δ f (A+C-t)) (F δ f (B-C+v)) (F δ f (u+v-t)) ∧
      InPolytope (F δ f C) (F δ f (B-C+v)) (F δ f v) := by
    rw [mid]
    simp only [add, sub, mid]
    exact step (h δ hδ hδp f hf) (scaled_dual_le ht hδ hδp f hf)
      (scaled_dual_le hu hδ hδp f hf) (scaled_dual_le hv hδ hδp f hf)
      (by simpa only [F, map_add, map_sub, add_div, sub_div] using scaled_dual_le hw hδ hδp f hf)
  exact ⟨fun δ hδ hδp f hf => (H δ hδ hδp f hf).1,
    fun δ hδ hδp f hf => (H δ hδ hδp f hf).2.1,
    fun δ hδ hδp f hf => (H δ hδ hδp f hf).2.2⟩

private theorem face_second {ε : ℝ} {A C t : E} (hε : 0 ≤ ε) (h : faceState ε A C t) :
    ‖C‖ ≤ (72537/50000 : ℝ)*ε := norm_of_scaled hε fun δ hd hp f hf => (bounds (h δ hd hp f hf)).2.1

private theorem padded_face {ε : ℝ} {A : E} (hA : ‖A‖ ≤ (72537/50000 : ℝ)*ε) :
    faceState ε A ((-(25000/72537) : ℝ) • A) 0 := by
  intro δ hd hp f hf
  have h : |f A / δ| ≤ 72537/50000 := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact ((dual_le f hf A).trans hA).trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  convert padded h using 2
  · rw [map_smul, smul_eq_mul]
    ring
  · simp

private theorem two_parent {g : V → V → E} {p : V → E} {a b z : V} {ε : ℝ}
    (hε : 0 ≤ ε) (hA : ‖residual g p a b‖ ≤ (72537/50000 : ℝ)*ε)
    (hu : ‖defect g a b z‖ ≤ ε) :
    ∃ q : E, ‖g a z - (q - p a)‖ ≤ (72537/50000 : ℝ)*ε ∧
      ‖g b z - (q - p b)‖ ≤ (72537/50000 : ℝ)*ε ∧
      faceState ε (residual g p a b) (g b z - (q - p b)) (defect g a b z) := by
  let A := residual g p a b
  let C := (-(25000/72537) : ℝ) • A
  let u := defect g a b z
  -- A virtual copy of b gives parent defect zero. The midpoint bridge makes
  -- the other two child defects -u/2 and u/2.
  let bridge := (1/2 : ℝ) • ((-g a b + g a z) + g b z)
  let v := bridge - g b z
  have ev : v = (-(1/2) : ℝ) • u := by dsimp [v, bridge, u, defect]; module
  let B := middle A C 0 u v
  let q := p b + g b z - B
  have hv : ‖v‖ ≤ ε := by
    rw [ev, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith [show ‖u‖ ≤ ε from hu]
  have hw : ‖u+v-0‖ ≤ ε := by
    rw [show u+v-0 = (1/2 : ℝ) • u by rw [ev]; module, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith [show ‖u‖ ≤ ε from hu]
  have H := step_face (padded_face hA) (by simpa using hε) hu hv hw
  change faceState ε A B u ∧ faceState ε (A+C-0) (B-C+v) (u+v-0) ∧ _ at H
  have e₁ : g b z - (q - p b) = B := by dsimp [q]; abel
  have e₂ : g a z - (q - p a) = A+B-u := by dsimp [q, A, u, residual, defect]; abel
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [e₂]
    apply norm_of_scaled hε
    intro δ hd hp f hf
    simpa only [map_add, map_sub, add_div, sub_div] using (bounds (H.1 δ hd hp f hf)).2.2
  · rw [e₁]
    exact face_second hε H.1
  · rw [e₁]
    exact H.1

private theorem three_parent {g : V → V → E} {p : V → E} {a b c z : V} {ε : ℝ}
    (hε : 0 ≤ ε) (h : faceState ε (residual g p a b) (residual g p b c) (defect g a b c))
    (ht : ‖defect g a b c‖ ≤ ε) (hu : ‖defect g a b z‖ ≤ ε)
    (hv : ‖defect g b c z‖ ≤ ε) (hw : ‖defect g a c z‖ ≤ ε) :
    ∃ q : E, let R (x : V) := g x z - (q - p x)
      (‖R a‖ ≤ (72537/50000 : ℝ)*ε ∧ ‖R b‖ ≤ (72537/50000 : ℝ)*ε ∧
        ‖R c‖ ≤ (72537/50000 : ℝ)*ε) ∧
      faceState ε (residual g p a b) (R b) (defect g a b z) ∧
      faceState ε (residual g p a c) (R c) (defect g a c z) ∧
      faceState ε (residual g p b c) (R c) (defect g b c z) := by
  let A := residual g p a b
  let C := residual g p b c
  let t := defect g a b c
  let u := defect g a b z
  let v := defect g b c z
  let B := middle A C t u v
  let q := p b + g b z - B
  let R (x : V) := g x z - (q - p x)
  have ew : u+v-t = defect g a c z := by dsimp [u, v, t, defect]; abel
  have er : A+C-t = residual g p a c := by dsimp [A,C,t,residual,defect]; abel
  have e₁ : R b = B := by dsimp [R,q]; abel
  have e₂ : R c = B-C+v := by dsimp [R,q,C,v,residual,defect]; abel
  have e₃ : R a = A+B-u := by dsimp [R,q,A,u,residual,defect]; abel
  have H := step_face h ht hu hv (by rw [ew]; exact hw)
  change faceState ε A B u ∧ faceState ε (A+C-t) (B-C+v) (u+v-t) ∧
    faceState ε C (B-C+v) v at H
  rw [ew, er, ← e₂, ← e₁] at H
  refine ⟨q, ⟨?_, face_second hε H.1, face_second hε H.2.2⟩, H⟩
  change ‖R a‖ ≤ _
  rw [e₃]
  apply norm_of_scaled hε
  intro δ hd hp f hf
  have hh := (bounds (H.1 δ hd hp f hf)).2.2
  rw [e₁] at hh
  simpa only [map_add, map_sub, add_div, sub_div] using hh

private theorem attach [LinearOrder V] {ε : ℝ} (hε : 0 ≤ ε) {P : Finset V}
    (hcard : P.card ≤ 3) (g : V → V → E) (p : V → E) (z : V)
    (hEdge : ∀ a ∈ P, ∀ b ∈ P, a < b → ‖residual g p a b‖ ≤ (72537/50000 : ℝ)*ε)
    (hFace : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a < b → b < c →
      faceState ε (residual g p a b) (residual g p b c) (defect g a b c) ∧ ‖defect g a b c‖ ≤ ε)
    (hDefect : ∀ a ∈ P, ∀ b ∈ P, a < b → ‖defect g a b z‖ ≤ ε) :
    ∃ q : E, let R (a : V) := g a z - (q - p a)
      (∀ a ∈ P, ‖R a‖ ≤ (72537/50000 : ℝ)*ε) ∧
      ∀ a ∈ P, ∀ b ∈ P, a < b → faceState ε (residual g p a b) (R b) (defect g a b z) := by
  have indexed {n : ℕ} (h : P.card = n) {x : V} (hx : x ∈ P) :
      ∃ i, P.orderEmbOfFin h i = x := Set.mem_range.mp (by simpa using hx)
  rcases (show P.card = 0 ∨ P.card = 1 ∨ P.card = 2 ∨ P.card = 3 by omega) with h | h | h | h
  · have he := Finset.card_eq_zero.mp h
    simp [he]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    refine ⟨p a + g a z, ?_, ?_⟩
    · intro b hb
      have hb' := Finset.mem_singleton.mp hb
      subst b
      change ‖g a z - (p a + g a z - p a)‖ ≤ _
      rw [show g a z - (p a + g a z - p a) = 0 by abel, norm_zero]
      exact mul_nonneg (by norm_num) hε
    · intro b hb c hc hbc
      exact False.elim (hbc.ne ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm))
  · let f := P.orderEmbOfFin h
    have mem (i : Fin 2) : f i ∈ P := P.orderEmbOfFin_mem h i
    have hlt : f 0 < f 1 := f.strictMono (by decide)
    obtain ⟨q, h₀, h₁, H⟩ := two_parent hε (hEdge _ (mem 0) _ (mem 1) hlt)
      (hDefect _ (mem 0) _ (mem 1) hlt)
    refine ⟨q, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, rfl⟩ := indexed h ha
      fin_cases i
      · exact h₀
      · exact h₁
    · intro a ha b hb hab
      obtain ⟨i, rfl⟩ := indexed h ha
      obtain ⟨j, rfl⟩ := indexed h hb
      have hij : i < j := f.lt_iff_lt.mp hab
      fin_cases i <;> fin_cases j
      all_goals first | exact H | exact False.elim ((by decide : ¬ _ < _) hij)
  · let f := P.orderEmbOfFin h
    have mem (i : Fin 3) : f i ∈ P := P.orderEmbOfFin_mem h i
    have h01 : f 0 < f 1 := f.strictMono (by decide)
    have h12 : f 1 < f 2 := f.strictMono (by decide)
    have hf := hFace _ (mem 0) _ (mem 1) _ (mem 2) h01 h12
    obtain ⟨q, ⟨h₀,h₁,h₂⟩, H₀,H₁,H₂⟩ := three_parent hε hf.1 hf.2
      (hDefect _ (mem 0) _ (mem 1) h01) (hDefect _ (mem 1) _ (mem 2) h12)
      (hDefect _ (mem 0) _ (mem 2) (h01.trans h12))
    refine ⟨q, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, rfl⟩ := indexed h ha
      fin_cases i
      · exact h₀
      · exact h₁
      · exact h₂
    · intro a ha b hb hab
      obtain ⟨i, rfl⟩ := indexed h ha
      obtain ⟨j, rfl⟩ := indexed h hb
      have hij : i < j := f.lt_iff_lt.mp hab
      fin_cases i <;> fin_cases j
      all_goals first | exact H₀ | exact H₁ | exact H₂ | exact False.elim ((by decide : ¬ _ < _) hij)

/-- For clique number at most four, an ordered elimination gives a gain potential
with error at most the radius of the invariant polygon times the defect tolerance. -/
theorem IsChordal.exists_cliqueFour_banach_gain_potential_polygon [Fintype V] {G : SimpleGraph V}
    (hG : G.IsChordal) (hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ 4)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hg : ∀ i j, g j i = -g i j)
    (ht : ∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k → ‖g i j + g j k - g i k‖ ≤ ε) :
    ∃ φ : V → E, ∀ i j, G.Adj i j → ‖g i j - (φ j - φ i)‖ ≤ (72537/50000 : ℝ) * ε := by
  classical
  obtain ⟨ord, ho⟩ := hG.exists_isPEO
  let rank := peoRank ord
  have hinj : Function.Injective rank := peoRank_injective ho.injective
  let : LinearOrder V := LinearOrder.lift' rank hinj
  have less {a b : V} : a < b ↔ rank a < rank b := Iff.rfl
  have ord_lt {a b : V} (h : rank a < rank b) : ord b < ord a := by
    rcases lt_trichotomy (ord a) (ord b) with hl | he | hg
    · exact False.elim (h.not_gt (peoRank_lt_of_ord_lt hl))
    · exact False.elim (h.ne (congrArg rank (ho.injective he)))
    · exact hg
  let earlier (z : V) := laterNbrs G ord z
  have earlier_mem {a z : V} : a ∈ earlier z ↔ rank a < rank z ∧ G.Adj a z := by
    change _ ∈ laterNbrs G ord _ ↔ _
    rw [mem_laterNbrs]
    exact ⟨fun h => ⟨peoRank_lt_of_ord_lt h.1, h.2.symm⟩, fun h => ⟨ord_lt h.1, h.2.symm⟩⟩
  have earlier_card (z : V) : (earlier z).card ≤ 3 := by
    have h := hclique _ (ho.peoBag_isClique (G := G) z)
    rw [Set.ncard_coe_finset] at h
    change (insert z (earlier z)).card ≤ 4 at h
    rw [Finset.card_insert_of_notMem (fun hz => (Nat.lt_irrefl _) (earlier_mem.mp hz).1)] at h
    omega
  have earlier_adj {a b z : V} (ha : a ∈ earlier z) (hb : b ∈ earlier z) (h : a < b) : G.Adj a b :=
    ho.isClique_later z ⟨ord_lt (earlier_mem.mp ha).1, (earlier_mem.mp ha).2.symm⟩
      ⟨ord_lt (earlier_mem.mp hb).1, (earlier_mem.mp hb).2.symm⟩ h.ne
  have stages (n : ℕ) : ∃ p : V → E,
      (∀ a b, a < b → rank b < n → G.Adj a b → ‖residual g p a b‖ ≤ (72537/50000 : ℝ)*ε) ∧
      (∀ a b c, a < b → b < c → rank c < n → G.Adj a b → G.Adj b c → G.Adj a c →
        faceState ε (residual g p a b) (residual g p b c) (defect g a b c)) := by
    induction n with
    | zero => exact ⟨fun _ => 0, fun _ _ _ h _ => (Nat.not_lt_zero _ h).elim,
        fun _ _ _ _ _ h _ _ _ => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨p, hE, hF⟩ := ih
      by_cases hex : ∃ z, rank z = n
      · obtain ⟨z, hz⟩ := hex
        have ed (a : V) (ha : a ∈ earlier z) : rank a < n ∧ G.Adj a z := by
          simpa only [hz] using earlier_mem.mp ha
        obtain ⟨q, hedge, hface⟩ := attach hε (earlier_card z) g p z
          (fun a ha b hb hab => hE a b hab (ed b hb).1 (earlier_adj ha hb hab))
          (fun a ha b hb c hc hab hbc =>
            let ab := earlier_adj ha hb hab
            let bc := earlier_adj hb hc hbc
            let ac := earlier_adj ha hc (hab.trans hbc)
            ⟨hF a b c hab hbc (ed c hc).1 ab bc ac, ht a b c ab bc ac⟩)
          (fun a ha b hb hab => ht a b z (earlier_adj ha hb hab) (ed b hb).2 (ed a ha).2)
        let p' (a : V) := if a = z then q else p a
        have stay (a : V) (ha : rank a < n) : p' a = p a := by
          have ne : a ≠ z := fun e => by subst a; omega
          simp [p', ne]
        have new : p' z = q := by simp [p']
        refine ⟨p', ?_, ?_⟩
        · intro a b hab hb adj
          have hab' := less.mp hab
          by_cases h : rank b < n
          · simpa only [residual, stay a (hab'.trans h), stay b h] using hE a b hab h adj
          · have eq : b = z := hinj (by omega)
            subst b
            have ha := earlier_mem.mpr ⟨hab',adj⟩
            simpa only [residual, new, stay a (ed a ha).1] using hedge a ha
        · intro a b c hab hbc hc ab bc ac
          have hab' := less.mp hab
          have hbc' := less.mp hbc
          by_cases h : rank c < n
          · simpa only [residual, stay a (hab'.trans (hbc'.trans h)), stay b (hbc'.trans h), stay c h]
              using hF a b c hab hbc h ab bc ac
          · have eq : c = z := hinj (by omega)
            subst c
            have ha := earlier_mem.mpr ⟨hab'.trans hbc', ac⟩
            have hb := earlier_mem.mpr ⟨hbc',bc⟩
            simpa only [residual, stay a (ed a ha).1, stay b (ed b hb).1, new] using hface a ha b hb hab
      · refine ⟨p, fun a b hab hb adj => hE a b hab ?_ adj,
          fun a b c hab hbc hc ab bc ac => hF a b c hab hbc ?_ ab bc ac⟩
        · have hne : rank b ≠ n := fun h => hex ⟨b, h⟩
          omega
        · have hne : rank c ≠ n := fun h => hex ⟨c, h⟩
          omega
  obtain ⟨p, hp, _⟩ := stages ((Finset.univ : Finset V).sup rank + 1)
  have hr (v : V) : rank v < (Finset.univ : Finset V).sup rank + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ _))
  refine ⟨p, fun a b hab => ?_⟩
  rcases lt_or_gt_of_ne hab.ne with h | h
  · exact hp a b h (hr b) hab
  · rw [show g a b - (p b - p a) = -(residual g p b a) by unfold residual; rw [hg b a]; abel, norm_neg]
    exact hp b a h (hr a) hab.symm

end ChordalUpper

section ExtremalConstants

/-- The supremum of the width-three path coefficients is attained as an asymptotic bound. -/
theorem pathPowerThree_banach_sup_four_thirds :
    (⨆ n : ℕ, BanachPathPower.banachCoefficient n 3) = (4/3 : ℝ) := by
  have hUpper (n : ℕ) : BanachPathPower.banachCoefficient n 3 ≤ 4/3 := by
    unfold BanachPathPower.banachCoefficient
    apply csInf_le ⟨0, fun c hc => hc.1⟩
    refine ⟨by norm_num, ?_⟩
    intro E _ _ _ g hg ht
    simpa only [mul_one] using pathPowerThree_banach_upper_four_thirds n g 1 zero_le_one hg ht
  have hb : BddAbove (Set.range fun n : ℕ => BanachPathPower.banachCoefficient n 3) :=
    ⟨4/3, by rintro _ ⟨n, rfl⟩; exact hUpper n⟩
  have hlim : Filter.Tendsto (fun n => BanachPathPower.banachCoefficient n 3) Filter.atTop
      (nhds (4/3 : ℝ)) := by
    simpa only [Nat.cast_ofNat, show (2 - 2 / (3 : ℝ)) = 4/3 by norm_num] using
      BanachPathPower.pathPower_banach_limit_tendsto 3 (by decide)
  exact (ciSup_le hUpper).antisymm (le_of_tendsto' hlim fun n => le_ciSup hb n)

private theorem path_clique {n : ℕ} {C : Set (Fin n)} (hC : (pathPowerThree n).IsClique C) :
    C.ncard ≤ 4 := by
  classical
  let c := C.toFinset
  have hcard : C.ncard = c.card := C.ncard_eq_toFinset_card'
  rw [hcard]
  by_cases hc : c.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image c Fin.val hc
    have span (x : Fin n) (hx : x ∈ c) : x.val ≤ a.val+3 := by
      by_cases h : a = x
      · subst x; omega
      · exact (hC (by simpa [c] using ha) (by simpa [c] using hx) h).2.2
    have hle := Finset.card_le_card_of_injOn (s := c) (t := Finset.range 4)
      (fun x : Fin n => x.val - a.val)
      (fun x hx => Finset.mem_range.mpr (by change x.val - a.val < 4; have := span x hx; omega))
      (fun x hx y hy he => by
        apply Fin.ext
        have := hmin x hx
        have := hmin y hy
        dsimp only at he
        omega)
    simpa using hle
  · simp [Finset.not_nonempty_iff_eq_empty.mp hc]

private def cliqueFourBounds : Set ℝ := {C | 0 ≤ C ∧
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsChordal →
    (∀ X : Set V, G.IsClique X → X.ncard ≤ 4) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (g : V → V → E),
      (∀ i j, g j i = -g i j) →
      (∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k → ‖g i j + g j k - g i k‖ ≤ 1) →
      ∃ φ : V → E, ∀ i j, G.Adj i j → ‖g i j - (φ j - φ i)‖ ≤ C}

/-- The infimum of nonnegative uniform Banach reconstruction bounds at unit defect
on chordal graphs with cliques of size at most four. -/
noncomputable def cliqueFourBanachCoefficient : ℝ := sInf cliqueFourBounds

/-- The width-three paths give the lower endpoint of the clique-four interval,
and the invariant polygon gives the upper endpoint. -/
theorem cliqueFour_banach_coefficient_bounds :
    (4/3 : ℝ) ≤ cliqueFourBanachCoefficient ∧
      cliqueFourBanachCoefficient ≤ (72537/50000 : ℝ) ∧ (72537/50000 : ℝ) < 3/2 := by
  have hupper : (72537/50000 : ℝ) ∈ cliqueFourBounds := by
    refine ⟨by norm_num, ?_⟩
    intro V _ G hG hK E _ _ _ g hg ht
    simpa only [mul_one] using hG.exists_cliqueFour_banach_gain_potential_polygon hK g 1 zero_le_one hg ht
  refine ⟨le_csInf ⟨_, hupper⟩ ?_, csInf_le ⟨0, fun c hc => hc.1⟩ hupper, by norm_num⟩
  intro c hc
  rw [← pathPowerThree_banach_sup_four_thirds]
  apply ciSup_le
  intro n
  unfold BanachPathPower.banachCoefficient
  apply csInf_le ⟨0, fun r hr => hr.1⟩
  obtain ⟨l, r, _, h, hi⟩ := BanachPathPower.pathPower_isIntervalGraph n 3
  have hChordal := (intervalGraph_isChordal_and_two_approximate_gain_potential
    (H := Multiplicative ℝ) l r h hi (fun _ _ => 1) 0 le_rfl (by simp) (by simp)).1
  exact ⟨hc.1, hc.2 (Fin n) (pathPowerThree n) hChordal (fun _ => path_clique)⟩

end ExtremalConstants

#print axioms IsChordal.exists_cliqueFour_banach_gain_potential_polygon
#print axioms pathPowerThree_causal_potential_error
#print axioms pathPowerThree_banach_upper_four_thirds
#print axioms pathPowerThree_banach_lower_four_thirds
#print axioms pathPowerThree_banach_sup_four_thirds
#print axioms cliqueFour_banach_coefficient_bounds

end SimpleGraph

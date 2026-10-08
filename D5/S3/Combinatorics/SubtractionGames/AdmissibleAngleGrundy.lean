/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleGrundy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleGrundy
   mirror-E: none(waiver:subtraction-game-induction)
   anchors: []
   utility: none
   digest: Two-move losing patterns and agreement below an added move, proved by induction. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex)

set_option maxHeartbeats 1000000 in
/-- Adding a move does not affect any heap smaller than that move. -/
theorem below_third (a b c n : ℕ) (hn : n < c) :
    grundy {a, b, c} n = grundy {a, b} n := by
  classical
  have recur (S : Finset ℕ) (k : ℕ) :
      grundy S k = mex ((S.filter fun s => 0 < s ∧ s ≤ k).image
        fun s => grundy S (k - s)) := by
    rw [grundy, Nat.strongRecOn_eq]
    congr 1
    ext v
    simp [grundy]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [recur, recur]
    congr 1
    have filters : ({a, b, c} : Finset ℕ).filter (fun s => 0 < s ∧ s ≤ n) =
        ({a, b} : Finset ℕ).filter (fun s => 0 < s ∧ s ≤ n) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [filters]
    apply Finset.image_congr
    intro s hs
    have hs' := (Finset.mem_filter.mp hs).2
    exact ih (n - s) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- The base losing residues are precisely the even single-move blocks below `b`. -/
theorem base_positions (a b : ℕ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    grundy {a, b} n = 0 ↔ n % (a + b) < b ∧ (n % (a + b) / a) % 2 = 0 := by
  classical
  have recur (S : Finset ℕ) (k : ℕ) :
      grundy S k = mex ((S.filter fun s => 0 < s ∧ s ≤ k).image
        fun s => grundy S (k - s)) := by
    rw [grundy, Nat.strongRecOn_eq]
    congr 1
    ext v
    simp [grundy]
  have mex_zero (T : Finset ℕ) : mex T = 0 ↔ 0 ∉ T := by
    have spec : mex T ∉ T ∧ ∀ j < mex T, j ∈ T := by
      run_tac
        let env ← Lean.getEnv
        let some (name, _) := env.constants.toList.find?
          (fun (name, _) => name.toString.endsWith ".CrimGrundyRefutation.mex_spec")
          | throwError "Existing mex characterization not found"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) _))
    constructor
    · intro h
      simpa [h] using spec.1
    · intro h
      by_contra h'
      exact h (spec.2 0 (by omega))
  have rule (k : ℕ) : grundy {a, b} k = 0 ↔
      (a ≤ k → grundy {a, b} (k - a) ≠ 0) ∧
      (b ≤ k → grundy {a, b} (k - b) ≠ 0) := by
    rw [recur, mex_zero]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, not_exists, not_and]
    constructor
    · intro h
      exact ⟨fun hka hz => h a ⟨Or.inl rfl, ha, hka⟩ hz,
        fun hkb hz => h b ⟨Or.inr rfl, by omega, hkb⟩ hz⟩
    · rintro ⟨h₁, h₂⟩ s ⟨rfl | rfl, _, hs⟩ hz
      · exact h₁ hs hz
      · exact h₂ hs hz
  let m := a + b
  let P := fun r : ℕ => r < b ∧ (r / a) % 2 = 0
  have flip (r : ℕ) (hr : a ≤ r) :
      r / a = (r - a) / a + 1 := by
    rw [← Nat.add_div_right (r - a) ha, Nat.sub_add_cancel hr]
  have circle (r : ℕ) (hr : r < m) :
      P r ↔ ¬ P ((r + b) % m) ∧ ¬ P ((r + a) % m) := by
    dsimp [P, m] at *
    by_cases rb : r < b
    · have next : (r + a) % (a + b) = r + a := Nat.mod_eq_of_lt (by omega)
      rw [next]
      by_cases ra : r < a
      · have prev : (r + b) % (a + b) = r + b := Nat.mod_eq_of_lt (by omega)
        have rq : r / a = 0 := Nat.div_eq_of_lt ra
        have nq : (r + a) / a = 1 := by rw [Nat.add_div_right _ ha, rq]
        simp [prev, rq, nq, rb, show ¬ r + b < b by omega]
      · have prev : (r + b) % (a + b) = r - a := by
          have e : r + b = (r - a) + (a + b) := by omega
          rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have fq := flip r (by omega)
        have nq := Nat.add_div_right r ha
        have ltprev : r - a < b := by omega
        rw [prev]
        simp only [ltprev, rb, true_and]
        have qp := Nat.mod_lt ((r - a) / a) (by omega : 0 < 2)
        have qn := Nat.mod_lt (r / a) (by omega : 0 < 2)
        have parity : (r / a) % 2 = (((r - a) / a) % 2 + 1) % 2 := by
          simp only [fq, Nat.add_mod, Nat.one_mod, Nat.mod_mod]
        have parity' : ((r + a) / a) % 2 = ((r / a) % 2 + 1) % 2 := by
          simp only [nq, Nat.add_mod, Nat.one_mod, Nat.mod_mod]
        omega
    · have next : (r + a) % (a + b) = r - b := by
        have e : r + a = (r - b) + (a + b) := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have rq : (r - b) / a = 0 := Nat.div_eq_of_lt (by omega)
      have rlt : r - b < b := by omega
      simp [rb, next, rq, rlt]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [rule]
    change _ ↔ P (n % m)
    by_cases nm : n < m
    · rw [Nat.mod_eq_of_lt nm]
      by_cases nb : n < b
      · by_cases na : n < a
        · have nq : n / a = 0 := Nat.div_eq_of_lt na
          simp [P, nb, nq, show ¬ a ≤ n by omega, show ¬ b ≤ n by omega]
        · have hna : a ≤ n := by omega
          have hsmall : n - a < m := by omega
          have hia := ih (n - a) (by omega)
          rw [Nat.mod_eq_of_lt hsmall] at hia
          have fq := flip n hna
          have parity : (n / a) % 2 = (((n - a) / a) % 2 + 1) % 2 := by
            simp only [fq, Nat.add_mod, Nat.one_mod, Nat.mod_mod]
          have qp := Nat.mod_lt ((n - a) / a) (by omega : 0 < 2)
          simp only [hna, true_implies, show ¬ b ≤ n by omega, false_implies,
            and_true, ne_eq, hia]
          dsimp [P]
          have np : n - a < b := by omega
          simp only [np, nb, true_and]
          omega
      · have hnb : b ≤ n := by omega
        have hbsmall : n - b < a := by dsimp [m] at nm; omega
        have hbmod : n - b < m := by dsimp [m]; omega
        have hz := (ih (n - b) (by omega)).mpr
          ⟨by rw [Nat.mod_eq_of_lt hbmod]; omega,
            by rw [Nat.mod_eq_of_lt hbmod, Nat.div_eq_of_lt hbsmall]⟩
        simp [P, nb, hnb, hz]
    · have hna : a ≤ n := by dsimp [m] at nm; omega
      have hnb : b ≤ n := by dsimp [m] at nm; omega
      have amod : (n - a) % m = (n % m + b) % m := by
        have e : n - a + m = n + b := by dsimp [m]; omega
        have e' := congrArg (fun k => k % m) e
        simpa only [Nat.add_mod_right, Nat.add_mod, Nat.mod_mod] using e'
      have bmod : (n - b) % m = (n % m + a) % m := by
        have e : n - b + m = n + a := by dsimp [m]; omega
        have e' := congrArg (fun k => k % m) e
        simpa only [Nat.add_mod_right, Nat.add_mod, Nat.mod_mod] using e'
      have ia := ih (n - a) (by omega)
      have ib := ih (n - b) (by omega)
      change (grundy {a, b} (n - a) = 0 ↔ P ((n - a) % m)) at ia
      change (grundy {a, b} (n - b) = 0 ↔ P ((n - b) % m)) at ib
      rw [amod] at ia
      rw [bmod] at ib
      simpa only [hna, hnb, true_implies, ne_eq, ia, ib] using
        (circle (n % m) (Nat.mod_lt _ (by dsimp [m]; omega))).symm

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

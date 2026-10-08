/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleCA
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleCA
   mirror-E: none(waiver:period-translate-obstruction)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: A forbidden pair of base losses contradicts a pure outcome period of c plus a. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleGrundy
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex)

/-- A period translate of a forbidden base pair would join two losses by a legal `b` move. -/
theorem ca_necessity (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (period : ∀ n, grundy {a, b, c} (n + (c + a)) = 0 ↔
      grundy {a, b, c} n = 0) : AdmissibleCA a b (c % (a + b)) := by
  classical
  let m := a + b
  let δ := b - a
  let ρ := c % m
  have hm : 0 < m := by dsimp [m]; omega
  have hr : ρ < m := Nat.mod_lt _ hm
  have memZ (r : ℕ) : r ∈ basePattern a b ↔
      r < m ∧ grundy {a, b} r = 0 := by simp [basePattern, m]
  have base (k : ℕ) : grundy {a, b} k = 0 ↔ k % m ∈ basePattern a b := by
    rw [memZ]
    have hr' := Nat.mod_lt k hm
    have hp := base_positions a b ha hab k
    have hp' := base_positions a b ha hab (k % m)
    dsimp [m] at hp' hr' ⊢
    rw [Nat.mod_mod] at hp'
    simpa only [hr', true_and] using hp.trans hp'.symm
  change basePattern a b ∩ Finset.range δ ∩
    shift m ((δ + m - ρ) % m) (basePattern a b) = ∅
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx, ht⟩
  rcases Finset.mem_inter.mp hx with ⟨hxz, hxd⟩
  have xd : x < δ := Finset.mem_range.mp hxd
  have xm : x < m := (memZ x).mp hxz |>.1
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp ht
  have zm : z < m := (memZ z).mp hz |>.1
  have congruent : Nat.ModEq m (z + (δ + m - ρ)) x := by
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt xm] using hzx
  have forward : Nat.ModEq m (z + δ) (x + c) := by
    have h := congruent.add_right ρ
    have e : z + (δ + m - ρ) + ρ = (z + δ) + m := by omega
    rw [e] at h
    have rc : Nat.ModEq m ρ c := by dsimp [Nat.ModEq, ρ]; simp
    have h' : Nat.ModEq m (z + δ) (x + ρ) := by
      simpa only [Nat.ModEq, Nat.add_mod_right] using h
    exact h'.trans (rc.add_left x)
  let y := x + c - δ
  have yc : y < c := by dsimp [y, δ] at *; omega
  have ye : y + δ = x + c := by dsimp [y, δ]; omega
  have yz : Nat.ModEq m y z := by
    apply Nat.ModEq.add_right_cancel' δ
    rw [ye]
    exact forward.symm
  have yz' : y % m = z := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt zm] using yz
  have yzero : grundy {a, b, c} y = 0 := by
    rw [below_third a b c y yc]
    exact base y |>.mpr (by rw [yz']; exact hz)
  have xzero : grundy {a, b, c} x = 0 := by
    rw [below_third a b c x (by dsimp [δ] at xd; omega)]
    exact (memZ x).mp hxz |>.2
  have translate := (period x).mpr xzero
  let k := x + (c + a)
  have recur : grundy {a, b, c} k =
      mex ((({a, b, c} : Finset ℕ).filter fun s => 0 < s ∧ s ≤ k).image
        fun s => grundy {a, b, c} (k - s)) := by
    rw [grundy, Nat.strongRecOn_eq]
    congr 1
    ext v
    simp [grundy]
  have missing (T : Finset ℕ) : mex T ∉ T := by
    have spec : mex T ∉ T ∧ ∀ j < mex T, j ∈ T := by
      run_tac
        let env ← Lean.getEnv
        let some (name, _) := env.constants.toList.find?
          (fun (name, _) => name.toString.endsWith ".CrimGrundyRefutation.mex_spec")
          | throwError "Existing mex characterization not found"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent name) _))
    exact spec.1
  have kb : k - b = y := by dsimp [k, y, δ]; omega
  rw [recur] at translate
  apply missing _
  rw [translate]
  apply Finset.mem_image.mpr
  refine ⟨b, ?_, ?_⟩
  · simp only [Finset.mem_filter]
    exact ⟨by simp, by omega, by dsimp [k]; omega⟩
  · simpa [kb] using yzero

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

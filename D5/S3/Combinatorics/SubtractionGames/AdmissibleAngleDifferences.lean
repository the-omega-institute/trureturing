/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleDifferences
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleDifferences
   mirror-E: none(waiver:interval-difference-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: Constructive containment of terminal-arc gap differences in two forbidden sets. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleGrundy
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs

set_option maxHeartbeats 3000000 in
/-- Every nonharmonic arc-gap difference also joins the arc to a base loss or to itself. -/
theorem difference_obstruction (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (he : 0 < (b - a) % a) (d u : ℕ) (hd : d ∈ gaps a b) (hu : u ∈ arc a b) :
    ∃ v ∈ arc a b, ∃ z, (z ∈ basePattern a b ∨ z ∈ arc a b) ∧
      Nat.ModEq (a + b) (u + v) (d + z) := by
  classical
  let q := (b - a) / a
  let e := (b - a) % a
  let m := a + b
  have er : e < a := Nat.mod_lt _ ha
  have ep : 0 < e := he
  have ea : a - e + e = a := by omega
  have decomp : b = (q + 1) * a + e := by
    have h := Nat.mod_add_div (b - a) a
    dsimp [q, e]
    nlinarith [Nat.sub_add_cancel (show a ≤ b by omega)]
  have memZ (z : ℕ) : z ∈ basePattern a b ↔ z < b ∧ (z / a) % 2 = 0 := by
    simp only [basePattern, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hz, hp⟩
      simpa only [Nat.mod_eq_of_lt hz] using (base_positions a b ha hab z).mp hp
    · intro hp
      have hz : z < a + b := by omega
      exact ⟨hz, (base_positions a b ha hab z).mpr
        (by simpa only [Nat.mod_eq_of_lt hz] using hp)⟩
  rcases Finset.mem_sdiff.mp hd with ⟨hd, hdz⟩
  rcases Finset.mem_Ico.mp hd with ⟨da, db⟩
  let k := d / a
  let r := d % a
  have rr : r < a := Nat.mod_lt _ ha
  have dd : d = k * a + r := by dsimp [k, r]; nlinarith [Nat.mod_add_div d a]
  have ko : k % 2 = 1 := by
    have := Nat.mod_lt k (by omega : 0 < 2)
    have hn : ¬ k % 2 = 0 := by
      intro h
      apply hdz
      exact (memZ d).mpr ⟨db, h⟩
    omega
  have kp : 0 < k := by
    by_contra h
    have hk : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk] at ko
    contradiction
  have ku : k ≤ q + 1 := by
    by_contra hn
    have : (q + 2) * a ≤ k * a := Nat.mul_le_mul_right a (by omega)
    nlinarith
  have join (A l B h T : ℕ) (hl : 0 < l) (hh : 0 < h)
      (h₁ : A + T < B + h) (h₂ : B < A + l + T) :
      ∃ z v, A ≤ z ∧ z < A + l ∧ B ≤ v ∧ v < B + h ∧ z + T = v := by
    let v := max B (A + T)
    have vb : B ≤ v := le_max_left _ _
    have va : A + T ≤ v := le_max_right _ _
    have vh : v < B + h := max_lt (by omega) h₁
    have vz : v < A + l + T := max_lt h₂ (by omega)
    exact ⟨v - T, v, by omega, by omega, vb, vh, by omega⟩
  by_cases qe : Even q
  · have qpar : q % 2 = 0 := Nat.even_iff.mp qe
    have arc_mem (v : ℕ) : v ∈ arc a b ↔
        (q + 1) * a ≤ v ∧ v < (q + 1) * a + e := by
      simp only [arc]
      change (v ∈ if Even q then _ else _) ↔ _
      rw [if_pos qe, Finset.mem_Ico]
    have uu := (arc_mem u).mp hu
    have ub : u < b := by nlinarith
    by_cases last : k = q + 1
    · have dv : d ∈ arc a b := by
        apply (arc_mem d).mpr
        constructor <;> nlinarith
      exact ⟨d, dv, u, Or.inr hu, by dsimp [Nat.ModEq]; rw [Nat.add_comm]⟩
    · have kq : k + 1 ≤ q := by omega
      let A := (q - k - 1) * a
      let B := (q + 1) * a
      have coord : A + (k + 1) * a = q * a := by
        have : q - k - 1 + (k + 1) = q := by omega
        dsimp [A]
        nlinarith
      let T := m + d - u
      have te : T + u = m + d := by
        dsimp [T, m]
        omega
      have h₁ : A + T < B + e := by dsimp [m, B] at *; nlinarith
      have h₂ : B < A + a + T := by dsimp [m, B] at *; nlinarith
      obtain ⟨z, v, az, za, bv, ve, eq⟩ := join A a B e T ha ep h₁ h₂
      have zv : z / a = q - k - 1 := by
        apply Nat.div_eq_of_lt_le
        · simpa only [A] using az
        · dsimp [A] at za
          nlinarith
      have zz : z ∈ basePattern a b := by
        apply (memZ z).mpr
        refine ⟨?_, ?_⟩
        · nlinarith
        · rw [zv]
          omega
      refine ⟨v, (arc_mem v).mpr ⟨bv, ve⟩, z, Or.inl zz, ?_⟩
      have eq' : u + v = d + z + m := by omega
      rw [eq']
      simp only [Nat.ModEq, m, Nat.add_mod_right]
  · have qpar : q % 2 = 1 := by
      have h := Nat.mod_lt q (by omega : 0 < 2)
      have h' := Nat.even_iff.not.mp qe
      omega
    have arc_mem (v : ℕ) : v ∈ arc a b ↔ q * a + e ≤ v ∧ v < (q + 1) * a := by
      simp only [arc]
      change (v ∈ if Even q then _ else _) ↔ _
      rw [if_neg qe, Finset.mem_Ico]
    have uu := (arc_mem u).mp hu
    have ub : u < b := by nlinarith
    have kq : k ≤ q := by omega
    by_cases last : k = q
    · by_cases ud : u ≤ d
      · let v := q * a + e + d - u
        have veq : v + u = q * a + e + d := by dsimp [v]; omega
        have vv : v ∈ arc a b := by
          apply (arc_mem v).mpr
          constructor <;> nlinarith
        have zarc : q * a + e ∈ arc a b := by
          apply (arc_mem _).mpr
          constructor <;> nlinarith
        refine ⟨v, vv, q * a + e, Or.inr zarc, ?_⟩
        have eq : u + v = d + (q * a + e) := by dsimp [v]; omega
        rw [eq]
      · let A := (q + 1) * a
        let B := q * a + e
        let T := u - d
        have tp : 0 < T := by dsimp [T]; omega
        have te : T + d = u := by dsimp [T]; omega
        have h₁ : B + T < A + e := by dsimp [A, B] at *; nlinarith
        have h₂ : A < B + (a - e) + T := by dsimp [A, B] at *; nlinarith
        obtain ⟨v, z, bv, va, az, ze, eq⟩ :=
          join B (a - e) A e T (by omega) ep h₁ h₂
        have zz : z ∈ basePattern a b := by
          apply (memZ z).mpr
          have zq : z / a = q + 1 := by
            apply Nat.div_eq_of_lt_le az
            dsimp [A] at ze
            nlinarith
          refine ⟨by dsimp [A] at ze; omega, ?_⟩
          rw [zq]
          omega
        have vv : v ∈ arc a b := by
          apply (arc_mem v).mpr
          dsimp [B] at bv va
          constructor <;> nlinarith
        refine ⟨v, vv, z, Or.inl zz, ?_⟩
        have eq' : u + v = d + z := by omega
        rw [eq']
    · have kq' : k + 2 ≤ q := by omega
      let A := (q - k - 2) * a
      let B := q * a + e
      have coord : A + (k + 2) * a = q * a := by
        have : q - k - 2 + (k + 2) = q := by omega
        dsimp [A]
        nlinarith
      let T := m + d - u
      have te : T + u = m + d := by dsimp [T, m]; omega
      have h₁ : A + T < B + (a - e) := by dsimp [m, B] at *; nlinarith
      have h₂ : B < A + a + T := by dsimp [m, B] at *; nlinarith
      obtain ⟨z, v, az, za, bv, ve, eq⟩ :=
        join A a B (a - e) T ha (by omega) h₁ h₂
      have zv : z / a = q - k - 2 := by
        apply Nat.div_eq_of_lt_le
        · simpa only [A] using az
        · dsimp [A] at za
          nlinarith
      have zz : z ∈ basePattern a b := by
        apply (memZ z).mpr
        refine ⟨by nlinarith, ?_⟩
        rw [zv]
        omega
      have vv : v ∈ arc a b := by
        apply (arc_mem v).mpr
        dsimp [B] at bv ve
        constructor <;> nlinarith
      refine ⟨v, vv, z, Or.inl zz, ?_⟩
      have eq' : u + v = d + z + m := by omega
      rw [eq']
      simp only [Nat.ModEq, m, Nat.add_mod_right]

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

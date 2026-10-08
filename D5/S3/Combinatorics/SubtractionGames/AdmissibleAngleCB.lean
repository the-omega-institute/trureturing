/- GID: D5/S3/Combinatorics/SubtractionGames/AdmissibleAngleCB
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SubtractionGames/AdmissibleAngleCB
   mirror-E: none(waiver:terminal-constraint-and-harmonic-rigidity)
   anchors: []
   utility: none
   digest: The terminal constraint forces both admissibility conditions for period c plus b. -/

import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleWindow
import D5.S3.Combinatorics.SubtractionGames.AdmissibleAngleDifferences

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

open AdmissibleAngleDefs
open D5.S0.Certificates.Games.CrimGrundyRefutation (mex)

set_option maxHeartbeats 1000000 in
/-- Terminal periodicity rules out both collisions, including the primitive harmonic boundary. -/
theorem cb_necessity (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b) (hbc : b < c)
    (primitive : Nat.gcd (Nat.gcd a b) c = 1)
    (period : ∀ n, grundy {a, b, c} (n + (c + b)) = 0 ↔
      grundy {a, b, c} n = 0) : AdmissibleCB a b (c % (a + b)) := by
  classical
  have hap : 0 < a := by omega
  let m := a + b
  let δ := b - a
  let q := δ / a
  let e := δ % a
  let ρ := c % m
  have hm : 0 < m := by dsimp [m]; omega
  have er : e < a := Nat.mod_lt _ hap
  have delta_eq : δ + a = b := Nat.sub_add_cancel (by omega)
  have decomp : b = (q + 1) * a + e := by
    have h := Nat.mod_add_div δ a
    dsimp [δ, q, e] at *
    nlinarith [Nat.sub_add_cancel (show a ≤ b by omega)]
  have memZ (z : ℕ) : z ∈ basePattern a b ↔ z < b ∧ (z / a) % 2 = 0 := by
    simp only [basePattern, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hz, hp⟩
      simpa only [Nat.mod_eq_of_lt hz] using (base_positions a b hap hab z).mp hp
    · intro hp
      have hz : z < a + b := by omega
      exact ⟨hz, (base_positions a b hap hab z).mpr
        (by simpa only [Nat.mod_eq_of_lt hz] using hp)⟩
  have base (k : ℕ) : grundy {a, b} k = 0 ↔ k % m ∈ basePattern a b := by
    simp only [basePattern, Finset.mem_filter, Finset.mem_range]
    have hr := Nat.mod_lt k hm
    have hp := base_positions a b hap hab k
    have hp' := base_positions a b hap hab (k % m)
    dsimp [m] at hp' hr ⊢
    rw [Nat.mod_mod] at hp'
    simpa only [hr, true_and] using hp.trans hp'.symm
  have arc_info (u : ℕ) (hu : u ∈ arc a b) :
      δ ≤ u ∧ u < b ∧ b ≤ u + a ∧ (u / a) % 2 = 1 := by
    change u ∈ if Even q then Finset.Ico ((q + 1) * a) ((q + 1) * a + e)
      else Finset.Ico (q * a + e) ((q + 1) * a) at hu
    by_cases hq : Even q
    · rw [if_pos hq, Finset.mem_Ico] at hu
      have uq : u / a = q + 1 := Nat.div_eq_of_lt_le hu.1 (by nlinarith)
      have qpar := Nat.even_iff.mp hq
      refine ⟨?_, by omega, ?_, ?_⟩
      · nlinarith only [delta_eq, decomp, hu.1, er]
      · nlinarith
      · rw [uq]
        omega
    · rw [if_neg hq, Finset.mem_Ico] at hu
      have uq : u / a = q := Nat.div_eq_of_lt_le (by omega) hu.2
      have qpar : q % 2 = 1 := by
        have := Nat.mod_lt q (by omega : 0 < 2)
        have := Nat.even_iff.not.mp hq
        omega
      refine ⟨?_, by nlinarith, ?_, by simpa [uq] using qpar⟩
      · nlinarith only [delta_eq, decomp, hu.1, er]
      · nlinarith
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
  have zero_rule (S : Finset ℕ) (k : ℕ) : grundy S k = 0 ↔
      ∀ s ∈ S, 0 < s → s ≤ k → grundy S (k - s) ≠ 0 := by
    rw [recur, mex_zero]
    simp only [Finset.mem_image, Finset.mem_filter, not_exists, not_and]
    constructor
    · intro h s hs hp hl hz
      exact h s ⟨hs, hp, hl⟩ hz
    · intro h s ⟨hs, hp, hl⟩ hz
      exact h s hs hp hl hz
  have terminal (u : ℕ) (hu : u ∈ arc a b) :
      (ρ + u + a) % m ∈ basePattern a b := by
    obtain ⟨ud, ub, _, uodd⟩ := arc_info u hu
    let r := u - δ
    have ra : r < a := by dsimp [r, δ]; omega
    have rz : grundy {a, b, c} r = 0 := by
      rw [below_third a b c r (by omega)]
      apply (base_positions a b hap hab r).mpr
      have rm : r < a + b := by omega
      simp [Nat.mod_eq_of_lt rm, Nat.div_eq_of_lt ra, show r < b by omega]
    have shifted := (period r).mpr rz
    have eq : r + (c + b) - a = c + u := by dsimp [r, δ]; omega
    have win : grundy {a, b, c} (c + u) ≠ 0 := by
      have := (zero_rule {a, b, c} (r + (c + b))).mp shifted a
        (by simp) hap (by omega)
      simpa only [eq] using this
    have uwin : grundy {a, b} u ≠ 0 := by
      intro hz
      have h := (base_positions a b hap hab u).mp hz
      have um : u < a + b := by omega
      rw [Nat.mod_eq_of_lt um] at h
      omega
    have vz : grundy {a, b} (c + u - b) = 0 := by
      by_contra hn
      exact win ((first_window a b c u hap hab hbc ub).mpr ⟨uwin, hn⟩)
    have vz' := (base (c + u - b)).mp vz
    have eq' : c + u - b + m = c + u + a := by dsimp [m]; omega
    have cong : (c + u - b) % m = (ρ + u + a) % m := by
      have h := congrArg (fun k => k % m) eq'
      dsimp [ρ]
      simpa only [Nat.add_mod_right, Nat.add_mod, Nat.mod_mod] using h
    rwa [cong] at vz'
  have nohit (z : ℕ) (hz : z ∈ basePattern a b ∨ z ∈ arc a b) :
      (z + a) % m ∉ basePattern a b := by
    rcases hz with hz | hz
    · obtain ⟨zb, zp⟩ := (memZ z).mp hz
      have zm : z + a < m := by dsimp [m]; omega
      intro h
      have h' := (memZ _).mp h
      rw [Nat.mod_eq_of_lt zm] at h'
      have hq := Nat.add_div_right z hap
      rw [hq] at h'
      omega
    · obtain ⟨_, zb, zba, _⟩ := arc_info z hz
      have zm : z + a < m := by dsimp [m]; omega
      intro h
      have h' := (memZ _).mp h
      rw [Nat.mod_eq_of_lt zm] at h'
      omega
  have avoids (v : ℕ) (hv : v ∈ arc a b) (z : ℕ)
      (hz : z ∈ basePattern a b ∨ z ∈ arc a b) : ¬ Nat.ModEq m (ρ + v) z := by
    intro hc
    have ht := terminal v hv
    have hc' := hc.add_right a
    change (ρ + v + a) % m = (z + a) % m at hc'
    rw [hc'] at ht
    exact nohit z hz ht
  by_cases he : e = 0
  · by_cases hq : Even q
    · have empty : arc a b = ∅ := by
        change (if Even q then Finset.Ico ((q + 1) * a) ((q + 1) * a + e)
          else Finset.Ico (q * a + e) ((q + 1) * a)) = ∅
        rw [if_pos hq, he]
        simp
      simp [AdmissibleCB, shift, empty]
    · have qodd : q % 2 = 1 := by
        have := Nat.mod_lt q (by omega : 0 < 2)
        have := Nat.even_iff.not.mp hq
        omega
      have bj : b = (q + 1) * a := by omega
      have inarc (j : ℕ) (hj : j < a) : q * a + j ∈ arc a b := by
        change q * a + j ∈ if Even q then
          Finset.Ico ((q + 1) * a) ((q + 1) * a + e)
          else Finset.Ico (q * a + e) ((q + 1) * a)
        rw [if_neg hq, he, Finset.mem_Ico]
        constructor <;> nlinarith
      have window (j : ℕ) (hj : j < a) : (c + b + j) % m ∈ basePattern a b := by
        have ht := terminal (q * a + j) (inarc j hj)
        have cong : (ρ + (q * a + j) + a) % m = (c + b + j) % m := by
          have rc : Nat.ModEq m ρ c := by dsimp [Nat.ModEq, ρ]; simp
          have h := rc.add_right (q * a + j + a)
          have eq₁ : ρ + (q * a + j + a) = ρ + (q * a + j) + a := by omega
          have eq₂ : c + (q * a + j + a) = c + b + j := by nlinarith only [bj]
          rw [eq₁, eq₂] at h
          exact h
        rwa [cong] at ht
      let t := (c + b) % m
      have tz : t ∈ basePattern a b := by simpa only [Nat.add_zero] using window 0 hap
      obtain ⟨tb, tqeven⟩ := (memZ t).mp tz
      have tr : t % a < a := Nat.mod_lt _ hap
      have td : t = (t / a) * a + t % a := by nlinarith [Nat.mod_add_div t a]
      have tq : t / a ≤ q := by
        by_contra h
        have : (q + 1) * a ≤ (t / a) * a := Nat.mul_le_mul_right a (by omega)
        have bound : (t / a) * a ≤ t := Nat.div_mul_le_self t a
        have bt : b ≤ t := by rw [bj]; exact this.trans bound
        exact (Nat.not_le_of_gt tb) bt
      have tq' : t / a + 1 ≤ q := by omega
      have tzero : t % a = 0 := by
        by_contra hn
        let j := a - t % a
        have ja : j < a := by dsimp [j]; omega
        have jrel : j + t % a = a := Nat.sub_add_cancel tr.le
        have tj : t + j = (t / a + 1) * a := by nlinarith only [td, jrel]
        have tja : t + j < m := by
          have : (t / a + 1) * a ≤ q * a := Nat.mul_le_mul_right a tq'
          dsimp [m]
          nlinarith
        have ht := window j ja
        have cong : (c + b + j) % m = (t + j) % m := by
          dsimp [t]
          simp only [Nat.add_mod, Nat.mod_mod]
        rw [cong, Nat.mod_eq_of_lt tja] at ht
        have h' := (memZ _).mp ht
        have jd : (t + j) / a = t / a + 1 := by
          rw [tj]
          exact Nat.mul_div_cancel _ hap
        rw [jd] at h'
        omega
      have ab : a ∣ b := ⟨q + 1, by nlinarith⟩
      have am : a ∣ m := Nat.dvd_add (dvd_refl a) ab
      have tc : Nat.ModEq m t (c + b) := by dsimp [Nat.ModEq, t]; simp
      have tc' := tc.of_dvd am
      change t % a = (c + b) % a at tc'
      have czero : c % a = 0 := by
        simpa only [Nat.add_mod, Nat.mod_eq_zero_of_dvd ab, Nat.add_zero, Nat.mod_mod]
          using tc'.symm.trans tzero
      have ac : a ∣ c := Nat.dvd_of_mod_eq_zero czero
      have ag : a ∣ Nat.gcd (Nat.gcd a b) c :=
        Nat.dvd_gcd (Nat.dvd_gcd (dvd_refl a) ab) ac
      rw [primitive] at ag
      have := Nat.le_of_dvd (by omega : 0 < 1) ag
      omega
  · change shift m ρ (arc a b) ∩ basePattern a b = ∅ ∧
      shift m ρ (gaps a b) ∩ arc a b = ∅
    constructor
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rcases Finset.mem_inter.mp hz with ⟨hv, hz⟩
      obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hv
      have hc : Nat.ModEq m (ρ + v) z := by
        have zm : z < m := by dsimp [m]; have := (memZ z).mp hz; omega
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt zm, Nat.add_comm] using eq
      exact avoids v hv z (Or.inl hz) hc
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      rcases Finset.mem_inter.mp hu with ⟨hd, hu⟩
      obtain ⟨d, hd, eq⟩ := Finset.mem_image.mp hd
      have ep : 0 < (b - a) % a := by change 0 < e; omega
      obtain ⟨v, hv, z, hz, hc⟩ := difference_obstruction a b hap hab ep d u hd hu
      have um : u < m := by dsimp [m]; have := arc_info u hu; omega
      have du : Nat.ModEq m (ρ + d) u := by
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt um, Nat.add_comm] using eq
      have dz : Nat.ModEq m (d + (ρ + v)) (d + z) := by
        have hd' := du.add_right v
        have eq' : ρ + d + v = d + (ρ + v) := by omega
        rw [eq'] at hd'
        exact hd'.trans hc
      exact avoids v hv z hz (Nat.ModEq.add_left_cancel' d dz)

end D5.S3.Combinatorics.SubtractionGames.AdmissibleAngle

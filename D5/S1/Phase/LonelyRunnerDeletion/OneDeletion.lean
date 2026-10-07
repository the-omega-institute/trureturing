/- GID: D5/S1/Phase/LonelyRunnerDeletion/OneDeletion
   generality: G
   mirror-B: D5/B/S1/Phase/LonelyRunnerDeletion/OneDeletion
   mirror-E: none(waiver:zhang-question-two-eleven-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.Basic]
   utility: none
   digest: Resolve both deletion bounds and characterize equality for every interval length. -/

import D5.S1.Phase.LonelyRunnerDeletion.OneDeletionDefs
import Mathlib.NumberTheory.DiophantineApproximation.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Phase.LonelyRunnerDeletion.OneDeletion

open OneDeletionDefs

/-- Zhang's deletion question, including the equality cases on the nonempty domain. -/
theorem result : OneDeletionDefs.claim := by
  intro N r hN hr hrN
  classical
  let V := (Finset.Icc 1 N).erase r
  have hmem (v : ℕ) : v ∈ V ↔ v ≠ r ∧ 1 ≤ v ∧ v ≤ N := by
    simp [V, Finset.mem_Icc]
  have hne : V.Nonempty := by
    by_cases h : r = 1
    · refine ⟨2, (hmem 2).mpr ?_⟩
      exact ⟨by omega, by omega, hN⟩
    · exact ⟨1, (hmem 1).mpr ⟨Ne.symm h, le_rfl, by omega⟩⟩
  let : Nonempty V := hne.to_subtype
  have hb (t : ℝ) : BddBelow (Set.range fun v : V =>
      |(v : ℝ) * t - round ((v : ℝ) * t)|) := by
    exact ⟨0, by rintro x ⟨v, rfl⟩; exact abs_nonneg _⟩
  have hu (t : ℝ) : (⨅ v : V, |(v : ℝ) * t - round ((v : ℝ) * t)|) ≤ 1/2 := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact (ciInf_le (hb t) v).trans (abs_sub_round _)
  have hs : BddAbove (Set.range fun t : ℝ =>
      ⨅ v : V, |(v : ℝ) * t - round ((v : ℝ) * t)|) := by
    exact ⟨1/2, by rintro x ⟨t, rfl⟩; exact hu t⟩
  have hw (c t : ℝ) (h : ∀ v : V,
      c ≤ |(v : ℝ) * t - round ((v : ℝ) * t)|) : c ≤ lonelyValue V := by
    exact (le_ciInf h).trans (le_ciSup hs t)
  have hp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hendpoint (h : r = N) : lonelyValue V = 1/(N:ℝ) := by
    subst r
    apply le_antisymm
    · apply ciSup_le
      intro t
      obtain ⟨k, hk, hkN, hd⟩ :=
        Real.exists_nat_abs_mul_sub_round_le t (show 0 < N-1 by omega)
      have hkv : k ∈ V := (hmem k).mpr ⟨by omega, by omega, by omega⟩
      have he : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        exact_mod_cast (show N-1+1=N by omega)
      exact (ciInf_le (hb t) ⟨k, hkv⟩).trans (by simpa [he] using hd)
    · apply hw (1/(N:ℝ)) (1/(N:ℝ))
      intro v
      obtain ⟨hvne, hv1, hvN⟩ := (hmem v).mp v.property
      have hvlt : (v:ℕ) < N := by omega
      rw [mul_one_div, abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hvlt]
      apply div_le_div_of_nonneg_right _ hp.le
      exact_mod_cast (show 1 ≤ min (v:ℕ) (N-(v:ℕ)) by omega)
  have hsmall (h : N = 2) : lonelyValue V = 1/(N:ℝ) := by
    subst N
    have hr12 : r = 1 ∨ r = 2 := by omega
    have hhalf : lonelyValue V ≤ 1/2 := ciSup_le hu
    apply le_antisymm (by simpa using hhalf)
    rcases hr12 with rfl | rfl
    · apply hw (1/2) (1/4)
      intro v
      have hv : (v:ℕ) = 2 := by
        have := (hmem v).mp v.property
        omega
      change 1/2 ≤ |((v:ℕ):ℝ) * (1/4) - round (((v:ℕ):ℝ) * (1/4))|
      norm_num [hv, round]
    · apply hw (1/2) (1/2)
      intro v
      have hv : (v:ℕ) = 1 := by
        have := (hmem v).mp v.property
        omega
      change 1/2 ≤ |((v:ℕ):ℝ) * (1/2) - round (((v:ℕ):ℝ) * (1/2))|
      norm_num [hv, round]
  have smallDeletion_denominator (N r : ℕ) (hN : 3 ≤ N) (hr : 1 ≤ r)
      (hhalf : 2 * r ≤ N) :
      ∃ q a : ℕ, N + r < q ∧ q < 2 * N ∧ Nat.ModEq q (a * r) 1 := by
    let m := N + 2 * r - 1
    let k := m / r
    let q := 1 + r * k
    let a := 1 + (r - 1) * k
    have hrpos : 0 < r := by omega
    have hm : m + 1 = N + 2 * r := by dsimp [m]; omega
    have hdivision : r * k + m % r = m := by
      simpa [k] using Nat.div_add_mod m r
    have hrem : m % r < r := Nat.mod_lt m hrpos
    have hlow : N + r < q := by dsimp [q]; omega
    have hupp : q ≤ N + 2 * r := by dsimp [q]; omega
    have hstrict : q < 2 * N := by
      by_cases heq : 2 * r = N
      · have hr2 : 2 ≤ r := by omega
        have hk : k < 4 := by
          apply (Nat.div_lt_iff_lt_mul hrpos).2
          omega
        have hrk : r * k ≤ r * 3 := Nat.mul_le_mul_left r (by omega)
        dsimp [q]
        omega
      · omega
    have hrsub : r - 1 + 1 = r := by omega
    have hinverse : a * r = 1 + (r - 1) * q := by
      dsimp [a, q]
      nlinarith [hrsub]
    refine ⟨q, a, hlow, hstrict, ?_⟩
    rw [hinverse]
    simp [Nat.ModEq, Nat.add_mod]
  have inverse_residue_distance (N r q a : ℕ) (hr : 1 ≤ r)
      (hq : N + r < q) (hinv : Nat.ModEq q (a * r) 1)
      (v : ℕ) (hv : v ∈ (Finset.Icc 1 N).erase r) :
      2 / (q : ℝ) ≤ |(v : ℝ) * ((a : ℝ) / q) - round ((v : ℝ) * ((a : ℝ) / q))| := by
    obtain ⟨hvr, hvI⟩ := Finset.mem_erase.mp hv
    obtain ⟨hv1, hvN⟩ := Finset.mem_Icc.mp hvI
    have hq0 : 0 < q := by omega
    have hvq : v < q := by omega
    have hrq : r < q := by omega
    let b := (v * a) % q
    have hbq : b < q := Nat.mod_lt _ hq0
    have hback : Nat.ModEq q ((v * a) * r) v := by
      simpa only [Nat.mul_assoc, Nat.mul_one] using hinv.mul_left v
    have hmod : Nat.ModEq q (v * a) b := (Nat.mod_modEq (v * a) q).symm
    have hbback : Nat.ModEq q v (b * r) := hback.symm.trans (hmod.mul_right r)
    have hb0 : b ≠ 0 := by
      intro hb
      have h : Nat.ModEq q v 0 := by simpa only [hb, Nat.zero_mul] using hbback
      have := h.eq_of_lt_of_lt hvq hq0
      omega
    have hb1 : b ≠ 1 := by
      intro hb
      have h : Nat.ModEq q v r := by simpa only [hb, Nat.one_mul] using hbback
      exact hvr (h.eq_of_lt_of_lt hvq hrq)
    have hblast : b ≠ q - 1 := by
      intro hb
      have hsum : b * r + r = q * r := by
        calc
          b * r + r = (b + 1) * r := by rw [Nat.add_mul, Nat.one_mul]
          _ = q * r := by rw [hb, Nat.sub_add_cancel (by omega)]
      have h : Nat.ModEq q (v + r) 0 := by
        have hadd := hbback.add_right r
        rw [hsum] at hadd
        exact hadd.trans (by simp [Nat.ModEq])
      have := h.eq_of_lt_of_lt (by omega) hq0
      omega
    have hb2 : 2 ≤ b := by omega
    have hqb2 : 2 ≤ q - b := by omega
    have hmin : 2 ≤ min b (q - b) := le_min hb2 hqb2
    have hminR : (2 : ℝ) ≤ (min b (q - b) : ℕ) := by exact_mod_cast hmin
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
    rw [← mul_div_assoc, ← Nat.cast_mul, abs_sub_round_div_natCast_eq]
    exact div_le_div_of_nonneg_right hminR hqR.le
  have hstrict (h3 : 3 ≤ N) (hrlt : r < N) : 1/(N:ℝ) < lonelyValue V := by
    by_cases hhalf : 2*r ≤ N
    · obtain ⟨q, a, hq, hqN, hinv⟩ := smallDeletion_denominator N r h3 hr hhalf
      have hqpos : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hqNreal : (q:ℝ) < 2*(N:ℝ) := by exact_mod_cast hqN
      have hratio : 1/(N:ℝ) < 2/(q:ℝ) := by
        apply (div_lt_div_iff₀ hp hqpos).mpr
        linarith
      apply hratio.trans_le
      apply hw (2/(q:ℝ)) ((a:ℝ)/q)
      intro v
      exact inverse_residue_distance N r q a hr hq hinv v v.property
    · have hrpos : 0 < r := by omega
      have hrR : 0 < (r:ℝ) := by exact_mod_cast hrpos
      have hrNR : (r:ℝ) < N := by exact_mod_cast hrlt
      have hratio : 1/(N:ℝ) < 1/(r:ℝ) := by
        apply (div_lt_div_iff₀ hp hrR).mpr
        simpa using hrNR
      apply hratio.trans_le
      apply hw (1/(r:ℝ)) (1/(r:ℝ))
      intro v
      obtain ⟨hvne, hv1, hvN⟩ := (hmem v).mp v.property
      have hmod : (v:ℕ) % r ≠ 0 := by
        intro hzero
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hzero
        have hk1 : 1 ≤ k := by
          by_contra h
          have hk0 : k = 0 := by omega
          simp [hk0] at hk
          omega
        have hk2 : k < 2 := by
          by_contra h
          have : 2 ≤ k := by omega
          have := Nat.mul_le_mul_left r this
          omega
        have : k = 1 := by omega
        exact hvne (by simpa only [this, Nat.mul_one] using hk)
      have hm : (v:ℕ) % r < r := Nat.mod_lt _ hrpos
      have hmin : 1 ≤ min ((v:ℕ) % r) (r - (v:ℕ) % r) := by omega
      rw [mul_one_div, abs_sub_round_div_natCast_eq]
      apply div_le_div_of_nonneg_right _ hrR.le
      exact_mod_cast hmin
  by_cases htwo : N = 2
  · have heq := hsmall htwo
    exact ⟨heq.ge, ⟨fun _ => Or.inr htwo, fun _ => heq⟩⟩
  · by_cases hend : r = N
    · have heq := hendpoint hend
      exact ⟨heq.ge, ⟨fun _ => Or.inl hend, fun _ => heq⟩⟩
    · have hslt := hstrict (by omega) (by omega)
      exact ⟨hslt.le, ⟨fun heq => False.elim (ne_of_gt hslt heq),
        fun h => False.elim (h.elim hend htwo)⟩⟩

end D5.S1.Phase.LonelyRunnerDeletion.OneDeletion

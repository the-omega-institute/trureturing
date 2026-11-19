/- GID: D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/LacunaryShadowingUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed finite tracer sets for the full lacunary progression subshift. -/

import D5.S1.Dynamics.Shadowing.LacunaryProgressionSubshift
import D5.S1.Dynamics.Shadowing.LacunaryPhaseCover

open Set Function SymbolicDynamics.FullShift
open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- The explicit phase cover repairs every natural-time pseudo-orbit with one
fixed set of at most m-1 whole orbits, all initially close. -/
theorem lacunary_neighborhood_upper (m : ℕ) (hm : 3 ≤ m) :
    NeighborhoodFiniteShadowing (m - 1) (lacunaryShift m) := by
  classical
  intro ε hε
  obtain ⟨R, hR⟩ := return_metric_window (ε / 2) (by positivity)
  obtain ⟨K, hRH, mask, hinitial, hwindow, hlong⟩ := lacunary_phase_cover m R hm
  let H : ℕ := (m - 1) * (m + 1) ^ K
  have hRH' : R ≤ H := hRH
  obtain ⟨δ, hδ, hcontrol⟩ := return_window_control H
  refine ⟨δ, hδ, fun z hz => ?_⟩
  let zz : ℕ → ℤ → ReturnBit := fun i => (z i).1
  have hedge : ∀ i : ℕ, ∀ j : ℤ, -(H : ℤ) ≤ j → j ≤ H →
      zz i (j + 1) = zz (i + 1) j := by
    intro i j hjl hju
    simpa [zz, lacunaryShift, shift_apply, add_comm] using
      hcontrol (shift 1 (z i).1) (z (i + 1)).1 (hz i) j hjl hju
  let c : ℤ → ReturnBit := signedDiagonal zz
  have hover (i : ℕ) (j : ℤ) (hjl : -(H : ℤ) ≤ j) (hju : j ≤ H) :
      c ((i : ℤ) + j) = (z i).1 j := by
    simpa [c, zz, pastExtension] using signed_diagonal_overlap hedge (i : ℤ) j hjl hju
  have hnegative (n : ℤ) (hn : n ≤ H) : c n = (z 0).1 n := by
    by_cases hn0 : 0 ≤ n
    · simpa using hover 0 n (by omega) hn
    · simp [c, signedDiagonal, pastExtension, hn0, zz, shift_apply]
  let tracerConfig : Fin (m - 1) → ℤ → ReturnBit :=
    fun a n => if mask a n then c n else returnZero
  have hlegal (a : Fin (m - 1)) : LacunaryLegal m (tracerConfig a) := by
    intro s k i j l hij hil hjl hones
    have hkeep (n : ℤ) (hn : tracerConfig a n = returnOne) :
        mask a n ∧ c n = returnOne := by
      dsimp only [tracerConfig] at hn
      split_ifs at hn with h
      · exact ⟨h, hn⟩
      · exact (return_zero_ne_one hn).elim
    obtain ⟨hiM, hiC⟩ := hkeep _ hones.1
    obtain ⟨hjM, hjC⟩ := hkeep _ hones.2.1
    obtain ⟨hlM, hlC⟩ := hkeep _ hones.2.2
    by_cases hk : K ≤ k
    · have hmasks := hlong a s k hk i j l hij hil hjl
      apply hmasks
      simpa only [Nat.cast_pow] using And.intro hiM (And.intro hjM hlM)
    · have hkK : k ≤ K := by omega
      have hpow : (m + 1) ^ k ≤ (m + 1) ^ K :=
        Nat.pow_le_pow_right (by omega) hkK
      have hcoord (v : Fin m) : 0 ≤ (v.val : ℤ) * ((m + 1 : ℕ) : ℤ) ^ k ∧
          (v.val : ℤ) * ((m + 1 : ℕ) : ℤ) ^ k ≤ H := by
        have hv : v.val ≤ m - 1 := by omega
        have hh := Nat.mul_le_mul hv hpow
        constructor
        · positivity
        · exact_mod_cast hh
      have hcshort : ¬ (c (s + (i.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne ∧
          c (s + (j.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne ∧
          c (s + (l.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) = returnOne) := by
        by_cases hs : 0 ≤ s
        · have hsn : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs
          have he (v : Fin m) :
              c (s + (v.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) =
                (z s.toNat).1 ((v.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) := by
            rw [← hsn]
            exact hover s.toNat _ (by have := (hcoord v).1; omega) (hcoord v).2
          simpa only [he, zero_add] using (z s.toNat).2 0 k i j l hij hil hjl
        · have he (v : Fin m) :
              c (s + (v.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) =
                (z 0).1 (s + (v.val : ℤ) * ((m + 1 : ℕ) : ℤ)^k) :=
            hnegative _ (by have := (hcoord v).2; omega)
          simpa only [he] using (z 0).2 s k i j l hij hil hjl
      exact hcshort ⟨hiC, hjC, hlC⟩
  let tracer : Fin (m - 1) → LacunaryPoint m := fun a => ⟨tracerConfig a, hlegal a⟩
  let A : Finset (LacunaryPoint m) := Finset.univ.image tracer
  have hindex : 0 < m - 1 := by omega
  let a₀ : Fin (m - 1) := ⟨0, hindex⟩
  have hA : A.Nonempty := ⟨tracer a₀, Finset.mem_image.mpr ⟨a₀, by simp, rfl⟩⟩
  have hinit (a : Fin (m - 1)) (n : ℤ) (hnl : -(R : ℤ) ≤ n) (hnu : n ≤ R) :
      (tracer a).1 n = c n := by
    exact if_pos (hinitial a n (abs_le.mpr ⟨hnl, hnu⟩))
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · have hd : Metric.diam (A : Set (LacunaryPoint m)) ≤ ε / 2 := by
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      intro x hx y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
      exact (hR (tracer a).1 (tracer b).1 fun n hnl hnu =>
        (hinit a n hnl hnu).trans (hinit b n hnl hnu).symm).le
    linarith
  · intro i
    obtain ⟨a, ha⟩ := hwindow i
    have hdist : dist ((lacunaryShift m)^[i] (tracer a)) (z i) < ε / 2 := by
      apply hR
      intro j hjl hju
      rw [lacunary_shift_iterate]
      change tracerConfig a ((i : ℤ) + j) = (z i).1 j
      rw [show tracerConfig a ((i : ℤ) + j) = c ((i : ℤ) + j) from
        if_pos (ha j (abs_le.mpr ⟨hjl, hju⟩))]
      exact hover i j (by omega) (by omega)
    apply (Metric.infDist_lt_iff (hA.to_set.image _)).mpr
    refine ⟨(lacunaryShift m)^[i] (tracer a), ?_, ?_⟩
    · exact ⟨tracer a, Finset.mem_image.mpr ⟨a, by simp, rfl⟩, rfl⟩
    · rw [dist_comm]
      linarith

end D5.S1.Dynamics.Shadowing

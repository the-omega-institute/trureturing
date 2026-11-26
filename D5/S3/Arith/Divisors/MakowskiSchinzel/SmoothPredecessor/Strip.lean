/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Strip
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Bounded repeated division recognizes prime-supported positive integers. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic

/-! Soundness of bounded removal of prime powers and smooth-number recognition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- Nondivisibility by the next power is the exact fuel condition for complete stripping. -/
theorem strip_spec {p m : ℕ} (k : ℕ) :
    (¬p ^ (k + 1) ∣ m) ↔ 0 < strip k p m ∧ strip k p m ≤ m ∧ ¬p ∣ strip k p m ∧
      ∃ e ≤ k, m = p ^ e * strip k p m := by
  constructor
  · intro hbound
    have hm : 0 < m := Nat.pos_of_ne_zero (fun hz => hbound (hz ▸ dvd_zero _))
    induction k generalizing m with
    | zero =>
      have hnd : ¬p ∣ m := by simpa using hbound
      exact ⟨hm, le_rfl, hnd, 0, le_rfl, by simp [strip]⟩
    | succ k ih =>
      by_cases hd : p ∣ m
      · have hp0 : 0 < p := Nat.pos_of_dvd_of_pos hd hm
        have hmdiv : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hd) hp0
        have hdivbound : ¬p ^ (k + 1) ∣ m / p := by
          intro hbad
          apply hbound
          have hx := Nat.mul_dvd_mul_left p hbad
          simpa only [← pow_succ', Nat.mul_div_cancel' hd] using hx
        obtain ⟨hpos, hle, hnd, e, hek, he⟩ := ih hdivbound hmdiv
        have heq : strip (k + 1) p m = strip k p (m / p) := by
          simp only [strip, Nat.dvd_iff_mod_eq_zero.mp hd, beq_self_eq_true, ite_true]
        rw [heq]
        refine ⟨hpos, hle.trans (Nat.div_le_self _ _), hnd, e + 1, by omega, ?_⟩
        calc
          m = p * (m / p) := (Nat.mul_div_cancel' hd).symm
          _ = p * (p ^ e * strip k p (m / p)) := congrArg (p * ·) he
          _ = p ^ (e + 1) * strip k p (m / p) := by rw [pow_succ]; ring
      · have heq : strip (k + 1) p m = m := by
          have hmod : m % p ≠ 0 := fun hz => hd (Nat.dvd_of_mod_eq_zero hz)
          simp only [strip, show (m % p == 0) = false by simp [hmod],
            Bool.false_eq_true, ite_false]
        rw [heq]
        exact ⟨hm, le_rfl, hd, 0, Nat.zero_le _, by simp⟩
  · rintro ⟨hpos, hle, hnd, e, hek, he⟩ hdiv
    by_cases hp : p = 0
    · subst p
      have hm : m = 0 := by simpa using hdiv
      omega
    have hpe : 0 < p ^ e := pow_pos (Nat.pos_of_ne_zero hp) e
    have hd : p ^ (e + 1) ∣ m :=
      (pow_dvd_pow p (by omega : e + 1 ≤ k + 1)).trans hdiv
    rw [he, pow_succ] at hd
    exact hnd (Nat.dvd_of_mul_dvd_mul_left hpe hd)


private theorem strip_zero (k p : ℕ) : strip k p 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [strip, Nat.zero_mod, beq_self_eq_true, ite_true,
      Nat.zero_div] using ih

private theorem strip_small {p : ℕ} (hp : p ≤ 1) (k m : ℕ) : strip k p m = m := by
  interval_cases p
  · by_cases hm : m = 0
    · simpa only [hm] using strip_zero k 0
    · cases k with
      | zero => rfl
      | succ k =>
        simp only [strip, Nat.mod_zero, beq_eq_false_iff_ne.mpr hm,
          Bool.false_eq_true, ite_false]
  · induction k with
    | zero => rfl
    | succ k ih =>
      change (if m % 1 == 0 then strip k 1 (m / 1) else m) = m
      simpa only [Nat.mod_one, beq_self_eq_true, ite_true, Nat.div_one] using ih

/-- Stripping preserves support when the prime is allowed or the fuel removes its full power. -/
theorem strip_factored_iff {p m : ℕ} (hp : p.Prime ∨ p ≤ 1) (k : ℕ)
    (s : Finset ℕ) (hbound : p ≤ 1 ∨ p ∈ s ∨ m = 0 ∨ ¬p ^ (k + 1) ∣ m) :
    strip k p m ∈ Nat.factoredNumbers s ↔ m ∈ Nat.factoredNumbers (insert p s) := by
  rcases hp with hp | hp
  · have hlarge : ¬p ≤ 1 := by have := hp.two_le; omega
    replace hbound := hbound.resolve_left hlarge
    clear hlarge
    rcases hbound with hmem | hbound
    · rw [Finset.insert_eq_of_mem hmem]
      induction k generalizing m with
      | zero => rfl
      | succ k ih =>
        by_cases hd : p ∣ m
        · simp only [strip, Nat.dvd_iff_mod_eq_zero.mp hd, beq_self_eq_true, ite_true]
          change strip k p (m / p) ∈ Nat.factoredNumbers s ↔ m ∈ Nat.factoredNumbers s
          refine (ih (m := m / p)).trans ?_
          constructor
          · intro h
            have hh := Nat.pow_mul_mem_factoredNumbers hp 1 h
            simpa only [pow_one, Nat.mul_div_cancel' hd, Finset.insert_eq_of_mem hmem] using hh
          · intro h
            exact Nat.mem_factoredNumbers_of_dvd h (Nat.div_dvd_of_dvd hd)
        · have hmod : m % p ≠ 0 := fun hz => hd (Nat.dvd_of_mod_eq_zero hz)
          simp only [strip, show (m % p == 0) = false by simp [hmod],
            Bool.false_eq_true, ite_false]
    by_cases hm0 : m = 0
    · simp [hm0, strip_zero, Nat.factoredNumbers]
    have hm : 0 < m := by omega
    obtain ⟨hpos, _hle, hnd, e, _hek, he⟩ := (strip_spec k).mp (hbound.resolve_left hm0)
    constructor
    · intro hs
      rw [he]
      exact Nat.pow_mul_mem_factoredNumbers hp e hs
    · intro hmfact
      rw [Nat.mem_factoredNumbers'] at hmfact ⊢
      intro r hr hd
      have hdvd : strip k p m ∣ m := by
        exact ⟨p ^ e, by simpa only [mul_comm] using he⟩
      have hin := hmfact r hr (hd.trans hdvd)
      rcases Finset.mem_insert.mp hin with hrp | hrs
      · subst r
        exact (hnd hd).elim
      · exact hrs
  · rw [strip_small hp, Nat.factoredNumbers_insert s (by
      intro hprime
      have := hprime.two_le
      omega)]

/-- Primewise fuel suffices for the Boolean test to recognize exactly the prime support. -/
theorem isSmooth_iff {ps : List ℕ} (hps : ∀ p ∈ ps, p.Prime ∨ p ≤ 1) {m : ℕ}
    (hbound : m = 0 ∨ ∀ p ∈ ps, p.Prime → ¬p ^ 65 ∣ m) :
    isSmooth ps m = true ↔ m ∈ Nat.factoredNumbers ps.toFinset := by
  have hz : ∀ ps : List ℕ, isSmooth ps 0 = false := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih => simpa only [isSmooth, strip_zero] using ih
  induction ps generalizing m with
  | nil => simp [isSmooth, Nat.factoredNumbers_empty]
  | cons p ps ih =>
    by_cases hm0 : m = 0
    · simp [hm0, hz, Nat.factoredNumbers]
    have hps' : ∀ r ∈ ps, r.Prime ∨ r ≤ 1 := fun r hr => hps r (by simp [hr])
    rcases hps p (by simp) with hp | hp
    · have hfuel := hbound.resolve_left hm0
      have hb : ¬p ^ (64 + 1) ∣ m := hfuel p List.mem_cons_self hp
      obtain ⟨_hpos, _hle, _hnd, e, _hek, he⟩ := (strip_spec 64).mp hb
      have hdvd : strip 64 p m ∣ m := ⟨p ^ e, by simpa only [mul_comm] using he⟩
      have htail : strip 64 p m = 0 ∨ ∀ r ∈ ps, r.Prime → ¬r ^ 65 ∣ strip 64 p m := by
        right
        intro r hr hrp hdiv
        exact hfuel r (List.mem_cons_of_mem p hr) hrp (hdiv.trans hdvd)
      change isSmooth ps (strip 64 p m) = true ↔
        m ∈ Nat.factoredNumbers (p :: ps).toFinset
      exact (ih hps' htail).trans
        (by simpa only [List.toFinset_cons] using
          strip_factored_iff (Or.inl hp) 64 ps.toFinset (Or.inr (Or.inr (Or.inr hb))))
    · have htail : m = 0 ∨ ∀ r ∈ ps, r.Prime → ¬r ^ 65 ∣ m := by
        right
        intro r hr
        exact (hbound.resolve_left hm0) r (List.mem_cons_of_mem p hr)
      change isSmooth ps (strip 64 p m) = true ↔ _
      rw [strip_small hp]
      simpa only [List.toFinset_cons, Nat.factoredNumbers_insert ps.toFinset (N := p) (by
        intro hprime
        have := hprime.two_le
        omega)] using ih hps' htail

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

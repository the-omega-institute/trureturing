/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Enumeration
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Bounded weighted enumeration of smooth multiples. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic

/-! Correctness of the bounded weighted folds defining the certificate enumerations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset

/-- The recursive power fold enumerates precisely the bounded exponent interval. -/
theorem powSum_eq_sum_range (n : ℕ) (f : ℕ → ℕ) {p X c : ℕ} :
    powSum n f p X c = (∑ e ∈ range n, if c * p ^ e ≤ X then f (c * p ^ e) else 0) ↔
      n ≤ 1 ∨ 1 ≤ p ∨ c ≤ X ∨ f 0 = 0 := by
  constructor
  · intro heq
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    by_cases hp : 1 ≤ p
    · exact Or.inr (Or.inl hp)
    by_cases hc : c ≤ X
    · exact Or.inr (Or.inr (Or.inl hc))
    have hp0 : p = 0 := by omega
    have hz : powSum n f p X c = 0 := by
      cases n with
      | zero => rfl
      | succ n => simp [powSum, hc]
    rw [hz] at heq
    have hf := (sum_eq_zero_iff.mp heq.symm) 1 (mem_range.mpr (by omega))
    exact Or.inr (Or.inr (Or.inr (by simpa [hp0] using hf)))
  · intro h
    by_cases hp : n ≤ 1 ∨ 1 ≤ p ∨ c ≤ X
    · clear h
      rcases hp with hn | hp
      · interval_cases n <;> simp [powSum]
      induction n generalizing c with
      | zero => simp [powSum]
      | succ n ih =>
        change (if c ≤ X then f c + powSum n f p X (c * p) else 0) = _
        conv_rhs => rw [sum_range_succ', add_comm]
        by_cases hc : c ≤ X
        · have hp' : 1 ≤ p ∨ c * p ≤ X := by
            by_cases hz : p = 0
            · simp [hz]
            · exact Or.inl (by omega)
          rw [if_pos hc, ih hp']
          simp only [pow_zero, mul_one, if_pos hc]
          congr 1
          apply sum_congr rfl
          intro e _
          rw [pow_succ]
          congr 2 <;> ring
        · have hp1 : 1 ≤ p := hp.resolve_right hc
          rw [if_neg hc]
          symm
          apply add_eq_zero.mpr
          constructor
          · simp [hc]
          · apply sum_eq_zero
            intro e _
            apply if_neg
            have hpow : 1 ≤ p ^ (e + 1) := one_le_pow₀ hp1
            have hle : c ≤ c * p ^ (e + 1) := by nlinarith
            omega
    · have hn : ¬n ≤ 1 := fun hn => hp (Or.inl hn)
      have hp0 : p = 0 := by
        by_contra hp0
        exact hp (Or.inr (Or.inl (Nat.pos_of_ne_zero hp0)))
      have hc : ¬c ≤ X := fun hc => hp (Or.inr (Or.inr hc))
      have hf : f 0 = 0 := by rcases h with h | h | h | h <;> simp_all
      cases n with
      | zero => omega
      | succ n =>
        simp only [powSum, if_neg hc]
        symm
        apply sum_eq_zero
        intro e _
        cases e with
        | zero => simp [hc]
        | succ e => simp [hp0, hf]

/-- Bounded positive multiples whose quotient has its prime support in `s`. -/
def factoredMultiples (s : Finset ℕ) (X c : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun m => c ∣ m ∧ m / c ∈ Nat.factoredNumbers s

/-- The prime-power branches partition bounded smooth multiples without repetition. -/
theorem sum_factoredMultiples_insert (w : ℕ → ℕ) (N : ℕ) {s : Finset ℕ} {p X c : ℕ}
    (hp : p.Prime) (hps : p ∉ s) (hX : c = 0 ∨ X < c * p ^ N) :
    (∑ e ∈ range N, ∑ m ∈ factoredMultiples s X (c * p ^ e), w m) =
      ∑ m ∈ factoredMultiples (insert p s) X c, w m := by
  by_cases hc0 : c = 0
  · subst c
    have hz (s : Finset ℕ) : factoredMultiples s X 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmI, hd, _⟩ := mem_filter.mp hm
      have hm0 : m = 0 := by simpa using hd
      have hmpos := (mem_Icc.mp hmI).1
      omega
    simp only [zero_mul, hz, sum_empty, sum_const_zero]
  have hc : 0 < c := by omega
  have hX := hX.resolve_left hc0
  let E := Nat.equivProdNatFactoredNumbers hp hps
  have hquot (e m : ℕ) (hd : c * p ^ e ∣ m) :
      m / c = p ^ e * (m / (c * p ^ e)) := by
    obtain ⟨k, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (mul_pos hc (pow_pos hp.pos _)), mul_assoc,
      Nat.mul_div_cancel_left _ hc]
  rw [sum_sigma']
  refine sum_bij (fun x _ => x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨e, m⟩ hx
    obtain ⟨_, hm⟩ := mem_sigma.mp hx
    obtain ⟨hmI, hdiv, hfact⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hmI, dvd_trans (dvd_mul_right c (p ^ e)) hdiv, ?_⟩
    rw [hquot e m hdiv]
    exact Nat.pow_mul_mem_factoredNumbers hp e hfact
  · intro a ha b hb hab
    have ha' := (mem_filter.mp (mem_sigma.mp ha).2).2
    have hb' := (mem_filter.mp (mem_sigma.mp hb).2).2
    have heq : E (a.1, ⟨a.2 / (c * p ^ a.1), ha'.2⟩) =
        E (b.1, ⟨b.2 / (c * p ^ b.1), hb'.2⟩) := by
      apply Subtype.ext
      change p ^ a.1 * (a.2 / (c * p ^ a.1)) =
        p ^ b.1 * (b.2 / (c * p ^ b.1))
      rw [← hquot _ _ ha'.1, ← hquot _ _ hb'.1, hab]
    have he : a.1 = b.1 := congrArg Prod.fst (E.injective heq)
    exact Sigma.ext he (heq_of_eq hab)
  · intro m hm
    obtain ⟨hmI, hcm, hfact⟩ := mem_filter.mp hm
    let x := E.symm ⟨m / c, hfact⟩
    have hprod : p ^ x.1 * x.2.val = m / c := by
      exact congrArg Subtype.val (E.apply_symm_apply ⟨m / c, hfact⟩)
    have hmul : c * (p ^ x.1 * x.2.val) = m := by
      rw [hprod, Nat.mul_div_cancel' hcm]
    have hr : 0 < x.2.val := Nat.pos_of_ne_zero x.2.property.1
    have hpow : c * p ^ x.1 ≤ m := by
      calc
        c * p ^ x.1 ≤ c * (p ^ x.1 * x.2.val) :=
          Nat.mul_le_mul_left c (Nat.le_mul_of_pos_right _ hr)
        _ = m := hmul
    have he : x.1 < N := by
      by_contra hn
      have hN : c * p ^ N ≤ c * p ^ x.1 :=
        Nat.mul_le_mul_left c (pow_le_pow_right' hp.one_lt.le (by omega))
      have hmX := (mem_Icc.mp hmI).2
      omega
    have hdiv : c * p ^ x.1 ∣ m := ⟨x.2.val, by simpa [mul_assoc] using hmul.symm⟩
    have hquotx : m / (c * p ^ x.1) = x.2.val := by
      rw [← hmul, ← mul_assoc,
        Nat.mul_div_cancel_left _ (mul_pos hc (pow_pos hp.pos _))]
    refine ⟨⟨x.1, m⟩, mem_sigma.mpr ⟨mem_range.mpr he, ?_⟩, rfl⟩
    exact mem_filter.mpr ⟨hmI, hdiv, by simpa only [hquotx] using x.2.property⟩

/-- The smooth fold is the weighted sum of bounded multiples with the prescribed support. -/
theorem smoothSum_eq_sum (w : ℕ → ℕ) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) {X c : ℕ}
    (hc : 0 < c ∨ w 0 = 0) (hcx : ps = [] → c ≤ X ∨ w c = 0)
    (hX : c = 0 ∨ ∀ p ∈ ps, X < c * p ^ 64) :
    smoothSum w ps X c = ∑ m ∈ factoredMultiples ps.toFinset X c, w m := by
  by_cases hc0 : c = 0
  · subst c
    have hw : w 0 = 0 := hc.resolve_left (by omega)
    have hsum (qs : List ℕ) : smoothSum w qs X 0 = 0 := by
      induction qs with
      | nil => exact hw
      | cons p qs ih =>
        change powSum 64 (fun c' => smoothSum w qs X c') p X 0 = 0
        have hpow (n : ℕ) : powSum n (fun c' => smoothSum w qs X c') p X 0 = 0 := by
          induction n with
          | zero => rfl
          | succ n ihn =>
            change (if 0 ≤ X then smoothSum w qs X 0 +
              powSum n (fun c' => smoothSum w qs X c') p X (0 * p) else 0) = 0
            simpa only [Nat.zero_le, ite_true, zero_mul, ih, zero_add] using ihn
        exact hpow 64
    have hset : factoredMultiples ps.toFinset X 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmI, hd, _⟩ := mem_filter.mp hm
      have hm0 : m = 0 := by simpa using hd
      have hmpos := (mem_Icc.mp hmI).1
      omega
    simp only [hsum, hset, sum_empty]
  replace hc : 0 < c := by omega
  replace hX := hX.resolve_left hc0
  clear hc0
  induction ps generalizing c with
  | nil =>
    by_cases hle : c ≤ X
    · have hcx := hle
      have heq : factoredMultiples ∅ X c = {c} := by
        ext m
        constructor
        · intro hm
          obtain ⟨_, hd, hfact⟩ := mem_filter.mp hm
          have hquot : m / c = 1 := by
            simpa only [Nat.factoredNumbers_empty, Set.mem_singleton_iff] using hfact
          have hmc : c = m := by
            simpa only [hquot, mul_one] using Nat.mul_div_cancel' hd
          simpa only [mem_singleton] using hmc.symm
        · intro hm
          have hmc : m = c := mem_singleton.mp hm
          subst m
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hc, hcx⟩, dvd_refl c, ?_⟩
          simp [Nat.factoredNumbers_empty, Nat.div_self hc]
      simpa only [smoothSum, List.toFinset_nil, heq, sum_singleton]
    · have hw : w c = 0 := (hcx rfl).resolve_left hle
      have hempty : factoredMultiples (∅ : Finset ℕ) X c = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hmI, hd, _⟩ := mem_filter.mp hm
        have hmpos : 0 < m := (mem_Icc.mp hmI).1
        have hmX := (mem_Icc.mp hmI).2
        have := Nat.le_of_dvd hmpos hd
        omega
      simp only [smoothSum, hw, List.toFinset_nil, hempty, sum_empty]
  | cons p ps ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    have hp := hprime p List.mem_cons_self
    have htail : ∀ r ∈ ps, r.Prime := fun r hr => hprime r (List.mem_cons_of_mem p hr)
    change powSum 64 (fun c' => smoothSum w ps X c') p X c = _
    have hX' : X < c * p ^ 64 := hX p List.mem_cons_self
    rw [(powSum_eq_sum_range _ _).mpr (Or.inr (Or.inl hp.one_lt.le)), List.toFinset_cons,
      ← sum_factoredMultiples_insert w 64 hp (by simpa using hnot) (Or.inr hX')]
    apply sum_congr rfl
    intro e _
    by_cases he : c * p ^ e ≤ X
    · rw [if_pos he]
      apply ih htail hnodup (fun _ => Or.inl he) (mul_pos hc (pow_pos hp.pos e))
      intro r hr
      exact (hX r (List.mem_cons_of_mem p hr)).trans_le
        (Nat.mul_le_mul_right (r ^ 64) (Nat.le_mul_of_pos_right c (pow_pos hp.pos e)))
    · rw [if_neg he]
      have hempty : factoredMultiples ps.toFinset X (c * p ^ e) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro m hm
        obtain ⟨hmI, hd, _⟩ := mem_filter.mp hm
        have hmpos : 0 < m := (mem_Icc.mp hmI).1
        have hmX := (mem_Icc.mp hmI).2
        have hle := Nat.le_of_dvd hmpos hd
        omega
      simp only [hempty, sum_empty]

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

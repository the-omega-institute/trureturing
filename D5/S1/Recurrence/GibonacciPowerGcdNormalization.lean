/- GID: D5/S1/Recurrence/GibonacciPowerGcdNormalization
   generality: I
   mirror-B: D5/B/S1/Recurrence/GibonacciPowerGcdNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.FrobeniusNumber, mathlib/module/Mathlib.NumberTheory.Real.GoldenRatio]
   utility: none
   digest: Signed Gibonacci power-window infinite gcds scale by the power of seed content. -/

import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
Mbirika--Spilker, arXiv:2204.12626v2, Section 6.1, Question 6.2.
The window uses exactly indices t+1 through t+k, with every natural t.
Nat.setGcd supplies the gcd of the full range of absolute window sums.
No nonzero-window assumption is imposed. All exponents in the source domain,
including odd exponents, and either individual zero seed are retained.
All declarations are unrestricted algebraic constructions or proofs, rather
than finite enumeration, checkers, numerical reductions or certified instances.
-/

namespace D5.S1.Recurrence.GibonacciPowerGcdNormalization

/-- The integer solution of the Fibonacci recurrence with the specified seeds. -/
def gibonacci (a b : ℤ) : ℕ → ℤ :=
  (Real.fibRec : LinearRecurrence ℤ).mkSol ![a, b]

/-- The source window, including both endpoints 1 and k. -/
def windowSum (a b : ℤ) (k e t : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc 1 k, gibonacci a b (t + i) ^ e

/-- Nonnegative gcd of an entire integer family, using Mathlib's set gcd. -/
noncomputable def familyGcd (f : ℕ → ℤ) : ℤ :=
  (Nat.setGcd (Set.range fun t => (f t).natAbs) : ℤ)

/-- The full infinite-window gcd in Question 6.2. -/
noncomputable def powerGcd (a b : ℤ) (k e : ℕ) : ℤ :=
  familyGcd (windowSum a b k e)

private theorem familyGcd_nonneg (f : ℕ → ℤ) : 0 ≤ familyGcd f :=
  Int.natCast_nonneg _

private theorem familyGcd_spec (f : ℕ → ℤ) (r : ℤ) :
    r ∣ familyGcd f ↔ ∀ t : ℕ, r ∣ f t := by
  unfold familyGcd
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, Nat.dvd_setGcd_iff]
  simp only [Set.forall_mem_range, Int.natAbs_dvd_natAbs]

private theorem familyGcd_scale (f : ℕ → ℤ) (c : ℤ) (hc : 0 < c) :
    familyGcd (fun t => c * f t) = c * familyGcd f := by
  let g := familyGcd (fun t => c * f t)
  have hcg : c ∣ g :=
    (familyGcd_spec _ c).mpr fun t => dvd_mul_right c (f t)
  obtain ⟨q, hq⟩ := hcg
  have hqf : ∀ t, q ∣ f t := by
    intro t
    have h := (familyGcd_spec _ g).mp (dvd_refl g) t
    rw [hq] at h
    exact (mul_dvd_mul_iff_left (ne_of_gt hc)).mp h
  apply Int.dvd_antisymm (familyGcd_nonneg _) (mul_nonneg hc.le (familyGcd_nonneg _))
  · change g ∣ _
    rw [hq]
    exact mul_dvd_mul_left c ((familyGcd_spec f q).mpr hqf)
  · apply (familyGcd_spec _ _).mpr
    intro t
    exact mul_dvd_mul_left c ((familyGcd_spec f _).mp (dvd_refl _) t)

private theorem gibonacci_spec (a b : ℤ) :
    gibonacci a b 0 = a ∧ gibonacci a b 1 = b ∧
      ∀ n, gibonacci a b (n + 2) = gibonacci a b (n + 1) + gibonacci a b n := by
  refine ⟨?_, ?_, ?_⟩
  · simp [gibonacci, LinearRecurrence.mkSol, Real.fibRec]
  · simp [gibonacci, LinearRecurrence.mkSol, Real.fibRec]
  · intro n
    have h := (Real.fibRec : LinearRecurrence ℤ).is_sol_mkSol ![a, b] n
    change gibonacci a b (n + 2) =
      ∑ i : Fin 2, (![1, 1] : Fin 2 → ℤ) i * gibonacci a b (n + i) at h
    simpa [Fin.sum_univ_two, add_comm] using h

private theorem gibonacci_scale (a b c : ℤ) (n : ℕ) :
    gibonacci (c * a) (c * b) n = c * gibonacci a b n := by
  have hinit : c • (![a, b] : Fin 2 → ℤ) = ![c * a, c * b] := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]
  have h := congrArg (fun u : (Real.fibRec : LinearRecurrence ℤ).solSpace =>
    (u : ℕ → ℤ) n)
    ((Real.fibRec : LinearRecurrence ℤ).toInit.symm.map_smul c ![a, b])
  change (Real.fibRec : LinearRecurrence ℤ).mkSol
    (c • (![a, b] : Fin 2 → ℤ)) n = c * gibonacci a b n at h
  rw [hinit] at h
  exact h

private theorem windowSum_scale (a b c : ℤ) (k e t : ℕ) :
    windowSum (c * a) (c * b) k e t = c ^ e * windowSum a b k e t := by
  simp only [windowSum, gibonacci_scale, mul_pow, Finset.mul_sum]

/-- The whole signed infinite-window assertion, with its source and gcd specifications. -/
theorem result (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (e : ℕ) (he : 3 ≤ e) :
    let d : ℤ := Int.gcd a b
    0 < d ∧
    d * (a / d) = a ∧ d * (b / d) = b ∧
    Int.gcd (a / d) (b / d) = 1 ∧
    (gibonacci a b 0 = a ∧ gibonacci a b 1 = b ∧
      ∀ n, gibonacci a b (n + 2) = gibonacci a b (n + 1) + gibonacci a b n) ∧
    (gibonacci (a / d) (b / d) 0 = a / d ∧
      gibonacci (a / d) (b / d) 1 = b / d ∧
      ∀ n, gibonacci (a / d) (b / d) (n + 2) =
        gibonacci (a / d) (b / d) (n + 1) + gibonacci (a / d) (b / d) n) ∧
    0 ≤ powerGcd a b k e ∧ 0 ≤ powerGcd (a / d) (b / d) k e ∧
    (∀ r : ℤ, r ∣ powerGcd a b k e ↔ ∀ t : ℕ, r ∣ windowSum a b k e t) ∧
    (∀ r : ℤ, r ∣ powerGcd (a / d) (b / d) k e ↔
      ∀ t : ℕ, r ∣ windowSum (a / d) (b / d) k e t) ∧
    powerGcd a b k e = d ^ e * powerGcd (a / d) (b / d) k e := by
  dsimp only
  let d : ℤ := Int.gcd a b
  have hd : 0 < d := by
    change (0 : ℤ) < (Int.gcd a b : ℤ)
    exact_mod_cast (Int.gcd_pos_iff.mpr hab)
  have ha : d * (a / d) = a := by
    simpa [d, mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb : d * (b / d) = b := by
    simpa [d, mul_comm] using Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  refine ⟨hd, ha, hb, Int.gcd_ediv_gcd_ediv_gcd (Int.gcd_pos_iff.mpr hab),
    gibonacci_spec a b, gibonacci_spec (a / d) (b / d),
    familyGcd_nonneg _, familyGcd_nonneg _, familyGcd_spec _, familyGcd_spec _, ?_⟩
  change familyGcd (windowSum a b k e) = d ^ e * familyGcd (windowSum (a / d) (b / d) k e)
  have hw : windowSum a b k e = fun t => d ^ e * windowSum (a / d) (b / d) k e t := by
    funext t
    calc
      windowSum a b k e t = windowSum (d * (a / d)) (d * (b / d)) k e t := by
        rw [ha, hb]
      _ = d ^ e * windowSum (a / d) (b / d) k e t :=
        windowSum_scale (a / d) (b / d) d k e t
  rw [hw]
  exact familyGcd_scale _ _ (pow_pos hd e)

#check @result
#print axioms result

end D5.S1.Recurrence.GibonacciPowerGcdNormalization

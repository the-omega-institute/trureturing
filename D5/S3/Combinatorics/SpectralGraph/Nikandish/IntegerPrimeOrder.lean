/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/IntegerPrimeOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integer prime orders and cancellation of a unique lowest order term. -/
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! General prime-power cancellation used by the full received shared-prime
root theorem. Zero has no exact order. Bounds on a remainder do allow zero.
These are symbolic integer lemmas, with no finite enumeration. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.IntegerPrimeOrder

def ExactOrder (p n : ℕ) (x : ℤ) : Prop :=
  (p : ℤ)^n ∣ x ∧ ¬(p : ℤ)^(n+1) ∣ x

theorem exact_valuation (p : ℕ) [Fact p.Prime] (x : ℤ) (hx : x ≠ 0) :
    ExactOrder p (padicValInt p x) x := by
  refine ⟨padicValInt_dvd x, ?_⟩
  rw [padicValInt_dvd_iff]
  omega

theorem valuation_of_exact (p n : ℕ) [Fact p.Prime] (x : ℤ)
    (h : ExactOrder p n x) : x ≠ 0 ∧ padicValInt p x = n := by
  have hx : x ≠ 0 := by intro hz; exact h.2 (hz ▸ dvd_zero _)
  have h1 := (padicValInt_dvd_iff n x).mp h.1
  have h2 := (padicValInt_dvd_iff (n+1) x).not.mp h.2
  exact ⟨hx, by omega⟩

theorem scaled_unit (p n : ℕ) [hp : Fact p.Prime] (u : ℤ)
    (hu : ¬(p : ℤ) ∣ u) : ExactOrder p n ((p : ℤ)^n*u) := by
  refine ⟨dvd_mul_right _ _, ?_⟩
  rintro ⟨v,hv⟩
  apply hu
  refine ⟨v, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero n (Int.natCast_ne_zero.mpr hp.out.ne_zero))
  calc
    (p : ℤ)^n*u = (p : ℤ)^(n+1)*v := hv
    _ = (p : ℤ)^n*((p : ℤ)*v) := by rw [pow_succ]; ring

theorem unit_decomposition (p n : ℕ) [Fact p.Prime] (x : ℤ)
    (h : ExactOrder p n x) :
    ∃ u : ℤ, x = (p : ℤ)^n*u ∧ ¬(p : ℤ) ∣ u := by
  obtain ⟨u,hu⟩ := h.1
  refine ⟨u,hu,?_⟩
  rintro ⟨v,hv⟩
  apply h.2
  refine ⟨v,?_⟩
  rw [hu,hv,pow_succ]
  ring

theorem unit_order (p : ℕ) (x : ℤ) (h : ¬(p : ℤ) ∣ x) : ExactOrder p 0 x := by
  simpa [ExactOrder] using And.intro (one_dvd x) h

theorem mul_order (p n m : ℕ) [hp : Fact p.Prime] (x y : ℤ)
    (hx : ExactOrder p n x) (hy : ExactOrder p m y) :
    ExactOrder p (n+m) (x*y) := by
  obtain ⟨u,hu,hu0⟩ := unit_decomposition p n x hx
  obtain ⟨v,hv,hv0⟩ := unit_decomposition p m y hy
  have huv : ¬(p : ℤ) ∣ u*v := by
    intro hd
    rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_mul.mp hd with h | h
    · exact hu0 h
    · exact hv0 h
  have he : x*y = (p : ℤ)^(n+m)*(u*v) := by rw [hu,hv,pow_add]; ring
  rw [he]
  exact scaled_unit p (n+m) (u*v) huv

theorem pow_order (p n k : ℕ) [Fact p.Prime] (x : ℤ)
    (hx : ExactOrder p n x) : ExactOrder p (n*k) (x^k) := by
  induction k with
  | zero => simpa [ExactOrder] using (unit_order p 1 (by
      exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one))
  | succ k ih => simpa [pow_succ,Nat.mul_succ] using mul_order p (n*k) n (x^k) x ih hx

theorem neg_order (p n : ℕ) (x : ℤ) (h : ExactOrder p n x) :
    ExactOrder p n (-x) := by simpa [ExactOrder] using h

theorem lower_power (p n m : ℕ) (x : ℤ) (hn : n ≤ m)
    (hx : (p : ℤ)^m ∣ x) : (p : ℤ)^n ∣ x :=
  (pow_dvd_pow (p : ℤ) hn).trans hx

theorem monomial_dvd (p e r t i j k N : ℕ) (h b c z : ℤ)
    (hh : (p : ℤ)^e ∣ h) (hb : (p : ℤ)^r ∣ b) (hc : (p : ℤ)^t ∣ c)
    (hN : N ≤ e*i+r*j+t*k) : (p : ℤ)^N ∣ h^i*b^j*c^k*z := by
  apply lower_power p N (e*i+r*j+t*k) _ hN
  have h1 : (p : ℤ)^(e*i) ∣ h^i := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hh i
  have h2 : (p : ℤ)^(r*j) ∣ b^j := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hb j
  have h3 : (p : ℤ)^(t*k) ∣ c^k := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hc k
  have hd := mul_dvd_mul (mul_dvd_mul h1 h2) h3
  have hd' : (p : ℤ)^(e*i+r*j+t*k) ∣ h^i*b^j*c^k := by
    simpa [pow_add] using hd
  exact dvd_mul_of_dvd_left hd' z

theorem cancel_power (p n : ℕ) [Fact p.Prime] (x : ℤ)
    (hx : (p : ℤ)^(n+1) ∣ (p : ℤ)^n*x) : (p : ℤ) ∣ x := by
  by_contra hn
  exact (scaled_unit p n x hn).2 hx

theorem add_high (p n : ℕ) (x y : ℤ) (hx : ExactOrder p n x)
    (hy : (p : ℤ)^(n+1) ∣ y) : ExactOrder p n (x+y) := by
  refine ⟨dvd_add hx.1 (lower_power p n (n+1) y (by omega) hy), ?_⟩
  intro hd
  exact hx.2 ((dvd_add_left hy).mp hd)

theorem equal_of_high_remainder (p n m : ℕ) (x y r : ℤ)
    (hx : ExactOrder p n x) (hy : ExactOrder p m y)
    (hr : (p : ℤ)^(n+1) ∣ r) (he : x+y+r=0) : n=m := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have hy' := lower_power p (n+1) m y (by omega) hy.1
    have hz : (p : ℤ)^(n+1) ∣ x := by
      have hs := dvd_add hy' hr
      have he' : y+r = -x := by linarith
      rwa [he',dvd_neg] at hs
    exact hx.2 hz
  · have hx' := lower_power p (m+1) n x (by omega) hx.1
    have hr' := lower_power p (m+1) (n+1) r (by omega) hr
    have hz : (p : ℤ)^(m+1) ∣ y := by
      have hs := dvd_add hx' hr'
      have he' : x+r = -y := by linarith
      rwa [he',dvd_neg] at hs
    exact hy.2 hz

end D5.S3.Combinatorics.SpectralGraph.IntegerPrimeOrder

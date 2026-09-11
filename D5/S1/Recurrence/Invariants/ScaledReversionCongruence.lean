/- GID: D5/S1/Recurrence/Invariants/ScaledReversionCongruence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/ScaledReversionCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Scaled reversion has a unique integral solution congruent to the geometric series. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

open PowerSeries
namespace D5.S1.Recurrence.Invariants.ScaledReversionCongruence
variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem coeff_pow_zero {f : PowerSeries R} (h : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) k) n hn

private theorem coeff_pow_diag {f : PowerSeries R} (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1) (n : ℕ) : coeff n (f ^ n) = 1 := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr h0
  have hu : constantCoeff u = 1 := by simpa using h1
  simp [mul_pow, coeff_X_pow_mul', hu]

private theorem agree_subst_inner {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) (a : PowerSeries R) : Agree d (a.subst f) (a.subst g) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hf), coeff_subst' (.of_constantCoeff_zero hg)]
  apply finsum_congr
  intro k
  rw [agree_pow h k n hn]

private theorem subst_first_difference {d : ℕ} {a b f : PowerSeries R}
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) (h : Agree d a b)
    (n : ℕ) (hn : n < d + 1) :
    coeff n ((a - b).subst f) = coeff n (a - b) := by
  rw [coeff_subst' (.of_constantCoeff_zero h0)]
  rw [finsum_eq_single _ n]
  · rw [coeff_pow_diag h0 h1, smul_eq_mul, mul_one]
  · intro k hk
    by_cases hkn : k < n
    · have hab : coeff k (a - b) = 0 := by
        rw [map_sub, h k (by omega), sub_self]
      rw [hab, zero_smul]
    · rw [coeff_pow_zero h0 (by omega : n < k), smul_zero]

private noncomputable def argument (r : R) (f : PowerSeries R) : PowerSeries R :=
  X - X ^ 2 * mk (fun n => r ^ n * coeff (n + 1) f)

private theorem argument_zero (r : R) (f : PowerSeries R) :
    constantCoeff (argument r f) = 0 := by simp [argument]

private theorem argument_one (r : R) (f : PowerSeries R) :
    coeff 1 (argument r f) = 1 := by simp [argument, coeff_X_pow_mul']

private theorem argument_agree (r : R) {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (argument r f) (argument r g) := by
  intro n hn
  simp only [argument, map_sub, coeff_X_pow_mul']
  by_cases h2 : 2 ≤ n
  · simp only [if_pos h2, coeff_mk]
    rw [h (n - 2 + 1) (by omega)]
  · simp only [if_neg h2]

private noncomputable def step (r : R) (f : PowerSeries R) : PowerSeries R :=
  f + X - f.subst (argument r f)

private theorem step_agree (r : R) {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (step r f) (step r g) := by
  intro n hn
  have hi := agree_subst_inner (argument_zero r f) (argument_zero r g)
    (argument_agree r h) f n hn
  have ho := subst_first_difference (argument_zero r g) (argument_one r g) h n hn
  rw [subst_sub (.of_constantCoeff_zero (argument_zero r g)), map_sub, map_sub] at ho
  simp only [step, map_sub, map_add]
  rw [hi]
  linear_combination -ho

private theorem solution_unique (r : R) {f g : PowerSeries R}
    (hf : f.subst (argument r f) = X) (hg : g.subst (argument r g) = X) : f = g := by
  have hsf : step r f = f := by simp [step, hf]
  have hsg : step r g = g := by simp [step, hg]
  have hall : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [hsf, hsg] using step_agree r ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation (r : R) : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => step r (approximation r k)

private theorem approximation_stable (r : R) {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation r d) (approximation r k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree r (ih (by omega))

private noncomputable def solution (r : R) : PowerSeries R :=
  mk (fun n => coeff n (approximation r (n + 1)))

private theorem solution_agree (r : R) (d : ℕ) :
    Agree d (solution r) (approximation r d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable r (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_equation (r : R) :
    (solution r).subst (argument r (solution r)) = X := by
  have hf : solution r = step r (solution r) := by
    ext n
    have hg := solution_agree r (n + 2) n (by omega)
    have hs := step_agree r (solution_agree r (n + 1)) n (by omega)
    exact hg.trans hs.symm
  dsimp [step] at hf
  linear_combination hf

private theorem subst_zero_series (f : PowerSeries R) : (0 : PowerSeries R).subst f = 0 := by
  simpa only [map_zero] using (subst_C (a := f) (0 : R))

private theorem approximation_one (r : R) : approximation r 1 = X := by
  simp [approximation, step, subst_zero_series]

private theorem solution_zero (r : R) : constantCoeff (solution r) = 0 := by
  have h := solution_agree r 1 0 (by omega)
  simpa [approximation_one, coeff_zero_eq_constantCoeff] using h

private theorem solution_one (r : R) : coeff 1 (solution r) = 1 := by
  have h := solution_agree r 2 1 (by omega)
  change coeff 1 (solution r) = coeff 1 (step r (approximation r 1)) at h
  rw [approximation_one, step, subst_X (.of_constantCoeff_zero (argument_zero r X))] at h
  simpa [argument_one] using h

private theorem map_argument {S : Type*} [CommRing S] (hom : R →+* S)
    (r : R) (f : PowerSeries R) :
    (argument r f).map hom = argument (hom r) (f.map hom) := by
  simp only [argument, map_sub, map_mul, map_pow, map_X]
  congr 2
  ext n
  simp [coeff_map]

private noncomputable def geometric : PowerSeries R := X * mk 1

private theorem geometric_argument :
    argument (-1 : R) geometric = X * rescale (-1) (mk 1) := by
  have hm := congrArg (rescale (-1 : R)) (mk_one_mul_one_sub_eq_one R)
  have ht : mk (fun n => (-1 : R) ^ n * coeff (n + 1) (geometric : PowerSeries R)) =
      rescale (-1) (mk 1) := by
    ext n
    simp [geometric]
  rw [argument, ht]
  simp at hm
  linear_combination -X * hm

private theorem geometric_equation :
    (geometric : PowerSeries R).subst (argument (-1 : R) geometric) = X := by
  let c : PowerSeries R := argument (-1) geometric
  have hc0 : constantCoeff c = 0 := argument_zero _ _
  have hs : HasSubst c := .of_constantCoeff_zero hc0
  have hgeom : (geometric : PowerSeries R) * (1 - X) = X := by
    rw [geometric, mul_assoc, mk_one_mul_one_sub_eq_one, mul_one]
  have he := congrArg (subst c) hgeom
  have hone : subst c (1 : PowerSeries R) = 1 := by
    rw [← coe_substAlgHom hs]
    exact map_one _
  have heq : (geometric : PowerSeries R).subst c * (1 - c) = c := by
    simpa only [subst_mul hs, subst_sub hs, subst_X hs, hone] using he
  have hden : c * (1 + X) = X := by
    dsimp [c]
    rw [geometric_argument, mul_assoc]
    have hm := congrArg (rescale (-1 : R)) (mk_one_mul_one_sub_eq_one R)
    have hi : rescale (-1 : R) (mk 1) * (1 + X) = 1 := by simpa using hm
    rw [hi, mul_one]
  have hunit : IsUnit (1 - c) := by
    rw [isUnit_iff_constantCoeff]
    simp [hc0]
  apply hunit.mul_right_cancel
  change geometric.subst c * (1 - c) = X * (1 - c)
  rw [heq]
  linear_combination hden

private theorem argument_rescale (r : R) (f : PowerSeries R)
    (h0 : constantCoeff f = 0) :
    C r * (X - argument r f) = X * rescale r f := by
  simp only [argument, sub_sub_cancel]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [coeff_C_mul, coeff_X_pow_mul', h0]
    | succ n =>
      simp [coeff_C_mul, pow_succ, mul_assoc, mul_left_comm]

noncomputable def a (q n : ℕ) : ℤ :=
  coeff n (approximation (q : ℤ) (n + 1))

noncomputable def generatingSeries (q : ℕ) : PowerSeries ℤ := mk (a q)

noncomputable def inner (q : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  argument (q : ℤ) f

theorem generating_equation (q : ℕ) :
    (generatingSeries q).subst (inner q (generatingSeries q)) = X ∧
    constantCoeff (generatingSeries q) = 0 ∧ coeff 1 (generatingSeries q) = 1 ∧
    C (q : ℤ) * (X - inner q (generatingSeries q)) =
      X * rescale (q : ℤ) (generatingSeries q) :=
  ⟨solution_equation (q : ℤ), solution_zero (q : ℤ), solution_one (q : ℤ),
    argument_rescale (q : ℤ) _ (solution_zero (q : ℤ))⟩

theorem generating_unique (q : ℕ) (f : PowerSeries ℤ)
    (hf : f.subst (inner q f) = X) : f = generatingSeries q :=
  solution_unique (q : ℤ) hf (generating_equation q).1

theorem generating_equation_rational (q : ℕ) (hq : 1 ≤ q) :
    let A := (generatingSeries q).map (Int.castRingHom ℚ)
    A.subst (X - C ((q : ℚ)⁻¹) * X * rescale (q : ℚ) A) = X := by
  let hom := Int.castRingHom ℚ
  let A := (generatingSeries q).map hom
  have hz : constantCoeff A = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    change hom (coeff 0 (generatingSeries q)) = 0
    rw [coeff_zero_eq_constantCoeff, (generating_equation q).2.1, map_zero]
  have hr := argument_rescale (q : ℚ) A hz
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hinv : C ((q : ℚ)⁻¹) * C (q : ℚ) = (1 : PowerSeries ℚ) := by
    rw [← map_mul, inv_mul_cancel₀ hq0, map_one]
  have ha : argument (q : ℚ) A = X - C ((q : ℚ)⁻¹) * X * rescale (q : ℚ) A := by
    calc
      argument (q : ℚ) A = X - C ((q : ℚ)⁻¹) * (C (q : ℚ) *
          (X - argument (q : ℚ) A)) := by rw [← mul_assoc, hinv, one_mul, sub_sub_cancel]
      _ = X - C ((q : ℚ)⁻¹) * X * rescale (q : ℚ) A := by rw [hr, mul_assoc]
  have he := congrArg (PowerSeries.map hom) (generating_equation q).1
  have hs : PowerSeries.map hom ((generatingSeries q).subst (inner q (generatingSeries q))) =
      A.subst ((inner q (generatingSeries q)).map hom) :=
    map_subst (.of_constantCoeff_zero (argument_zero (q : ℤ) _)) _
  rw [hs, map_X] at he
  have hi : (inner q (generatingSeries q)).map hom = argument (q : ℚ) A := by
    simpa [inner, hom, A] using map_argument hom (q : ℤ) (generatingSeries q)
  rw [hi, ha] at he
  exact he

theorem coeff_congruence (q : ℕ) (hq : 1 ≤ q) (n : ℕ) (hn : 1 ≤ n) :
    a q n % (q + 1 : ℤ) = 1 := by
  let hom := Int.castRingHom (ZMod (q + 1))
  have hqmod : hom (q : ℤ) = -1 := by
    have h : (q : ZMod (q + 1)) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (ZMod.natCast_self (q + 1))
    simpa [hom] using (eq_neg_iff_add_eq_zero.mpr h)
  have hf : ((generatingSeries q).map hom).subst
      (argument (-1 : ZMod (q + 1)) ((generatingSeries q).map hom)) = X := by
    have he := congrArg (PowerSeries.map hom) (generating_equation q).1
    have hs : PowerSeries.map hom ((generatingSeries q).subst (inner q (generatingSeries q))) =
        ((generatingSeries q).map hom).subst ((inner q (generatingSeries q)).map hom) :=
      map_subst (.of_constantCoeff_zero (argument_zero (q : ℤ) _)) _
    rw [hs, map_X] at he
    simpa only [inner, map_argument, hqmod] using he
  have he := solution_unique (-1 : ZMod (q + 1)) hf geometric_equation
  have hb : coeff n (geometric : PowerSeries (ZMod (q + 1))) = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [geometric]
  have hc : (a q n : ZMod (q + 1)) = 1 := by
    have hec := congrArg (coeff n) he
    simpa [coeff_map, generatingSeries, hb, hom] using hec
  have hr := (ZMod.intCast_eq_intCast_iff' (a q n) 1 (q + 1)).mp hc
  have hmod : (1 : ℤ) % (q + 1 : ℤ) = 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, hmod] using hr

theorem hanna_a393856 (n : ℕ) (hn : 1 ≤ n) : a 4 n % 5 = 1 := by
  simpa using coeff_congruence 4 (by omega) n hn

theorem hanna_a393857 (n : ℕ) (hn : 1 ≤ n) : a 5 n % 6 = 1 := by
  simpa using coeff_congruence 5 (by omega) n hn

#print axioms generating_equation
#print axioms generating_unique
#print axioms generating_equation_rational
#print axioms coeff_congruence
#print axioms hanna_a393856
#print axioms hanna_a393857

end D5.S1.Recurrence.Invariants.ScaledReversionCongruence


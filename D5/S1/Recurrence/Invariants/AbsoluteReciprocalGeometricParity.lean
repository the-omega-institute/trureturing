/- GID: D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Degree contraction and geometric cancellation prove A383377 parity. -/

import Mathlib.RingTheory.PowerSeries.Inverse

open PowerSeries
namespace D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_mul {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have h1 := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) u
  have h2 := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') g
  convert dvd_add h1 h2 using 1
  ring

private theorem pow_low {q : PowerSeries R} (hq : constantCoeff q = 0)
    {n k : ℕ} (h : n < k) : coeff n (q ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hq) k) n h

-- Finite geometric sums agree to arbitrary degree, so their telescoping identity is exact.
private theorem geometric_fixed (F U : PowerSeries R) (hU : U * F = 1)
    (hF : ∀ N, coeff N F = ∑ n ∈ Finset.range (N + 1),
      coeff N (X ^ n * U ^ n)) : F = 1 + X := by
  let q : PowerSeries R := X * U
  have hq : constantCoeff q = 0 := by simp [q]
  have happrox (d : ℕ) : Agree d F (∑ n ∈ Finset.range d, q ^ n) := by
    intro k hk
    rw [map_sum, hF k]
    simp only [q, mul_pow]
    apply Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ d))
    intro n hn hnk
    simpa only [q, mul_pow] using pow_low hq (show k < n by simpa using hnk)
  have hgeom : F * (1 - q) = 1 := by
    ext k
    have h := agree_mul (happrox (k + 1))
      (show Agree (k + 1) (1 - q) (1 - q) from fun _ _ => rfl) k (by omega)
    rw [geom_sum_mul_neg, map_sub, pow_low hq (by omega : k < k + 1), sub_zero] at h
    exact h
  have hqF : F * q = X := by
    dsimp [q]
    calc
      F * (X * U) = X * (U * F) := by ring
      _ = X := by rw [hU, mul_one]
  rw [mul_sub, mul_one, hqF] at hgeom
  exact (sub_eq_iff_eq_add.mp hgeom)

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp h |>.trans
    (sub_dvd_pow_sub_pow f g k))

private theorem agree_inv {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : Agree d f g) : Agree d (invOfUnit f 1) (invOfUnit g 1) := by
  apply (agree_iff _ _ _).mpr
  have he : invOfUnit f 1 - invOfUnit g 1 =
      -(f - g) * (invOfUnit f 1 * invOfUnit g 1) := by
    have hf' := invOfUnit_mul f 1 hf
    have hg' := invOfUnit_mul g 1 hg
    linear_combination invOfUnit g 1 * hf' - invOfUnit f 1 * hg'
  rw [he]
  exact dvd_mul_of_dvd_left (dvd_neg.mpr ((agree_iff _ _ _).mp h)) _

noncomputable def absSeries (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => |coeff n F|)

private theorem agree_abs {d : ℕ} {f g : PowerSeries ℤ}
    (h : Agree d f g) : Agree d (absSeries f) (absSeries g) := by
  intro n hn
  simp only [absSeries, coeff_mk, h n hn]

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun N => ∑ n ∈ Finset.range (N + 1),
    coeff N (X ^ n * absSeries (invOfUnit F 1 ^ n)))

private theorem step_zero (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step, absSeries, constantCoeff_mk]

private theorem step_agree {d : ℕ} {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (h : Agree d f g) : Agree (d + 1) (step f) (step g) := by
  intro N hN
  simp only [step, coeff_mk]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hz : n = 0
  · simp [hz]
  · have hnN : n ≤ N := by simpa using hn
    rw [coeff_X_pow_mul', coeff_X_pow_mul', if_pos hnN, if_pos hnN]
    exact agree_abs (agree_pow (agree_inv hf hg h) n) (N - n) (by omega)

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | depth + 1 => step (approximation depth)

private theorem approximation_zero (depth : ℕ) :
    constantCoeff (approximation depth) = 1 := by
  cases depth with
  | zero => simp [approximation]
  | succ depth => exact step_zero _

private theorem approximation_stable {depth stage : ℕ} (hle : depth ≤ stage) :
    Agree depth (approximation depth) (approximation stage) := by
  induction depth generalizing stage with
  | zero => intro index hi; omega
  | succ depth ih =>
    cases stage with
    | zero => omega
    | succ stage =>
      exact step_agree (approximation_zero depth) (approximation_zero stage)
        (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (depth : ℕ) :
    Agree depth generatingSeries (approximation depth) := by
  intro index hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : index + 1 ≤ depth) index (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N generatingSeries = ∑ n ∈ Finset.range (N + 1),
      coeff N (X ^ n * absSeries (invOfUnit generatingSeries 1 ^ n)) := by
  have hz : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    rw [generating_agree 1 0 (by omega), coeff_zero_eq_constantCoeff]
    exact approximation_zero 1
  refine ⟨hz, fun N => ?_⟩
  have hg := generating_agree (N + 2) N (by omega)
  have hs := step_agree hz (approximation_zero (N + 1))
    (generating_agree (N + 1)) N (by omega)
  simpa only [step, coeff_mk] using hg.trans hs.symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : ∀ N, coeff N B = ∑ n ∈ Finset.range (N + 1),
      coeff N (X ^ n * absSeries (invOfUnit B 1 ^ n))) : B = generatingSeries := by
  have hb : B = step B := by ext N; simpa only [step, coeff_mk] using hB N
  have ha : generatingSeries = step generatingSeries := by
    ext N; simpa only [step, coeff_mk] using generating_equation.2 N
  have h (d : ℕ) : Agree d B generatingSeries := by
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      simpa only [← hb, ← ha] using step_agree h0 generating_equation.1 ih
  ext n
  exact h (n + 1) n (by omega)

private theorem map_abs (P : PowerSeries ℤ) :
    (absSeries P).map (Int.castRingHom (ZMod 2)) = P.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp [coeff_map, absSeries, ZMod.intCast_abs_mod_two]

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) = 1 + X := by
  let hom := Int.castRingHom (ZMod 2)
  let F := generatingSeries.map hom
  let U := (invOfUnit generatingSeries 1).map hom
  have hU : U * F = 1 := by
    simpa only [map_mul, map_one] using
      congrArg (PowerSeries.map hom) (invOfUnit_mul generatingSeries 1 generating_equation.1)
  apply geometric_fixed F U hU
  intro N
  have he := congrArg hom (generating_equation.2 N)
  simpa only [hom, map_sum, ← coeff_map, map_mul, map_pow,
    PowerSeries.map_X, map_abs] using he

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : Even (a n) := by
  apply ZMod.intCast_eq_zero_iff_even.mp
  have he := congrArg (coeff n) mod_two_identity
  simpa [coeff_map, generatingSeries, coeff_one, coeff_X, show n ≠ 0 by omega,
    show n ≠ 1 by omega] using he

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity

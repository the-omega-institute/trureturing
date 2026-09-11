/- GID: D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Absolute reciprocal square contraction and binary Catalan support prove A380710. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

open PowerSeries

namespace D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity

noncomputable def absSeries (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => |coeff n F|)

private def Agree (n : ℕ) (F G : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries ℤ) :
    Agree n F G ↔ (X : PowerSeries ℤ) ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem agree_mul {n : ℕ} {F G U V : PowerSeries ℤ}
    (h : Agree n F G) (h' : Agree n U V) : Agree n (F * U) (G * V) := by
  apply (agree_iff _ _ _).mpr
  have h1 := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) U
  have h2 := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') G
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_abs {n : ℕ} {F G : PowerSeries ℤ} (h : Agree n F G) :
    Agree n (absSeries F) (absSeries G) := by
  intro i hi
  simp only [absSeries, coeff_mk, h i hi]

-- Multiplication by the two inverses transports the difference without losing a degree.
private theorem agree_inv {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree n (invOfUnit F 1) (invOfUnit G 1) := by
  have hFI := mul_invOfUnit F 1 (by simpa using hF)
  have hGI := mul_invOfUnit G 1 (by simpa using hG)
  apply (agree_iff _ _ _).mpr
  have hd := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h)
    (-(invOfUnit F 1 * invOfUnit G 1))
  convert hd using 1
  linear_combination invOfUnit G 1 * hFI - invOfUnit F 1 * hGI

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  1 + X * F * absSeries (invOfUnit (F ^ 2) 1)

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  simp [step]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree (n + 1) (step F) (step G) := by
  have hi := agree_inv (by simp [hF]) (by simp [hG]) (agree_pow h 2)
  have hm := (agree_iff _ _ _).mp (agree_mul h (agree_abs hi))
  apply (agree_iff _ _ _).mpr
  convert mul_dvd_mul_left X hm using 1
  · ring
  · dsimp [step]; ring

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) : constantCoeff (approximation n) = 1 := by
  cases n with
  | zero => simp [approximation]
  | succ n => exact step_constant _

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      exact step_agree (approximation_constant n) (approximation_constant m) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    generatingSeries = 1 + X * generatingSeries *
      absSeries (invOfUnit (generatingSeries ^ 2) 1) := by
  have h0 : constantCoeff generatingSeries = 1 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
      coeff_zero_eq_constantCoeff, approximation_constant]
  refine ⟨h0, ?_⟩
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree h0 (approximation_constant (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : B = 1 + X * B * absSeries (invOfUnit (B ^ 2) 1)) :
    B = generatingSeries := by
  have h : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      have hs := step_agree h0 generating_equation.1 ih
      simpa only [step, ← hB, ← generating_equation.2] using hs
  ext i
  exact h (i + 1) i (by omega)

private theorem map_abs (F : PowerSeries ℤ) :
    (absSeries F).map (Int.castRingHom (ZMod 2)) = F.map (Int.castRingHom (ZMod 2)) := by
  ext n
  simp only [coeff_map, absSeries, coeff_mk]
  by_cases h : 0 ≤ coeff n F
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), map_neg, CharTwo.neg_eq]

private theorem reduced_quadratic :
    (generatingSeries.map (Int.castRingHom (ZMod 2))) ^ 2 =
      generatingSeries.map (Int.castRingHom (ZMod 2)) + X := by
  let hom := Int.castRingHom (ZMod 2)
  let F := generatingSeries.map hom
  let U := (invOfUnit (generatingSeries ^ 2) 1).map hom
  have hE : F = 1 + X * F * U := by
    simpa only [map_add, map_one, map_mul, map_X, hom, map_abs] using
      congrArg (PowerSeries.map hom) generating_equation.2
  have hI : F ^ 2 * U = 1 := by
    have hi := mul_invOfUnit (generatingSeries ^ 2) 1
      (by simp [generating_equation.1])
    simpa only [map_mul, map_pow, map_one] using congrArg (PowerSeries.map hom) hi
  change F ^ 2 = F + X
  calc
    F ^ 2 = F * (1 + X * F * U) := by rw [← hE]; ring
    _ = F + X * (F ^ 2 * U) := by ring
    _ = F + X := by rw [hI, mul_one]

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) =
    1 + CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 2)) := by
  let F := generatingSeries.map (Int.castRingHom (ZMod 2))
  let K := CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 2))
  have hF0 : constantCoeff F = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [F, coeff_map, coeff_zero_eq_constantCoeff, generating_equation.1]
  have hK0 : constantCoeff K = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [K, coeff_map, coeff_zero_eq_constantCoeff,
      CatalanCompositionSquareParity.catalan_equation.1]
  have hK : K = X + K ^ 2 := by
    simpa only [map_add, map_X, map_pow] using
      congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
        CatalanCompositionSquareParity.catalan_equation.2.2
  have hJ : (1 + K) ^ 2 = (1 + K) + X := by
    have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (C (R := ZMod 2)) (CharTwo.two_eq_zero (R := ZMod 2))
    linear_combination -hK + (K - X) * htwo
  have hu : IsUnit (1 - F - (1 + K)) := by
    rw [isUnit_iff_constantCoeff]
    simp [hF0, hK0]
  have he : (1 - F - (1 + K)) * (F - (1 + K)) = (1 - F - (1 + K)) * 0 := by
    linear_combination hJ - reduced_quadratic
  exact sub_eq_zero.mp (hu.mul_left_cancel he)

theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have he := congrArg (coeff n) mod_two_identity
  simp only [coeff_map, generatingSeries, coeff_mk, map_add, coeff_one,
    if_neg (by omega : n ≠ 0), zero_add] at he
  change (a n : ZMod 2) =
    coeff n (CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 2))) at he
  rw [he]
  exact CatalanCompositionSquareParity.binary_catalan n

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.AbsoluteReciprocalSquareParity

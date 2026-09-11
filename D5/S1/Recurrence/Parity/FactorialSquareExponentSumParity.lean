/- GID: D5/S1/Recurrence/Parity/FactorialSquareExponentSumParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/FactorialSquareExponentSumParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Parametric contraction proves Hanna's A222014 parity law via A222013. -/

import D5.S1.Recurrence.Parity.FactorialProductSumCatalanParity

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Parity.FactorialSquareExponentSumParity

variable {R : Type*} [CommRing R]

private noncomputable def denominator (denominatorExponent : ℕ → ℕ → ℕ)
    (r : ℕ) (F : PowerSeries R) : PowerSeries R :=
  ∏ k ∈ Finset.range r,
    (1 + C ((k + 1 : ℕ) : R) * X * F ^ (denominatorExponent r k))

private theorem denominator_constant (denominatorExponent : ℕ → ℕ → ℕ)
    (r : ℕ) (F : PowerSeries R) :
    constantCoeff (denominator denominatorExponent r F) = 1 := by
  simp [denominator]

/-- A factorial-product summand with independent numerator and denominator
exponent functions. This contains both A222013 and A222014 as exact
specializations. -/
noncomputable def parameterizedTerm (numeratorExponent : ℕ → ℕ)
    (denominatorExponent : ℕ → ℕ → ℕ) (r : ℕ)
    (F : PowerSeries R) : PowerSeries R :=
  C (r.factorial : R) * X ^ r * F ^ (numeratorExponent r) *
    invOfUnit (denominator denominatorExponent r F) 1

private theorem parameterized_term_order (numeratorExponent : ℕ → ℕ)
    (denominatorExponent : ℕ → ℕ → ℕ) (r : ℕ)
    (F : PowerSeries R) :
    X ^ r ∣ parameterizedTerm numeratorExponent denominatorExponent r F := by
  refine ⟨C (r.factorial : R) * F ^ (numeratorExponent r) *
    invOfUnit (denominator denominatorExponent r F) 1, ?_⟩
  dsimp [parameterizedTerm]
  ring

/-- The coefficient window is uniform in both exponent functions: the
explicit factor `X ^ r`, rather than any growth condition on the exponents,
forces every coefficient below `r` to vanish. -/
theorem parameterized_term_coeff_eq_zero (numeratorExponent : ℕ → ℕ)
    (denominatorExponent : ℕ → ℕ → ℕ) (r N : ℕ)
    (h : N < r) (F : PowerSeries R) :
    coeff N (parameterizedTerm numeratorExponent denominatorExponent r F) = 0 :=
  X_pow_dvd_iff.mp
    (parameterized_term_order numeratorExponent denominatorExponent r F) N h

-- This verifies that the general term really contains the frozen A222013 term.
private theorem triangular_specialization (r : ℕ) (F : PowerSeries ℤ) :
    parameterizedTerm (fun n ↦ n * (n + 1) / 2) (fun _ k ↦ k + 1) r F =
      FactorialProductSumCatalanParity.term r F := by
  rfl

/-- The A222014 summand, with numerator exponent `r ^ 2` and denominator
exponent `r` in every factor. -/
noncomputable def term (r : ℕ) (F : PowerSeries ℤ) : PowerSeries ℤ :=
  parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) r F

theorem term_coeff_eq_zero (r N : ℕ) (h : N < r) (F : PowerSeries ℤ) :
    coeff N (term r F) = 0 :=
  parameterized_term_coeff_eq_zero _ _ r N h F

private def Agree (n : ℕ) (F G : PowerSeries R) : Prop :=
  ∀ i < n, coeff i F = coeff i G

private theorem agree_iff (n : ℕ) (F G : PowerSeries R) :
    Agree n F G ↔ X ^ n ∣ F - G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_refl (n : ℕ) (F : PowerSeries R) : Agree n F F := by
  intro i hi
  rfl

private theorem agree_add {n : ℕ} {F G H J : PowerSeries R}
    (h : Agree n F G) (h' : Agree n H J) : Agree n (F + H) (G + J) := by
  intro i hi
  simp only [map_add, h i hi, h' i hi]

private theorem agree_mul {n : ℕ} {F G H J : PowerSeries R}
    (h : Agree n F G) (h' : Agree n H J) : Agree n (F * H) (G * J) := by
  apply (agree_iff _ _ _).mpr
  have hd := dvd_add (dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) H)
    (dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') G)
  convert hd using 1
  ring

private theorem agree_pow {n : ℕ} {F G : PowerSeries R}
    (h : Agree n F G) (k : ℕ) : Agree n (F ^ k) (G ^ k) :=
  (agree_iff _ _ _).mpr
    (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G k))

private theorem denominator_agree {n : ℕ} {F G : PowerSeries R}
    (h : Agree n F G) (denominatorExponent : ℕ → ℕ → ℕ) (r : ℕ) :
    Agree n (denominator denominatorExponent r F)
      (denominator denominatorExponent r G) := by
  classical
  simp only [denominator]
  induction Finset.range r using Finset.induction_on with
  | empty => exact agree_refl _ _
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact agree_mul (agree_add (agree_refl _ _)
      (agree_mul (agree_refl _ _) (agree_pow h _))) ih

private theorem inverse_agree {n : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (h : Agree n F G) : Agree n (invOfUnit F 1) (invOfUnit G 1) := by
  have hiF := invOfUnit_mul F 1 hF
  have hiG := mul_invOfUnit G 1 hG
  have he : invOfUnit F 1 - invOfUnit G 1 =
      -(invOfUnit F 1 * (F - G) * invOfUnit G 1) := by
    calc
      invOfUnit F 1 - invOfUnit G 1 =
          invOfUnit F 1 * (G * invOfUnit G 1) -
            (invOfUnit F 1 * F) * invOfUnit G 1 := by
        rw [hiF, hiG, mul_one, one_mul]
      _ = _ := by ring
  apply (agree_iff _ _ _).mpr
  rw [he]
  exact dvd_neg.mpr (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h) _) _)

private theorem parameterized_term_agree {n : ℕ} {F G : PowerSeries R}
    (h : Agree n F G) (numeratorExponent : ℕ → ℕ)
    (denominatorExponent : ℕ → ℕ → ℕ) (r : ℕ) :
    Agree (n + r) (parameterizedTerm numeratorExponent denominatorExponent r F)
      (parameterizedTerm numeratorExponent denominatorExponent r G) := by
  have hb := agree_mul (agree_mul (agree_refl n (C (r.factorial : R)))
    (agree_pow h (numeratorExponent r)))
    (inverse_agree (denominator_constant denominatorExponent r F)
      (denominator_constant denominatorExponent r G)
      (denominator_agree h denominatorExponent r))
  apply (agree_iff _ _ _).mpr
  have hd := mul_dvd_mul_left (X ^ r) ((agree_iff _ _ _).mp hb)
  convert hd using 1
  · rw [← pow_add, Nat.add_comm]
  · dsimp [parameterizedTerm]
    ring

private theorem term_zero (F : PowerSeries R) :
    parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) 0 F = 1 := by
  have hi : invOfUnit (1 : PowerSeries R) 1 = 1 := by
    simpa using mul_invOfUnit (1 : PowerSeries R) 1 (by simp)
  simp [parameterizedTerm, denominator, hi]

private noncomputable def step (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun N ↦ ∑ r ∈ Finset.range (N + 1), coeff N (term r F))

private theorem step_constant (F : PowerSeries ℤ) : constantCoeff (step F) = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [step, term, term_zero]

private theorem step_agree {n : ℕ} {F G : PowerSeries ℤ}
    (h : Agree n F G) : Agree (n + 1) (step F) (step G) := by
  intro i hi
  simp only [step, coeff_mk]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hz : r = 0
  · subst r
    simp [term, term_zero]
  · exact parameterized_term_agree h _ _ r i (by omega)

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | n + 1 => step (approximation n)

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact step_agree (ih (by omega))

/-- The coefficient sequence obtained from the stabilized diagonal of the
finite coefficient windows. -/
noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) :
    Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree (generating_agree (i + 1)) i (by omega)).symm

/-- The coefficientwise formal meaning of the A222014 infinite sum. -/
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ N, coeff N generatingSeries =
      ∑ r ∈ Finset.range (N + 1), coeff N (term r generatingSeries) := by
  refine ⟨?_, ?_⟩
  · rw [generating_fixed]
    exact step_constant _
  · intro N
    simpa only [step, coeff_mk] using congrArg (coeff N) generating_fixed

theorem generating_unique (B : PowerSeries ℤ) (_h0 : constantCoeff B = 1)
    (hB : ∀ N, coeff N B = ∑ r ∈ Finset.range (N + 1), coeff N (term r B)) :
    B = generatingSeries := by
  have hf : B = step B := by
    ext N
    simpa only [step, coeff_mk] using hB N
  have ha : ∀ n, Agree n B generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih => simpa only [← hf, ← generating_fixed] using step_agree ih
  ext i
  exact ha (i + 1) i (by omega)

private theorem map_inverse {S : Type*} [CommRing S] (hom : R →+* S)
    (F : PowerSeries R) (hF : constantCoeff F = 1) :
    (invOfUnit F 1).map hom = invOfUnit (F.map hom) 1 := by
  have hz : constantCoeff (F.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      hF, map_one]
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_left_cancel
  rw [mul_invOfUnit _ 1 hz, ← map_mul, mul_invOfUnit _ 1 hF, map_one]

private theorem map_parameterized_term {S : Type*} [CommRing S] (hom : R →+* S)
    (numeratorExponent : ℕ → ℕ) (denominatorExponent : ℕ → ℕ → ℕ)
    (r : ℕ) (F : PowerSeries R) :
    (parameterizedTerm numeratorExponent denominatorExponent r F).map hom =
      parameterizedTerm numeratorExponent denominatorExponent r (F.map hom) := by
  simp only [parameterizedTerm, map_mul, map_pow]
  rw [map_inverse hom _ (denominator_constant denominatorExponent r F)]
  simp [denominator]

private theorem term_one (F : PowerSeries R) :
    parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) 1 F =
      X * F * invOfUnit (1 + X * F) 1 := by
  simp [parameterizedTerm, denominator]

private theorem term_mod_two_zero (r : ℕ) (hr : 2 ≤ r)
    (F : PowerSeries (ZMod 2)) :
    parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) r F = 0 := by
  have hf : (r.factorial : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial (by omega) hr)
  simp [parameterizedTerm, hf]

private theorem reduced_window (N : ℕ) (F : PowerSeries (ZMod 2)) :
    ∑ r ∈ Finset.range (N + 1),
        coeff N (parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) r F) =
      coeff N (1 + X * F * invOfUnit (1 + X * F) 1) := by
  cases N with
  | zero => simp [term_zero, coeff_zero_eq_constantCoeff]
  | succ N =>
    rw [Finset.sum_range_succ' _ (N + 1), Finset.sum_eq_single 0]
    · simp [term_zero, term_one, add_comm]
    · intro r hr hr0
      rw [term_mod_two_zero (r + 1) (by omega), map_zero]
    · simp

private theorem reduced_fixed :
    let C := generatingSeries.map (Int.castRingHom (ZMod 2))
    C = 1 + X * C * invOfUnit (1 + X * C) 1 := by
  dsimp only
  ext N
  have he := congrArg (Int.castRingHom (ZMod 2)) (generating_equation.2 N)
  simp only [map_sum] at he
  rw [coeff_map, he]
  have hm : ∀ r, (Int.castRingHom (ZMod 2)) (coeff N (term r generatingSeries)) =
      coeff N (parameterizedTerm (fun n ↦ n ^ 2) (fun n _ ↦ n) r
        (generatingSeries.map (Int.castRingHom (ZMod 2)))) := by
    intro r
    rw [← coeff_map, term, map_parameterized_term]
  simp_rw [hm]
  exact reduced_window N _

theorem mod_two_equation :
    let C := generatingSeries.map (Int.castRingHom (ZMod 2))
    C = 1 + X * C ^ 2 := by
  let C := generatingSeries.map (Int.castRingHom (ZMod 2))
  have hi : invOfUnit (1 + X * C) 1 * (1 + X * C) = 1 :=
    invOfUnit_mul _ 1 (by simp)
  have he : C * (1 + X * C) = 1 + X * C + X * C := by
    calc
      C * (1 + X * C) =
          (1 + X * C * invOfUnit (1 + X * C) 1) * (1 + X * C) :=
        congrArg (fun F ↦ F * (1 + X * C)) reduced_fixed
      _ = 1 + X * C + X * C := by
        rw [add_mul, one_mul, mul_assoc, hi, mul_one]
  have hz : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
  change C = 1 + X * C ^ 2
  linear_combination he + (X * C - X * C ^ 2) * hz

private theorem reduced_series_eq_frozen :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      FactorialProductSumCatalanParity.generatingSeries.map
        (Int.castRingHom (ZMod 2)) := by
  let C := generatingSeries.map (Int.castRingHom (ZMod 2))
  let P := FactorialProductSumCatalanParity.generatingSeries.map
    (Int.castRingHom (ZMod 2))
  have hC : constantCoeff C = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map,
      coeff_zero_eq_constantCoeff, generating_equation.1, map_one]
  have hP : constantCoeff P = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map,
      coeff_zero_eq_constantCoeff,
      FactorialProductSumCatalanParity.generating_equation.1, map_one]
  have eC : C = 1 + X * C ^ 2 := mod_two_equation
  have eP : P = 1 + X * P ^ 2 :=
    FactorialProductSumCatalanParity.mod_two_equation
  have hu : IsUnit (1 - X * C - X * P) := by
    rw [isUnit_iff_constantCoeff]
    simp [hC, hP]
  change C = P
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  linear_combination eC - eP

/-- The reduced A222014 series has the same Catalan support as the frozen
A222013 series. -/
theorem mod_two_identity :
    X * generatingSeries.map (Int.castRingHom (ZMod 2)) =
      Invariants.CatalanCompositionSquareParity.catalanSeries.map
        (Int.castRingHom (ZMod 2)) := by
  rw [reduced_series_eq_frozen]
  exact FactorialProductSumCatalanParity.mod_two_identity

/-- The coefficients of A222014 are odd exactly one below a power of two. -/
theorem hanna_conjecture (n : ℕ) : Odd (a n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have he := congrArg (coeff n) reduced_series_eq_frozen
  simp only [coeff_map, generatingSeries, coeff_mk,
    FactorialProductSumCatalanParity.generatingSeries] at he
  change (Int.castRingHom (ZMod 2)) (a n) = 1 ↔ ∃ k : ℕ, n + 1 = 2 ^ k
  rw [he]
  change ((FactorialProductSumCatalanParity.a n : ZMod 2) = 1 ↔
    ∃ k : ℕ, n + 1 = 2 ^ k)
  rw [ZMod.intCast_eq_one_iff_odd]
  exact FactorialProductSumCatalanParity.hanna_conjecture n

#print axioms parameterized_term_coeff_eq_zero
#print axioms term_coeff_eq_zero
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_equation
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.FactorialSquareExponentSumParity

/- GID: D5/S1/Recurrence/Invariants/HannaProductPartitionModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaProductPartitionModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna A356508 product-partition coefficients have the conjectured residues modulo four. -/

/-
result: proof_shape: bind-only; escape_witness: none; admission_basis: open-problem-resolution (#18879; Proved)
Direct frozen dependencies: D5.S1.Recurrence.Invariants.UnitReversionSquareParity, D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour, D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.
The source definitions IsGF and claim retain the verbatim coefficientwise equations; proofs use the existing frozen coefficient-agreement, inverse, and partition-product declarations.
All private theorem helpers are consumed by result through the fixed-point and residue chains; they are classified individually in the delivery record.
-/

import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour
import D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace D5.S1.Recurrence.Invariants.HannaProductPartitionModFour

open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity

/-- OEIS A356508: "G.f. A(x) satisfies: 2 = Product_{n>=1} (1 + x^n*A(x)) * (1 + x^(n-1)/A(x))" (offset 0).
The product is taken coefficientwise: the factors `n ≥ m + 2` are `1` modulo `x^(m+1)`, so the coefficient of
`x^m` is that of the factors `n ≤ m + 1`. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A ≠ 0 ∧ ∀ m : ℕ,
    coeff m (∏ n ∈ Finset.Icc 1 (m + 1), (1 + X ^ n * A) * (1 + X ^ (n - 1) * A⁻¹)) =
      coeff m (2 : PowerSeries ℚ)

/-- OEIS A356508 (P. D. Hanna), conjecture: "a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd
number of partitions (A052002), otherwise a(n) == 0 (mod 4) when n > 0". The terms are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 0 < n → ∃ z : ℤ, coeff n A = z ∧
      ((∃ k : ℕ, 0 < k ∧ n = 2 * k ∧ Odd (Fintype.card (Nat.Partition k))) → z ≡ 2 [ZMOD 4]) ∧
      ((¬ ∃ k : ℕ, 0 < k ∧ n = 2 * k ∧ Odd (Fintype.card (Nat.Partition k))) → z ≡ 0 [ZMOD 4])

section Generic
variable {R : Type*} [CommRing R]
private noncomputable def pair (A : PowerSeries R) (i : ℕ) : PowerSeries R :=
  (1 + X ^ (i + 1) * A) * (1 + X ^ (i + 1) * invOfUnit A 1)
private noncomputable def product (A : PowerSeries R) (N : ℕ) : PowerSeries R :=
  ∏ i ∈ Finset.range N, pair A i
private noncomputable def P (A : PowerSeries R) : PowerSeries R :=
  mk fun n => coeff n (product A n)
private noncomputable def step (A : PowerSeries R) : PowerSeries R :=
  1 + (A + 1) * (P A - 1)

private theorem agree_refl_local (d : ℕ) (F : PowerSeries R) : Agree d F F := by
  intro n hn
  rfl

private theorem agree_add_local {d : ℕ} {F G H K : PowerSeries R}
    (h : Agree d F G) (h' : Agree d H K) : Agree d (F + H) (G + K) := by
  intro n hn
  simp only [map_add, h n hn, h' n hn]

private theorem inverse_agree {d : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (h : Agree d F G) : Agree d (invOfUnit F 1) (invOfUnit G 1) := by
  have hFi := invOfUnit_mul F 1 hF
  have hGi := mul_invOfUnit G 1 hG
  have he : invOfUnit F 1 - invOfUnit G 1 =
      -(invOfUnit F 1 * (F - G) * invOfUnit G 1) := by
    linear_combination invOfUnit G 1 * hFi - invOfUnit F 1 * hGi
  apply (agree_iff _ _ _).mpr
  rw [he]
  exact dvd_neg.mpr (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h) _) _)

private theorem agree_shift {d : ℕ} {F G : PowerSeries R}
    (h : Agree d F G) : Agree (d + 1) (X * F) (X * G) := by
  exact agree_X h

private theorem agree_mono_local {d e : ℕ} {F G : PowerSeries R}
    (h : Agree d F G) (he : e ≤ d) : Agree e F G :=
  fun n hn => h n (lt_of_lt_of_le hn he)

private theorem agree_product (s : Finset ℕ) {d : ℕ} {f g : ℕ → PowerSeries R}
    (h : ∀ i ∈ s, Agree d (f i) (g i)) :
    Agree d (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (agree_refl_local d (1 : PowerSeries R))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact agree_mul (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

private theorem pair_low (A : PowerSeries R) (i : ℕ) :
    Agree (i + 1) (pair A i) 1 := by
  have hA : Agree (i + 1) (1 + X ^ (i + 1) * A) 1 := by
    intro n hn
    simp only [map_add, coeff_one, coeff_X_pow_mul']
    by_cases hn0 : n = 0
    · subst n; simp
    · rw [if_neg hn0, if_neg (by omega : ¬ i + 1 ≤ n)]
      simp
  have hB : Agree (i + 1) (1 + X ^ (i + 1) * invOfUnit A 1) 1 := by
    intro n hn
    simp only [map_add, coeff_one, coeff_X_pow_mul']
    by_cases hn0 : n = 0
    · subst n; simp
    · rw [if_neg hn0, if_neg (by omega : ¬ i + 1 ≤ n)]
      simp
  simpa only [pair, mul_one] using agree_mul hA hB

private theorem product_stable (A : PowerSeries R) {d N : ℕ} (h : d ≤ N) :
    Agree d (product A N) (product A d) := by
  classical
  induction N, h using Nat.le_induction with
  | base => exact agree_refl_local _ _
  | succ N hN ih =>
    simp only [product, Finset.prod_range_succ]
    simpa only [product, mul_one] using
      agree_mul ih (agree_mono_local (pair_low A N) (by omega))

private theorem P_window (A : PowerSeries R) (n N : ℕ) (hN : n ≤ N) :
    coeff n (P A) = coeff n (product A N) := by
  have hl : Agree (n + 1) (product A (N + 1)) (product A N) := by
    simpa only [product, Finset.prod_range_succ, mul_one] using
      agree_mul (agree_refl_local (n + 1) (product A N))
        (agree_mono_local (pair_low A N) (by omega))
  have hr : Agree (n + 1) (product A (n + 1)) (product A n) := by
    simpa only [product, Finset.prod_range_succ, mul_one] using
      agree_mul (agree_refl_local (n + 1) (product A n)) (pair_low A n)
  have hs := product_stable A (d := n + 1) (N := N + 1) (by omega : n + 1 ≤ N + 1)
  have hleft := hl n (by omega)
  have hmid := hs n (by omega)
  have hright := hr n (by omega)
  simpa only [P, coeff_mk] using hright.symm.trans (hmid.symm.trans hleft)

private theorem P_constant (A : PowerSeries R) : constantCoeff (P A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [P, product, pair]

private theorem P_agree {d : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) (h : Agree d A B) :
    Agree (d + 1) (P A) (P B) := by
  intro n hn
  have hp := agree_product (Finset.range n) (d := d + 1)
    (f := fun i => pair A i) (g := fun i => pair B i) (fun i hi => by
      have ha := agree_shift h
      have hb := agree_shift (inverse_agree hA hB h)
      have hx : Agree (d + 1) (X ^ (i + 1) * A) (X ^ (i + 1) * B) := by
        simpa [pow_succ, mul_assoc] using
          agree_mul (agree_pow (agree_refl_local (d + 1) X) i) ha
      have hy : Agree (d + 1) (X ^ (i + 1) * invOfUnit A 1)
          (X ^ (i + 1) * invOfUnit B 1) := by
        simpa [pow_succ, mul_assoc] using
          agree_mul (agree_pow (agree_refl_local (d + 1) X) i) hb
      exact agree_mul
        (agree_add_local (agree_refl_local (d + 1) 1) hx)
        (agree_add_local (agree_refl_local (d + 1) 1) hy))
  simpa only [P, coeff_mk, product] using hp n (by omega)

private theorem step_constant (A : PowerSeries R) : constantCoeff (step A) = 1 := by
  simp [step, P_constant]

private theorem agree_mul_succ {d : ℕ} {U V W Z : PowerSeries R}
    (hu : Agree d U V) (hw : Agree (d + 1) W Z)
    (hW0 : constantCoeff W = 0) (hZ0 : constantCoeff Z = 0) :
    Agree (d + 1) (U * W) (V * Z) := by
  apply (agree_iff _ _ _).mpr
  have hud := (agree_iff _ _ _).mp hu
  have hwd := X_dvd_iff.mpr hW0
  have hzd := X_dvd_iff.mpr hZ0
  have hfirst : X ^ (d + 1) ∣ (U - V) * W := by
    rcases hud with ⟨a, ha⟩
    rcases hwd with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [ha, hb]
    calc
      X ^ d * a * (X * b) = X ^ d * X * (a * b) := by ring
      _ = X ^ (d + 1) * (a * b) := by rw [pow_succ]
  have hsecond : X ^ (d + 1) ∣ V * (W - Z) := by
    exact dvd_mul_of_dvd_right ((agree_iff _ _ _).mp hw) V
  convert dvd_add hfirst hsecond using 1
  ring

private theorem step_agree {d : ℕ} {A B : PowerSeries R} (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) (hd : 1 ≤ d) (h : Agree d A B) :
    Agree (d + 1) (step A) (step B) := by
  have hu : Agree d (A + 1) (B + 1) :=
    agree_add_local h (agree_refl_local d 1)
  have hp := P_agree hA hB h
  have hv : Agree (d + 1) (P A - 1) (P B - 1) := by
    intro k hk
    rw [map_sub, map_sub, hp k hk]
  have hm := agree_mul_succ hu hv (by simp [P_constant]) (by simp [P_constant])
  exact agree_add_local (agree_refl_local (d + 1) 1) hm

private noncomputable def approx : ℕ → PowerSeries R
  | 0 => 1
  | n + 1 => step (approx n)

private theorem approx_constant (n : ℕ) : constantCoeff (approx (R := R) n) = 1 := by
  induction n with
  | zero => simp [approx]
  | succ n ih => simpa [approx] using step_constant (approx n)

private theorem approx_stable {d n : ℕ} (h : d ≤ n) :
    Agree (d + 1) (approx (R := R) d) (approx n) := by
  induction d generalizing n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    simp [approx_constant]
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n => exact step_agree (approx_constant d) (approx_constant n) (by omega) (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk fun n => coeff n (approx (R := R) n)

private theorem solution_constant : constantCoeff (solution (R := R)) = 1 := by
  have h := approx_stable (R := R) (d := 0) (n := 0) (by omega)
  simpa [solution, coeff_zero_eq_constantCoeff, approx_constant] using h 0 (by omega)

private theorem solution_agree (d : ℕ) :
    Agree (d + 1) (solution (R := R)) (approx d) := by
  intro n hn
  simpa only [solution, coeff_mk] using approx_stable (R := R) (by omega : n ≤ d) n (by omega)

private theorem solution_fixed : solution (R := R) = step solution := by
  ext n
  have h1 := solution_agree (R := R) (n + 1) n (by omega)
  have h2 := step_agree (R := R) solution_constant (approx_constant n) (by omega : 1 ≤ n + 1) (solution_agree (R := R) n)
  exact h1.trans (h2 n (by omega)).symm

private theorem fixed_unique {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (hAf : A = step A) (hBf : B = step B) : A = B := by
  have h : ∀ d, Agree d A B := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      cases d with
      | zero =>
        intro n hn
        have : n = 0 := by omega
        subst n
        simpa [coeff_zero_eq_constantCoeff] using hA.trans hB.symm
      | succ d =>
        simpa only [← hAf, ← hBf] using
          step_agree (R := R) (d := d + 1) hA hB (by omega) ih
  ext n
  exact h (n + 1) n (by omega)

private theorem fixed_equation (A : PowerSeries R) (h0 : constantCoeff A = 1)
    (h : A = step A) : (1 + A) * P A = 2 * A := by
  dsimp [step] at h
  linear_combination -h

end Generic

end D5.S1.Recurrence.Invariants.HannaProductPartitionModFour

namespace D5.S1.Recurrence.Invariants.HannaProductPartitionModFour
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
section Bridge
variable {R : Type*} [CommRing R]

private theorem P_window_agree (A : PowerSeries R) (N : ℕ) :
    Agree (N + 1) (P A) (product A N) := by
  intro k hk
  exact P_window A k N (by omega)

private theorem finite_split (A B : PowerSeries R) (m : ℕ) :
    (∏ n ∈ Finset.Icc 1 (m + 1), (1 + X ^ n * A) * (1 + X ^ (n - 1) * B)) =
      (1 + B) * (∏ i ∈ Finset.range m, (1 + X ^ (i + 1) * A) *
        (1 + X ^ (i + 1) * B)) * (1 + X ^ (m + 1) * A) := by
  induction m with
  | zero =>
    simp only [Finset.Icc_self, Finset.prod_singleton, Nat.sub_self, pow_zero, pow_one]
    simpa using (mul_comm (1 + X * A) (1 + B))
  | succ m ih =>
    conv_lhs => rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1 + 1), ih]
    conv_rhs => rw [Finset.prod_range_succ]
    simp only [Nat.add_sub_cancel]
    generalize (∏ i ∈ Finset.range m, (1 + X ^ (i + 1) * A) *
      (1 + X ^ (i + 1) * B)) = Z
    ring

private theorem original_coeff (A : PowerSeries R) (m : ℕ) :
    coeff m (∏ n ∈ Finset.Icc 1 (m + 1),
      (1 + X ^ n * A) * (1 + X ^ (n - 1) * invOfUnit A 1)) =
        coeff m ((1 + invOfUnit A 1) * P A) := by
  rw [finite_split]
  have hp := agree_mul (show Agree (m + 1) (1 + invOfUnit A 1) (1 + invOfUnit A 1) from fun _ _ => rfl)
    (P_window_agree A m)
  have ht : Agree (m + 1) (1 + X ^ (m + 1) * A) 1 := by
    intro k hk
    simp only [map_add, coeff_X_pow_mul', if_neg (by omega : ¬ m + 1 ≤ k), add_zero]
  have he := agree_mul
    (show Agree (m + 1) ((1 + invOfUnit A 1) * product A m)
      ((1 + invOfUnit A 1) * product A m) from fun _ _ => rfl) ht
  simp only [mul_one] at he
  simpa only [product, pair] using
    (he m (by omega)).trans (hp m (by omega)).symm

private theorem source_constant (A : PowerSeries ℚ) (hA : IsGF A) :
    constantCoeff A = 1 := by
  have hc := hA.2 0
  simp only [Finset.Icc_self, Finset.prod_singleton, pow_one, Nat.sub_self, pow_zero,
    one_mul, coeff_zero_eq_constantCoeff, map_mul, map_add, map_one,
    constantCoeff_X, zero_mul, add_zero, one_mul, constantCoeff_inv, map_ofNat] at hc
  have he : (constantCoeff A)⁻¹ = 1 := by linarith
  simpa only [inv_inv, inv_one] using congrArg Inv.inv he

private theorem source_fixed (A : PowerSeries ℚ) (hA : IsGF A) : A = step A := by
  have h0 := source_constant A hA
  have hinv : invOfUnit A 1 = A⁻¹ := invOfUnit_eq' A 1 h0
  have he : (1 + invOfUnit A 1) * P A = 2 := by
    ext m
    rw [← original_coeff, hinv]
    exact hA.2 m
  have hi := mul_invOfUnit A 1 h0
  have he' : (1 + A) * P A = 2 * A := by
    calc
      (1 + A) * P A = P A + A * P A := by ring
      _ = A * invOfUnit A 1 * P A + A * P A := by rw [hi]; ring
      _ = A * ((1 + invOfUnit A 1) * P A) := by ring
      _ = 2 * A := by rw [he]; ring
  dsimp [step]
  linear_combination -he'

private theorem fixed_source (A : PowerSeries ℚ) (h0 : constantCoeff A = 1)
    (h : A = step A) : IsGF A := by
  refine ⟨by rw [h0]; norm_num, fun m => ?_⟩
  have hi : A⁻¹ = invOfUnit A 1 := (invOfUnit_eq' A 1 h0).symm
  have hf := fixed_equation A h0 h
  have he : (1 + invOfUnit A 1) * P A = 2 := by
    calc
      (1 + invOfUnit A 1) * P A = P A + invOfUnit A 1 * P A := by ring
      _ = P A * (A * invOfUnit A 1) + invOfUnit A 1 * P A := by
        rw [mul_invOfUnit A 1 h0]
        ring
      _ = ((1 + A) * P A) * invOfUnit A 1 := by ring
      _ = (2 * A) * invOfUnit A 1 := by rw [hf]
      _ = 2 * (A * invOfUnit A 1) := by ring
      _ = 2 := by rw [mul_invOfUnit A 1 h0]; ring
  rw [hi, original_coeff, he]

private theorem map_P {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (h0 : constantCoeff A = 1) :
    (P A).map f = P (A.map f) := by
  have hmi : (invOfUnit A 1).map f = invOfUnit (A.map f) 1 := by
    exact D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour.map_inv f A h0
  ext n
  simp only [P, coeff_map, coeff_mk]
  rw [← coeff_map]
  congr 1
  simp only [product, pair, map_prod, map_mul, map_add, map_one, map_pow, map_X,
    hmi]

private theorem map_step {S : Type*} [CommRing S] (f : R →+* S)
    (A : PowerSeries R) (h0 : constantCoeff A = 1) :
    (step A).map f = step (A.map f) := by
  have hmi : (invOfUnit A 1).map f = invOfUnit (A.map f) 1 := by
    exact D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour.map_inv f A h0
  simp only [step, map_add, map_mul, map_one, map_sub, map_P f A h0, hmi]

private theorem map_solution {S : Type*} [CommRing S] (f : R →+* S) :
    (solution (R := R)).map f = solution (R := S) := by
  have h0 : constantCoeff ((solution (R := R)).map f) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      solution_constant, map_one]
  apply fixed_unique h0 solution_constant _ solution_fixed
  exact (congrArg (PowerSeries.map f) solution_fixed).trans
    (map_step f _ solution_constant)

private theorem source_is_integral (A : PowerSeries ℚ) (h : IsGF A) :
    A = (solution (R := ℤ)).map (Int.castRingHom ℚ) := by
  rw [map_solution]
  exact fixed_unique (source_constant A h) solution_constant (source_fixed A h) solution_fixed

private theorem source_exists : ∃ A, IsGF A := by
  exact ⟨solution, fixed_source solution solution_constant solution_fixed⟩

end Bridge

section Modular
private noncomputable def Q : PowerSeries (ZMod 4) :=
  expand 2 (by decide)
    (D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionSeries.map
      (Int.castRingHom (ZMod 4)))
private noncomputable def E : PowerSeries (ZMod 4) :=
  expand 2 (by decide) ((pentagonalSeries ℤ).map (Int.castRingHom (ZMod 4)))

private theorem E_mul_Q : E * Q = 1 := by
  have hp : pentagonalSeries ℤ *
      D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionSeries = 1 := by
    exact partition_reciprocal
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 4))) hp
  have h' := congrArg (expand 2 (by decide)) h
  simpa only [E, Q, map_mul, map_one] using h'

private theorem Q_constant : constantCoeff Q = 1 := by
  rw [← coeff_zero_eq_constantCoeff, Q, coeff_expand]
  simp [D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionSeries,
    D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionCount]

private noncomputable def candidate : PowerSeries (ZMod 4) := 2 * Q - 1

private theorem candidate_constant : constantCoeff candidate = 1 := by
  norm_num [candidate, Q_constant, map_ofNat]

private theorem candidate_square : candidate ^ 2 = 1 := by
  dsimp [candidate]
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  linear_combination (Q ^ 2 - Q) * h4

private theorem candidate_inverse : invOfUnit candidate 1 = candidate := by
  have hu : IsUnit candidate := isUnit_iff_constantCoeff.mpr (by rw [candidate_constant]; exact isUnit_one)
  apply hu.mul_left_cancel
  rw [mul_invOfUnit _ 1 candidate_constant, ← pow_two, candidate_square]

private theorem candidate_two : 2 * candidate = 2 := by
  dsimp [candidate]
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  linear_combination (Q - 1) * h4

private theorem pair_two (i : ℕ) :
    2 * pair candidate i = 2 * (1 - X ^ (2 * (i + 1))) := by
  dsimp [pair]
  rw [candidate_inverse]
  have hpow : (X : PowerSeries (ZMod 4)) ^ (2 * (i + 1)) =
      (X ^ (i + 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1 <;> omega
  rw [hpow]
  have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
    rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  calc
    2 * ((1 + X ^ (i + 1) * candidate) * (1 + X ^ (i + 1) * candidate)) =
        2 + 4 * X ^ (i + 1) * candidate + 2 * (X ^ (i + 1)) ^ 2 * candidate ^ 2 := by ring
    _ = 2 + 4 * X ^ (i + 1) * candidate + 2 * (X ^ (i + 1)) ^ 2 := by
      rw [candidate_square]
      ring
    _ = 2 * (1 - (X ^ (i + 1)) ^ 2) := by
      have h4x : 4 * X ^ (i + 1) * candidate = 0 := by
        calc
          4 * X ^ (i + 1) * candidate =
              (4 : PowerSeries (ZMod 4)) * (X ^ (i + 1) * candidate) := by ring
          _ = 0 := by rw [h4, zero_mul]
      have h4xx : (4 : PowerSeries (ZMod 4)) * (X ^ (i + 1)) ^ 2 = 0 := by
        calc
          4 * (X ^ (i + 1)) ^ 2 =
              (4 : PowerSeries (ZMod 4)) * (X ^ (i + 1)) ^ 2 := by ring
          _ = 0 := by rw [h4, zero_mul]
      linear_combination h4x + h4xx

private theorem product_two (N : ℕ) :
    2 * product candidate N =
      2 * ∏ i ∈ Finset.range N, (1 - (X : PowerSeries (ZMod 4)) ^ (2 * (i + 1))) := by
  induction N with
  | zero => simp [product]
  | succ N ih =>
    simp only [product, Finset.prod_range_succ] at ih ⊢
    calc
      2 * ((∏ i ∈ Finset.range N, pair candidate i) * pair candidate N) =
          (2 * ∏ i ∈ Finset.range N, pair candidate i) * pair candidate N := by ring
      _ = (2 * ∏ i ∈ Finset.range N, (1 - X ^ (2 * (i + 1)))) * pair candidate N := by rw [ih]
      _ = (∏ i ∈ Finset.range N, (1 - X ^ (2 * (i + 1)))) * (2 * pair candidate N) := by ring
      _ = _ := by rw [pair_two]; ring

private theorem E_window (n : ℕ) : ∃ N, n ≤ N ∧
    coeff n E = coeff n (∏ i ∈ Finset.range N,
      (1 - (X : PowerSeries (ZMod 4)) ^ (2 * (i + 1)))) := by
  have he := Filter.tendsto_finset_range.eventually
    (coeff_prod_one_sub_X_pow_eventually_eq ℤ (n / 2))
  obtain ⟨N, hN, hE⟩ := (Filter.eventually_ge_atTop n |>.and he).exists
  refine ⟨N, hN, ?_⟩
  have hm : (∏ i ∈ Finset.range N,
      (1 - (X : PowerSeries (ZMod 4)) ^ (2 * (i + 1)))) =
      expand 2 (by decide) ((∏ i ∈ Finset.range N,
        (1 - (X : PowerSeries ℤ) ^ (i + 1))).map (Int.castRingHom (ZMod 4))) := by
    simp only [map_prod, map_sub, map_one, map_pow, map_X, expand_X, ← pow_mul]
  rw [hm, E, coeff_expand, coeff_expand]
  split_ifs
  · rw [coeff_map, coeff_map, hE]
  · rfl

private theorem P_two : 2 * P candidate = 2 * E := by
  ext n
  obtain ⟨N, hN, he⟩ := E_window n
  have h := congrArg (coeff n) (product_two N)
  rw [show (2 : PowerSeries (ZMod 4)) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, coeff_C_mul] at h ⊢
  rw [P_window candidate n N hN, he]
  exact h

private theorem candidate_fixed : candidate = step candidate := by
  have he0 : (1 + candidate) * P candidate = 2 := by
    calc
      (1 + candidate) * P candidate = Q * (2 * P candidate) := by dsimp [candidate]; ring
      _ = Q * (2 * E) := by rw [P_two]
      _ = 2 * (E * Q) := by ring
      _ = 2 := by rw [E_mul_Q, mul_one]
  have he : (1 + candidate) * P candidate = 2 * candidate := by
    rw [candidate_two]
    exact he0
  dsimp [step]
  linear_combination -he

private theorem solution_mod_four :
    (solution (R := ℤ)).map (Int.castRingHom (ZMod 4)) = candidate := by
  rw [map_solution]
  exact fixed_unique solution_constant candidate_constant solution_fixed candidate_fixed

private theorem coefficient_formula (n : ℕ) (hn : 0 < n) :
    ((coeff n (solution (R := ℤ)) : ℤ) : ZMod 4) =
      2 * if 2 ∣ n then (Fintype.card (Nat.Partition (n / 2)) : ZMod 4) else 0 := by
  have h := congrArg (coeff n) solution_mod_four
  rw [coeff_map, candidate, map_sub,
    show (2 : PowerSeries (ZMod 4)) = C 2 from (map_ofNat C 2).symm,
    coeff_C_mul, coeff_one, if_neg (by omega : n ≠ 0), sub_zero,
    Q, coeff_expand] at h
  simpa [D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionSeries,
    D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.partitionCount] using h

private theorem odd_double_mod_four (p : ℕ) (hp : Odd p) : 2 * (p : ZMod 4) = 2 := by
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  push_cast
  calc
    2 * (2 * (k : ZMod 4) + 1) = 4 * (k : ZMod 4) + 2 := by ring
    _ = 2 := by rw [show (4 : ZMod 4) = 0 by decide]; ring

private theorem even_double_mod_four (p : ℕ) (hp : Even p) : 2 * (p : ZMod 4) = 0 := by
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  push_cast
  calc
    2 * ((k : ZMod 4) + (k : ZMod 4)) = 4 * (k : ZMod 4) := by ring
    _ = 0 := by rw [show (4 : ZMod 4) = 0 by decide]; ring
end Modular

/-- The OEIS A356508 conjecture holds for every coefficientwise solution. -/
theorem result : claim := by
  refine ⟨source_exists, ?_⟩
  intro A hA n hn
  refine ⟨coeff n (solution (R := ℤ)), ?_, ?_, ?_⟩
  · rw [source_is_integral A hA, coeff_map]
    rfl
  · rintro ⟨k, hk, rfl, hp⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
    rw [coefficient_formula _ (by omega), if_pos (dvd_mul_right 2 k),
      Nat.mul_div_cancel_left k (by decide)]
    exact odd_double_mod_four _ hp
  · intro h
    apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
    rw [coefficient_formula n hn]
    by_cases hd : 2 ∣ n
    · rw [if_pos hd]
      apply even_double_mod_four
      have ho : ¬ Odd (Fintype.card (Nat.Partition (n / 2))) := by
        intro ho
        exact h ⟨n / 2, by omega, by omega, ho⟩
      exact Nat.not_odd_iff_even.mp ho
    · rw [if_neg hd, mul_zero]
      rfl

end D5.S1.Recurrence.Invariants.HannaProductPartitionModFour

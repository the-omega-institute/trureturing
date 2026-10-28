/- GID: D5/S1/Recurrence/Residue/BalaA193237ModFiveSeven
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/BalaA193237ModFiveSeven
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's unbounded modulo-five and modulo-seven coefficient congruences. -/

/-
proof_shape: F: bind-only (definition); consumers: IsGF, result, source237.
proof_shape: IsGF: bind-only (definition); consumers: claim.
proof_shape: claim: bind-only (definition); consumers: result.
proof_shape: root_step_agree: bind-only; consumers: integral_cube_root.
proof_shape: integral_cube_root: bind-only; consumers: integral_inverse_cube.
proof_shape: integral_inverse_cube: bind-only; consumers: integral_inverse_of_nine.
proof_shape: normalized_cube_unique: bind-only; consumers: resolve.
proof_shape: integral_inverse_of_nine: bind-only; consumers: resolve.
proof_shape: triangular: bind-only (definition); consumers: D5.S1.Recurrence.Residue.BalaA193236ModFiveSeven.source236, map_triangular, resolve, source237, triangular_constant, triangular_divisible, triangular_inverse_congruences, triangular_support_five, triangular_support_seven.
proof_shape: Supported: bind-only (definition); consumers: cube_support_five, square_support_seven, support_mul, transfer_five, transfer_seven.
proof_shape: support_mul: bind-only; consumers: cube_support_five, square_support_seven.
proof_shape: twice_triangle: bind-only; consumers: triangular_support_five, triangular_support_seven.
proof_shape: triangular_support_five: bind-only; consumers: triangular_inverse_congruences.
proof_shape: triangular_support_seven: bind-only; consumers: triangular_inverse_congruences.
proof_shape: cube_support_five: bind-only; consumers: transfer_five.
proof_shape: square_support_seven: bind-only; consumers: transfer_seven.
proof_shape: prime_power_support: bind-only; consumers: mul_prime_power_vanish.
proof_shape: mul_prime_power_vanish: bind-only; consumers: transfer_five, transfer_seven.
proof_shape: transfer_five: bind-only; consumers: triangular_inverse_congruences.
proof_shape: transfer_seven: bind-only; consumers: triangular_inverse_congruences.
proof_shape: map_triangular: bind-only; consumers: triangular_inverse_congruences.
proof_shape: triangular_inverse_congruences: bind-only; consumers: resolve.
proof_shape: triangular_constant: bind-only; consumers: resolve.
proof_shape: triangular_divisible: bind-only; consumers: resolve.
proof_shape: weight237: bind-only (definition); consumers: result, source237, weight237_nine.
proof_shape: weight237_nine: bind-only; consumers: result.
proof_shape: source237: bind-only; consumers: result.
proof_shape: resolve: bind-only; consumers: D5.S1.Recurrence.Residue.BalaA193236ModFiveSeven.result, result.
proof_shape: result: bind-only; consumers: none.
escape_witness: none
admission_basis: open-problem-resolution (#22112; Proved)
Direct frozen dependencies: F: none.
Direct frozen dependencies: IsGF: none.
Direct frozen dependencies: claim: none.
Direct frozen dependencies: root_step_agree: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Direct frozen dependencies: integral_cube_root: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Direct frozen dependencies: integral_inverse_cube: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Direct frozen dependencies: normalized_cube_unique: none.
Direct frozen dependencies: integral_inverse_of_nine: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Direct frozen dependencies: triangular: none.
Direct frozen dependencies: Supported: none.
Direct frozen dependencies: support_mul: none.
Direct frozen dependencies: twice_triangle: none.
Direct frozen dependencies: triangular_support_five: none.
Direct frozen dependencies: triangular_support_seven: none.
Direct frozen dependencies: cube_support_five: none.
Direct frozen dependencies: square_support_seven: none.
Direct frozen dependencies: prime_power_support: none.
Direct frozen dependencies: mul_prime_power_vanish: none.
Direct frozen dependencies: transfer_five: none.
Direct frozen dependencies: transfer_seven: none.
Direct frozen dependencies: map_triangular: none.
Direct frozen dependencies: triangular_inverse_congruences: none.
Direct frozen dependencies: triangular_constant: none.
Direct frozen dependencies: triangular_divisible: none.
Direct frozen dependencies: weight237: none.
Direct frozen dependencies: weight237_nine: none.
Direct frozen dependencies: source237: none.
Direct frozen dependencies: resolve: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Direct frozen dependencies: result: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22201.
The source coefficient sum, normalization and claim retain their literal expressions.
-/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

set_option autoImplicit false
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

namespace D5.S1.Recurrence.Residue.BalaA193237ModFiveSeven

/-- The series inside the reciprocal cube root in OEIS A193237, with its literal weights.
The coefficient sum is finite: j(j+1)/2 = m implies j ≤ m. -/
noncomputable def F : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ j ∈ Finset.range (m + 1),
      if j * (j + 1) / 2 = m then
        ((2 * j + 1 : ℕ) : ℚ) * 3 ^ j * (-1) ^ (j * (j + 1) / 2)
      else 0

/-- The reciprocal cube root with constant coefficient one: A^3 * F = 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧ A ^ 3 * F = 1

/-- Both clauses of Bala's %F conjecture, with existence and integral coefficients. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ A : PowerSeries ℚ, IsGF A →
      ∃ a : ℕ → ℤ,
        (∀ m : ℕ, coeff m A = (a m : ℚ)) ∧
          ∀ n : ℕ, (5 : ℤ) ∣ a (5 * n + 4) ∧ (7 : ℤ) ∣ a (7 * n + 5)


variable {R : Type*} [CommRing R]

private theorem root_step_agree (H : PowerSeries R) {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree d f g) :
    Agree (d + 1) (1 + H - 3 * (f - 1)^2 - 3 * (f - 1)^3)
      (1 + H - 3 * (g - 1)^2 - 3 * (g - 1)^3) := by
  apply (agree_iff _ _ _).mpr
  let v := -3 * ((f-1)+(g-1)) - 3 * ((f-1)^2+(f-1)*(g-1)+(g-1)^2)
  have hv : (X : PowerSeries R) ∣ v := by
    apply X_dvd_iff.mpr
    simp [v, hf, hg]
  have he : (1 + H - 3 * (f - 1)^2 - 3 * (f - 1)^3) -
      (1 + H - 3 * (g - 1)^2 - 3 * (g - 1)^3) = (f-g)*v := by
    dsimp [v]; ring
  rw [he, pow_succ]
  exact mul_dvd_mul ((agree_iff _ _ _).mp h) hv

private theorem integral_cube_root (H : PowerSeries ℤ) (hH : constantCoeff H = 0) :
    ∃ B : PowerSeries ℤ, constantCoeff B = 1 ∧ B^3 = 1 + 9 * H := by
  obtain ⟨f, hf, he, _⟩ := exists_unique_fixed
    (fun f : PowerSeries ℤ => 1 + H - 3 * (f-1)^2 - 3 * (f-1)^3)
    (by intro f hf; simp [hf, hH])
    (by intro d f g _ hf hg h; exact root_step_agree H hf hg h)
  refine ⟨1 + 3 * (f-1), by simp [hf], ?_⟩
  linear_combination 9 * he

private theorem integral_inverse_cube (H : PowerSeries ℤ) (hH : constantCoeff H = 0) :
    ∃ A : PowerSeries ℤ, constantCoeff A = 1 ∧ A^3 * (1 + 9 * H) = 1 := by
  obtain ⟨B, hB, he⟩ := integral_cube_root H hH
  refine ⟨invOfUnit B 1, by simp, ?_⟩
  rw [← he, ← mul_pow, invOfUnit_mul B 1 (by simpa using hB), one_pow]

private theorem normalized_cube_unique (F A B : PowerSeries ℚ)
    (hF : constantCoeff F = 1) (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (heA : A^3 * F = 1) (heB : B^3 * F = 1) : A = B := by
  have h : (A-B) * ((A^2 + A*B + B^2)*F) = 0 := by
    linear_combination heA - heB
  have hn : (A^2 + A*B + B^2)*F ≠ 0 := by
    intro hz
    have hh := congrArg constantCoeff hz
    norm_num [hA, hB, hF] at hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hn)

private theorem integral_inverse_of_nine (F : PowerSeries ℤ)
    (h0 : constantCoeff F = 1) (hd : ∀ n, 0 < n → (9 : ℤ) ∣ coeff n F) :
    ∃ A : PowerSeries ℤ, constantCoeff A = 1 ∧ A^3 * F = 1 := by
  let H : PowerSeries ℤ := mk fun n => if n = 0 then 0 else coeff n F / 9
  have hH : constantCoeff H = 0 := constantCoeff_mk
  have hF : F = 1 + 9 * H := by
    ext n
    by_cases hn : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, map_add, map_mul, map_ofNat, map_one,
        h0, hH, mul_zero, add_zero]
    · simp only [map_add, coeff_one, if_neg hn, coeff_ofNat_mul, H, coeff_mk,
        if_neg hn, zero_add]
      have hh := hd n (by omega)
      omega
  rw [hF]
  exact integral_inverse_cube H hH

noncomputable def triangular {R : Type*} [Semiring R] (w : ℕ → R) : PowerSeries R :=
  mk fun m => ∑ j ∈ Finset.range (m+1),
    if j*(j+1)/2 = m then ((2*j+1 : ℕ) : R)*w j else 0

private def Supported {R : Type*} [Semiring R] (p : ℕ) (s : Finset ℕ) (F : PowerSeries R) : Prop :=
  ∀ n, coeff n F ≠ 0 → n % p ∈ s

private theorem support_mul {R : Type*} [Semiring R] (p : ℕ) (s t u : Finset ℕ)
    (F G : PowerSeries R) (hF : Supported p s F) (hG : Supported p t G)
    (hadd : ∀ i j, i%p ∈ s → j%p ∈ t → (i+j)%p ∈ u) :
    Supported p u (F*G) := by
  intro n hn
  by_contra hnu
  apply hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hi : coeff ij.1 F = 0
  · simp [hi]
  by_cases hj : coeff ij.2 G = 0
  · simp [hj]
  exact (hnu (he ▸ hadd _ _ (hF _ hi) (hG _ hj))).elim

private theorem twice_triangle (j : ℕ) : 2 * (j*(j+1)/2) = j*(j+1) := by
  have h : 2 ∣ j*(j+1) := Nat.two_dvd_mul_add_one j
  exact Nat.mul_div_cancel' h

private theorem triangular_support_five (w : ℕ → ZMod 5) :
    Supported 5 {0,1} (triangular w) := by
  intro m hm
  by_contra hres
  apply hm
  rw [triangular, coeff_mk]
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with ht
  · have hd := twice_triangle j
    have he := congrArg (fun n : ℕ => n%5) hd
    rw [ht] at he
    rw [Nat.mul_mod 2 m 5, Nat.mul_mod j (j+1) 5, Nat.add_mod j 1 5] at he
    have hjlt : j%5 < 5 := Nat.mod_lt _ (by decide)
    have hmlt : m%5 < 5 := Nat.mod_lt _ (by decide)
    have hjr : j%5 = 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hres
      interval_cases h : j%5 <;> norm_num only [h] at he <;> omega
    have hz : ((2*j+1 : ℕ) : ZMod 5) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (by omega)
    rw [hz, zero_mul]
  · rfl

private theorem triangular_support_seven (w : ℕ → ZMod 7) :
    Supported 7 {0,1,3} (triangular w) := by
  intro m hm
  by_contra hres
  apply hm
  rw [triangular, coeff_mk]
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with ht
  · have hd := twice_triangle j
    have he := congrArg (fun n : ℕ => n%7) hd
    rw [ht] at he
    rw [Nat.mul_mod 2 m 7, Nat.mul_mod j (j+1) 7, Nat.add_mod j 1 7] at he
    have hjlt : j%7 < 7 := Nat.mod_lt _ (by decide)
    have hmlt : m%7 < 7 := Nat.mod_lt _ (by decide)
    have hjr : j%7 = 3 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hres
      interval_cases h : j%7 <;> norm_num only [h] at he <;> omega
    have hz : ((2*j+1 : ℕ) : ZMod 7) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (by omega)
    rw [hz, zero_mul]
  · rfl

private theorem cube_support_five (F : PowerSeries (ZMod 5)) (hF : Supported 5 {0,1} F) :
    Supported 5 {0,1,2,3} (F^3) := by
  have h2 : Supported 5 {0,1,2} (F*F) := by
    apply support_mul 5 {0,1} {0,1} {0,1,2} F F hF hF
    intro i j hi hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    omega
  simpa [pow_succ, pow_two] using
    support_mul 5 {0,1,2} {0,1} {0,1,2,3} (F*F) F h2 hF (by
      intro i j hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at *
      omega)

private theorem square_support_seven (F : PowerSeries (ZMod 7)) (hF : Supported 7 {0,1,3} F) :
    Supported 7 {0,1,2,3,4,6} (F^2) := by
  rw [pow_two]
  apply support_mul 7 {0,1,3} {0,1,3} {0,1,2,3,4,6} F F hF hF
  intro i j hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at *
  omega

private theorem prime_power_support (p : ℕ) [Fact p.Prime] (F : PowerSeries (ZMod p))
    (n : ℕ) (hn : n%p ≠ 0) : coeff n (F^p) = 0 := by
  have he := PowerSeries.map_frobenius_expand p (NeZero.ne p) (f := F)
  rw [ZMod.frobenius_zmod, PowerSeries.map_id] at he
  simp only [id_eq] at he
  rw [← he, coeff_expand, if_neg (by simpa [Nat.dvd_iff_mod_eq_zero] using hn)]

private theorem mul_prime_power_vanish (p : ℕ) [Fact p.Prime]
    (A G : PowerSeries (ZMod p)) (r n : ℕ)
    (hG : ∀ j, j%p = r → coeff j G = 0) (hn : n%p = r) :
    coeff n (A^p * G) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1%p = 0
  · have hm : (ij.1+ij.2)%p = r := by rw [he]; exact hn
    rw [Nat.add_mod, hi, zero_add, Nat.mod_mod] at hm
    rw [hG ij.2 hm, mul_zero]
  · rw [prime_power_support p A ij.1 hi, zero_mul]

private theorem transfer_five (F A : PowerSeries (ZMod 5))
    (hF : Supported 5 {0,1} F) (he : A^3 * F = 1) (n : ℕ) :
    coeff (5*n+4) A = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ha : A = (A^2)^5 * F^3 := by
    calc
      A = A * (A^3 * F)^3 := by rw [he]; ring
      _ = _ := by ring
  rw [ha]
  apply mul_prime_power_vanish 5 (A^2) (F^3) 4 (5*n+4) _ (by omega)
  intro j hj
  by_contra hc
  have hs := cube_support_five F hF j hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  omega

private theorem transfer_seven (F A : PowerSeries (ZMod 7))
    (hF : Supported 7 {0,1,3} F) (he : A^3 * F = 1) (n : ℕ) :
    coeff (7*n+5) A = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have ha : A = A^7 * F^2 := by
    calc
      A = A * (A^3 * F)^2 := by rw [he]; ring
      _ = _ := by ring
  rw [ha]
  apply mul_prime_power_vanish 7 A (F^2) 5 (7*n+5) _ (by omega)
  intro j hj
  by_contra hc
  have hs := square_support_seven F hF j hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  omega

private theorem map_triangular {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : ℕ → R) :
    PowerSeries.map f (triangular w) = triangular (fun j => f (w j)) := by
  ext n
  simp [triangular, coeff_map, map_sum, apply_ite, map_ofNat]

private theorem triangular_inverse_congruences (w : ℕ → ℤ) (A : PowerSeries ℤ)
    (he : A^3 * triangular w = 1) (n : ℕ) :
    (5 : ℤ) ∣ coeff (5*n+4) A ∧ (7 : ℤ) ∣ coeff (7*n+5) A := by
  have hfive : coeff (5*n+4) (A.map (Int.castRingHom (ZMod 5))) = 0 := by
    apply transfer_five (triangular (fun j => (w j : ZMod 5))) _
      (triangular_support_five _) _ n
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5))) he
    simpa only [map_mul, map_pow, map_one, map_triangular, Int.coe_castRingHom] using h
  have hseven : coeff (7*n+5) (A.map (Int.castRingHom (ZMod 7))) = 0 := by
    apply transfer_seven (triangular (fun j => (w j : ZMod 7))) _
      (triangular_support_seven _) _ n
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 7))) he
    simpa only [map_mul, map_pow, map_one, map_triangular, Int.coe_castRingHom] using h
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa [coeff_map] using hfive),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa [coeff_map] using hseven)⟩

private theorem triangular_constant {R : Type*} [CommRing R] (w : ℕ → R) :
    constantCoeff (triangular w) = w 0 := by
  simp [triangular, ← coeff_zero_eq_constantCoeff_apply]

private theorem triangular_divisible (w : ℕ → ℤ)
    (hw : ∀ j, 0 < j → (9 : ℤ) ∣ ((2*j+1 : ℕ) : ℤ)*w j)
    (n : ℕ) (hn : 0 < n) : (9 : ℤ) ∣ coeff n (triangular w) := by
  rw [triangular, coeff_mk]
  apply Finset.dvd_sum
  intro j hj
  split_ifs with ht
  · apply hw j
    by_contra hj0
    have : j = 0 := Nat.eq_zero_of_not_pos hj0
    subst j
    norm_num at ht
    omega
  · exact dvd_zero 9

private noncomputable def weight237 (j : ℕ) : ℤ := 3^j * (-1)^(j*(j+1)/2)
private theorem weight237_nine (j : ℕ) (hj : 0 < j) :
    (9 : ℤ) ∣ ((2*j+1 : ℕ) : ℤ)*weight237 j := by
  rcases j with _ | _ | k
  · omega
  · norm_num [weight237]
  · change (9 : ℤ) ∣ ((2*(k+2)+1 : ℕ) : ℤ) *
        (3^(k+2) * (-1)^((k+2)*(k+2+1)/2))
    refine ⟨(((2*(k+2)+1 : ℕ) : ℤ)*3^k) * (-1)^((k+2)*(k+2+1)/2), ?_⟩
    rw [pow_add]
    ring

private theorem source237 : F =
    PowerSeries.map (Int.castRingHom ℚ) (triangular weight237) := by
  ext n
  simp only [F, triangular, coeff_mk, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with ht
  · simp only [weight237, map_mul, map_pow, map_neg, map_one, map_ofNat,
      map_natCast]
    ring
  · simp

theorem resolve (F : PowerSeries ℚ) (w : ℕ → ℤ)
    (hw0 : w 0 = 1)
    (hw9 : ∀ j, 0 < j → (9 : ℤ) ∣ ((2*j+1 : ℕ) : ℤ)*w j)
    (hF : F = PowerSeries.map (Int.castRingHom ℚ) (triangular w)) :
    (∃ A : PowerSeries ℚ, constantCoeff A = 1 ∧ A^3 * F = 1) ∧
      ∀ A : PowerSeries ℚ, (constantCoeff A = 1 ∧ A^3 * F = 1) →
        ∃ a : ℕ → ℤ, (∀ m, coeff m A = (a m : ℚ)) ∧
          ∀ n, (5 : ℤ) ∣ a (5*n+4) ∧ (7 : ℤ) ∣ a (7*n+5) := by
  have hz : constantCoeff (triangular w) = 1 := by
    rw [triangular_constant, hw0]
  obtain ⟨B, hB0, hB⟩ := integral_inverse_of_nine (triangular w) hz
    (triangular_divisible w hw9)
  let A0 : PowerSeries ℚ := B.map (Int.castRingHom ℚ)
  have ha0 : constantCoeff A0 = 1 :=
    Eq.symm (Rat.ext (id (Eq.symm hB0)) rfl)
  have ha : A0^3 * F = 1 := by
    rw [hF]
    simpa only [map_mul, map_pow, map_one, A0] using
      congrArg (PowerSeries.map (Int.castRingHom ℚ)) hB
  have hF0 : constantCoeff F = 1 := by
    rw [hF]
    change ((constantCoeff (triangular w) : ℤ) : ℚ) = 1
    rw [hz, Int.cast_one]
  refine ⟨⟨A0, ha0, ha⟩, ?_⟩
  intro A hA
  have hu : A = A0 := normalized_cube_unique F A A0 hF0 hA.1 ha0 hA.2 ha
  refine ⟨fun m => coeff m B, ?_, ?_⟩
  · intro m
    rw [hu]
    rfl
  · intro n
    exact triangular_inverse_congruences w B hB n

theorem result : claim := by
  exact resolve F weight237 (by norm_num [weight237]) weight237_nine source237

end D5.S1.Recurrence.Residue.BalaA193237ModFiveSeven

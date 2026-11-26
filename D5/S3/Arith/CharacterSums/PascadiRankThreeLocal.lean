/- GID: D5/S3/Arith/CharacterSums/PascadiRankThreeLocal
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiRankThreeLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local saturation and coordinate discriminant of a nonzero Dixon triple. -/

import D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-! Local saturation and the discriminant strata of a nonzero Dixon triple. -/

namespace D5.S3.Arith.CharacterSums.PrimeCube

open Polynomial
open scoped BigOperators

noncomputable section

set_option maxRecDepth 4000

/-- Subtracting a multiple of (L) by a linear polynomial adds multiples
of the third row of the Dixon matrix to its first two rows. -/
private theorem residual_sub_linear_mul (l m q r s : Fin 3 → ℤ) (lam δ : ℤ) :
    residual l m (fun i => q i - lam * l i)
      (fun i => r i - δ * l i - lam * m i) (fun i => s i - δ * m i) =
      residual l m q r s := by
  have hM : residualMatrix l m (fun i => q i - lam * l i)
      (fun i => r i - δ * l i - lam * m i) (fun i => s i - δ * m i) =
      !![1,0,-lam; 0,1,-δ; 0,0,1] * residualMatrix l m q r s := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [residualMatrix, bracket, Matrix.det_fin_three, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> ring
  unfold residual
  rw [hM, Matrix.det_mul]
  simp [Matrix.det_fin_three]

private theorem bracket_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b c : Fin 3 → R) :
    f (bracket a b c) = bracket (f ∘ a) (f ∘ b) (f ∘ c) := by
  simp [bracket, Matrix.det_fin_three]

private theorem bracket_plucker {R : Type*} [CommRing R] (l m s q r : Fin 3 → R) :
    bracket r q l * bracket s l m =
      bracket r s l * bracket q l m - bracket q s l * bracket r l m := by
  simp [bracket, Matrix.det_fin_three]
  ring

/-- The single term of Dixon degree five after the constant and linear
columns have been scaled by the third and first powers of the prime. -/
private theorem residual_fifth_term (l m Q R s : Fin 3 → ℤ) (P : ℤ) :
    P ^ 6 ∣ residual l m (fun i => P ^ 3 * Q i) (fun i => P * R i) s -
      P ^ 5 * (bracket R Q l * bracket s R l * bracket m s l) := by
  have hM : residualMatrix l m (fun i => P ^ 3 * Q i) (fun i => P * R i) s =
      !![P ^ 4 * bracket R Q l, P ^ 3 * bracket s Q l + P ^ 4 * bracket R Q m,
          P ^ 3 * bracket s Q m;
         P ^ 3 * bracket s Q l, P * bracket s R l + P ^ 3 * bracket s Q m,
          P * bracket s R m;
         P ^ 3 * bracket m Q l, P * bracket m R l, bracket m s l] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [residualMatrix, bracket, Matrix.det_fin_three] <;> ring
  change P ^ 6 ∣ (residualMatrix l m (fun i => P ^ 3 * Q i)
    (fun i => P * R i) s).det - _
  rw [hM]
  refine ⟨bracket R Q l * (P * bracket s Q m * bracket m s l -
      bracket s R m * bracket m R l) -
    (bracket s Q l + P * bracket R Q m) *
      (bracket s Q l * bracket m s l - P * bracket s R m * bracket m Q l) +
    bracket s Q m * (P * bracket s Q l * bracket m R l -
      (P * bracket s R l + P ^ 3 * bracket s Q m) * bracket m Q l), ?_⟩
  simp [Matrix.det_fin_three] <;> ring

private theorem prime_cancel_pow {p : ℕ} [Fact p.Prime] {u x : ℤ} {n : ℕ}
    (hu : ¬ (p : ℤ) ∣ u) (h : (p : ℤ) ^ n ∣ u * x) : (p : ℤ) ^ n ∣ x :=
  (((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr hu).pow_left
    (m := n)).dvd_of_dvd_mul_left h

private theorem pow_cancel {P x : ℤ} (hP : P ≠ 0) {n k : ℕ}
    (h : P ^ (n + k) ∣ P ^ n * x) : P ^ k ∣ x := by
  rw [pow_add] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hP)).mp h

private theorem fifth_term_unit {p : ℕ} [Fact p.Prime] (l m Q R s : Fin 3 → ℤ)
    (h : ¬ (p : ℤ) ^ 6 ∣
      residual l m (fun i => (p : ℤ) ^ 3 * Q i) (fun i => (p : ℤ) * R i) s) :
    ¬ (p : ℤ) ∣ bracket R Q l * bracket s R l * bracket m s l := by
  intro hdiv
  apply h
  have ht := residual_fifth_term l m Q R s (p : ℤ)
  have hm := mul_dvd_mul (dvd_refl ((p : ℤ) ^ 5)) hdiv
  rw [← pow_succ] at hm
  simpa only [sub_add_cancel] using dvd_add ht hm

private theorem bracket_cyclic (q l m : Fin 3 → ℤ) :
    bracket m q l = bracket q l m := by
  simp [bracket, Matrix.det_fin_three]
  ring

private theorem bracket_translate_eval (l m q r s : Fin 3 → ℤ) (β lam δ : ℤ) :
    let L := fun i => l i + β * m i
    let Q := fun i => q i + β * r i + β ^ 2 * s i - lam * L i
    let R := fun i => r i + 2 * β * s i - δ * L i - lam * m i
    let S := fun i => s i - δ * m i
    bracket Q L m = bracket q l m + β * bracket r l m + β ^ 2 * bracket s l m ∧
      bracket R L m = bracket r l m + 2 * β * bracket s l m ∧
      bracket S L m = bracket s l m := by
  dsimp
  constructor
  · simp [bracket, Matrix.det_fin_three] <;> ring
  constructor
  · simp [bracket, Matrix.det_fin_three] <;> ring
  · simp [bracket, Matrix.det_fin_three] <;> ring

private theorem bracket_height (a b c : Fin 3 → ℤ) (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (ha : ∀ i, |(a i : ℝ)| ≤ A) (hb : ∀ i, |(b i : ℝ)| ≤ B)
    (hc : ∀ i, |(c i : ℝ)| ≤ C) :
    |((bracket a b c : ℤ) : ℝ)| ≤ 6 * A * B * C := by
  let a' : Fin 3 → ℝ := fun i => (a i : ℝ) / A
  let b' : Fin 3 → ℝ := fun i => (b i : ℝ) / B
  let c' : Fin 3 → ℝ := fun i => (c i : ℝ) / C
  have H := bracket_uniform_bound a' b' c' 1
    (fun i => by
      simpa [a', abs_div, abs_of_pos hA] using
        (div_le_iff₀ hA).2 (by simpa only [one_mul] using ha i))
    (fun i => by
      simpa [b', abs_div, abs_of_pos hB] using
        (div_le_iff₀ hB).2 (by simpa only [one_mul] using hb i))
    (fun i => by
      simpa [c', abs_div, abs_of_pos hC] using
        (div_le_iff₀ hC).2 (by simpa only [one_mul] using hc i))
  have hmap := bracket_map (Int.castRingHom ℝ) a b c
  change ((bracket a b c : ℤ) : ℝ) = bracket (fun i => (a i : ℝ)) (fun i => (b i : ℝ))
    (fun i => (c i : ℝ)) at hmap
  have hscale := bracket_scale a' b' c' A B C
  have ha' (i : Fin 3) : A * a' i = (a i : ℝ) := by dsimp [a']; field_simp
  have hb' (i : Fin 3) : B * b' i = (b i : ℝ) := by dsimp [b']; field_simp
  have hc' (i : Fin 3) : C * c' i = (c i : ℝ) := by dsimp [c']; field_simp
  simp only [ha', hb', hc'] at hscale
  rw [hmap, hscale, abs_mul, abs_of_pos (by positivity : 0 < A * B * C)]
  norm_num at H
  calc
    _ ≤ A * B * C * 6 := mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by ring

private theorem quadratic_coefficients (a b c : ℤ) :
    (quadratic a b c).coeff 0 = a ∧ (quadratic a b c).coeff 1 = b ∧
      (quadratic a b c).coeff 2 = c := by
  simp only [quadratic, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C]
  norm_num

private theorem primitive_cofactors (A B C : ℤ) (hC : C ≠ 0) :
    ∃ g a b c : ℤ, g ≠ 0 ∧ (quadratic a b c).IsPrimitive ∧
      A = g * a ∧ B = g * b ∧ C = g * c := by
  let F := quadratic A B C
  have hF : F ≠ 0 := by
    intro h
    have := congrArg (fun f : ℤ[X] => f.coeff 2) h
    exact hC ((quadratic_coefficients A B C).2.2.symm.trans (by simpa [F] using this))
  let f := F.primPart
  have hdeg : F.natDegree ≤ 2 := by
    unfold F quadratic
    compute_degree
  have hfdeg : f.natDegree ≤ 2 := by simpa [f, natDegree_primPart] using hdeg
  have hf : f = quadratic (f.coeff 0) (f.coeff 1) (f.coeff 2) := by
    ext i
    rcases i with _ | _ | _ | i
    · exact (quadratic_coefficients _ _ _).1.symm
    · exact (quadratic_coefficients _ _ _).2.1.symm
    · exact (quadratic_coefficients _ _ _).2.2.symm
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hfdeg (by omega))]
      simp only [quadratic, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C]
      have h₀ : i + 1 + 1 + 1 ≠ 0 := by omega
      have h₁ : i + 1 + 1 + 1 ≠ 1 := by omega
      have h₂ : i + 1 + 1 + 1 ≠ 2 := by omega
      simp [h₀, h₁, h₂]
  have hmul (i : ℕ) : F.coeff i = F.content * f.coeff i := by
    rw [← coeff_C_mul, ← F.eq_C_content_mul_primPart]
  have h := quadratic_coefficients A B C
  refine ⟨F.content, f.coeff 0, f.coeff 1, f.coeff 2, ?_, ?_,
    h.1.symm.trans (hmul 0), h.2.1.symm.trans (hmul 1), h.2.2.symm.trans (hmul 2)⟩
  · exact fun hg => hF (content_eq_zero_iff.mp hg)
  · rw [← hf]
    exact F.isPrimitive_primPart

private theorem abs_factor_le (g x : ℤ) (hg : g ≠ 0) : |(x : ℝ)| ≤ |((g * x : ℤ) : ℝ)| := by
  have h : (1 : ℤ) ≤ |g| := by have := abs_pos.mpr hg; omega
  have h' : (1 : ℝ) ≤ |(g : ℝ)| := by exact_mod_cast h
  rw [Int.cast_mul, abs_mul]
  simpa using mul_le_mul_of_nonneg_right h' (abs_nonneg (x : ℝ))

private theorem pivot_exists {p : ℕ} [Fact p.Prime] (l m s : Fin 3 → ℤ) (I J : ℝ)
    (hI : 1 ≤ I) (_hJ : 1 ≤ J) (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I)
    (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J) (hsize : 18 * (I * J) < (p : ℝ))
    (hunit : ¬ (p : ℤ) ∣ bracket s l m) :
    ∃ i j, ¬ (p : ℤ) ∣ l i * m j - l j * m i := by
  have hn : bracket s l m ≠ 0 := fun h => hunit (h ▸ dvd_zero _)
  have heq : bracket s l m =
      s 0 * (l 1 * m 2 - l 2 * m 1) - s 1 * (l 0 * m 2 - l 2 * m 0) +
        s 2 * (l 0 * m 1 - l 1 * m 0) := by
    simp [bracket, Matrix.det_fin_three]
    ring
  obtain ⟨i,j,hij⟩ : ∃ i j, l i * m j - l j * m i ≠ 0 := by
    by_contra! h
    exact hn (by rw [heq, h 1 2, h 0 2, h 0 1]; ring)
  refine ⟨i,j,fun hd => ?_⟩
  have H (i j : Fin 3) : |(l i : ℝ) * (m j : ℝ)| ≤ 3 * I * (3 * J) := by
    rw [abs_mul]
    exact mul_le_mul (hl i) (hm j) (abs_nonneg _) (by positivity)
  have hbound : |((l i * m j - l j * m i : ℤ) : ℝ)| ≤ 18 * (I * J) := by
    push_cast
    calc
      _ ≤ |(l i : ℝ) * (m j : ℝ)| + |(l j : ℝ) * (m i : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith only [H i j, H j i]
  have hle : (p : ℝ) ≤ |((l i * m j - l j * m i : ℤ) : ℝ)| := by
    exact_mod_cast Int.le_abs_of_dvd hij hd
  exact (not_lt_of_ge hle) (hbound.trans_lt hsize)

private theorem gap_identity (l m R S : Fin 3 → ℤ) (i j : Fin 3) :
    (l i * m j - l j * m i) * bracket S R l =
      bracket R l m * (l i * S j - l j * S i) -
        bracket S l m * (l i * R j - l j * R i) := by
  fin_cases i <;> fin_cases j <;> simp [bracket, Matrix.det_fin_three] <;> ring

/-- The actual cofactor line, its primitive integral generator, and its two
local discriminant strata. In the ramified case the last expression is the
derivative of the row with L proportional to T after its quadratic term
has been eliminated. Its scale is a product of p-units. -/
structure RankThreeKernel (p : ℕ) (l m q r s : Fin 3 → ℤ)
    (β lam δ : ℤ) (I J : ℝ) (g a b c d : ℤ) : Prop where
  cofactor_q : bracket q l m = g * a
  cofactor_r : bracket r l m = g * b
  cofactor_s : bracket s l m = g * c
  primitive : (quadratic a b c).IsPrimitive
  pure_combination : ∃ x : Fin 3 → ℤ,
    (∑ i, x i * l i) = 0 ∧ (∑ i, x i * m i) = 0 ∧
    (∑ i, x i * q i) = g * a ∧ (∑ i, x i * r i) = g * b ∧ (∑ i, x i * s i) = g * c
  minor_unit : ¬ (p : ℤ) ∣ bracket s l m
  leading_unit : ¬ (p : ℤ) ∣ c
  value : (p : ℤ)^3 ∣ a + β * b + β^2 * c
  derivative : (p : ℤ) ∣ b + 2 * β * c
  height_a : |(a : ℝ)| ≤ 54 * I^2 * (I * J)
  height_b : |(b : ℝ)| ≤ 108 * (I * J)^2
  height_c : |(c : ℝ)| ≤ 54 * J^2 * (I * J)
  discriminant : b^2 - 4 * a * c = (p : ℤ)^2 * d
  discriminant_nonzero : d ≠ 0
  discriminant_height : |(d : ℝ)| ≤ 23328 * (I * J)^4 / (p : ℝ)^2
  local_strata :
    ∃ i j : Fin 3, ¬ (p : ℤ) ∣ l i * m j - l j * m i ∧
      ((¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ)^2 ∣ b + 2 * β * c ∧
        ∃ t : ℤ, b + 2 * β * c = (p : ℤ) * t ∧
          (t : ZMod p) ≠ 0 ∧ (d : ZMod p) = (t : ZMod p)^2) ∨
       ((p : ℤ) ∣ d ∧ ¬ (p : ℤ)^2 ∣ d ∧
        ¬ (p : ℤ)^4 ∣ a + β * b + β^2 * c ∧ (p : ℤ)^2 ∣ b + 2 * β * c ∧
        let L := fun k => l k + β * m k
        let R := fun k => r k + 2 * β * s k - δ * L k - lam * m k
        let S := fun k => s k - δ * m k
        let gap := c * (L i * R j - L j * R i) -
          (b + 2 * β * c) * (L i * S j - L j * S i)
        (p : ℤ) ∣ gap ∧ ¬ (p : ℤ)^2 ∣ gap))

private theorem discriminant_strata {p : ℕ} [Fact p.Prime] (a b c : ℤ)
    (hodd : p ≠ 2) (ha : (p : ℤ)^3 ∣ a) (hb : (p : ℤ) ∣ b)
    (hc : ¬ (p : ℤ) ∣ c) (hlimit : ¬ ((p : ℤ)^4 ∣ a ∧ (p : ℤ)^2 ∣ b)) :
    ∃ d : ℤ, b^2 - 4 * a * c = (p : ℤ)^2*d ∧ d ≠ 0 ∧
      ((¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ)^2 ∣ b ∧
        ∃ t : ℤ, b = (p : ℤ)*t ∧ (t : ZMod p) ≠ 0 ∧
          (d : ZMod p) = (t : ZMod p)^2) ∨
        ((p : ℤ) ∣ d ∧ ¬ (p : ℤ)^2 ∣ d ∧ ¬ (p : ℤ)^4 ∣ a ∧ (p : ℤ)^2 ∣ b)) := by
  let P : ℤ := p
  have hP : Prime P := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  obtain ⟨u, hu⟩ := ha
  obtain ⟨t, ht⟩ := hb
  let d := t^2 - 4 * P * u * c
  have hd : b^2 - 4 * a * c = P^2 * d := by rw [hu, ht]; dsimp [d, P]; ring
  have hz : (d : ZMod p) = (t : ZMod p)^2 := by simp [d, P]
  have htwo : ¬ P ∣ 2 := by
    intro h
    change (p : ℤ) ∣ (↑(2 : ℕ) : ℤ) at h
    have hn : p ∣ 2 := by exact_mod_cast h
    exact hodd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hn)
  have hfour : ¬ P ∣ 4 := by
    simpa only [show (2 : ℤ) * 2 = 4 by decide] using hP.not_dvd_mul htwo htwo
  have h4c : ¬ P ∣ 4*c := hP.not_dvd_mul hfour hc
  by_cases hpd : P ∣ d
  · have hdz : (d : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hpd
    have ht0 : (t : ZMod p) = 0 := by
      have ht2 := hz.symm.trans hdz
      simpa only [pow_two, mul_eq_zero, or_self] using ht2
    have hpt : P ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ht0
    have hb2 : P^2 ∣ b := by rw [ht, pow_two]; exact mul_dvd_mul dvd_rfl hpt
    have ha4 : ¬ P^4 ∣ a := fun h => hlimit ⟨h,hb2⟩
    have hd2 : ¬ P^2 ∣ d := by
      intro h
      have hd4 : P^4 ∣ b^2 - 4 * a * c := by
        rw [hd, show (4 : ℕ) = 2+2 by decide, pow_add]
        exact mul_dvd_mul dvd_rfl h
      have hb4 : P^4 ∣ b^2 := by simpa only [← pow_mul] using pow_dvd_pow_of_dvd hb2 2
      have hh : P^4 ∣ (4*c)*a := by
        convert dvd_sub hb4 hd4 using 1
        ring
      exact ha4 (prime_cancel_pow h4c hh)
    exact ⟨d, hd, fun h => hd2 (h ▸ dvd_zero _), Or.inr ⟨hpd,hd2,ha4,hb2⟩⟩
  · have htn : (t : ZMod p) ≠ 0 := by
      intro h
      apply hpd
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simp [hz,h])
    have hb2 : ¬ P^2 ∣ b := by
      intro h
      rw [ht] at h
      have ht' : P ^ 1 ∣ t := pow_cancel hP.ne_zero (n := 1) (k := 1)
        (by simpa only [pow_one] using h)
      exact htn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by simpa only [pow_one] using ht'))
    exact ⟨d, hd, fun h => hpd (h ▸ dvd_zero _), Or.inl ⟨hpd,hb2,t,ht,htn,hz⟩⟩

set_option maxHeartbeats 1600000 in
/-- For the original three rows, an exact fifth-power Dixon residual makes
the cofactor minor in the leading quadratic column a p-unit. The primitive
kernel inherits the two congruences and has precisely the two local strata. -/
theorem nonzero_dixon_rank_three {p : ℕ} [Fact p.Prime] (l m q r s : Fin 3 → ℤ)
    (β lam δ : ℤ) (I J : ℝ) (hI : 1 ≤ I) (hJ : 1 ≤ J) (hodd : p ≠ 2)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I) (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I^2) (hr : ∀ i, |(r i : ℝ)| ≤ 2*I*J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J^2) (hsize : 18 * (I * J) < (p : ℝ))
    (hval : ∀ i, (p : ℤ)^3 ∣ q i + β * r i + β^2 * s i - lam * (l i + β * m i))
    (hder : ∀ i, (p : ℤ) ∣ r i + 2 * β * s i - δ * (l i + β * m i) - lam*m i)
    (hD : ¬ (p : ℤ)^6 ∣ residual l m q r s) :
    ∃ g a b c d, RankThreeKernel p l m q r s β lam δ I J g a b c d := by
  let P : ℤ := p
  have hP : Prime P := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  let L : Fin 3 → ℤ := fun i => l i + β * m i
  let U : Fin 3 → ℤ := fun i => q i + β*r i + β^2*s i - lam*L i
  let V : Fin 3 → ℤ := fun i => r i + 2*β*s i - δ*L i - lam*m i
  let S : Fin 3 → ℤ := fun i => s i - δ*m i
  choose Q hQ using hval
  choose R hR using hder
  have hU : U = fun i => P^3 * Q i := funext hQ
  have hV : V = fun i => P * R i := funext hR
  have hshear : residual L m U V S = residual l m q r s :=
    (residual_sub_linear_mul L m (fun i => q i + β*r i + β^2*s i)
      (fun i => r i + 2*β*s i) s lam δ).trans (residual_translate l m q r s β)
  have hexact := fifth_term_unit (p := p) L m Q R S (by rwa [← hU, ← hV, hshear])
  have hX : ¬ P ∣ bracket R Q L :=
    fun h => hexact ((h.mul_right _).mul_right _)
  have hY : ¬ P ∣ bracket S R L :=
    fun h => hexact ((h.mul_left _).mul_right _)
  have hZ : ¬ P ∣ bracket S L m := fun h =>
    hexact ((bracket_cyclic S L m ▸ h).mul_left _)
  obtain ⟨hqT, hrT, hsT⟩ := bracket_translate_eval l m q r s β lam δ
  change bracket U L m = _ at hqT
  change bracket V L m = _ at hrT
  change bracket S L m = _ at hsT
  have hunit : ¬ P ∣ bracket s l m := hsT ▸ hZ
  have hn : bracket s l m ≠ 0 := fun h => hunit (h ▸ dvd_zero _)
  obtain ⟨g,a,b,c,hg,hprim,ha,hb,hc⟩ :=
    primitive_cofactors (bracket q l m) (bracket r l m) (bracket s l m) hn
  have hgc : ¬ P ∣ g * c := hc ▸ hunit
  have hgunit : ¬ P ∣ g := fun h => hgc (h.mul_right _)
  have hcunit : ¬ P ∣ c := fun h => hgc (h.mul_left _)
  let A := a + β*b + β^2*c
  let B := b + 2*β*c
  have hA : P^3 * bracket Q L m = g*A := by
    have H := bracket_scale Q L m (P^3) 1 1
    simp only [one_mul, mul_one, ← hU] at H
    rw [← H, hqT, ha, hb, hc]
    dsimp [A]
    ring
  have hB : P * bracket R L m = g*B := by
    have H := bracket_scale R L m P 1 1
    simp only [one_mul, mul_one, ← hV] at H
    rw [← H, hrT, hb, hc]
    dsimp [B]
    ring
  have hA3 : P^3 ∣ A := prime_cancel_pow hgunit (hA ▸ dvd_mul_right _ _)
  have hB1 : P ∣ B := by
    have hh : P^1 ∣ g*B := by rw [pow_one, ← hB]; exact dvd_mul_right _ _
    simpa only [pow_one] using prime_cancel_pow hgunit hh
  have hlimit : ¬ (P^4 ∣ A ∧ P^2 ∣ B) := by
    rintro ⟨ha4,hb2⟩
    have hA' : P ∣ bracket Q L m := by
      simpa only [pow_one] using pow_cancel hP.ne_zero (n := 3) (k := 1)
        (hA.symm ▸ ha4.mul_left g)
    have hB' : P ∣ bracket R L m := by
      simpa only [pow_one] using pow_cancel hP.ne_zero (n := 1) (k := 1)
        (by simpa only [pow_one] using (hB.symm ▸ hb2.mul_left g))
    have h := dvd_sub (hA'.mul_left (bracket R S L)) (hB'.mul_left (bracket Q S L))
    rw [← bracket_plucker] at h
    exact hP.not_dvd_mul hX hZ h
  obtain ⟨d,hd,hd0,hcases⟩ := discriminant_strata A B c hodd hA3 hB1 hcunit hlimit
  have hdorig : b^2 - 4 * a * c = P^2 * d := by
    rw [← hd]
    dsimp [A,B]
    ring
  have hIp : 0 < I := by linarith
  have hJp : 0 < J := by linarith
  have haB : |(a : ℝ)| ≤ 54 * I^2 * (I*J) := by
    have hh := bracket_height q l m (I^2) (3*I) (3*J)
      (by positivity) (by positivity) (by positivity) hq hl hm
    rw [ha] at hh
    exact (abs_factor_le g a hg).trans (hh.trans_eq (by ring))
  have hbB : |(b : ℝ)| ≤ 108 * (I*J)^2 := by
    have hh := bracket_height r l m (2*I*J) (3*I) (3*J)
      (by positivity) (by positivity) (by positivity) hr hl hm
    rw [hb] at hh
    exact (abs_factor_le g b hg).trans (hh.trans_eq (by ring))
  have hcB : |(c : ℝ)| ≤ 54 * J^2 * (I*J) := by
    have hh := bracket_height s l m (J^2) (3*I) (3*J)
      (by positivity) (by positivity) (by positivity) hs hl hm
    rw [hc] at hh
    exact (abs_factor_le g c hg).trans (hh.trans_eq (by ring))
  have hdiscB : |((b^2 - 4 * a * c : ℤ) : ℝ)| ≤ 23328 * (I*J)^4 := by
    push_cast
    calc
      _ ≤ |(b : ℝ)^2| + |4*(a : ℝ)*(c : ℝ)| := abs_sub _ _
      _ = |(b : ℝ)|^2 + 4*(|(a : ℝ)| * |(c : ℝ)|) := by norm_num [abs_pow, abs_mul]; ring
      _ ≤ (108 * (I*J)^2)^2 + 4*((54 * I^2 * (I*J))*(54 * J^2 * (I*J))) := by
        gcongr
      _ = _ := by ring
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hdB : |(d : ℝ)| ≤ 23328 * (I*J)^4 / (p : ℝ)^2 := by
    rw [hdorig, Int.cast_mul, Int.cast_pow, abs_mul] at hdiscB
    have hcast : (P : ℝ) = (p : ℝ) := by simp [P]
    rw [hcast, abs_of_pos (pow_pos hpR 2)] at hdiscB
    exact (le_div_iff₀ (pow_pos hpR 2)).2 (by simpa [mul_comm] using hdiscB)
  obtain ⟨i,j,hij⟩ := pivot_exists l m s I J hI hJ hl hm hsize hunit
  let x : Fin 3 → ℤ :=
    ![l 1*m 2 - l 2*m 1, l 2*m 0 - l 0*m 2, l 0*m 1 - l 1*m 0]
  have hx (v : Fin 3 → ℤ) : (∑ i, x i * v i) = bracket v l m := by
    simp [x, Fin.sum_univ_three, bracket, Matrix.det_fin_three] <;> ring
  have hxL : (∑ i, x i * l i) = 0 := by
    rw [hx]
    simp [bracket, Matrix.det_fin_three] <;> ring
  have hxM : (∑ i, x i * m i) = 0 := by
    rw [hx]
    simp [bracket, Matrix.det_fin_three] <;> ring
  refine ⟨g,a,b,c,d,ha,hb,hc,hprim,⟨x,hxL,hxM,(hx q).trans ha,(hx r).trans hb,(hx s).trans hc⟩,hunit,hcunit,hA3,hB1,haB,hbB,hcB,hdorig,hd0,hdB,
    i,j,hij,?_⟩
  rcases hcases with he | ⟨hd1,hd2,ha4,hb2⟩
  · exact Or.inl he
  · refine Or.inr ⟨hd1,hd2,ha4,hb2,?_⟩
    let gap := c * (L i * V j - L j * V i) - B * (L i * S j - L j * S i)
    change P ∣ gap ∧ ¬ P^2 ∣ gap
    have hgapeq : (L i*m j - L j*m i) * bracket S V L = -(g * gap) := by
      rw [gap_identity, hrT, hsT, hb, hc]
      dsimp [gap,B]
      ring
    have hLij : ¬ P ∣ L i*m j - L j*m i := by
      convert hij using 2 <;> dsimp [L] <;> ring
    have hbr : bracket S V L = P * bracket S R L := by
      have hh := bracket_scale S R L 1 P 1
      simpa only [one_mul, mul_one, ← hV] using hh
    constructor
    · dsimp [gap]
      rw [hV]
      exact dvd_sub
        ((dvd_sub ((dvd_mul_right P (R j)).mul_left (L i))
          ((dvd_mul_right P (R i)).mul_left (L j))).mul_left c)
        (hB1.mul_right _)
    · intro hgap
      have H : P^2 ∣ (L i*m j - L j*m i) * bracket S V L := by
        rw [hgapeq]
        exact dvd_neg.mpr (hgap.mul_left g)
      have H' := prime_cancel_pow hLij H
      rw [hbr] at H'
      have hh : P^1 ∣ bracket S R L := pow_cancel hP.ne_zero (n := 1) (k := 1)
        (by simpa only [pow_one] using H')
      exact hY (by simpa only [pow_one] using hh)

end

end D5.S3.Arith.CharacterSums.PrimeCube

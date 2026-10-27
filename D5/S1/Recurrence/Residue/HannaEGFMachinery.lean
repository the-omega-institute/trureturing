/- GID: D5/S1/Recurrence/Residue/HannaEGFMachinery
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/HannaEGFMachinery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Recurrence/Residue/HannaA232694Congruences.result; instance=D5/S1/Recurrence/Residue/HannaA232694Congruences.multiple3
   digest: Integral derivative-substitution recurrences and modular residual transfer. -/

/-
admission_basis: escape-witness
escape_witness: multiple_cancel (triangular cancellation), residual_transfer (integral inverse recurrence and modular transport)
Direct frozen dependencies: generated per declaration in the Stage A envelope.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21758.
The rational series equation is stated as printed; coefficient congruences concern n! times coeff n A.
The convolution and power constructions are reused from ExponentialImplicitParityPeriodThree.
-/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext constantCoeff_encode)

open D5.S1.Recurrence.Parity.ExponentialImplicitParityPeriodThree

namespace D5.S1.Recurrence.Residue.HannaEGFMachinery
variable {R S : Type*} [CommRing R] [CommRing S]

private def seqInv (f : ℕ → R) : ℕ → R
  | 0 => 1
  | n+1 => - ∑ i : Fin (n+1), ((n+1).choose (i+1) : R) * f (i+1) * seqInv f (n-i)
termination_by n => n

private def inner (f : ℕ → R) (k : ℕ) (recip : Bool) : ℕ → R
  | 0 => 0
  | n+1 => (n+1 : R) * (if recip then seqInv (fun j => f (j+1)) n
    else egfPow (fun j => f (j+1)) k n)

private def rhs (f : ℕ → R) (k p : ℕ) (recip : Bool) : ℕ → R :=
  egfPow (composition f (inner f k recip)) p

private theorem conv_map (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
    φ (egfMul f g n) = egfMul (fun j => φ (f j)) (fun j => φ (g j)) n := by
  simp [egfMul]

private theorem seqPow_map (φ : R →+* S) (f : ℕ → R) (k n : ℕ) :
    φ (egfPow f k n) = egfPow (fun j => φ (f j)) k n := by
  induction k generalizing n with
  | zero => simp [egfPow, egfOne]
  | succ k ih =>
    rw [egfPow, conv_map, egfPow]
    congr 1
    funext j
    exact ih j

private theorem seqInv_map (φ : R →+* S) (f : ℕ → R) (n : ℕ) :
    φ (seqInv f n) = seqInv (fun j => φ (f j)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [seqInv]
    | succ n =>
      simp only [seqInv, map_neg, map_sum, map_mul, map_natCast]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [ih (n-i) (by omega)]

private theorem seqInv_congr {f g : ℕ → R} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) : seqInv f n = seqInv g n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [seqInv]
    | succ n =>
      simp only [seqInv]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [h (i+1) (by omega), ih (n-i) (by omega) (fun j hj => h j (by omega))]

private theorem inner_map (φ : R →+* S) (f : ℕ → R) (k n : ℕ) (r : Bool) :
    φ (inner f k r n) = inner (fun j => φ (f j)) k r n := by
  cases n with
  | zero => simp [inner]
  | succ n => cases r <;> simp [inner, seqInv_map, seqPow_map]

private theorem inner_congr {f g : ℕ → R} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) (k : ℕ) (r : Bool) :
    inner f k r n = inner g k r n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [inner]
    congr 1
    split
    · exact seqInv_congr (fun i hi => h (i+1) (by omega))
    · exact egfPow_congr_at (m := k) (fun i hi => h (i+1) (by omega))

private theorem rhs_map (φ : R →+* S) (f : ℕ → R) (k p n : ℕ) (r : Bool) :
    φ (rhs f k p r n) = rhs (fun j => φ (f j)) k p r n := by
  rw [rhs, seqPow_map, rhs]
  congr 1
  funext j
  rw [composition_map]
  congr 1
  funext i
  exact inner_map φ f k i r

private theorem rhs_congr {f g : ℕ → R} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) (k p : ℕ) (r : Bool) :
    rhs f k p r n = rhs g k p r n := by
  apply egfPow_congr_at (m := p)
  intro i hi
  apply composition_congr (fun j hj => h j (by omega))
  intro j hj
  exact inner_congr (fun t ht => h t (by omega)) k r

private theorem encode_coeff (f : PowerSeries ℚ) : encode (eCoeff f) = f := by
  exact egfSeries_egfCoeffs f

private theorem eCoeff_pow (f : PowerSeries ℚ) (k n : ℕ) :
    eCoeff (f ^ k) n = egfPow (eCoeff f) k n := by
  have he := congrArg (fun F : PowerSeries ℚ => eCoeff F n) (egfSeries_pow (eCoeff f) k)
  change eCoeff (encode (egfPow (eCoeff f) k)) n = eCoeff (encode (eCoeff f) ^ k) n at he
  simpa only [eCoeff_encode, encode_coeff] using he.symm

private theorem encode_mul (f g : ℕ → ℚ) : encode (egfMul f g) = encode f * encode g := by
  exact egfSeries_mul f g

private theorem seqInv_spec (f : ℕ → R) (hf : f 0 = 1) (n : ℕ) :
    egfMul f (seqInv f) n = egfOne n := by
  cases n with
  | zero => simp [egfMul, seqInv, egfOne, hf]
  | succ n =>
    rw [egfMul, sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, hf, Nat.sub_zero]
    rw [seqInv, Fin.sum_univ_eq_sum_range (fun i =>
      ((n+1).choose (i+1) : R) * f (i+1) * seqInv f (n-i))]
    simp only [egfOne, Nat.succ_ne_zero, if_false]
    have he : (∑ i ∈ range (n+1), ((n+1).choose (i+1) : R) * f (i+1) *
        seqInv f (n+1-(i+1))) =
        ∑ i ∈ range (n+1), ((n+1).choose (i+1) : R) * f (i+1) * seqInv f (n-i) := by
      apply sum_congr rfl
      intro i hi
      rw [show n+1-(i+1) = n-i by omega]
    rw [he]
    ring

private theorem encode_unit : encode (egfOne : ℕ → ℚ) = 1 := by
  change egfSeries (egfOne : ℕ → ℚ) = 1
  simpa only [egfPow, pow_zero] using egfSeries_pow (fun _ : ℕ => (0 : ℚ)) 0

private theorem eCoeff_inv {f : PowerSeries ℚ} (hf : constantCoeff f = 1) (n : ℕ) :
    eCoeff f⁻¹ n = seqInv (eCoeff f) n := by
  have he : encode (seqInv (eCoeff f)) = f⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hf]; norm_num)).mpr
    rw [mul_comm]
    calc
      f * encode (seqInv (eCoeff f)) =
          encode (eCoeff f) * encode (seqInv (eCoeff f)) := by rw [encode_coeff]
      _ = encode (egfMul (eCoeff f) (seqInv (eCoeff f))) := (encode_mul _ _).symm
      _ = 1 := ?_
    have hs : egfMul (eCoeff f) (seqInv (eCoeff f)) = egfOne :=
      funext (seqInv_spec _ (by simpa using hf))
    rw [hs]
    exact encode_unit
  rw [← he, eCoeff_encode]

private theorem seqPow_zero (f : ℕ → R) (k : ℕ) : egfPow f k 0 = f 0 ^ k := by
  induction k with
  | zero => simp [egfPow, egfOne]
  | succ k ih => simp [egfPow, egfMul, ih, pow_succ', mul_comm]

private theorem rhs_zero (f : ℕ → R) (k p : ℕ) (r : Bool) : rhs f k p r 0 = f 0 ^ p := by
  simp [rhs, seqPow_zero, composition]

noncomputable def sourceRhs (f : PowerSeries ℚ) (k p : ℕ) (r : Bool) : PowerSeries ℚ :=
  (f.subst (X * (if r then (PowerSeries.derivative (R := ℚ) f)⁻¹
    else (PowerSeries.derivative (R := ℚ) f)^k)))^p

private theorem eCoeff_inner (f : PowerSeries ℚ) (k : ℕ) (r : Bool)
    (hf : r = true → constantCoeff (PowerSeries.derivative (R := ℚ) f) = 1) (n : ℕ) :
    eCoeff (X * (if r then (PowerSeries.derivative (R := ℚ) f)⁻¹
      else (PowerSeries.derivative (R := ℚ) f)^k)) n = inner (eCoeff f) k r n := by
  cases n with
  | zero => simp only [eCoeff_zero, map_mul, constantCoeff_X, zero_mul, inner]
  | succ n =>
    rw [eCoeff_X_mul]
    cases r with
    | false => simp only [Bool.false_eq_true, if_false, inner, eCoeff_pow]
               congr 2
               funext j
               exact eCoeff_derivative f j
    | true => simp only [if_true, inner, eCoeff_inv (hf rfl)]
              congr 2
              funext j
              exact eCoeff_derivative f j

private theorem eCoeff_rhs (f : PowerSeries ℚ) (k p : ℕ) (r : Bool)
    (hf : r = true → constantCoeff (PowerSeries.derivative (R := ℚ) f) = 1) (n : ℕ) :
    eCoeff (sourceRhs f k p r) n = rhs (eCoeff f) k p r n := by
  rw [sourceRhs, eCoeff_pow, rhs]
  congr 1
  funext j
  rw [eCoeff_composition _ _ (by rw [map_mul, constantCoeff_X, zero_mul])]
  congr 1
  funext i
  exact eCoeff_inner f k r hf i

private noncomputable def update (k p : ℕ) (r : Bool) (f : PowerSeries R) : PowerSeries R :=
  mk (fun n => match n with
    | 0 => 1
    | n+1 => rhs (fun j => coeff j f) k p r n)

private theorem exists_unique_sequence (k p : ℕ) (r : Bool) :
    ∃ a : ℕ → R, a 0 = 1 ∧ (∀ n, a (n+1) = rhs a k p r n) ∧
      ∀ b : ℕ → R, b 0 = 1 → (∀ n, b (n+1) = rhs b k p r n) → b = a := by
  obtain ⟨f, hf0, hff, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (update (R := R) k p r) (by intro f hf; simp [update]) (by
        intro d f g hd hf hg h
        intro n hn
        cases n with
        | zero => simp [update]
        | succ n =>
          simp only [update, coeff_mk]
          exact rhs_congr (fun i hi => h i (by omega)) k p r)
  refine ⟨fun n => coeff n f, ?_, ?_, ?_⟩
  · simpa only [coeff_zero_eq_constantCoeff] using hf0
  · intro n
    simpa only [update, coeff_mk] using congrArg (coeff (n+1)) hff
  · intro b hb0 hb
    have hbfix : mk b = update k p r (mk b) := by
      ext n
      cases n with
      | zero => simpa [update] using hb0
      | succ n => simpa [update] using hb n
    have hbeq := huniq (mk b) (by simpa using hb0) hbfix
    funext n
    simpa using congrArg (coeff n) hbeq

private theorem sequence_unique (k p : ℕ) (r : Bool) {a b : ℕ → R}
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, a (n+1) = rhs a k p r n)
    (hb : ∀ n, b (n+1) = rhs b k p r n) : a = b := by
  obtain ⟨c, hc0, hce, hcu⟩ := exists_unique_sequence (R := R) k p r
  exact (hcu a ha0 ha).trans (hcu b hb0 hb).symm

private theorem solution_sequence (A : PowerSeries ℚ) (k p : ℕ) (r : Bool)
    (h0 : constantCoeff A = 1)
    (he : PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r) :
    ∀ n, eCoeff A (n+1) = rhs (eCoeff A) k p r n := by
  have h1 : constantCoeff (PowerSeries.derivative (R := ℚ) A) = 1 := by
    rw [he, sourceRhs, map_pow]
    have hs := eCoeff_composition A
      (X * (if r then (PowerSeries.derivative (R := ℚ) A)⁻¹
        else (PowerSeries.derivative (R := ℚ) A)^k))
          (by rw [map_mul, constantCoeff_X, zero_mul]) 0
    simpa [composition, h0] using congrArg (fun q : ℚ => q^p) hs
  intro n
  rw [← eCoeff_derivative, he, eCoeff_rhs A k p r (fun _ => h1)]

private theorem integral_solution_exists_unique (k p : ℕ) (r : Bool) :
    ∃ A : PowerSeries ℚ, constantCoeff A = 1 ∧
      PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r ∧
      Integral A ∧ ∀ B : PowerSeries ℚ, constantCoeff B = 1 →
        PowerSeries.derivative (R := ℚ) B = sourceRhs B k p r → B = A := by
  obtain ⟨a, ha0, ha, _⟩ := exists_unique_sequence (R := ℤ) k p r
  let A := encode (fun n => (a n : ℚ))
  have hA0 : constantCoeff A = 1 := by simp [A, ha0]
  have hA1 : constantCoeff (PowerSeries.derivative (R := ℚ) A) = 1 := by
    rw [← eCoeff_zero, eCoeff_derivative]
    simp only [A, eCoeff_encode]
    rw [ha 0, rhs_zero, ha0, one_pow, Int.cast_one]
  have hAe : PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r := by
    apply eCoeff_ext
    intro n
    rw [eCoeff_derivative, eCoeff_rhs A k p r (fun _ => hA1)]
    rw [show eCoeff A = (fun j => (a j : ℚ)) from funext (eCoeff_encode _)]
    dsimp only
    rw [ha n]
    have hm := rhs_map (Int.castRingHom ℚ) a k p n r
    simpa only [Int.coe_castRingHom, eCoeff_encode] using hm
  refine ⟨A, hA0, hAe, ?_, ?_⟩
  · intro n
    exact ⟨a n, eCoeff_encode _ n⟩
  · intro B hB0 hBe
    apply eCoeff_ext
    exact congrFun (sequence_unique k p r (by simpa using hB0) (by simpa using hA0)
      (solution_sequence B k p r hB0 hBe) (solution_sequence A k p r hA0 hAe))

private theorem any_solution_integral (A : PowerSeries ℚ) (k p : ℕ) (r : Bool)
    (h0 : constantCoeff A = 1)
    (he : PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r) : Integral A := by
  obtain ⟨B, hB0, hBe, hBi, hBu⟩ := integral_solution_exists_unique k p r
  rw [hBu A h0 he]
  exact hBi

private theorem modular_transfer (m k p : ℕ) (r : Bool) (a f : ℕ → ℤ)
    (ha0 : a 0 = 1) (hf0 : f 0 = 1)
    (ha : ∀ n, a (n+1) = rhs a k p r n)
    (hf : ∀ n, (m : ℤ) ∣ f (n+1) - rhs f k p r n) :
    ∀ n, (m : ℤ) ∣ a n - f n := by
  have hmap : (fun n => (a n : ZMod m)) = (fun n => (f n : ZMod m)) := by
    apply sequence_unique k p r
    · simp [ha0]
    · simp [hf0]
    · intro n
      rw [ha n]
      simpa only [Int.coe_castRingHom] using rhs_map (Int.castRingHom (ZMod m)) a k p n r
    · intro n
      have hcast : ((f (n+1) - rhs f k p r n : ℤ) : ZMod m) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hf n)
      have hm := rhs_map (Int.castRingHom (ZMod m)) f k p n r
      simp only [Int.coe_castRingHom] at hm
      rw [Int.cast_sub, hm] at hcast
      exact sub_eq_zero.mp hcast
  intro n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub, congrFun hmap n, sub_self]

private theorem source_transfer (A : PowerSeries ℚ) (k p m : ℕ) (r : Bool)
    (h0 : constantCoeff A = 1)
    (he : PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r)
    (f : ℕ → ℤ) (hf0 : f 0 = 1)
    (hf : ∀ n, (m : ℤ) ∣ f (n+1) - rhs f k p r n) :
    ∃ a : ℕ → ℤ, (∀ n, eCoeff A n = (a n : ℚ)) ∧
      ∀ n, (m : ℤ) ∣ a n - f n := by
  choose a ha using any_solution_integral A k p r h0 he
  have ha0 : a 0 = 1 := by
    have h := ha 0
    simp only [eCoeff_zero, h0] at h
    exact_mod_cast h.symm
  have hae : ∀ n, a (n+1) = rhs a k p r n := by
    intro n
    have h := solution_sequence A k p r h0 he n
    have hm := rhs_map (Int.castRingHom ℚ) a k p n r
    simp only [Int.coe_castRingHom] at hm
    rw [ha, show eCoeff A = (fun j => (a j : ℚ)) from funext ha, ← hm] at h
    exact_mod_cast h
  exact ⟨a, ha, modular_transfer m k p r a f ha0 hf0 hae hf⟩

theorem residual_transfer (A F : PowerSeries ℚ) (k p m : ℕ) (r : Bool)
    (h0 : constantCoeff A = 1)
    (he : PowerSeries.derivative (R := ℚ) A = sourceRhs A k p r)
    (f : ℕ → ℤ) (hF : ∀ n, eCoeff F n = (f n : ℚ)) (hf0 : f 0 = 1)
    (hF1 : r = true → constantCoeff (PowerSeries.derivative (R := ℚ) F) = 1)
    (hr : ∀ n, ∃ z : ℤ, eCoeff (PowerSeries.derivative (R := ℚ) F -
      sourceRhs F k p r) n = (m : ℚ) * z) :
    ∃ a : ℕ → ℤ, (∀ n, eCoeff A n = (a n : ℚ)) ∧
      ∀ n, (m : ℤ) ∣ a n - f n := by
  apply source_transfer A k p m r h0 he f hf0
  intro n
  obtain ⟨z,hz⟩ := hr n
  refine ⟨z, ?_⟩
  have hsub (u v : PowerSeries ℚ) : eCoeff (u-v) n = eCoeff u n - eCoeff v n := by
    simp [eCoeff, mul_sub]
  have hm := rhs_map (Int.castRingHom ℚ) f k p n r
  simp only [Int.coe_castRingHom] at hm
  rw [hsub, eCoeff_derivative, hF, eCoeff_rhs F k p r hF1,
    show eCoeff F = (fun j => (f j : ℚ)) from funext hF, ← hm] at hz
  exact_mod_cast hz


private theorem integral_mul {F G : PowerSeries ℚ} (hF : Integral F) (hG : Integral G) :
    Integral (F*G) := by
  choose f hf using hF
  choose g hg using hG
  intro n
  refine ⟨egfMul f g n, ?_⟩
  rw [eCoeff_mul]
  simp only [hf, hg, egfMul, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem integral_derivative {F : PowerSeries ℚ} (hF : Integral F) :
    Integral (PowerSeries.derivative (R := ℚ) F) := by
  intro n
  simpa using hF (n+1)

theorem integral_pow {F : PowerSeries ℚ} (hF : Integral F) (k : ℕ) : Integral (F^k) := by
  induction k with
  | zero =>
    intro n
    refine ⟨if n = 0 then 1 else 0, ?_⟩
    cases n <;> simp [eCoeff]
  | succ k ih => simpa [pow_succ] using integral_mul ih hF

theorem integral_X_mul {F : PowerSeries ℚ} (hF : Integral F) : Integral (X*F) := by
  intro n
  cases n with
  | zero => exact ⟨0, by simp⟩
  | succ n =>
    obtain ⟨z,hz⟩ := hF n
    refine ⟨(n+1)*z, ?_⟩
    simp [eCoeff_X_mul, hz]

theorem integral_inv {F : PowerSeries ℚ} (hF : Integral F)
    (h0 : constantCoeff F = 1) : Integral F⁻¹ := by
  choose f hf using hF
  intro n
  refine ⟨seqInv f n, ?_⟩
  rw [eCoeff_inv h0, show eCoeff F = (fun j => (f j : ℚ)) from funext hf]
  simpa only [Int.coe_castRingHom] using (seqInv_map (Int.castRingHom ℚ) f n).symm

theorem integral_sub {F G : PowerSeries ℚ} (hF : Integral F) (hG : Integral G) :
    Integral (F-G) := by
  intro n
  obtain ⟨a,ha⟩ := hF n
  obtain ⟨b,hb⟩ := hG n
  refine ⟨a-b, ?_⟩
  simp [eCoeff, mul_sub] at ha hb ⊢
  rw [ha, hb]

def Multiple (m : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ n, ∃ z : ℤ, eCoeff F n = (m : ℚ) * z

private theorem conv_cancel_zero {f g : ℕ → R} (hf : f 0 = 1)
    (h : ∀ n, egfMul f g n = 0) : ∀ n, g n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := h n
    cases n with
    | zero => simpa [egfMul, hf] using he
    | succ n =>
      rw [egfMul, sum_range_succ'] at he
      have hs : (∑ i ∈ range (n+1), ((n+1).choose (i+1) : R) * f (i+1) *
          g (n+1-(i+1))) = 0 := by
        apply sum_eq_zero
        intro i hi
        rw [ih (n+1-(i+1)) (by have := mem_range.mp hi; omega), mul_zero]
      rw [hs] at he
      simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, hf,
        Nat.sub_zero, zero_add] using he

theorem multiple_cancel {U V : PowerSeries ℚ} (m : ℕ)
    (hU : Integral U) (hV : Integral V) (hU0 : constantCoeff U = 1)
    (hUV : Multiple m (U*V)) : Multiple m V := by
  choose u hu using hU
  choose v hv using hV
  have hu0 : u 0 = 1 := by
    have hh := hu 0
    simp only [eCoeff_zero, hU0] at hh
    exact_mod_cast hh.symm
  have hconv : ∀ n, egfMul (fun i => (u i : ZMod m)) (fun i => (v i : ZMod m)) n = 0 := by
    intro n
    obtain ⟨z,hz⟩ := hUV n
    have he : eCoeff (U*V) n = ((egfMul u v n : ℤ) : ℚ) := by
      rw [eCoeff_mul]
      simp [hu, hv, egfMul]
    rw [he] at hz
    have hz' : egfMul u v n = (m : ℤ)*z := by exact_mod_cast hz
    have hm := conv_map (Int.castRingHom (ZMod m)) u v n
    simp only [Int.coe_castRingHom] at hm
    rw [← hm, hz']
    simp
  have hz := conv_cancel_zero (by simp [hu0] : (u 0 : ZMod m) = 1) hconv
  intro n
  obtain ⟨z,hz'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (v n) m).mp (hz n)
  refine ⟨z, ?_⟩
  rw [hv, hz']
  push_cast
  rfl

noncomputable def finiteSeries (a : List ℚ) : PowerSeries ℚ :=
  a.foldr (fun q F => C q + X * F) 0

private theorem coeff_finiteSeries (a : List ℚ) (n : ℕ) :
    coeff n (finiteSeries a) = (a[n]?).getD 0 := by
  induction a generalizing n with
  | nil => simp [finiteSeries]
  | cons a l ih =>
    cases n with
    | zero => simp [finiteSeries]
    | succ n => simpa [finiteSeries, coeff_C] using ih n

theorem finite_multiple (a : List ℚ) (z : List ℤ) (m : ℕ)
    (he : ∀ n : Fin a.length, (n.val.factorial : ℚ) * a[n.val]! =
      (m : ℚ) * (z[n.val]! : ℚ)) : Multiple m (finiteSeries a) := by
  intro n
  by_cases hn : n < a.length
  · refine ⟨z[n]!, ?_⟩
    rw [eCoeff, coeff_finiteSeries]
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hn] using he ⟨n,hn⟩
  · refine ⟨0, ?_⟩
    simp [eCoeff, coeff_finiteSeries, List.getElem?_eq_none (by omega : a.length ≤ n)]

theorem clear_inverse_power (U : PowerSeries ℚ) (hU : constantCoeff U = 1)
    (n j : ℕ) (hj : j ≤ n) :
    U^n * (X * U⁻¹)^j = X^j * U^(n-j) := by
  have hinv : U^j * (U⁻¹)^j = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ (by rw [hU]; norm_num), one_pow]
  have hp : U^n = U^(n-j)*U^j := (pow_sub_mul_pow U hj).symm
  calc
    U^n * (X * U⁻¹)^j = X^j * (U^(n-j) * (U^j * (U⁻¹)^j)) := by
      rw [hp, mul_pow]
      ring
    _ = X^j * U^(n-j) := by rw [hinv, mul_one]

end D5.S1.Recurrence.Residue.HannaEGFMachinery

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
namespace D5.S1.Recurrence.Residue.HannaEGFMachinery

private theorem coeff_inner_pow (k j n : ℕ) :
    coeff n ((X * (exp ℚ)^k)^j) =
      if j ≤ n then ((k*j : ℕ) : ℚ)^(n-j) / (n-j).factorial else 0 := by
  rw [mul_pow, ← pow_mul, exp_pow_eq_rescale_exp, coeff_X_pow_mul']
  split_ifs <;> simp [coeff_exp, div_eq_mul_inv]

private theorem exp_rhs_coeff (k n : ℕ) :
    eCoeff ((exp ℚ).subst (X * (exp ℚ)^k)) n =
      ∑ j ∈ range (n+1), (n.choose j : ℚ) * ((k*j : ℕ) : ℚ)^(n-j) := by
  rw [eCoeff, coeff_subst' (PowerSeries.HasSubst.X'.mul_left)]
  have hs : Function.support (fun j => coeff j (exp ℚ) •
      coeff n ((X * (exp ℚ)^k)^j)) ⊆ (range (n+1) : Set ℕ) := by
    intro j hj
    by_contra h
    have hjn : ¬j ≤ n := by simpa using h
    exact hj (by simp [coeff_inner_pow, hjn])
  rw [finsum_eq_sum_of_support_subset _ hs, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn := mem_range_succ_iff.mp hj
  rw [coeff_inner_pow, if_pos hjn, coeff_exp, smul_eq_mul]
  have hc : (n.choose j : ℚ) * j.factorial * (n-j).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  rw [← hc]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  field_simp


def expSum (k n : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), (n.choose j : ℤ) * ((k*j : ℕ) : ℤ)^(n-j)

theorem expSum_mod (k m n : ℕ) (hk : m ∣ k) : (m : ℤ) ∣ expSum k n - 1 := by
  rw [expSum, sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one,
    add_sub_cancel_right]
  apply dvd_sum
  intro j hj
  have hjn : j < n := mem_range.mp hj
  apply dvd_mul_of_dvd_right
  apply dvd_pow _ (by omega : n-j ≠ 0)
  exact_mod_cast (dvd_mul_of_dvd_left hk j)

theorem expSum_four_mod_eight (n : ℕ) : (8 : ℤ) ∣ expSum 4 n - 1 := by
  cases n with
  | zero => simp [expSum]
  | succ n =>
    rw [expSum, sum_range_succ, sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one,
      add_sub_cancel_right, Nat.choose_succ_self_right,
      show n+1-n = 1 by omega, pow_one]
    apply dvd_add
    · apply dvd_sum
      intro j hj
      have hjn : j < n := mem_range.mp hj
      apply dvd_mul_of_dvd_right
      have htwo : 2 ≤ n+1-j := by omega
      have hp : (16 : ℤ) ∣ ((4*j : ℕ) : ℤ)^(n+1-j) := by
        have hb : (4 : ℤ)^2 ∣ ((4*j : ℕ) : ℤ)^2 :=
          pow_dvd_pow_of_dvd (by exact_mod_cast (dvd_mul_right 4 j)) 2
        exact hb.trans (pow_dvd_pow _ htwo)
      exact (by norm_num : (8 : ℤ) ∣ 16).trans hp
    · have hev : Even (n*(n+1)) := Nat.even_mul_succ_self n
      obtain ⟨z,hz⟩ := hev
      refine ⟨(z : ℤ), ?_⟩
      push_cast
      have hh : (n : ℤ)*((n : ℤ)+1) = 2*z := by
        have hh := congrArg (fun q : ℕ => (q : ℤ)) hz
        push_cast at hh
        nlinarith [hh]
      nlinarith

theorem exp_residual (k m : ℕ)
    (h : ∀ n, (m : ℤ) ∣ expSum k n - 1) :
    ∀ n, ∃ z : ℤ, eCoeff (PowerSeries.derivative (R := ℚ) (exp ℚ) -
      (exp ℚ).subst (X * (PowerSeries.derivative (R := ℚ) (exp ℚ))^k)) n =
        (m : ℚ)*z := by
  intro n
  obtain ⟨z,hz⟩ := h n
  refine ⟨-z, ?_⟩
  have he (F G : PowerSeries ℚ) : eCoeff (F-G) n = eCoeff F n - eCoeff G n := by
    simp [eCoeff, mul_sub]
  simp only [derivative_exp]
  rw [he, eCoeff_exp, exp_rhs_coeff]
  have hc : (∑ j ∈ range (n+1), (n.choose j : ℚ) * ((k*j : ℕ) : ℚ)^(n-j)) =
      (expSum k n : ℚ) := by simp [expSum]
  rw [hc]
  have hh : (expSum k n : ℚ)-1 = (m : ℚ)*z := by exact_mod_cast hz
  push_cast
  linarith

end D5.S1.Recurrence.Residue.HannaEGFMachinery

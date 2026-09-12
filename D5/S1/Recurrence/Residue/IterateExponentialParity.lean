/- GID: D5/S1/Recurrence/Residue/IterateExponentialParity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateExponentialParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Parity of integral coefficients of the exponential of X exp(X). -/

import D5.S1.Recurrence.Residue.QuarticEGFModFour

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFModFour (F)
open private coeff_F_pow eCoeff_F from D5.S1.Recurrence.Residue.QuarticEGFModFour

namespace D5.S1.Recurrence.Residue.IterateExponentialParity

private def linear (n : ℕ) : ℤ := n

private def expLinear : ℕ → ℤ := composition (fun _ => 1) linear

private theorem expLinear_coeff (m : ℕ) :
    eCoeff ((exp ℚ).subst F) m =
      ∑ k ∈ range (m + 1), (m.choose k : ℚ) * (k : ℚ) ^ (m - k) := by
  rw [eCoeff, coeff_subst' (.of_constantCoeff_zero (show constantCoeff F = 0 by simp [F]))]
  have hs : (Function.support (fun k => coeff k (exp ℚ) • coeff m (F ^ k))) ⊆
      (range (m + 1) : Set ℕ) := by
    intro k hk
    by_contra h
    have hkm : ¬k ≤ m := by simpa using h
    exact hk (by simp [coeff_F_pow, hkm])
  rw [finsum_eq_sum_of_support_subset _ hs, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkm := mem_range_succ_iff.mp hk
  rw [coeff_exp, coeff_F_pow, if_pos hkm, smul_eq_mul]
  have hc : (m.choose k : ℚ) * k.factorial * (m - k).factorial = m.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
  rw [← hc]
  simp only [Algebra.algebraMap_self_apply]
  field_simp

private theorem expLinear_formula (m : ℕ) :
    expLinear m = ∑ k ∈ range (m + 1), (m.choose k : ℤ) * (k : ℤ) ^ (m - k) := by
  have h := expLinear_coeff m
  rw [eCoeff_composition _ _ (by simp [F]),
    show eCoeff (exp ℚ) = (fun _ => 1) from funext eCoeff_exp,
    show eCoeff F = (fun n : ℕ => (n : ℚ)) from funext eCoeff_F] at h
  have he : (expLinear m : ℚ) =
      composition (fun _ => 1) (fun n : ℕ => (n : ℚ)) m := by
    simpa [expLinear, linear] using
      composition_map (Int.castRingHom ℚ) (fun _ => 1) linear m
  rw [← he] at h
  exact_mod_cast h

private theorem expLinear_parity (m : ℕ) (hm : 2 ≤ m) :
    (expLinear m : ZMod 2) = 1 - (m : ZMod 2) := by
  have hp (k : ℕ) (hk : k < m) : (k : ZMod 2) ^ (m - k) = k := by
    have hz : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases hz k with h | h
    · rw [h, zero_pow (by omega : m - k ≠ 0)]
    · rw [h, one_pow]
  have he : (∑ k ∈ range (m + 1), (k : ZMod 2) * m.choose k) = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod 2)) (Nat.sum_range_mul_choose m)
    push_cast at h
    simpa [show (2 : ZMod 2) = 0 by decide,
      zero_pow (by omega : m - 1 ≠ 0)] using h
  rw [sum_range_succ] at he
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at he
  rw [expLinear_formula]
  push_cast
  rw [sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
  have hs : (∑ k ∈ range m, (m.choose k : ZMod 2) * (k : ZMod 2) ^ (m - k)) =
      ∑ k ∈ range m, (k : ZMod 2) * m.choose k := by
    apply sum_congr rfl
    intro k hk
    rw [hp k (mem_range.mp hk), mul_comm]
  rw [hs]
  calc
    _ = ((∑ k ∈ range m, (k : ZMod 2) * m.choose k) + m) + (1 - m) := by ring
    _ = 1 - m := by rw [he, zero_add]

/-- Every even-indexed integral coefficient of exp(X exp(X)) is odd. -/
private theorem expLinear_mod_two (m : ℕ) (hm : m % 2 = 0) : (expLinear m : ZMod 2) = 1 := by
  by_cases hz : m = 0
  · subst m
    simp [expLinear, composition]
  · rw [expLinear_parity m (by omega), ← ZMod.natCast_mod m 2, hm]
    simp

/-- Every odd-indexed integral coefficient after degree one is even. -/
private theorem expLinear_mod_two_odd (m : ℕ) (hm : m % 2 = 1) (hm3 : 3 ≤ m) :
    (expLinear m : ZMod 2) = 0 := by
  rw [expLinear_parity m (by omega), ← ZMod.natCast_mod m 2, hm]
  simp

#print axioms expLinear_mod_two
#print axioms expLinear_mod_two_odd

end D5.S1.Recurrence.Residue.IterateExponentialParity

namespace D5.S1.Recurrence.Residue.IterateExponentialParity

open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
  (iterate iterate_map iterate_congr iterateComp iterateComp_zero_coeff eCoeff_iterate
    encode eCoeff_encode constantCoeff_encode eCoeff_ext)

private def stepK (k : ℕ) {R : Type*} [CommSemiring R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => (n + 1 : R) * composition (fun _ => 1) (iterate f k) n

private theorem stepK_map (k : ℕ) {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : ℕ → R) (n : ℕ) :
    φ (stepK k f n) = stepK k (fun j => φ (f j)) n := by
  cases n with
  | zero => simp [stepK]
  | succ n =>
    simp only [stepK, map_mul, map_add, map_natCast, map_one, composition_map]
    congr 2
    funext j
    exact iterate_map φ f k j

private theorem stepK_contract (k : ℕ) {R : Type*} [CommSemiring R] {f g : ℕ → R} {d : ℕ}
    (h : ∀ i < d, f i = g i) : ∀ i < d + 1, stepK k f i = stepK k g i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    simp only [stepK]
    congr 1
    apply composition_congr (fun _ _ => rfl)
    intro j hj
    exact iterate_congr (fun t ht => h t (by omega)) k

private theorem stepK_coeff (k : ℕ) {f : PowerSeries ℚ} (hf : constantCoeff f = 0) :
    eCoeff (X * (exp ℚ).subst (iterateComp f k)) = stepK k (eCoeff f) := by
  funext n
  cases n with
  | zero => simp [stepK]
  | succ n =>
    rw [eCoeff_X_mul, eCoeff_composition _ _ (iterateComp_zero_coeff hf k),
      eCoeff_iterate hf]
    simp only [show eCoeff (exp ℚ) = (fun _ => 1) from funext eCoeff_exp, stepK]

private def approximationK (k : ℕ) : ℕ → ℕ → ℕ
  | 0 => fun n => n
  | d + 1 => stepK k (approximationK k d)

private theorem approximationK_stable (k : ℕ) {d stage : ℕ} (h : d ≤ stage) :
    ∀ i < d, approximationK k d i = approximationK k stage i := by
  induction d generalizing stage with
  | zero => intro i hi; omega
  | succ d ih =>
    cases stage with
    | zero => omega
    | succ stage => exact stepK_contract k (ih (by omega))

def aK (k n : ℕ) : ℕ := approximationK k (n + 1) n

private theorem aK_agrees (k d : ℕ) : ∀ i < d, aK k i = approximationK k d i := by
  intro i hi
  exact approximationK_stable k (by omega : i + 1 ≤ d) i (by omega)

private theorem aK_fixed (k : ℕ) : aK k = stepK k (aK k) := by
  funext n
  have h := stepK_contract k (aK_agrees k (n + 1)) n (by omega)
  exact (aK_agrees k (n + 2) n (by omega)).trans h.symm

@[simp] private theorem aK_zero (k : ℕ) : aK k 0 = 0 := by rw [aK_fixed k]; rfl

noncomputable def AK (k : ℕ) : PowerSeries ℚ := encode (fun n => (aK k n : ℚ))

theorem A_equation (k : ℕ) :
    constantCoeff (AK k) = 0 ∧ AK k = X * (exp ℚ).subst (iterateComp (AK k) k) := by
  have hz : constantCoeff (AK k) = 0 := by simp [AK]
  refine ⟨hz, eCoeff_ext ?_⟩
  intro n
  rw [stepK_coeff k hz]
  change eCoeff (encode _) n = _
  rw [eCoeff_encode,
    show eCoeff (AK k) = (fun n => (aK k n : ℚ)) from funext (eCoeff_encode _)]
  exact (congrArg (fun j : ℕ => (j : ℚ)) (congrFun (aK_fixed k) n)).trans
    (stepK_map k (Nat.castRingHom ℚ) (aK k) n)

theorem fixed_unique (k : ℕ) {f g : PowerSeries ℚ} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0)
    (ef : f = X * (exp ℚ).subst (iterateComp f k))
    (eg : g = X * (exp ℚ).subst (iterateComp g k)) : f = g := by
  have hf' : eCoeff f = stepK k (eCoeff f) :=
    (congrArg eCoeff ef).trans (stepK_coeff k hf)
  have hg' : eCoeff g = stepK k (eCoeff g) :=
    (congrArg eCoeff eg).trans (stepK_coeff k hg)
  have h : ∀ d, ∀ i < d, eCoeff f i = eCoeff g i := by
    intro d
    induction d with
    | zero => intro i hi; omega
    | succ d ih =>
      intro i hi
      rw [hf', hg']
      exact stepK_contract k ih i hi
  exact eCoeff_ext (fun n => h (n + 1) n (by omega))

#print axioms stepK_map
#print axioms stepK_contract
#print axioms stepK_coeff
#print axioms approximationK_stable
#print axioms aK_agrees
#print axioms aK_fixed
#print axioms aK_zero
#print axioms A_equation
#print axioms fixed_unique

end D5.S1.Recurrence.Residue.IterateExponentialParity

namespace D5.S1.Recurrence.Residue.IterateExponentialParity

open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (identity iterate iterate_map)
open private D5.S1.Recurrence.Residue.QuarticEGFModFour.linear
  square square_mod_two composition_assoc composition_identity_right
  composition_identity_left from D5.S1.Recurrence.Residue.QuarticEGFModFour

private theorem iterate_linear_period (k n : ℕ) :
    ((iterate linear (k + 2) n : ℤ) : ZMod 2) = ((iterate linear k n : ℤ) : ZMod 2) := by
  have hz : iterate linear k 0 = 0 := by
    cases k <;> simp [iterate, identity, composition, linear]
  have hs : (fun j => ((composition linear linear j : ℤ) : ZMod 2)) =
      (fun j => ((identity j : ℤ) : ZMod 2)) := by
    funext j
    have h := square_mod_two j
    unfold square at h
    have hl : D5.S1.Recurrence.Residue.QuarticEGFModFour.linear = linear := by
      funext t
      rfl
    rw [hl] at h
    simpa [identity] using h
  have ha : iterate linear (k + 2) = composition (composition linear linear)
      (iterate linear k) := (composition_assoc linear linear (iterate linear k) rfl hz).symm
  rw [ha]
  change (Int.castRingHom (ZMod 2)) (composition (composition linear linear)
    (iterate linear k) n) = _
  rw [composition_map]
  change composition (fun j => ((composition linear linear j : ℤ) : ZMod 2))
    (fun j => ((iterate linear k j : ℤ) : ZMod 2)) n = _
  rw [hs]
  have hm := composition_map (Int.castRingHom (ZMod 2)) identity (iterate linear k) n
  rw [composition_identity_left _ hz] at hm
  exact hm.symm

private theorem iterate_linear_parity (k n : ℕ) :
    ((iterate linear k n : ℤ) : ZMod 2) =
      if k % 2 = 0 then (identity n : ZMod 2) else (n : ZMod 2) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [iterate, identity]
  | one => simp [iterate, composition_identity_right, linear]
  | more k ih _ => simpa [Nat.add_mod] using (iterate_linear_period k n).trans ih

private theorem linear_mod_two_fixed (k : ℕ) :
    stepK k (fun n : ℕ => (n : ZMod 2)) = (fun n : ℕ => (n : ZMod 2)) := by
  have hi : iterate (fun n : ℕ => (n : ZMod 2)) k =
      (fun n => if k % 2 = 0 then identity n else (n : ZMod 2)) := by
    funext n
    have hm := iterate_map (Int.castRingHom (ZMod 2)) linear k n
    simpa [linear, iterate_linear_parity] using hm.symm
  have hc (n : ℕ) : composition (fun _ => (1 : ZMod 2)) identity n = 1 := by
    have h := congrFun (composition_identity_right (fun _ => 1)) n
    have hm := congrArg (fun z : ℤ => (z : ZMod 2)) h
    change (Int.castRingHom (ZMod 2)) (composition (fun _ => 1) identity n) = _ at hm
    rw [composition_map] at hm
    change composition (fun _ => (1 : ZMod 2)) (fun j => if j = 1 then 1 else 0) n = 1
    simpa [identity] using hm
  funext n
  cases n with
  | zero => simp [stepK]
  | succ n =>
    simp only [stepK, hi]
    by_cases hk : k % 2 = 0
    · simp [hk, hc]
    · simp only [hk, if_false]
      have he : composition (fun _ => (1 : ZMod 2)) (fun j : ℕ => (j : ZMod 2)) n =
          (expLinear n : ZMod 2) := by
        simpa [expLinear, linear] using
          (composition_map (Int.castRingHom (ZMod 2)) (fun _ => 1) linear n).symm
      rw [he]
      by_cases hn : n % 2 = 0
      · simp [expLinear_mod_two n hn]
      · have hz : ((n + 1 : ℕ) : ZMod 2) = 0 := by
          rw [← ZMod.natCast_mod (n + 1) 2, show (n + 1) % 2 = 0 by omega]
          rfl
        have hz' : (n : ZMod 2) + 1 = 0 := by simpa using hz
        simp [hz, hz']

private theorem approximation_mod_two (k d n : ℕ) :
    (approximationK k d n : ZMod 2) = n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    change (Nat.castRingHom (ZMod 2)) (stepK k (approximationK k d) n) = _
    rw [stepK_map]
    change stepK k (fun j => (approximationK k d j : ZMod 2)) n = _
    rw [show (fun j => (approximationK k d j : ZMod 2)) = (fun j : ℕ => (j : ZMod 2))
      from funext ih, linear_mod_two_fixed]

/-- For every iterate count, the fixed-point coefficients agree with their indices modulo two. -/
private theorem parity_mod_two (k n : ℕ) (hn : 1 ≤ n) : Nat.ModEq 2 (aK k n) n := by
  cases n with
  | zero => omega
  | succ n =>
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    exact approximation_mod_two k (n + 2) (n + 1)

/-- A positive-degree coefficient of the fixed point is odd exactly when its degree is odd. -/
theorem odd_iff_odd (k n : ℕ) (hn : 1 ≤ n) : Odd (aK k n) ↔ Odd n := by
  rw [Nat.odd_iff, Nat.odd_iff, (parity_mod_two k n hn : aK k n % 2 = n % 2)]

/-- The A396803 endpoint: the third-iterate coefficients are odd exactly at odd index. -/
theorem parity_iterate_three (n : ℕ) (hn : 1 ≤ n) : Odd (aK 3 n) ↔ Odd n :=
  odd_iff_odd 3 n hn

/-- The A396805 endpoint, specialized from the k-general parity theorem. -/
theorem parity_iterate_five (n : ℕ) (hn : 1 ≤ n) : Odd (aK 5 n) ↔ Odd n :=
  odd_iff_odd 5 n hn

/-- The A396806 endpoint, specialized from the k-general parity theorem. -/
theorem parity_iterate_six (n : ℕ) (hn : 1 ≤ n) : Odd (aK 6 n) ↔ Odd n :=
  odd_iff_odd 6 n hn

#print axioms odd_iff_odd
#print axioms A_equation
#print axioms fixed_unique
#print axioms parity_iterate_three
#print axioms parity_iterate_five
#print axioms parity_iterate_six

end D5.S1.Recurrence.Residue.IterateExponentialParity

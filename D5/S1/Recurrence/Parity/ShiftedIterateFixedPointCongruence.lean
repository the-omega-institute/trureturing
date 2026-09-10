/- GID: D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Shifted-iterate contraction and geometric reduction prove Hanna A378575 and A378576. -/

import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence

open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
  (iterate mobius mobius_iterate)

namespace D5.S1.Recurrence.Parity.ShiftedIterateFixedPointCongruence

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp h |>.trans
    (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {f : PowerSeries R} (hf : constantCoeff f = 0)
    {n k : ℕ} (h : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) n h

private theorem agree_subst {d : ℕ} {f g u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hfg : Agree d f g) (huv : Agree d u v) :
    Agree d (f.subst u) (g.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [hfg k hk, agree_pow huv k n hn]
  · rw [pow_low hu (by omega : n < k), pow_low hv (by omega : n < k),
      smul_zero, smul_zero]

private theorem iterate_zero (f : PowerSeries R) (hf : constantCoeff f = 0)
    (r : ℕ) : constantCoeff (iterate f r) = 0 := by
  induction r with
  | zero => simp [iterate]
  | succ r ih => exact constantCoeff_subst_eq_zero hf _ ih

private theorem iterate_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) (r : ℕ) : Agree d (iterate f r) (iterate g r) := by
  induction r with
  | zero => intro n hn; rfl
  | succ r ih => exact agree_subst hf hg ih h

private noncomputable def step (r : ℕ) (f : PowerSeries R) : PowerSeries R :=
  X + X * iterate f r

private theorem step_zero (r : ℕ) (f : PowerSeries R) :
    constantCoeff (step r f) = 0 := by simp [step]

-- Multiplication by X raises the degree of agreement of every compositional iterate.
private theorem step_contract (r : ℕ) {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (step r f) (step r g) := by
  apply (agree_iff _ _ _).mpr
  have hd := mul_dvd_mul_left X ((agree_iff _ _ _).mp (iterate_agree hf hg h r))
  rw [← pow_succ'] at hd
  convert hd using 1
  dsimp [step]
  ring

private theorem fixed_unique (r : ℕ) {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (hfe : f = step r f) (hge : g = step r g) : f = g := by
  have ha : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [← hfe, ← hge] using step_contract r hf hg ih
  ext n
  exact ha (n + 1) n (by omega)

private noncomputable def approximation (r : ℕ) : ℕ → PowerSeries R
  | 0 => 0
  | d + 1 => step r (approximation r d)

private theorem approximation_zero (r d : ℕ) :
    constantCoeff (approximation (R := R) r d) = 0 := by
  cases d with
  | zero => simp [approximation]
  | succ d => exact step_zero r _

private theorem approximation_stable (r : ℕ) {d e : ℕ} (h : d ≤ e) :
    Agree d (approximation (R := R) r d) (approximation r e) := by
  induction d generalizing e with
  | zero => intro n hn; omega
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      exact step_contract r (approximation_zero r d) (approximation_zero r e)
        (ih (by omega))

noncomputable def a (r n : ℕ) : ℤ :=
  coeff n (approximation r (n + 1))

noncomputable def generatingSeries (r : ℕ) : PowerSeries ℤ := mk (a r)

private theorem generating_agree (r d : ℕ) :
    Agree d (generatingSeries r) (approximation r d) := by
  intro n hn
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) r (by omega : n + 1 ≤ d) n (by omega)

theorem generating_equation (r : ℕ) (_hr : 2 ≤ r) :
    constantCoeff (generatingSeries r) = 0 ∧ coeff 1 (generatingSeries r) = 1 ∧
    generatingSeries r = X + X * iterate (generatingSeries r) r := by
  have hz : constantCoeff (generatingSeries r) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, generating_agree r 1 0 (by omega),
      coeff_zero_eq_constantCoeff]
    exact approximation_zero r 1
  have he : generatingSeries r = step r (generatingSeries r) := by
    ext n
    have ha := generating_agree r (n + 2) n (by omega)
    have hb := step_contract r hz (approximation_zero r (n + 1))
      (generating_agree r (n + 1)) n (by omega)
    exact ha.trans hb.symm
  refine ⟨hz, ?_, he⟩
  have h1 := congrArg (coeff 1) he
  simpa [step, iterate_zero _ hz] using h1

theorem generating_unique (r : ℕ) (hr : 2 ≤ r) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 0) (hB : B = X + X * iterate B r) :
    B = generatingSeries r :=
  fixed_unique r h0 (generating_equation r hr).1 hB (generating_equation r hr).2.2

private theorem map_iterates {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (hf : constantCoeff f = 0) (r : ℕ) :
    (iterate f r).map hom = iterate (f.map hom) r := by
  induction r with
  | zero => simp [iterate]
  | succ r ih =>
    calc
      (iterate f (r + 1)).map hom =
          ((iterate f r).map hom).subst (f.map hom) :=
        map_subst (.of_constantCoeff_zero hf) _
      _ = iterate (f.map hom) (r + 1) := by rw [ih]; rfl

private theorem mobius_fixed (r : ℕ) (hc : (r : R) = 1) :
    mobius (1 : R) = step r (mobius 1) := by
  rw [step, mobius_iterate, hc, one_mul]
  have h := mk_one_mul_one_sub_eq_one R
  have hm : mobius (1 : R) = X * mk 1 := by simp [mobius]
  rw [hm]
  linear_combination X * h

theorem mod_identity (r m : ℕ) (hr : 2 ≤ r) (_hm : 2 ≤ m) (hdiv : m ∣ r - 1) :
    (generatingSeries r).map (Int.castRingHom (ZMod m)) = mobius 1 := by
  let hom := Int.castRingHom (ZMod m)
  have hz : constantCoeff ((generatingSeries r).map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      (generating_equation r hr).1, map_zero]
  have he : (generatingSeries r).map hom = step r ((generatingSeries r).map hom) := by
    have h := congrArg (PowerSeries.map hom) (generating_equation r hr).2.2
    simpa [step, map_iterates hom (generating_equation r hr).1] using h
  have hc : (r : ZMod m) = 1 := by
    have hzero := (ZMod.natCast_eq_zero_iff (r - 1) m).mpr hdiv
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hzero
    exact sub_eq_zero.mp hzero
  exact fixed_unique r hz (by simp [mobius]) he (mobius_fixed r hc)

theorem shift_iterate_mod (r m : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hdiv : m ∣ r - 1) (n : ℕ) (hn : 1 ≤ n) : a r n % m = 1 := by
  have hb : coeff n (mobius (1 : ZMod m)) = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [mobius]
  have hc : (a r n : ZMod m) = 1 := by
    simpa [coeff_map, generatingSeries, hb] using
      congrArg (coeff n) (mod_identity r m hr hm hdiv)
  have h := (ZMod.intCast_eq_intCast_iff' (a r n) 1 m).mp (by simpa only [Int.cast_one] using hc)
  simpa [Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ 1) (by omega : (1 : ℤ) < m)] using h

theorem hanna_conjecture_five (n : ℕ) (hn : 1 ≤ n) : a 5 n % 4 = 1 :=
  shift_iterate_mod 5 4 (by omega) (by omega) (by norm_num) n hn

theorem hanna_conjecture_six (n : ℕ) (hn : 1 ≤ n) : a 6 n % 5 = 1 :=
  shift_iterate_mod 6 5 (by omega) (by omega) (by norm_num) n hn

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_identity
#print axioms shift_iterate_mod
#print axioms hanna_conjecture_five
#print axioms hanna_conjecture_six

end D5.S1.Recurrence.Parity.ShiftedIterateFixedPointCongruence

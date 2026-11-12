/- GID: D5/S3/Arith/LocalDold/PeriodicRepair
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/PeriodicRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact transforms and repair divisibilities for zero and half residues. -/
import D5.S3.Arith.LocalDold.BackwardZero
import D5.S1.Dynamics.PeriodicOrbits.CountableRealization
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat

/-! Exact all-index periodic transforms; no recurrence valuation bridge is assumed. -/

set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.PeriodicRepair
open D5.S3.Arith.LocalDold.BackwardZero
open scoped ArithmeticFunction.Moebius

/-- The zero-residue periodic sample, including its baseline fixed points. -/
def zeroSample (R : ℕ) (C : ℤ) (n : ℕ) : ℤ := 1 + if R ∣ n then C else 0

private theorem mobius_of_sum {u w : ℕ → ℤ}
    (hs : ∀ n, 0 < n → ∑ d ∈ n.divisors, w d = u n)
    {n : ℕ} (hn : 0 < n) : mobiusSum u n = w n := by
  have h := ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := w) (g := u)).mp hs) n hn
  unfold mobiusSum
  rw [← Nat.sum_divisorsAntidiagonal' (f := fun a b => μ a * u b)]
  exact h

/-- The transform has exactly the baseline and the prescribed cycle-length spike.
When R=1 the two contributions combine at the same index. -/
theorem zero_transform {R n : ℕ} (hR : 0 < R) (hn : 0 < n) (C : ℤ) :
    mobiusSum (zeroSample R C) n =
      (if n = 1 then 1 else 0) + (if n = R then C else 0) := by
  apply mobius_of_sum (w := fun d =>
    (if d = 1 then 1 else 0) + (if d = R then C else 0)) ?_ hn
  intro k hk
  simp [zeroSample, Finset.sum_add_distrib, Nat.mem_divisors, hk.ne', hR.ne']

private theorem mobius_scale (u : ℕ → ℤ) (c : ℤ) (n : ℕ) :
    mobiusSum (fun d => c*u d) n = c*mobiusSum u n := by
  unfold mobiusSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Every multiplier is classified, not only one sufficient repair. -/
theorem zero_dold_iff {R : ℕ} (hR : 0 < R) (C c : ℕ) :
    Dold (fun n => (c : ℤ)*zeroSample R (C : ℤ) n) ↔ R ∣ c*C := by
  constructor
  · intro h
    by_cases h1 : R = 1
    · simp [h1]
    · have ht := h R hR
      rw [mobius_scale, zero_transform hR hR, ite_eq_right h1, ite_eq_left rfl, zero_add] at ht
      exact_mod_cast ht
  · intro h n hn
    rw [mobius_scale, zero_transform hR hn]
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases he : n = R
      · subst n
        simpa [h1] using (show (R : ℤ) ∣ (c : ℤ)*(C : ℤ) by exact_mod_cast h)
      · simp [h1,he]

/-- Odd multiples of D select exactly the half-residue of period 2D. -/
def halfSample (D : ℕ) (C : ℤ) (n : ℕ) : ℤ :=
  zeroSample D C n - zeroSample (2*D) C n + 1

private theorem mobius_add (u v : ℕ → ℤ) (n : ℕ) :
    mobiusSum (fun d => u d + v d) n = mobiusSum u n + mobiusSum v n := by
  simp [mobiusSum, mul_add, Finset.sum_add_distrib]

private theorem mobius_sub (u v : ℕ → ℤ) (n : ℕ) :
    mobiusSum (fun d => u d - v d) n = mobiusSum u n - mobiusSum v n := by
  simp [mobiusSum, mul_sub, Finset.sum_sub_distrib]

/-- A half residue has a positive D spike and a negative 2D spike. -/
theorem half_transform {D n : ℕ} (hD : 0 < D) (hn : 0 < n) (C : ℤ) :
    mobiusSum (halfSample D C) n =
      (if n = 1 then 1 else 0) +
        (if n = D then C else 0) - (if n = 2*D then C else 0) := by
  have hc : mobiusSum (fun _ => (1 : ℤ)) n = if n=1 then 1 else 0 := by
    have he : zeroSample 1 0 = fun _ => (1 : ℤ) := by
      funext k
      simp [zeroSample]
    simpa only [he, ite_self, add_zero] using zero_transform (R := 1) (by omega) hn (0 : ℤ)
  unfold halfSample
  rw [mobius_add, mobius_sub, zero_transform hD hn,
    zero_transform (by omega : 0 < 2*D) hn, hc]
  ring

/-- The negative orbit contribution survives every positive multiplier. -/
theorem half_negative {D : ℕ} (hD : 0 < D) {C c : ℕ} (hC : 0 < C) (hc : 0 < c) :
    mobiusSum (fun n => (c : ℤ)*halfSample D (C : ℤ) n) (2*D) < 0 := by
  rw [mobius_scale, half_transform hD (by omega),
    ite_eq_right (by omega : 2*D ≠ 1), ite_eq_right (by omega : 2*D ≠ D), ite_eq_left rfl]
  have hp : (0 : ℤ) < c := by exact_mod_cast hc
  have hp' : (0 : ℤ) < C := by exact_mod_cast hC
  nlinarith

private theorem repair_divisor {R : ℕ} (hR : 0 < R) (C c : ℕ) :
    R ∣ c*C ↔ R / Nat.gcd R C ∣ c := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left R C) (Nat.gcd_pos_of_pos_left C hR)]
  simpa [Nat.mul_comm, gcd_eq_nat_gcd] using (dvd_mul_gcd_iff_dvd_mul (k := R) (m := c) (n := C)).symm

/-- The positive repairs are precisely multiples of R/gcd(R,C). -/
theorem zero_repair_iff {R : ℕ} (hR : 0 < R) (C c : ℕ) :
    Dold (fun n => (c : ℤ)*zeroSample R (C : ℤ) n) ↔ R / Nat.gcd R C ∣ c := by
  rw [zero_dold_iff hR, repair_divisor hR]

/-- Half-residue Dold repair has the same exact denominator despite its negative orbit. -/
theorem half_repair_iff {D : ℕ} (hD : 0 < D) (C c : ℕ) :
    Dold (fun n => (c : ℤ)*halfSample D (C : ℤ) n) ↔
      (2*D) / Nat.gcd (2*D) C ∣ c := by
  rw [← repair_divisor (by omega : 0 < 2*D)]
  constructor
  · intro h
    have ht := h (2*D) (by omega)
    rw [mobius_scale, half_transform hD (by omega),
      ite_eq_right (by omega : 2*D ≠ 1), ite_eq_right (by omega : 2*D ≠ D),
      ite_eq_left rfl] at ht
    have ht' : (2*D : ℤ) ∣ -((c : ℤ)*(C : ℤ)) := by simpa using ht
    exact_mod_cast (dvd_neg.mp ht')
  · intro h n hn
    rw [mobius_scale, half_transform hD hn]
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases he : n = D
      · subst n
        have ht : (D : ℤ) ∣ (c : ℤ)*(C : ℤ) := by
          exact_mod_cast (dvd_trans (dvd_mul_left D 2) h)
        simpa [h1, show D ≠ 2*D by omega] using ht
      · by_cases he' : n = 2*D
        · subst n
          have ht : (2*D : ℤ) ∣ (c : ℤ)*(C : ℤ) := by exact_mod_cast h
          simpa [h1,he] using (dvd_neg.mpr ht)
        · simp [h1,he,he']

open D5.S1.Dynamics.PeriodicOrbits.CountableRealization

/-- A finite collection of fixed points and R-cycles, including coincident lengths at R=1. -/
def zeroMultiplicity (R M K : ℕ) (d : ℕ) : ℕ :=
  (if d=1 then M else 0) + (if d=R then K else 0)

private theorem sparse_card {R : ℕ} (hR : 0 < R) (M K : ℕ) {n : ℕ} (hn : 0 < n) :
    fixedCard (rotation (zeroMultiplicity R M K)) n =
      M + if R ∣ n then R*K else 0 := by
  rw [fixed_card _ hn]
  simp [zeroMultiplicity, mul_add, Finset.sum_add_distrib, Nat.mem_divisors, hn.ne']

private theorem sparse_finite {R : ℕ} (hR : 0 < R) (M K : ℕ) :
    Finite (Carrier (zeroMultiplicity R M K)) := by
  apply finite_carrier_of_support _ hR
  intro d hd
  by_cases h1 : d=1
  · simp [h1]
  · have hr : d=R := by
      by_contra hr
      simp [zeroMultiplicity,h1,hr] at hd
    simp [hr]

/-- Every integral zero-residue repair is realized by an actual finite permutation,
simultaneously at all positive indices. -/
theorem zero_finite_model {R : ℕ} (hR : 0 < R) (C M : ℕ) (h : R ∣ M*C) :
    ∃ c : ℕ → ℕ, Finite (Carrier c) ∧ ∀ n : ℕ, 0 < n →
      (fixedCard (rotation c) n : ℤ) = (M : ℤ)*zeroSample R (C : ℤ) n := by
  let K := M*C/R
  have hK : R*K = M*C := Nat.mul_div_cancel' h
  refine ⟨zeroMultiplicity R M K, sparse_finite hR M K, fun n hn => ?_⟩
  rw [sparse_card hR M K hn, hK]
  by_cases hd : R ∣ n <;> simp [zeroSample,hd] <;> ring

/-- Every integral half-residue repair is a difference of two actual finite
permutations, while half_negative excludes a positive realization. -/
theorem half_finite_signed_model {D : ℕ} (hD : 0 < D) (C M : ℕ) (h : 2*D ∣ M*C) :
    ∃ cp cm : ℕ → ℕ, Finite (Carrier cp) ∧ Finite (Carrier cm) ∧
      ∀ n : ℕ, 0 < n →
        (fixedCard (rotation cp) n : ℤ) - (fixedCard (rotation cm) n : ℤ) =
          (M : ℤ)*halfSample D (C : ℤ) n := by
  have hd : D ∣ M*C := dvd_trans (dvd_mul_left D 2) h
  let Kp := M*C/D
  let Km := M*C/(2*D)
  have hKp : D*Kp = M*C := Nat.mul_div_cancel' hd
  have hKm : (2*D)*Km = M*C := Nat.mul_div_cancel' h
  refine ⟨zeroMultiplicity D M Kp, zeroMultiplicity (2*D) 0 Km,
    sparse_finite hD M Kp, sparse_finite (by omega) 0 Km, fun n hn => ?_⟩
  rw [sparse_card hD M Kp hn, sparse_card (by omega) 0 Km hn, hKp, hKm]
  by_cases hd' : D ∣ n <;> by_cases he : 2*D ∣ n <;>
    simp [halfSample,zeroSample,hd',he] <;> ring

/-- The signed divisibility-indicator formula is exactly the half residue. -/
theorem half_residue {D : ℕ} (hD : 0 < D) (C : ℤ) (n : ℕ) :
    halfSample D C n = 1 + if n % (2*D) = D then C else 0 := by
  by_cases hd : D ∣ n
  · obtain ⟨q,rfl⟩ := hd
    have hm : (D*q) % (2*D) = D*(q%2) := by
      rw [Nat.mul_comm 2 D, Nat.mul_mod_mul_left]
    have he : 2*D ∣ D*q ↔ q%2=0 := by
      rw [Nat.dvd_iff_mod_eq_zero,hm]
      exact mul_eq_zero.trans (or_iff_right hD.ne')
    have hd' : D ∣ D*q := dvd_mul_right D q
    have hq := Nat.mod_lt q (by omega : 0 < 2)
    by_cases hz : q%2=0
    · simp [halfSample,zeroSample,hd',he,hm,hz,show (0 : ℕ) ≠ D by omega]
    · have ho : q%2=1 := by omega
      simp [halfSample,zeroSample,hd',he,hm,ho,add_comm]
  · have h2 : ¬2*D ∣ n := fun h => hd ((dvd_mul_left D 2).trans h)
    have hm : n % (2*D) ≠ D := by
      intro he
      apply hd
      rw [← Nat.mod_add_div n (2*D),he]
      exact dvd_add dvd_rfl (dvd_mul_of_dvd_left (dvd_mul_left D 2) _)
    simp [halfSample,zeroSample,hd,h2,hm]

private theorem period_mul {u : ℕ → ℤ} {R : ℕ} (hu : Function.Periodic u R)
    (m k : ℕ) : u (m+k*R)=u m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m+(k+1)*R=(m+k*R)+R by ring,hu,ih]

/-- A periodic integer sequence admitting a fixed positive Dold repair is invariant
under every unit multiplier modulo its period. This is the scalar mismatch necessity. -/
theorem periodic_unit_invariance {u : ℕ → ℤ} {R c : ℕ}
    (hR : 0 < R) (hu : Function.Periodic u R) (hc : 0 < c)
    (hD : Dold (fun n => (c : ℤ)*u n))
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hcop : r.Coprime R) : u (m*r)=u m := by
  by_contra hne
  let delta : ℤ := (c : ℤ)*(u (m*r)-u m)
  have hdelta : delta ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') (sub_ne_zero.mpr hne)
  obtain ⟨q,hqb,hq,hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max r (max m delta.natAbs)) (q := R) (a := r) hR.ne' hcop
  have hqr : r ≤ q := by omega
  obtain ⟨k,hk⟩ : ∃ k, q=r+k*R := by
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hqr).mp hqmod.symm
    exact ⟨k,(Nat.eq_add_of_sub_eq hqr hk).trans (by ac_rfl)⟩
  have he : u (m*q)=u (m*r) := by
    rw [hk,show m*(r+k*R)=m*r+(m*k)*R by ring]
    exact period_mul hu _ _
  have hmc : m.Coprime q :=
    (hq.coprime_iff_not_dvd.mpr (fun h =>
      (not_le_of_gt (show m < q by omega)) (Nat.le_of_dvd hm h))).symm
  have hd := dold_prime_congruence hD hm hq hmc
  change (q : ℤ) ∣ (c : ℤ)*u (m*q)-(c : ℤ)*u m at hd
  rw [he,← mul_sub] at hd
  have hdn : q ∣ delta.natAbs := by exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hd)
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hdelta) hdn
  omega

/-- A single residue class, with a positive jump above the baseline. -/
def residueSample (R z : ℕ) (C : ℤ) (n : ℕ) : ℤ :=
  1 + if n % R = z then C else 0

/-- The minus-one unit forces a zero or half residue for every positive Dold repair. -/
theorem residue_repair_necessary {R z C c : ℕ} (hR : 0 < R) (hz : z < R)
    (hC : 0 < C) (hc : 0 < c)
    (hD : Dold (fun n => (c : ℤ)*residueSample R z (C : ℤ) n)) : R ∣ 2*z := by
  by_cases hz0 : z=0
  · simp [hz0]
  · have hzpos : 0 < z := by omega
    have hr : 0 < R-1 := by omega
    have hcop : (R-1).Coprime R := by
      apply (Nat.coprime_sub_self_right (m := R-1) (n := R) (by omega)).mp
      simp [show R-(R-1)=1 by omega]
    have hp : Function.Periodic (residueSample R z (C : ℤ)) R := by
      intro n
      simp [residueSample,Nat.add_mod]
    have he := periodic_unit_invariance hR hp hc hD hzpos hr hcop
    have hm : z*(R-1) % R = z := by
      by_contra h
      simp [residueSample,Nat.mod_eq_of_lt hz,h] at he
      omega
    have hs : (z*(R-1)+z)%R=0 := by
      rw [show z*(R-1)+z=z*((R-1)+1) by ring,
        Nat.sub_add_cancel (by omega : 1 ≤ R)]
      simp
    rw [Nat.add_mod,hm,Nat.mod_eq_of_lt hz] at hs
    exact Nat.dvd_of_mod_eq_zero (by simpa [two_mul] using hs)

private theorem zero_or_half {R z : ℕ} (hR : 0 < R) (hz : z < R)
    (hd : R ∣ 2*z) : z=0 ∨ R=2*z := by
  by_cases h0 : z=0
  · exact Or.inl h0
  · obtain ⟨q,hq⟩ := hd
    have hp : 0 < q := by
      by_contra h
      have he : q=0 := by omega
      simp [he] at hq
      omega
    have hl : q<2 := by nlinarith
    have he : q=1 := by omega
    right
    simpa [he] using hq.symm

private theorem residue_zero (R : ℕ) (C : ℤ) :
    residueSample R 0 C = zeroSample R C := by
  funext n
  simp [residueSample,zeroSample,Nat.dvd_iff_mod_eq_zero]

/-- Complete exact multiplier classification for one periodic residue class. -/
theorem residue_dold_iff {R z C c : ℕ} (hR : 0 < R) (hz : z < R)
    (hC : 0 < C) (hc : 0 < c) :
    Dold (fun n => (c : ℤ)*residueSample R z (C : ℤ) n) ↔
      R ∣ 2*z ∧ R / Nat.gcd R C ∣ c := by
  constructor
  · intro hD
    have hd := residue_repair_necessary hR hz hC hc hD
    refine ⟨hd,?_⟩
    rcases zero_or_half hR hz hd with h0 | he
    · subst z
      rw [residue_zero] at hD
      exact (zero_repair_iff hR C c).mp hD
    · have hzpos : 0 < z := by omega
      subst R
      have hs : residueSample (2*z) z (C : ℤ) = halfSample z (C : ℤ) :=
        funext (fun n => (half_residue hzpos (C : ℤ) n).symm)
      rw [hs] at hD
      exact (half_repair_iff hzpos C c).mp hD
  · rintro ⟨hd,hcdiv⟩
    rcases zero_or_half hR hz hd with h0 | he
    · subst z
      rw [residue_zero]
      exact (zero_repair_iff hR C c).mpr hcdiv
    · have hzpos : 0 < z := by omega
      subst R
      have hs : residueSample (2*z) z (C : ℤ) = halfSample z (C : ℤ) :=
        funext (fun n => (half_residue hzpos (C : ℤ) n).symm)
      rw [hs]
      exact (half_repair_iff hzpos C c).mpr hcdiv

private theorem table_transform {X : Type*} (f : X → X) (u : ℕ → ℤ)
    (ht : ∀ n : ℕ, 0 < n → (fixedCard f n : ℤ) = u n)
    {n : ℕ} (hn : 0 < n) :
    mobiusSum u n = D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.delta (fixedCard f) n := by
  unfold mobiusSum D5.S1.Dynamics.PeriodicOrbits.OrbitCounting.delta
  rw [← Nat.sum_divisorsAntidiagonal' (f := fun a b => μ a * u b)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ht p.2 (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp))]

/-- No map with finite positive-time fixed sets realizes any positive half-residue
multiple. Neither finiteness of the whole space nor injectivity is assumed. -/
theorem half_no_model {X : Type*} (f : X → X)
    (hf : ∀ n : ℕ, 0 < n → Finite {x : X // f^[n] x = x})
    {D C c : ℕ} (hD : 0 < D) (hC : 0 < C) (hc : 0 < c) :
    ¬ ∀ n : ℕ, 0 < n →
      (fixedCard f n : ℤ) = (c : ℤ)*halfSample D (C : ℤ) n := by
  intro ht
  have hn : 0 < 2*D := by omega
  have hh := (necessary f hf hn).1
  rw [← table_transform f _ ht hn] at hh
  exact (not_lt_of_ge hh) (half_negative hD hC hc)

/-- Almost realizability of a single residue class is exactly the zero-residue
case. The constructed model is a finite permutation; the obstruction applies to all maps. -/
theorem residue_almost_realizable_iff {R z C : ℕ} (hR : 0 < R) (hz : z < R)
    (hC : 0 < C) :
    (∃ c : ℕ, 0 < c ∧ ∃ (X : Type) (f : X → X),
      (∀ n : ℕ, 0 < n → Finite {x : X // f^[n] x = x}) ∧
      ∀ n : ℕ, 0 < n →
        (fixedCard f n : ℤ) = (c : ℤ)*residueSample R z (C : ℤ) n) ↔ z=0 := by
  constructor
  · rintro ⟨c,hc,X,f,hf,ht⟩
    have hD : Dold (fun n => (c : ℤ)*residueSample R z (C : ℤ) n) := by
      intro n hn
      rw [table_transform f _ ht hn]
      exact (necessary f hf hn).2
    have hd := (residue_dold_iff hR hz hC hc).mp hD
    rcases zero_or_half hR hz hd.1 with h0 | he
    · exact h0
    · by_contra h0
      have hzpos : 0 < z := by omega
      subst R
      apply half_no_model f hf hzpos hC hc
      intro n hn
      rw [ht n hn,half_residue hzpos]
      rfl
  · intro h0
    subst z
    let M := R / Nat.gcd R C
    have hg : 0 < Nat.gcd R C := Nat.gcd_pos_of_pos_left C hR
    have hM : 0 < M := Nat.div_pos (Nat.le_of_dvd hR (Nat.gcd_dvd_left R C)) hg
    have hd : R ∣ M*C := (repair_divisor hR C M).mpr dvd_rfl
    obtain ⟨cp,hcp,ht⟩ := zero_finite_model hR C M hd
    letI : Finite (Carrier cp) := hcp
    refine ⟨M,hM,Carrier cp,rotation cp,fun n hn => inferInstance,?_⟩
    intro n hn
    rw [residue_zero]
    exact ht n hn

#print axioms residue_dold_iff
#print axioms half_no_model
#print axioms residue_almost_realizable_iff

#print axioms half_residue
#print axioms periodic_unit_invariance
#print axioms residue_repair_necessary

#print axioms zero_repair_iff
#print axioms half_repair_iff
#print axioms zero_finite_model
#print axioms half_finite_signed_model

#print axioms zero_transform
#print axioms zero_dold_iff
#print axioms half_transform
#print axioms half_negative
end D5.S3.Arith.LocalDold.PeriodicRepair

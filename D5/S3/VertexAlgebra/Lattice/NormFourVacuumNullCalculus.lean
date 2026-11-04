/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumNullCalculus
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumNullCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private actual creation, current and transport calculus for vacuum coefficients. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
import Batteries.Tactic.OpenPrivate

/-! Private coefficient calculus for the actual norm-four lattice vacuum relation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open private creation_derivation charge_pairing charge_transport translated_sum translated_X translated_mul
  from D5.S3.VertexAlgebra.LatticeSugawaraConformal
open private osc osc_zero osc_neg deriv_osc creation_zero currentMode currentMode_single
  currentMode_negative pairing_left gram_smul quadratic_product_formula
  opposite_phase neg_norm
  from D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents
open LatticeActualGeneratorLocality LatticeActualProductKernel
open LatticeActualStateFieldCalculus MvPolynomial
open NormFourVirasoroVector
open scoped BigOperators VertexOperator

noncomputable section

-- P r is the actual sum_i a_i X_(i,r), with oscillator weight r+1.
private abbrev P (D : LatticeData) (a : Charge D) (r : ℕ) : Oscillator D :=
  osc D a r

private theorem P_neg (D : LatticeData) (a : Charge D) (r : ℕ) :
    P D (-a) r = -P D a r := osc_neg D a r

private theorem derivation_sum_apply {ι : Type*} (D : LatticeData) (s : Finset ι)
    (f : ι → Derivation ℂ (Oscillator D) (Oscillator D)) (p : Oscillator D) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Derivation.zero_apply]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

private def alongPartial (D : LatticeData) (a : Charge D) (r : ℕ) :
    Derivation ℂ (Oscillator D) (Oscillator D) :=
  ∑ i : Fin D.rank, (a i : ℂ) •
    ∑ j : Fin D.rank, (D.G i j : ℂ) • pderiv (j, r)

private theorem partial_P (D : LatticeData) (a : Charge D) (j : Fin D.rank)
    (r t : ℕ) :
    pderiv (j, r) (P D a t) = if r = t then C (a j : ℂ) else 0 := by
  classical
  by_cases h : r = t
  · subst t
    simp [P, osc, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      smul_eq_C_mul]
  · simp [P, osc, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      smul_eq_C_mul, h, Ne.symm h]

private theorem alongPartial_P (D : LatticeData) (a : Charge D) (r t : ℕ) :
    alongPartial D a r (P D a t) =
      if r = t then (bilinear D a a : ℂ) • (1 : Oscillator D) else 0 := by
  classical
  simp only [alongPartial, derivation_sum_apply, Derivation.smul_apply, partial_P]
  by_cases h : r = t
  · simp only [h, ite_true, MvPolynomial.C_eq_smul_one]
    exact gram_smul D a 1
  · simp [h]

private theorem current_single (D : LatticeData) (a b : Charge D)
    (n : ℤ) (p : Oscillator D) :
    currentMode D a n (Finsupp.single b p) = Finsupp.single b
      (if n < 0 then P D a (-n - 1).toNat * p
       else if n = 0 then (bilinear D a b : ℂ) • p
       else (n : ℂ) • alongPartial D a (n - 1).toNat p) := by
  classical
  rw [currentMode_single]
  by_cases hn : n < 0
  · simp only [hn, ite_true, neutralPolynomialMode, LinearMap.mulLeft_apply,
      P, osc, smul_mul_assoc, Finset.sum_mul]
  · by_cases hz : n = 0
    · subst n
      simp only [lt_self_iff_false, ite_false, ite_true, neutralPolynomialMode,
        LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← Finset.sum_smul, pairing_left]
    · simp only [hn, hz, ite_false, neutralPolynomialMode, LinearMap.smul_apply,
        LinearMap.sum_apply, Derivation.coeFn_coe, alongPartial,
        derivation_sum_apply, Derivation.smul_apply]
      congr 1
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring

-- Finite creation coefficients, scaled by 6!, so every later calculation has
-- integral polynomial coefficients.  No exponential truncation is assumed.
private def E (D : LatticeData) (a : Charge D) : ℕ → Oscillator D
  | 0 => 720
  | 1 => 720 * P D a 0
  | 2 => 360 * P D a 0 ^ 2 + 360 * P D a 1
  | 3 => 120 * P D a 0 ^ 3 + 360 * P D a 0 * P D a 1 + 240 * P D a 2
  | 4 => 30 * P D a 0 ^ 4 + 180 * P D a 0 ^ 2 * P D a 1 +
      90 * P D a 1 ^ 2 + 240 * P D a 0 * P D a 2 + 180 * P D a 3
  | 5 => 6 * P D a 0 ^ 5 + 60 * P D a 0 ^ 3 * P D a 1 +
      90 * P D a 0 * P D a 1 ^ 2 + 120 * P D a 0 ^ 2 * P D a 2 +
      120 * P D a 1 * P D a 2 + 180 * P D a 0 * P D a 3 + 144 * P D a 4
  | 6 => P D a 0 ^ 6 + 15 * P D a 0 ^ 4 * P D a 1 +
      45 * P D a 0 ^ 2 * P D a 1 ^ 2 + 15 * P D a 1 ^ 3 +
      40 * P D a 0 ^ 3 * P D a 2 + 120 * P D a 0 * P D a 1 * P D a 2 +
      40 * P D a 2 ^ 2 + 90 * P D a 0 ^ 2 * P D a 3 +
      90 * P D a 1 * P D a 3 + 144 * P D a 0 * P D a 4 + 120 * P D a 5
  | _ => 0

private theorem deriv_ofNat (D : LatticeData) (n : ℕ) [n.AtLeastTwo] :
    oscillatorDerivation D (ofNat(n) : Oscillator D) = 0 := by
  exact Derivation.map_natCast (oscillatorDerivation D) n

private theorem E_step (D : LatticeData) (a : Charge D) (n : ℕ) (hn : n ≤ 5) :
    oscillatorDerivation D (E D a n) + P D a 0 * E D a n =
      (n + 1 : ℂ) • E D a (n + 1) := by
  interval_cases n <;>
    simp [E, P, Derivation.leibniz, Derivation.leibniz_pow, deriv_osc,
      smul_eq_C_mul, deriv_ofNat, map_ofNat] <;> ring

private theorem creation720_nat (D : LatticeData) (a : Charge D)
    (n : ℕ) : n ≤ 6 → (720 : ℂ) • creationCoeff D a n = E D a n := by
  induction n with
  | zero =>
    intro hn
    simp [creation_zero, E, smul_eq_C_mul, map_ofNat]
  | succ n ih =>
    intro hn
    have hn5 : n ≤ 5 := by omega
    have ih' := ih (by omega)
    have hrec : (n + 1 : ℂ) • ((720 : ℂ) • creationCoeff D a (n + 1)) =
        oscillatorDerivation D ((720 : ℂ) • creationCoeff D a n) +
          P D a 0 * ((720 : ℂ) • creationCoeff D a n) := by
      rw [Derivation.map_smul, creation_derivation]
      simp only [show P D a 0 = chargePolynomial D a by rfl,
        Nat.cast_add, Nat.cast_one, Int.cast_natCast, smul_sub, mul_smul_comm]
      module
    simp only [ih'] at hrec
    rw [E_step D a n hn5] at hrec
    have hne : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    calc
      (720 : ℂ) • creationCoeff D a (↑(n + 1) : ℤ) =
          (n + 1 : ℂ)⁻¹ • ((n + 1 : ℂ) •
            ((720 : ℂ) • creationCoeff D a (n + 1))) := by
              simp only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, one_smul, Nat.cast_add, Nat.cast_one]
      _ = (n + 1 : ℂ)⁻¹ • ((n + 1 : ℂ) • E D a (n + 1)) := by rw [hrec]
      _ = E D a (n + 1) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

private def Ei (D : LatticeData) (a : Charge D) (t : ℤ) : Oscillator D :=
  if t < 0 then 0 else E D a t.toNat

private theorem creation720 (D : LatticeData) (a : Charge D) (t : ℤ)
    (ht : t ≤ 6) : (720 : ℂ) • creationCoeff D a t = Ei D a t := by
  by_cases h : t < 0
  · simp [creationCoeff, Ei, h]
  · have he : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    simpa only [Ei, if_neg h, he] using
      creation720_nat D a t.toNat (by omega)

-- Every transport below is a transport of the actual P r, not a formal rank-one
-- generator identified with P r without proof.
private theorem transport_P (D : LatticeData) (b a : Charge D) (r : ℕ) :
    translatedPolynomial D b (P D a r) = Polynomial.C (P D a r) -
      Polynomial.C ((bilinear D b a : ℂ) • (1 : Oscillator D)) *
        Polynomial.X ^ (r + 1) := by
  classical
  by_cases hr : r = 0
  · subst r
    simpa only [P, osc_zero, Nat.zero_add, pow_one] using charge_transport D b a
  ·
    have hb : (∑ i : Fin D.rank, (a i : ℂ) *
        (bilinear D b (unitCharge D i) : ℂ)) = (bilinear D b a : ℂ) := by
      exact_mod_cast charge_pairing D b a
    rw [show P D a r = ∑ i : Fin D.rank, (a i : ℂ) • X (i, r) by rfl,
      translated_sum]
    simp only [translated_smul, translated_X, translationVariable, smul_sub,
      Finset.sum_sub_distrib]
    simp only [← smul_mul_assoc, Polynomial.smul_C, smul_smul,
      ← Finset.sum_mul, ← map_sum]
    rw [← Finset.sum_smul, hb]

private theorem transport_one (D : LatticeData) (b : Charge D) :
    translatedPolynomial D b (1 : Oscillator D) = 1 := by
  simp [translatedPolynomial]

private theorem transport_pow (D : LatticeData) (b : Charge D)
    (p : Oscillator D) (n : ℕ) :
    translatedPolynomial D b (p ^ n) = (translatedPolynomial D b p) ^ n := by
  simp [translatedPolynomial]

-- Only these eight actual inputs occur before weight six.
private inductive Atom where
  | one | x1 | x1sq | x2 | x1x2 | x1four | x1x3 | x2sq

private def Atom.value (D : LatticeData) (a : Charge D) : Atom → Oscillator D
  | .one => 1
  | .x1 => P D a 0
  | .x1sq => P D a 0 ^ 2
  | .x2 => P D a 1
  | .x1x2 => P D a 0 * P D a 1
  | .x1four => P D a 0 ^ 4
  | .x1x3 => P D a 0 * P D a 2
  | .x2sq => P D a 1 ^ 2

private def Atom.frequency : Atom → ℕ
  | .one => 0
  | .x1 | .x1sq | .x1four => 1
  | .x2 | .x1x2 | .x2sq => 2
  | .x1x3 => 3

private def Atom.degree : Atom → ℕ
  | .one => 0
  | .x1 => 1
  | .x1sq | .x2 => 2
  | .x1x2 => 3
  | .x1four | .x1x3 | .x2sq => 4

private theorem Atom.tail (D : LatticeData) (a : Charge D)
    (u : Atom) (r : ℕ) (hr : u.frequency ≤ r) :
    alongPartial D a r (u.value D a) = 0 := by
  cases u <;>
    simp only [Atom.frequency] at hr <;>
    simp only [Atom.value, Derivation.leibniz, Derivation.leibniz_pow,
      alongPartial_P, Derivation.map_one_eq_zero]
  all_goals split_ifs <;> simp_all <;> omega

-- The finite annihilation coefficients of the eight inputs.  The variable q is
-- an actual scalar in the oscillator ring, namely (b,a) times 1.
private def Atom.coefficient (D : LatticeData) (a : Charge D)
    (q : Oscillator D) : Atom → ℕ → Oscillator D
  | .one, 0 => 1
  | .x1, 0 => P D a 0
  | .x1, 1 => -q
  | .x1sq, 0 => P D a 0 ^ 2
  | .x1sq, 1 => -2 * q * P D a 0
  | .x1sq, 2 => q ^ 2
  | .x2, 0 => P D a 1
  | .x2, 2 => -q
  | .x1x2, 0 => P D a 0 * P D a 1
  | .x1x2, 1 => -q * P D a 1
  | .x1x2, 2 => -q * P D a 0
  | .x1x2, 3 => q ^ 2
  | .x1four, 0 => P D a 0 ^ 4
  | .x1four, 1 => -4 * q * P D a 0 ^ 3
  | .x1four, 2 => 6 * q ^ 2 * P D a 0 ^ 2
  | .x1four, 3 => -4 * q ^ 3 * P D a 0
  | .x1four, 4 => q ^ 4
  | .x1x3, 0 => P D a 0 * P D a 2
  | .x1x3, 1 => -q * P D a 2
  | .x1x3, 3 => -q * P D a 0
  | .x1x3, 4 => q ^ 2
  | .x2sq, 0 => P D a 1 ^ 2
  | .x2sq, 2 => -2 * q * P D a 1
  | .x2sq, 4 => q ^ 2
  | _, _ => 0

private theorem Atom.transport (D : LatticeData) (a b : Charge D) (u : Atom) :
    translatedPolynomial D b (u.value D a) =
      ∑ d ∈ Finset.range (u.degree + 1), Polynomial.monomial d
        (u.coefficient D a ((bilinear D b a : ℂ) • 1) d) := by
  cases u <;>
    simp [Atom.value, Atom.degree, Atom.coefficient, transport_one,
      translated_mul, transport_pow, transport_P, Finset.sum_range_succ,
      ← Polynomial.C_mul_X_pow_eq_monomial, smul_eq_C_mul, map_mul, map_pow, map_neg, map_ofNat] <;> ring

private def rawPolynomial (D : LatticeData) (a b c : Charge D)
    (k : ℕ) (u : Atom) : Oscillator D :=
  ∑ d ∈ Finset.range (u.degree + 1),
    u.coefficient D a ((bilinear D b a : ℂ) • 1) d *
      Ei D b ((k : ℤ) - 2 - bilinear D b c + d)

-- The finite sum has been proved equal to the full production raw coefficient.
-- In particular negative creation indices, including the same-sign ±2a
-- channels, use the actual definition of creationCoeff.
private theorem raw_atom (D : LatticeData) (a b c : Charge D) (k : ℕ) (u : Atom)
    (hbound : (k : ℤ) - 2 - bilinear D b c + u.degree ≤ 6) :
    (720 : ℂ) • rawCoeff D b ((k : ℤ) - 2)
      (Finsupp.single c (u.value D a)) =
    epsilon D b c • Finsupp.single (b + c) (rawPolynomial D a b c k u) := by
  classical
  have hc : (720 : ℂ) • convolution D b ((k : ℤ) - 2 - bilinear D b c)
      (translatedPolynomial D b (u.value D a)) = rawPolynomial D a b c k u := by
    rw [Atom.transport, map_sum]
    simp only [convolution_monomial, Finset.smul_sum, ← mul_smul_comm]
    unfold rawPolynomial
    apply Finset.sum_congr rfl
    intro d hd
    rw [creation720 D b _ (by have := Finset.mem_range.mp hd; omega)]
  rw [raw_single_convolution, smul_comm (720 : ℂ) (epsilon D b c),
    Finsupp.smul_single, hc]

private def currentPolynomial (D : LatticeData) (a b : Charge D)
    (n : ℤ) (p : Oscillator D) : Oscillator D :=
  if n < 0 then P D a (-n - 1).toNat * p
  else if n = 0 then (bilinear D a b : ℂ) • p
  else (n : ℂ) • alongPartial D a (n - 1).toNat p

private def quadraticPolynomial (D : LatticeData) (a b : Charge D)
    (k : ℕ) (u : Atom) : Oscillator D :=
  (∑ j ∈ Finset.range (k + u.frequency),
    P D a j * currentPolynomial D a b (1 - (k : ℤ) + j) (u.value D a)) +
  (∑ j ∈ Finset.range (u.frequency + 1),
    P D a (k + j - 1) * currentPolynomial D a b j (u.value D a))

private theorem quadratic_atom (D : LatticeData) (a b : Charge D)
    (k : ℕ) (hk : 1 ≤ k) (u : Atom) :
    mu D (quadraticState D a) (1 - (k : ℤ))
      (Finsupp.single b (u.value D a)) =
    Finsupp.single b (quadraticPolynomial D a b k u) := by
  classical
  have tail (n : ℤ) (hn : (u.frequency : ℤ) < n) :
      currentMode D a n (Finsupp.single b (u.value D a)) = 0 := by
    rw [current_single]
    have hn0 : ¬ n < 0 := by omega
    have hn1 : n ≠ 0 := by omega
    rw [if_neg hn0, if_neg hn1, Atom.tail D a u _ (by omega)]
    simp
  rw [quadratic_product_formula]
  have first : (∑ᶠ j : ℕ, currentMode D a (-(j : ℤ) - 1)
      (currentMode D a (1 - (k : ℤ) + j)
        (Finsupp.single b (u.value D a)))) =
      ∑ j ∈ Finset.range (k + u.frequency), currentMode D a (-(j : ℤ) - 1)
        (currentMode D a (1 - (k : ℤ) + j)
          (Finsupp.single b (u.value D a))) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (by dsimp only; rw [tail _ (by omega), map_zero])
  have second : (∑ᶠ j : ℕ, currentMode D a (1 - (k : ℤ) - j - 1)
      (currentMode D a j (Finsupp.single b (u.value D a)))) =
      ∑ j ∈ Finset.range (u.frequency + 1),
        currentMode D a (1 - (k : ℤ) - j - 1)
          (currentMode D a j (Finsupp.single b (u.value D a))) := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    apply Finset.mem_range.mpr
    by_contra h
    exact hj (by dsimp only; rw [tail _ (by omega), map_zero])
  rw [first, second]
  change _ = Finsupp.single b (quadraticPolynomial D a b k u)
  unfold quadraticPolynomial
  rw [Finsupp.single_add, Finsupp.single_finsetSum, Finsupp.single_finsetSum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [current_single D a b (1 - (k : ℤ) + j)]
    change currentMode D a (-(j : ℤ) - 1)
      (Finsupp.single b (currentPolynomial D a b (1 - (k : ℤ) + j) (u.value D a))) = _
    exact currentMode_negative D a b j _
  · apply Finset.sum_congr rfl
    intro j hj
    rw [current_single D a b (j : ℤ)]
    have hi : 1 - (k : ℤ) - j - 1 = -((k + j - 1 : ℕ) : ℤ) - 1 := by omega
    rw [hi]
    change currentMode D a (-((k + j - 1 : ℕ) : ℤ) - 1)
      (Finsupp.single b (currentPolynomial D a b j (u.value D a))) = _
    exact currentMode_negative D a b (k + j - 1) _

-- 16 * 6! times the exact production mode.  This scaling serves only to keep
-- the finite coefficient certificates integral; it changes no target state.
private def A (D : LatticeData) (a : Charge D) (s : ℂ) (k : ℕ) :
    Module.End ℂ (Carrier D) := (11520 : ℂ) • mode D a s (-(k : ℤ))

private theorem A_expansion (D : LatticeData) (a : Charge D) (s : ℂ)
    (k : ℕ) (v : Carrier D) :
    A D a s k v = (720 : ℂ) • mu D (quadraticState D a) (1 - (k : ℤ)) v +
      (4 * s) • ((720 : ℂ) • rawCoeff D a ((k : ℤ) - 2) v +
        (720 : ℂ) • rawCoeff D (-a) ((k : ℤ) - 2) v) := by
  simp only [A, mode, show -(k : ℤ) + 1 = 1 - (k : ℤ) by omega,
    vector, chargedState, map_add, map_smul,
    Pi.add_apply, Pi.smul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, mu,
    stateField_ground, actual_modes,
    show -(1 - (k : ℤ)) - 1 = (k : ℤ) - 2 by omega]
  module

private theorem A_atom (D : LatticeData) (a b : Charge D) (s : ℂ)
    (k : ℕ) (hk : 1 ≤ k) (u : Atom)
    (hp : (k : ℤ) - 2 - bilinear D a b + u.degree ≤ 6)
    (hm : (k : ℤ) - 2 - bilinear D (-a) b + u.degree ≤ 6) :
    A D a s k (Finsupp.single b (u.value D a)) =
      Finsupp.single b ((720 : ℂ) • quadraticPolynomial D a b k u) +
      (4 * s) • (epsilon D a b •
        Finsupp.single (a + b) (rawPolynomial D a a b k u) +
        epsilon D (-a) b •
          Finsupp.single (-a + b) (rawPolynomial D a (-a) b k u)) := by
  rw [A_expansion, quadratic_atom D a b k hk u,
    raw_atom D a a b k u hp, raw_atom D a (-a) b k u hm,
    Finsupp.smul_single]

private def atom (D : LatticeData) (a b : Charge D) (u : Atom) : Carrier D :=
  Finsupp.single b (u.value D a)

private def tri (D : LatticeData) (a : Charge D) (p q r : Oscillator D) : Carrier D :=
  Finsupp.single 0 p + Finsupp.single a q + Finsupp.single (-a) r

private abbrev S (D : LatticeData) (s : ℂ) : Oscillator D := C s

private theorem phase_same (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D a a = 1 := by
  rw [epsilon,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square, ha]
  norm_num [paritySign]

private theorem phase_zero (D : LatticeData) (a : Charge D) : epsilon D a 0 = 1 := by
  simp [epsilon, lowerCocycleExponent, paritySign]

private theorem phase_neg_left (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D (-a) a = 1 := by
  simpa only [neg_neg] using opposite_phase D (-a) (neg_norm D a ha)

private theorem phase_neg_same (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) : epsilon D (-a) (-a) = 1 :=
  phase_same D (-a) (neg_norm D a ha)

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumNull

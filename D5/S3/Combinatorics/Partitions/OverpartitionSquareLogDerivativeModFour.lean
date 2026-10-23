/- GID: D5/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/OverpartitionSquareLogDerivativeModFour
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Square-indexed overpartition logarithmic coefficients have the predicted residues. -/

/-
Public theorem result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#18874; Proved)
Direct frozen dependencies (declaration statement_id, not module pins):
  D5/S1/Recurrence/LinearRows/LinearExponentDyadicSupport.derivative_map
    sha256:8f1b29dc2fe48e39dfdec69ee4aec1c153907e4acd3d245b192222ea8bb6f9a8
  D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.four_zero
    sha256:f02dace9445f05a15afa22749293c90a1056dfca858141f725bdd68c650c9206
  D5/S1/Recurrence/Parity/BilateralQuarticPowerThetaModFour.map_inv
    sha256:84254a37d7611374957fadbf596aab8f80ead28f1020c63db9c0f1261844a9e7
  D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs.geom
    sha256:da285321e1c883abc963dc11ac3324d3e73c6d36c7091a9595cd08d956d187a8
  D5/S1/Recurrence/Invariants/ScaledReversionCongruence.geometric
    sha256:c395044e46171a2f375a1307f93dd04dc7323a6a10bfd5c4936657bcbc6e83fa
All private theorems have proof_shape: bind-only and escape_witness: none.
Their consumers are:
  geo_eq_expand -> geo_mul; geo_mul -> factor_eq, factor_rational;
  map_geo -> map_factor; factor_eq -> product_mod_four;
  map_factor -> pbarZ_cast, pbarZ_mod_four; factor_rational -> pbarZ_cast;
  pbarZ_cast -> GZ_cast; product_mod_four -> pbarZ_mod_four;
  pbarZ_mod_four -> pbarZ_square; pbarZ_zero -> GZ_zero, GZ_mod_four;
  square_divisors_odd -> pbarZ_square; pbarZ_square -> GZ_mod_four;
  GZ_zero -> logZ_cast, logZ_mod_four; GZ_cast -> logZ_cast;
  GZ_mod_four -> logZ_mod_four; logZ_cast -> result;
  logZ_mod_four -> logZ_coeff_mod_four; logZ_coeff_mod_four -> result.
The four source definitions retain the expressions in #18874. The integer geometric
series is reused from AndrewsElBachraouiDefs, with coefficient maps inside the proofs.
The positive geometric tail is ScaledReversionCongruence.geometric.
The private owner lemmas derivative_map, four_zero and map_inv are reused through OpenPrivate.
The argument uses symbolic products over arbitrary finite sets, divisor factorization
and formal-series identities. Characteristic normalization is not a certified instance,
bounded enumeration, checker or numeric reduction; utility is none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19996
-/

import D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
import D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
import D5.S1.Recurrence.Invariants.ScaledReversionCongruence

/-! The overpartition product linearizes modulo four. Square divisor counts and
the integer unit inverse then give the logarithmic derivative congruences. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.OverpartitionSquareLogDerivativeModFour

open PowerSeries
open D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs (geom)
open D5.S1.Recurrence.Invariants.ScaledReversionCongruence (geometric)
open private derivative_map from D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport
open private map_inv four_zero from D5.S1.Recurrence.Parity.BilateralQuarticPowerThetaModFour

noncomputable def pbar (m : ℕ) : ℚ :=
  coeff m (∏ k ∈ Finset.Icc 1 m, (1 + X ^ k) * ((1 : PowerSeries ℚ) - X ^ k)⁻¹)
noncomputable def G : PowerSeries ℚ := mk fun n => pbar (n ^ 2)
noncomputable def logDerivative : PowerSeries ℚ := X * derivative (R := ℚ) G * G⁻¹

def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ z : ℤ, coeff m logDerivative = z ∧
    (Odd m → z ≡ 2 [ZMOD 4]) ∧ (Even m → z ≡ 0 [ZMOD 4])

variable {R S : Type*} [CommRing R] [CommRing S]
private noncomputable def factor (k : ℕ) : PowerSeries R :=
  (1 + X ^ k) * (geom k).map (Int.castRingHom R)
private noncomputable def pbarZ (m : ℕ) : ℤ :=
  coeff m (∏ k ∈ Finset.Icc 1 m, factor k)
private noncomputable def GZ : PowerSeries ℤ := mk fun n => pbarZ (n ^ 2)
private noncomputable def logZ : PowerSeries ℤ :=
  X * derivative (R := ℤ) GZ * invOfUnit GZ 1

private theorem geo_eq_expand (k : ℕ) (hk : k ≠ 0) :
    ((geom k).map (Int.castRingHom R)) = expand k hk (mk 1) := by
  ext n
  simp [geom, coeff_expand]

private theorem geo_mul (k : ℕ) (hk : k ≠ 0) :
    ((geom k).map (Int.castRingHom R)) * (1 - X ^ k) = 1 := by
  rw [geo_eq_expand k hk]
  simpa using congrArg (expand k hk) (mk_one_mul_one_sub_eq_one R)

private theorem map_geo (f : R →+* S) (k : ℕ) :
    ((geom k).map (Int.castRingHom R)).map f = (geom k).map (Int.castRingHom S) := by
  change (MvPowerSeries.map f) ((MvPowerSeries.map (Int.castRingHom R)) (geom k)) =
    (MvPowerSeries.map (Int.castRingHom S)) (geom k)
  rw [MvPowerSeries.map_map, RingHom.eq_intCast' (f.comp (Int.castRingHom R))]

private theorem factor_eq (k : ℕ) (hk : k ≠ 0) :
    factor (R := R) k = 1 + 2 * (((geom k).map (Int.castRingHom R)) - 1) := by
  have h := geo_mul (R := R) k hk
  unfold factor
  linear_combination -h

private theorem map_factor (f : R →+* S) (k : ℕ) :
    (factor k).map f = factor k := by
  simp [factor, map_geo]

private theorem factor_rational (k : ℕ) (hk : k ≠ 0) :
    factor (R := ℚ) k = (1 + X ^ k) * ((1 : PowerSeries ℚ) - X ^ k)⁻¹ := by
  unfold factor
  congr 1
  apply (eq_inv_iff_mul_eq_one ?_).mpr (geo_mul k hk)
  simp [hk]

private theorem pbarZ_cast (m : ℕ) : (pbarZ m : ℚ) = pbar m := by
  change (Int.castRingHom _) (coeff m (∏ k ∈ Finset.Icc 1 m, factor (R := ℤ) k)) = _
  rw [← coeff_map]
  simp only [map_prod, map_factor]
  unfold pbar
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  exact factor_rational k (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)

private theorem product_mod_four (s : Finset ℕ) (hs : ∀ k ∈ s, k ≠ 0) :
    (∏ k ∈ s, factor (R := ZMod 4) k) =
      1 + 2 * ∑ k ∈ s, ((geom k).map (Int.castRingHom (ZMod 4)) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk,
      ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)),
      factor_eq k (hs k (Finset.mem_insert_self k s))]
    linear_combination ((geom k).map (Int.castRingHom (ZMod 4)) - 1) *
      (∑ j ∈ s, ((geom j).map (Int.castRingHom (ZMod 4)) - 1)) * four_zero

private theorem pbarZ_mod_four (m : ℕ) (hm : 0 < m) :
    (pbarZ m : ZMod 4) = 2 * (m.divisors.card : ZMod 4) := by
  change (Int.castRingHom _) (coeff m (∏ k ∈ Finset.Icc 1 m, factor (R := ℤ) k)) = _
  rw [← coeff_map]
  simp only [map_prod, map_factor]
  rw [product_mod_four _ (fun k hk => Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)]
  simp only [map_add, coeff_one, hm.ne', coeff_ofNat_mul,
    map_sum, map_sub, coeff_map, geom, coeff_mk]
  have he : (Finset.Icc 1 m).filter (fun k => k ∣ m) = m.divisors := by
    rfl
  simp only [ite_false, apply_ite, map_one, map_zero, sub_zero, zero_add]
  rw [← Finset.sum_filter, he]
  simp

private theorem pbarZ_zero : pbarZ 0 = 1 := by simp [pbarZ]

private theorem square_divisors_odd (n : ℕ) (hn : 0 < n) :
    Odd ((n ^ 2).divisors.card) := by
  rw [← ZMod.natCast_eq_one_iff_odd]
  change (((n ^ 2).divisors.card : ZMod 2)) = 1
  rw [Nat.card_divisors (pow_ne_zero _ hn.ne')]
  push_cast
  apply Finset.prod_eq_one
  intro p hp
  rw [Nat.factorization_pow]
  change (((2 * n.factorization p : ℕ) : ZMod 2) + 1) = 1
  push_cast
  simp only [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul, zero_add]

private theorem pbarZ_square (n : ℕ) (hn : 0 < n) :
    (pbarZ (n ^ 2) : ZMod 4) = 2 := by
  rw [pbarZ_mod_four _ (pow_pos hn _)]
  obtain ⟨k, hk⟩ := square_divisors_odd n hn
  rw [hk]
  push_cast
  have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  linear_combination (k : ZMod 4) * h4

private theorem GZ_zero : constantCoeff GZ = 1 := by simp [GZ, pbarZ_zero]
private theorem GZ_cast : GZ.map (Int.castRingHom ℚ) = G := by
  ext n
  simp [GZ, G, pbarZ_cast]

private theorem GZ_mod_four : GZ.map (Int.castRingHom (ZMod 4)) = 1 + 2 * geometric := by
  ext n
  cases n with
  | zero => simp [GZ, geometric, pbarZ_zero]
  | succ n => simp [GZ, geometric, pbarZ_square (n + 1) (Nat.succ_pos n)]

private theorem logZ_cast : logZ.map (Int.castRingHom ℚ) = logDerivative := by
  have hi : (invOfUnit GZ 1).map (Int.castRingHom ℚ) = G⁻¹ := by
    rw [map_inv (Int.castRingHom ℚ) GZ GZ_zero, GZ_cast]
    apply PowerSeries.invOfUnit_eq' G 1
    rw [← GZ_cast, ← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, GZ_zero]
    norm_num
  simp only [logZ, logDerivative, map_mul, map_X, derivative_map, GZ_cast, hi]

private theorem logZ_mod_four : logZ.map (Int.castRingHom (ZMod 4)) =
    2 * X * derivative (R := ZMod 4) geometric := by
  let B := (invOfUnit GZ 1).map (Int.castRingHom (ZMod 4))
  have hi : B * (1 + 2 * geometric) = 1 := by
    rw [← GZ_mod_four, ← map_mul, invOfUnit_mul GZ 1 GZ_zero, map_one]
  have hb : B = 1 - 2 * geometric := by
    linear_combination (1 - 2 * geometric) * hi + B * geometric ^ 2 * four_zero
  have hd : derivative (R := ZMod 4) (1 + 2 * geometric) =
      2 * derivative (R := ZMod 4) geometric := by
    rw [show (2 : PowerSeries (ZMod 4)) = C 2 from (map_ofNat C 2).symm]
    simp [Derivation.leibniz]
  simp only [logZ, map_mul, map_X, derivative_map, GZ_mod_four, hd]
  change X * (2 * derivative (R := ZMod 4) geometric) * B = _
  rw [hb]
  linear_combination -(X * derivative (R := ZMod 4) geometric * geometric) * four_zero

private theorem logZ_coeff_mod_four (m : ℕ) (hm : 0 < m) :
    ((coeff m logZ : ℤ) : ZMod 4) = 2 * (m : ZMod 4) := by
  have h := congrArg (coeff m) logZ_mod_four
  rw [coeff_map] at h
  change (Int.castRingHom (ZMod 4)) (coeff m logZ) = _
  rw [h, mul_assoc, coeff_ofNat_mul]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [coeff_succ_X_mul, coeff_derivative]
  simp [geometric, coeff_succ_X_mul]

theorem result : claim := by
  intro m hm
  have h4 : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  refine ⟨coeff m logZ, ?_, ?_, ?_⟩
  · have h := congrArg (coeff m) logZ_cast
    simpa using h.symm
  · intro ho
    apply (ZMod.intCast_eq_intCast_iff (coeff m logZ) 2 4).mp
    change ((coeff m logZ : ℤ) : ZMod 4) = 2
    rw [logZ_coeff_mod_four m hm]
    obtain ⟨k, hk⟩ := ho
    rw [hk]
    push_cast
    linear_combination (k : ZMod 4) * h4
  · intro he
    apply (ZMod.intCast_eq_intCast_iff (coeff m logZ) 0 4).mp
    change ((coeff m logZ : ℤ) : ZMod 4) = 0
    rw [logZ_coeff_mod_four m hm]
    obtain ⟨k, hk⟩ := he
    rw [hk]
    push_cast
    linear_combination (k : ZMod 4) * h4

end D5.S3.Combinatorics.Partitions.OverpartitionSquareLogDerivativeModFour

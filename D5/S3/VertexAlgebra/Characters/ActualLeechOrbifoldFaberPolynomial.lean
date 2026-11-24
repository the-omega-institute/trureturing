/- GID: D5/S3/VertexAlgebra/Characters/ActualLeechOrbifoldFaberPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/ActualLeechOrbifoldFaberPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Faber polar polynomials and their unnormalized Hecke values for the native Leech character. -/

import D5.S3.VertexAlgebra.Characters.ActualLeechOrbifoldHeckeModularity
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.LaurentSeries

/-! The triangular coefficient recurrence constructs the Faber polynomials of the
native Leech orbifold character. Multiplying the substituted polynomial by a
sufficient power of the cusp coordinate lets us compare its formal and
convergent expansions using ordinary power series. -/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped BigOperators Manifold Matrix MatrixGroups ModularForm Topology

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldFaberPolynomial

open Polynomial
open ActualLeechOrbifoldTraceSeries (character)
open ActualLeechOrbifoldHeckeExpansion
  (coeff coeff_zero heckeSum triangularSum triangularPoint coe_triangularPoint
    heckeCoeff heckeCoeff_zero heckeSum_hasSum)
open ActualLeechOrbifoldHeckeModularity
  (heckeSum_smul heckeSum_mdifferentiable eq_heckeSum_of_sub_pole_isZeroAtImInfty)

local notation "𝕢" => Function.Periodic.qParam 1
local notation "ι" => HahnSeries.ofPowerSeries ℤ ℂ
local notation "T" => (PowerSeries.X : PowerSeries ℂ)

private def withPole (G : PowerSeries ℂ) : LaurentSeries ℂ :=
  HahnSeries.single (-1) 1 * ι G

private def evaluate (G : PowerSeries ℂ) : Polynomial ℂ →+* LaurentSeries ℂ :=
  Polynomial.eval₂RingHom (HahnSeries.C : ℂ →+* LaurentSeries ℂ) (withPole G)

private theorem withPole_pow (G : PowerSeries ℂ) (n : ℕ) :
    withPole G ^ n = HahnSeries.single (-(n : ℤ)) 1 * ι (G ^ n) := by
  rw [withPole, mul_pow, HahnSeries.single_pow, ← map_pow]
  simp

private theorem coeff_ofPowerSeries_of_neg (A : PowerSeries ℂ) {k : ℤ} (hk : k < 0) :
    (ι A).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
  rintro ⟨n, hn⟩
  exact hk.not_ge (hn ▸ Int.natCast_nonneg n)

private theorem coeff_withPole_pow_of_lt (G : PowerSeries ℂ) {n : ℕ} {k : ℤ}
    (hk : k < -(n : ℤ)) : (withPole G ^ n).coeff k = 0 := by
  rw [withPole_pow, HahnSeries.coeff_single_mul, one_mul]
  exact coeff_ofPowerSeries_of_neg _ (by omega)

private theorem coeff_withPole_pow_at_pole {G : PowerSeries ℂ}
    (hG : G.constantCoeff = 1) (n : ℕ) :
    (withPole G ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [withPole_pow, HahnSeries.coeff_single_mul, sub_self, one_mul]
  change (ι (G ^ n)).coeff (↑(0 : ℕ)) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, hG, one_pow]

/-- Subtract the lower polar terms of the power `J^n` using the already
normalized polynomials. The term indexed by zero cancels the constant. -/
private def faber (G : PowerSeries ℂ) (n : ℕ) : Polynomial ℂ :=
  X ^ n - ∑ j : Fin n, C ((withPole G ^ n).coeff (-(j.val : ℤ))) * faber G j.val
termination_by n
decreasing_by exact j.isLt

private theorem faber_coeff (G : PowerSeries ℂ) (n : ℕ) :
    (faber G n).natDegree = n ∧ (faber G n).Monic := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [faber]
    have hs : (∑ j : Fin n, C ((withPole G ^ n).coeff (-(j.val : ℤ))) *
        faber G j.val).natDegree ≤ n := by
      apply natDegree_sum_le_of_forall_le
      intro j _
      exact (natDegree_C_mul_le _ _).trans ((ih j.val j.isLt).1.le.trans j.isLt.le)
    have hb := natDegree_sub_le_of_le (by simp : (X ^ n : Polynomial ℂ).natDegree ≤ n) hs
    have hc : (X ^ n - ∑ j : Fin n, C ((withPole G ^ n).coeff (-(j.val : ℤ))) *
        faber G j.val : Polynomial ℂ).coeff n = 1 := by
      rw [coeff_sub, coeff_X_pow_self, finsetSum_coeff]
      refine sub_eq_self.mpr (Finset.sum_eq_zero fun j _ => ?_)
      have hj : (faber G j.val).natDegree < n := by
        rw [(ih j.val j.isLt).1]
        exact j.isLt
      rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt hj, mul_zero]
    rw [max_self] at hb
    exact ⟨le_antisymm hb (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero)),
      monic_of_natDegree_le_of_coeff_eq_one n hb hc⟩

private theorem evaluate_coeff_faber {G : PowerSeries ℂ} (hG : G.constantCoeff = 1)
    (n m : ℕ) : (evaluate G (faber G n)).coeff (-(m : ℤ)) = if m = n then 1 else 0 := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    rw [faber, map_sub, map_pow, map_sum, HahnSeries.coeff_sub, HahnSeries.coeff_sum]
    have hX : evaluate G X = withPole G := Polynomial.eval₂_X _ _
    rw [hX]
    simp only [map_mul, show ∀ a : ℂ, evaluate G (C a) = HahnSeries.single 0 a
      from fun a => Polynomial.eval₂_C _ _, HahnSeries.coeff_single_zero_mul,
      fun j : Fin n => ih j.val j.isLt m]
    by_cases hm : m < n
    · let j : Fin n := ⟨m, hm⟩
      rw [Finset.sum_eq_single j]
      · simp [j, hm.ne]
      · intro i _ hi
        have hi' : m ≠ i.val := fun h => hi (Fin.ext h.symm)
        simp [hi']
      · simp
    · have hsum : (∑ j : Fin n, (withPole G ^ n).coeff (-(j.val : ℤ)) *
          (if m = j.val then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have hne : m ≠ j.val := by omega
        simp [hne]
      rw [hsum, sub_zero]
      rcases eq_or_lt_of_le (Nat.le_of_not_gt hm) with rfl | hlt
      · simp [coeff_withPole_pow_at_pole hG]
      · rw [coeff_withPole_pow_of_lt G (by omega), ite_eq_right hlt.ne']

private theorem evaluate_coeff_at_degree {G : PowerSeries ℂ} (hG : G.constantCoeff = 1)
    (P : Polynomial ℂ) (n : ℕ) (hP : P.natDegree ≤ n) :
    (evaluate G P).coeff (-(n : ℤ)) = P.coeff n := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)]
  rw [map_sum, HahnSeries.coeff_sum, Finset.sum_eq_single n]
  · simp only [map_mul, map_pow, show ∀ a : ℂ, evaluate G (C a) = HahnSeries.single 0 a
      from fun a => Polynomial.eval₂_C _ _, HahnSeries.coeff_single_zero_mul,
      show evaluate G X = withPole G from Polynomial.eval₂_X _ _,
      coeff_withPole_pow_at_pole hG, mul_one]
  · intro j hj hjne
    have hjlt : j < n := by
      have := Finset.mem_range.mp hj
      omega
    simp only [map_mul, map_pow, show ∀ a : ℂ, evaluate G (C a) = HahnSeries.single 0 a
      from fun a => Polynomial.eval₂_C _ _, HahnSeries.coeff_single_zero_mul,
      show evaluate G X = withPole G from Polynomial.eval₂_X _ _,
      coeff_withPole_pow_of_lt G (show -(n : ℤ) < -(j : ℤ) by omega), mul_zero]
  · simp

private theorem eq_faber_of_polar {G : PowerSeries ℂ} (hG : G.constantCoeff = 1)
    (P : Polynomial ℂ) (n : ℕ)
    (hP : ∀ m : ℕ, (evaluate G P).coeff (-(m : ℤ)) = if m = n then 1 else 0) :
    P = faber G n := by
  by_contra hne
  let D := P - faber G n
  have hD : D ≠ 0 := sub_ne_zero.mpr hne
  apply (show D.coeff D.natDegree ≠ 0 by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hD)
  rw [← evaluate_coeff_at_degree hG D D.natDegree le_rfl]
  simp only [D, map_sub, HahnSeries.coeff_sub, hP, evaluate_coeff_faber hG, sub_self]

/-- The formal power series for `q J(q)` from the native dimensions. -/
def normalizedCharacter : PowerSeries ℂ :=
  1 + T * PowerSeries.mk ActualLeechOrbifoldHeckeExpansion.coeff

private theorem constantCoeff_normalizedCharacter : normalizedCharacter.constantCoeff = 1 := by
  simp [normalizedCharacter]

/-- The actual native Laurent series `J = q⁻¹ + ∑_{k ≥ 1} c(k) q^k`. -/
def characterLaurent : LaurentSeries ℂ := withPole normalizedCharacter

/-- The polynomial determined by the native Laurent coefficients and the
triangular Faber recurrence. -/
def faberPolynomial (n : ℕ) : Polynomial ℂ := faber normalizedCharacter n

/-- The native coefficient recurrence, including the constant cancellation at index zero. -/
theorem faberPolynomial_recurrence (n : ℕ) :
    faberPolynomial n = X ^ n - ∑ j : Fin n,
      C ((characterLaurent ^ n).coeff (-(j.val : ℤ))) * faberPolynomial j.val := by
  change faber normalizedCharacter n = X ^ n - ∑ j : Fin n,
    C ((withPole normalizedCharacter ^ n).coeff (-(j.val : ℤ))) * faber normalizedCharacter j.val
  rw [faber]

/-- The Faber polynomial has degree `n` and leading coefficient one. -/
theorem faberPolynomial_monic_degree (n : ℕ) :
    (faberPolynomial n).Monic ∧ (faberPolynomial n).natDegree = n :=
  (faber_coeff normalizedCharacter n).symm

/-- The full nonpositive part of `P_n(J)` consists of `q⁻ⁿ` alone. -/
theorem coeff_faberPolynomial_characterLaurent (n m : ℕ) :
    ((faberPolynomial n).eval₂ HahnSeries.C characterLaurent).coeff (-(m : ℤ)) =
      if m = n then 1 else 0 :=
  evaluate_coeff_faber constantCoeff_normalizedCharacter n m

/-- The nonpositive Laurent coefficients uniquely determine the polynomial. -/
theorem eq_faberPolynomial_of_polar (P : Polynomial ℂ) (n : ℕ)
    (hP : ∀ m : ℕ, (P.eval₂ HahnSeries.C characterLaurent).coeff (-(m : ℤ)) =
      if m = n then 1 else 0) : P = faberPolynomial n :=
  eq_faber_of_polar constantCoeff_normalizedCharacter P n hP

/-- The native Laurent series has the vacuum pole and the supplied regular coefficients. -/
theorem characterLaurent_eq :
    characterLaurent = HahnSeries.single (-1) 1 +
      ι (PowerSeries.mk ActualLeechOrbifoldHeckeExpansion.coeff) := by
  rw [characterLaurent, withPole, normalizedCharacter, map_add, (HahnSeries.ofPowerSeries ℤ ℂ).map_one, map_mul,
    HahnSeries.ofPowerSeries_X, mul_add, mul_one, ← mul_assoc, HahnSeries.single_mul_single]
  simp

private theorem heckeSum_one : heckeSum 1 = character := by
  funext τ
  unfold heckeSum
  have he : (1 : ℕ).divisors.attach =
      {⟨1, Nat.mem_divisors_self 1 one_ne_zero⟩} := by
    ext a
    simp only [Finset.mem_attach, Finset.mem_singleton, true_iff]
    exact Subtype.ext (by simpa [Nat.divisors_one] using a.property)
  rw [he, Finset.sum_singleton]
  have hp : triangularPoint (a := 1) (d := 1) one_pos one_pos 0 τ = τ := by
    apply UpperHalfPlane.ext
    simp [coe_triangularPoint]
  simp [triangularSum, hp]

private theorem heckeCoeff_one (m : ℕ) : heckeCoeff 1 m = coeff m := by
  simp [heckeCoeff, Nat.divisors_one]

private def SeriesHasSum (q : ℂ) (A : PowerSeries ℂ) (z : ℂ) : Prop :=
  HasSum (fun k : ℕ => PowerSeries.coeff k A * q ^ k) z

private theorem SeriesHasSum.add {q a b : ℂ} {A B : PowerSeries ℂ}
    (hA : SeriesHasSum q A a) (hB : SeriesHasSum q B b) : SeriesHasSum q (A + B) (a + b) := by
  refine (HasSum.add hA hB).congr_fun fun k => ?_
  rw [map_add, add_mul]

private theorem SeriesHasSum.mul {q a b : ℂ} {A B : PowerSeries ℂ}
    (hA : SeriesHasSum q A a) (hB : SeriesHasSum q B b) : SeriesHasSum q (A * B) (a * b) := by
  have hAn := summable_norm_iff.mpr (HasSum.summable hA)
  have hBn := summable_norm_iff.mpr (HasSum.summable hB)
  have hterm (k : ℕ) :
      (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
          (PowerSeries.coeff ij.1 A * q ^ ij.1) * (PowerSeries.coeff ij.2 B * q ^ ij.2)) =
        PowerSeries.coeff k (A * B) * q ^ k := by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, pow_add]
    ring
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hAn hBn).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hAn hBn,
    HasSum.tsum_eq hA, HasSum.tsum_eq hB] at hs
  exact hs.congr_fun fun k => (hterm k).symm

private theorem seriesHasSum_monomial (q a : ℂ) (n : ℕ) :
    SeriesHasSum q (PowerSeries.monomial n a) (a * q ^ n) := by
  unfold SeriesHasSum
  have h := hasSum_single (f := fun k : ℕ => PowerSeries.coeff k (PowerSeries.monomial n a) *
      q ^ k) n (fun k hk => by simp [PowerSeries.coeff_monomial, hk])
  simpa using h

private theorem seriesHasSum_C (q a : ℂ) : SeriesHasSum q (PowerSeries.C a) a := by
  simpa [PowerSeries.monomial_zero_eq_C_apply] using seriesHasSum_monomial q a 0

private theorem seriesHasSum_X_pow (q : ℂ) (n : ℕ) : SeriesHasSum q (T ^ n) (q ^ n) := by
  simpa [PowerSeries.X_pow_eq] using seriesHasSum_monomial q 1 n

private theorem SeriesHasSum.pow {q a : ℂ} {A : PowerSeries ℂ}
    (hA : SeriesHasSum q A a) (n : ℕ) : SeriesHasSum q (A ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using seriesHasSum_X_pow q 0
  | succ n ih => simpa only [pow_succ] using ih.mul hA

private theorem seriesHasSum_normalizedCharacter (τ : ℍ) :
    SeriesHasSum (𝕢 τ) normalizedCharacter (𝕢 τ * character τ) := by
  have hs := heckeSum_hasSum Nat.zero_lt_one τ
  rw [heckeSum_one, pow_one] at hs
  simp only [heckeCoeff_one] at hs
  have ha : SeriesHasSum (𝕢 τ) (PowerSeries.mk ActualLeechOrbifoldHeckeExpansion.coeff)
      (character τ - (𝕢 τ)⁻¹) := by
    unfold SeriesHasSum
    simp only [PowerSeries.coeff_mk]
    simpa only [Finset.sum_range_one, coeff_zero, zero_mul, add_zero] using
      (hasSum_nat_add_iff (f := fun k : ℕ => coeff k * 𝕢 τ ^ k) 1).mp hs
  have h := (seriesHasSum_X_pow (𝕢 τ) 0).add ((seriesHasSum_X_pow (𝕢 τ) 1).mul ha)
  simp only [pow_zero, pow_one] at h
  have hq : 𝕢 τ ≠ 0 := Function.Periodic.qParam_ne_zero (τ : ℂ)
  have he : 1 + 𝕢 τ * (character τ - (𝕢 τ)⁻¹) = 𝕢 τ * character τ := by
    rw [mul_sub, mul_inv_cancel₀ hq]
    ring
  rwa [he] at h

private def normalizedEval (G : PowerSeries ℂ) (P : Polynomial ℂ) (n : ℕ) : PowerSeries ℂ :=
  ∑ j ∈ Finset.range (n + 1), PowerSeries.C (P.coeff j) * T ^ (n - j) * G ^ j

private theorem ofPowerSeries_normalizedEval (G : PowerSeries ℂ) (P : Polynomial ℂ)
    (n : ℕ) (hP : P.natDegree ≤ n) :
    ι (normalizedEval G P n) = HahnSeries.single (n : ℤ) 1 * evaluate G P := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)]
  rw [normalizedEval, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [map_mul, map_pow (evaluate G), HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X_pow, show ∀ a : ℂ, evaluate G (C a) = HahnSeries.C a
      from fun a => Polynomial.eval₂_C _ _, show evaluate G X = withPole G
      from Polynomial.eval₂_X _ _, withPole_pow]
  rw [Int.ofNat_sub hjle, sub_eq_add_neg]
  have hsingle : (HahnSeries.single (n : ℤ) 1 : LaurentSeries ℂ) *
      HahnSeries.single (-(j : ℤ)) 1 = HahnSeries.single ((n : ℤ) + -(j : ℤ)) 1 := by
    rw [HahnSeries.single_mul_single, mul_one]
  rw [← hsingle]
  ac_rfl

private theorem seriesHasSum_normalizedEval {q z : ℂ} {G : PowerSeries ℂ}
    (hG : SeriesHasSum q G (q * z)) (P : Polynomial ℂ) (n : ℕ) (hP : P.natDegree ≤ n) :
    SeriesHasSum q (normalizedEval G P n) (q ^ n * P.eval z) := by
  rw [normalizedEval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
  unfold SeriesHasSum
  simp only [map_sum, Finset.sum_mul]
  apply hasSum_sum
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h := ((seriesHasSum_C q (P.coeff j)).mul (seriesHasSum_X_pow q (n - j))).mul (hG.pow j)
  change SeriesHasSum q _ _
  convert h using 1
  have hq : q ^ (n - j) * q ^ j = q ^ n := by rw [← pow_add, Nat.sub_add_cancel hjle]
  calc
    q ^ n * (P.coeff j * z ^ j) = (q ^ (n - j) * q ^ j) * (P.coeff j * z ^ j) := by rw [hq]
    _ = P.coeff j * q ^ (n - j) * (q * z) ^ j := by
      rw [mul_pow]
      ring

/-- The formal positive tail of the Faber evaluation, starting at (q^1). -/
def positivePart (n : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => ((faberPolynomial n).eval₂ HahnSeries.C characterLaurent).coeff
    ((k : ℤ) + 1)

private theorem normalizedEval_faberPolynomial (n : ℕ) :
    normalizedEval normalizedCharacter (faberPolynomial n) n = 1 + T ^ (n + 1) * positivePart n := by
  ext k
  have h := congrArg (fun A : LaurentSeries ℂ => A.coeff (k : ℤ))
    (ofPowerSeries_normalizedEval normalizedCharacter (faberPolynomial n) n
      (faberPolynomial_monic_degree n).2.le)
  simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_single_mul, one_mul] at h
  rw [h, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul']
  by_cases hk : k ≤ n
  · have he : (k : ℤ) - (n : ℤ) = -((n - k : ℕ) : ℤ) := by omega
    rw [he]
    change ((faberPolynomial n).eval₂ HahnSeries.C characterLaurent).coeff
      (-((n - k : ℕ) : ℤ)) = _
    rw [coeff_faberPolynomial_characterLaurent, ite_eq_right (by omega : ¬n + 1 ≤ k), add_zero]
    have heq : n - k = n ↔ k = 0 := by omega
    simp only [heq]
  · have he : (k : ℤ) - (n : ℤ) = ((k - (n + 1) : ℕ) : ℤ) + 1 := by omega
    rw [he, ite_eq_left (by omega : n + 1 ≤ k), ite_eq_right (by omega : k ≠ 0),
      zero_add, positivePart, PowerSeries.coeff_mk]
    rfl

private theorem seriesHasSum_positivePart (n : ℕ) (τ : ℍ) :
    SeriesHasSum (𝕢 τ) (positivePart n)
      (((faberPolynomial n).eval (character τ) - (𝕢 τ ^ n)⁻¹) / 𝕢 τ) := by
  let q := 𝕢 τ
  let z := (faberPolynomial n).eval (character τ)
  have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero (τ : ℂ)
  have h := seriesHasSum_normalizedEval (seriesHasSum_normalizedCharacter τ) (faberPolynomial n)
    n (faberPolynomial_monic_degree n).2.le
  rw [normalizedEval_faberPolynomial] at h
  change SeriesHasSum q _ (q ^ n * z) at h
  unfold SeriesHasSum at h ⊢
  apply (hasSum_mul_right_iff (pow_ne_zero (n + 1) hq)).mp
  have hfinite : (∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (1 + T ^ (n + 1) * positivePart n) * q ^ k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      have hlt := Finset.mem_range.mp hk
      simp [PowerSeries.coeff_one, PowerSeries.coeff_X_pow_mul', hk0, hlt.not_ge]
    · simp
  have hv : (z - (q ^ n)⁻¹) / q * q ^ (n + 1) + 1 = q ^ n * z := by
    rw [pow_succ, ← mul_assoc, mul_right_comm (_ / q), div_mul_cancel₀ _ hq,
      sub_mul, inv_mul_cancel₀ (pow_ne_zero n hq)]
    ring
  have htail : HasSum (fun k : ℕ => PowerSeries.coeff (k + (n + 1))
      (1 + T ^ (n + 1) * positivePart n) * q ^ (k + (n + 1)))
      ((z - (q ^ n)⁻¹) / q * q ^ (n + 1)) := by
    have hh := (hasSum_nat_add_iff (f := fun k : ℕ =>
      PowerSeries.coeff k (1 + T ^ (n + 1) * positivePart n) * q ^ k) (n + 1)
      (g := (z - (q ^ n)⁻¹) / q * q ^ (n + 1))).mpr
    rw [hfinite, hv] at hh
    exact hh h
  refine htail.congr_fun fun k => ?_
  change PowerSeries.coeff k (positivePart n) * q ^ k * q ^ (n + 1) =
    PowerSeries.coeff (k + (n + 1)) (1 + T ^ (n + 1) * positivePart n) * q ^ (k + (n + 1))
  rw [map_add, PowerSeries.coeff_one, ite_eq_right (by omega : k + (n + 1) ≠ 0),
    PowerSeries.coeff_X_pow_mul, zero_add, pow_add q k (n + 1), mul_assoc]

/-- The positive formal coefficients sum to the remainder of the analytic Faber evaluation. -/
theorem faberPolynomial_hasSum (n : ℕ) (τ : ℍ) :
    HasSum (fun k : ℕ => ((faberPolynomial n).eval₂ HahnSeries.C characterLaurent).coeff
      ((k : ℤ) + 1) * 𝕢 τ ^ (k + 1))
      ((faberPolynomial n).eval (character τ) - (𝕢 τ ^ n)⁻¹) := by
  have hq : 𝕢 τ ≠ 0 := Function.Periodic.qParam_ne_zero (τ : ℂ)
  have h := (HasSum.mul_right (𝕢 τ) (seriesHasSum_positivePart n τ))
  rw [div_mul_cancel₀ _ hq] at h
  refine h.congr_fun fun k => ?_
  simp only [positivePart, PowerSeries.coeff_mk, pow_succ, mul_assoc]

private theorem hasFPowerSeriesAt_of_half {c : ℕ → ℂ}
    (hs : Summable fun k => c k * ((1 / 2 : ℝ) : ℂ) ^ k) :
    HasFPowerSeriesAt (FormalMultilinearSeries.ofScalarsSum c)
      (FormalMultilinearSeries.ofScalars ℂ c) (0 : ℂ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ c
  have hr : (↑(1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hs.norm
  exact (p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num) hr)).hasFPowerSeriesAt

private theorem hasFPowerSeriesAt_positivePart (n : ℕ) :
    HasFPowerSeriesAt (FormalMultilinearSeries.ofScalarsSum fun k => PowerSeries.coeff k (positivePart n))
      (FormalMultilinearSeries.ofScalars ℂ fun k => PowerSeries.coeff k (positivePart n)) (0 : ℂ) := by
  apply hasFPowerSeriesAt_of_half
  let q : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hq : ‖q‖ < 1 := by norm_num [q]
  have hq0 : q ≠ 0 := by norm_num [q]
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0⟩
  have hτ : 𝕢 τ = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
  have hs := HasSum.summable (seriesHasSum_positivePart n τ)
  rwa [hτ] at hs

/-- The analytic remainder divided by `q` tends to the first positive formal coefficient. -/
theorem faberPolynomial_sub_pole_div_q_tendsto (n : ℕ) :
    Filter.Tendsto (fun τ : ℍ =>
      ((faberPolynomial n).eval (character τ) - (𝕢 τ ^ n)⁻¹) / 𝕢 τ)
      atImInfty (𝓝 (PowerSeries.coeff 0 (positivePart n))) := by
  have h := (hasFPowerSeriesAt_positivePart n).continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty (h := 1) one_pos)
  rw [FormalMultilinearSeries.ofScalarsSum_zero, smul_eq_mul, mul_one] at h
  refine h.congr fun τ => ?_
  rw [Function.comp_apply, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using HasSum.tsum_eq (seriesHasSum_positivePart n τ)

/-- The analytic remainder is of order at least one at the cusp. -/
theorem faberPolynomial_sub_pole_isBigO (n : ℕ) :
    Asymptotics.IsBigO atImInfty
      (fun τ : ℍ => (faberPolynomial n).eval (character τ) - (𝕢 τ ^ n)⁻¹)
      (fun τ : ℍ => 𝕢 τ) :=
  Asymptotics.isBigO_of_div_tendsto_nhds
    (Filter.Eventually.of_forall fun τ h => (Function.Periodic.qParam_ne_zero (τ : ℂ) h).elim)
    _ (faberPolynomial_sub_pole_div_q_tendsto n)

/-- After removal of the pole, the Faber evaluation vanishes at the cusp. -/
theorem faberPolynomial_sub_pole_isZeroAtImInfty (n : ℕ) :
    IsZeroAtImInfty (fun τ => (faberPolynomial n).eval (character τ) - (𝕢 τ ^ n)⁻¹) := by
  change Filter.Tendsto _ atImInfty (𝓝 0)
  have h := (faberPolynomial_sub_pole_div_q_tendsto n).mul
    (qParam_tendsto_atImInfty (h := 1) one_pos)
  simpa only [Pi.mul_apply, div_mul_cancel₀ _ (Function.Periodic.qParam_ne_zero _), mul_zero]
    using h

/-- Polynomial evaluation at the native character preserves level-one invariance. -/
theorem faberPolynomial_eval_smul (n : ℕ) (G : SL(2, ℤ)) (τ : ℍ) :
    (faberPolynomial n).eval (character (G • τ)) = (faberPolynomial n).eval (character τ) := by
  rw [← heckeSum_one, heckeSum_smul Nat.zero_lt_one]

/-- Polynomial evaluation at the native character is holomorphic on the upper half-plane. -/
theorem faberPolynomial_eval_mdifferentiable (n : ℕ) :
    MDiff (fun τ : ℍ => (faberPolynomial n).eval (character τ)) := by
  have hJ : MDiff character := heckeSum_one ▸ heckeSum_mdifferentiable Nat.zero_lt_one
  let F : ℕ → ℍ → ℂ := fun j τ => (faberPolynomial n).coeff j * character τ ^ j
  have he : (fun τ : ℍ => (faberPolynomial n).eval (character τ)) =
      ∑ j ∈ Finset.range ((faberPolynomial n).natDegree + 1), F j := by
    funext τ
    rw [Finset.sum_apply, Polynomial.eval_eq_sum_range]
  rw [he]
  exact MDifferentiable.sum fun j _ => mdifferentiable_const.mul (hJ.pow j)

/-- The Faber evaluation is the actual unnormalized Hecke sum. -/
theorem faberPolynomial_eval_eq_heckeSum {n : ℕ} (hn : 0 < n) (τ : ℍ) :
    (faberPolynomial n).eval (character τ) = heckeSum n τ := by
  let f : SlashInvariantForm 𝒮ℒ 0 :=
    { toFun := fun τ => (faberPolynomial n).eval (character τ)
      slash_action_eq' G hG := by
        rcases hG with ⟨G, rfl⟩
        funext τ
        change ((fun z : ℍ => (faberPolynomial n).eval (character z)) ∣[(0 : ℤ)] G) τ =
          (faberPolynomial n).eval (character τ)
        simpa only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
          using faberPolynomial_eval_smul n G τ }
  exact congrFun (eq_heckeSum_of_sub_pole_isZeroAtImInfty hn f
    (faberPolynomial_eval_mdifferentiable n) (faberPolynomial_sub_pole_isZeroAtImInfty n)) τ

/-- The entire formal Faber evaluation has the coefficients of the actual
unnormalized Hecke expansion. -/
theorem faberPolynomial_eval₂_characterLaurent_eq_hecke {n : ℕ} (hn : 0 < n) :
    (faberPolynomial n).eval₂ HahnSeries.C characterLaurent =
      HahnSeries.single (-(n : ℤ)) 1 + ι (PowerSeries.mk (heckeCoeff n)) := by
  let A := (faberPolynomial n).eval₂ HahnSeries.C characterLaurent
  let f : ℕ → ℂ := fun m => if m = 0 then 0 else A.coeff (m : ℤ)
  let g := heckeCoeff n
  have hsum (q : ℂ) (hq : ‖q‖ < 1) :
      ∃ z, HasSum (fun m : ℕ => f m * q ^ m) z ∧ HasSum (fun m : ℕ => g m * q ^ m) z := by
    by_cases hq0 : q = 0
    · subst q
      have hf (m : ℕ) : f m * (0 : ℂ) ^ m = 0 := by cases m <;> simp [f]
      have hg (m : ℕ) : g m * (0 : ℂ) ^ m = 0 := by
        cases m <;> simp [g, heckeCoeff_zero]
      exact ⟨0, by simpa only [hf] using hasSum_zero, by simpa only [hg] using hasSum_zero⟩
    · let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
        Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0⟩
      have hτ : 𝕢 τ = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
      have hf := faberPolynomial_hasSum n τ
      rw [faberPolynomial_eval_eq_heckeSum hn, hτ] at hf
      have hg := heckeSum_hasSum hn τ
      rw [hτ] at hg
      refine ⟨heckeSum n τ - (q ^ n)⁻¹, ?_, ?_⟩
      · simpa [Finset.sum_range_one, f] using
          (hasSum_nat_add_iff (f := fun m : ℕ => f m * q ^ m) 1).mp
            (by simpa [f, A] using hf)
      · simpa only [Finset.sum_range_one, g, heckeCoeff_zero,
          zero_mul, add_zero] using
          (hasSum_nat_add_iff (f := fun m : ℕ => g m * q ^ m) 1).mp hg
  obtain ⟨_, hf, hg⟩ := hsum ((1 / 2 : ℝ) : ℂ) (by norm_num)
  have hfg : FormalMultilinearSeries.ofScalars ℂ f = FormalMultilinearSeries.ofScalars ℂ g := by
    apply (hasFPowerSeriesAt_of_half hf.summable).eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesAt_of_half hg.summable)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    obtain ⟨_, hqf, hqg⟩ := hsum q (by simpa [Metric.mem_ball, dist_zero_right] using hq)
    rw [FormalMultilinearSeries.ofScalars_sum_eq, FormalMultilinearSeries.ofScalars_sum_eq]
    simpa only [smul_eq_mul] using hqf.tsum_eq.trans hqg.tsum_eq.symm
  have hcoeff (m : ℕ) : f m = g m := by
    have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p m (fun _ => 1)) hfg
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] using h
  apply HahnSeries.ext
  funext k
  rw [HahnSeries.coeff_add]
  by_cases hk : k ≤ 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [coeff_faberPolynomial_characterLaurent, HahnSeries.coeff_single]
    cases m with
    | zero =>
      have h0 : (ι (PowerSeries.mk (heckeCoeff n))).coeff 0 = 0 := by
        change (ι (PowerSeries.mk (heckeCoeff n))).coeff (↑(0 : ℕ)) = 0
        rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, heckeCoeff_zero]
      simp [show (0 : ℕ) ≠ n from Nat.ne_of_lt hn, h0, show (0 : ℤ) ≠ -(n : ℤ) by omega]
    | succ m =>
      rw [coeff_ofPowerSeries_of_neg _ (by omega), add_zero]
      have he : (-(↑(m + 1) : ℤ) = -(n : ℤ)) ↔ m + 1 = n := by omega
      simp only [he]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    have hm : m ≠ 0 := by omega
    rw [HahnSeries.coeff_single_of_ne (by omega : (m : ℤ) ≠ -(n : ℤ)), zero_add,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]
    simpa [f, g, A, hm] using hcoeff m

end D5.S3.VertexAlgebra.ActualLeechOrbifoldFaberPolynomial

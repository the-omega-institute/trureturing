/- GID: D5/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude
   generality: I
   mirror-B: D5/B/S3/Analytic/AlgebraicSeries/HannaA3958Infinitude
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All four Hanna negative-coefficient sequences have infinite defined domains. -/

/-
proof_shape: bind-only for every theorem; definitions introduce the displayed source objects.
escape_witness: none
admission_basis: open-problem-resolution (#21728, #21729, #21730, #21731; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22312
Direct frozen dependencies (declaration identities at the merged dev base):
  F1: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed
    sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981
  F2: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree
    sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34
  F3: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_X
    sha256:cb4bbeb74f9bb4de6a237dc609532d94ac61147a4a3cd321ca192132b9b26215
  F4: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_mul
    sha256:b4802ea85bb0964fd0f4727040613a738a00c26e68db4c758612d114939c9e3a
  F5: D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_pow
    sha256:0c9456bb3300b1f38308df2b3a2abc2d51d68b3b05356990e7bc5cfc4bfb0dbb
  F6: D5/S3/Weil/Probability/CanonicalLiNonnegativeConverse.nonnegative_series_positive_boundary_obstruction
    sha256:9a33ee5a16dd0faa27fa323c6aff6a578666e345064587d6fabe79d7ba22cbbb
Public settling theorems (proof_shape; escape_witness; direct frozen dependencies):
  A395835.result: bind-only; none; F1, F2, F3, F5, F4, F6.
  A395836.result836: bind-only; none; F1, F2, F3, F5, F4, F6.
  A395837.result837: bind-only; none; F1, F2, F3, F5, F4, F6.
  A395838.result838: bind-only; none; F1, F2, F3, F5, F4, F6.
The four infinitude claims follow from uniform negative-coefficient existence.
IsLeast appears directly in the source predicates; no first-negative alias is introduced.
All analytic helpers and settling results share this module; no separate escape witness is asserted.
Private theorem consumers (all proof_shape: bind-only; escape_witness: none):
  Inverse.power_bound -> Inverse.equation_bounds.
  Inverse.equation_bounds -> Boundary.finite_boundary_obstruction, Global.radius_le_one.
  Inverse.boundary_numerator_pos -> Inverse.boundary_deriv_ne_zero.
  Inverse.phi_analytic -> Inverse.boundary_inverse, Inverse.q_analytic, Inverse.zero_germ.
  Inverse.q_analytic -> Inverse.boundary_inverse, Inverse.zero_germ.
  Inverse.phi_hasDerivAt -> Inverse.q_hasDerivAt.
  Inverse.q_hasDerivAt -> Inverse.boundary_deriv_ne_zero, Inverse.zero_germ.
  Inverse.zero_germ -> Assembly.convergent_germ.
  Inverse.boundary_deriv_ne_zero -> Inverse.boundary_inverse.
  Inverse.boundary_inverse -> Boundary.finite_boundary_obstruction.
  Inverse.step_constant -> Inverse.constant_eq_one, Inverse.series_exists_unique.
  Inverse.step_contract -> Inverse.series_exists_unique.
  Inverse.series_exists_unique -> Global.common_result, Assembly.germ_coefficients.
  Inverse.constant_eq_one -> Inverse.firstNegative_pos, Global.radius_le_one, Global.has_negative.
  Inverse.firstNegative_pos -> Inverse.result837_of_common.
  Inverse.firstNegative_of_negative -> Inverse.common_of_all.
  Inverse.common_of_all -> Global.common_result.
  Inverse.all_defined_of_common -> Inverse.result838_of_common.
  Inverse.result835_of_common -> A395835.result.
  Inverse.result836_of_common -> A395836.result836.
  Inverse.result837_of_common -> A395837.result837.
  Inverse.result838_of_common -> A395838.result838.
  Taylor.series_congr -> Assembly.taylor_equation.
  Taylor.series_const -> Assembly.taylor_equation, Taylor.series_pow.
  Taylor.series_id -> Assembly.taylor_equation.
  Taylor.series_add -> Assembly.taylor_equation.
  Taylor.series_sub -> Assembly.taylor_equation.
  Taylor.series_mul -> Assembly.taylor_equation, Taylor.series_pow.
  Taylor.series_pow -> Assembly.taylor_equation.
  Boundary.scalar_real -> Global.real_equation_inside, Boundary.finite_boundary_obstruction.
  Boundary.scalarSeries_sum -> Global.scalar_equation_on_disk.
  Boundary.real_summable -> Boundary.finite_boundary_obstruction, Global.radius_le_one.
  Boundary.realSum_ge_one -> Boundary.finite_boundary_obstruction, Global.radius_le_one.
  Boundary.finite_boundary_obstruction -> Global.has_negative.
  Assembly.mapped_equation -> Assembly.germ_coefficients.
  Assembly.taylor_equation -> Assembly.germ_coefficients.
  Assembly.germ_coefficients -> Assembly.convergent_germ.
  Assembly.convergent_germ -> Global.scalar_equation_on_disk.
  Global.scalar_equation_on_disk -> Global.real_equation_inside, Global.has_negative.
  Global.real_equation_inside -> Global.radius_le_one, Global.has_negative.
  Global.radius_le_one -> Global.has_negative.
  Global.has_negative -> Global.common_result.
  Global.common_result -> A395836.result836, A395837.result837, A395835.result, A395838.result838.

-/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse

/-!
Hanna's algebraic formal series has a negative coefficient for every parameter at least two.
The four index and coefficient readouts consequently have infinite defined domains.
-/
namespace D5.S3.Analytic.AlgebraicSeries.HannaA3958Infinitude
noncomputable section

set_option autoImplicit false
open Filter Set
open scoped Topology
namespace Inverse

private def phi (n : ℕ) (t : ℂ) : ℂ := 1 + t - t ^ n

private def q (n : ℕ) (t : ℂ) : ℂ := t / (phi n t) ^ 2

private theorem power_bound (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (hpow : t ^ n ≤ t) : t ≤ 1 := by
  exact le_of_not_gt (fun ht => (lt_self_pow₀ (a := t) (m := n) ht (by omega)).not_ge hpow)

private theorem equation_bounds (n : ℕ) (hn : 2 ≤ n) (x f : ℝ)
    (hx : 0 < x) (hf : 1 ≤ f)
    (heq : f = 1 + x * f ^ 2 - x ^ n * f ^ (2 * n)) :
    0 < x * f ^ 2 ∧ x ≤ x * f ^ 2 ∧ x * f ^ 2 ≤ 1 ∧ f ≤ 2 := by
  have hfp : 0 < f := lt_of_lt_of_le zero_lt_one hf
  have ht : 0 < x * f ^ 2 := mul_pos hx (sq_pos_of_pos hfp)
  have hp : (x * f ^ 2) ^ n = x ^ n * f ^ (2 * n) := by
    rw [mul_pow, ← pow_mul]
  have htn : (x * f ^ 2) ^ n ≤ x * f ^ 2 := by rw [hp]; linarith
  have ht1 := power_bound n hn (x * f ^ 2) htn
  have hpn : 0 ≤ x ^ n * f ^ (2 * n) := by positivity
  have hf2 : 1 ≤ f ^ 2 := by exact one_le_pow₀ hf
  refine ⟨ht, ?_, ht1, ?_⟩
  · nlinarith
  · linarith

private theorem boundary_numerator_pos (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < 1 - t + (2 * (n : ℝ) - 1) * t ^ n := by
  have hn' : (2 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hp : 0 < (2 * (n : ℝ) - 1) * t ^ n :=
    mul_pos (by linarith) (pow_pos ht n)
  linarith

private theorem phi_analytic (n : ℕ) (t : ℂ) : AnalyticAt ℂ (phi n) t := by
  exact ((analyticAt_const.add analyticAt_id).sub (analyticAt_id.pow n))

private theorem q_analytic (n : ℕ) (t : ℂ) (ht : phi n t ≠ 0) :
    AnalyticAt ℂ (q n) t := by
  exact analyticAt_id.div ((phi_analytic n t).pow 2) (pow_ne_zero 2 ht)

private theorem phi_hasDerivAt (n : ℕ) (t : ℂ) :
    HasDerivAt (phi n) (1 - (n : ℂ) * t ^ (n - 1)) t := by
  simpa only [zero_add, mul_one] using!
    ((hasDerivAt_const t (1 : ℂ)).add (hasDerivAt_id t)).sub ((hasDerivAt_id t).pow n)

private theorem q_hasDerivAt (n : ℕ) (hn : 1 ≤ n) (t : ℂ) (ht : phi n t ≠ 0) :
    HasDerivAt (q n) ((1 - t + (2 * (n : ℂ) - 1) * t ^ n) / (phi n t) ^ 3) t := by
  have hpow : t ^ (n - 1) * t = t ^ n := by
    simpa only [pow_one] using pow_sub_mul_pow t hn
  have hnum : phi n t - 2 * t * (1 - (n : ℂ) * t ^ (n - 1)) =
      1 - t + (2 * (n : ℂ) - 1) * t ^ n := by
    dsimp only [phi]
    linear_combination 2 * (n : ℂ) * hpow
  have hd := (hasDerivAt_id t).div ((phi_hasDerivAt n t).pow 2) (pow_ne_zero 2 ht)
  change HasDerivAt (id / phi n ^ 2) _ t
  convert hd using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [← hnum]
  field_simp [ht]


private theorem zero_germ (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0 = 1 ∧
      ∀ᶠ x in 𝓝 (0 : ℂ), f x = 1 + x * f x ^ 2 - x ^ n * f x ^ (2 * n) := by
  have hn0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have hphi0 : phi n 0 = 1 := by simp [phi, hn0]
  have hq0 : q n 0 = 0 := by simp [q]
  have hqa := q_analytic n 0 (by rw [hphi0]; exact one_ne_zero)
  have hqd : deriv (q n) 0 = 1 := by
    simpa [hphi0, hn0] using (q_hasDerivAt n hn 0 (by rw [hphi0]; exact one_ne_zero)).deriv
  have hqd0 : deriv (q n) 0 ≠ 0 := by exact ne_zero_of_eq_one hqd
  let T := hqa.hasStrictDerivAt.localInverse _ _ _ hqd0
  have hTa : AnalyticAt ℂ T 0 := by
    simpa only [hq0] using hqa.analyticAt_localInverse hqd0
  have hT0 : T 0 = 0 := by
    have h : T (q n 0) = 0 := HasStrictFDerivAt.localInverse_apply_image ..
    simpa only [hq0] using h
  let f := fun x => phi n (T x)
  have hfa : AnalyticAt ℂ f 0 := (phi_analytic n (T 0)).comp hTa
  have hf0 : f 0 = 1 := by dsimp [f]; rw [hT0, hphi0]
  refine ⟨f, hfa, hf0, ?_⟩
  have hinv : ∀ᶠ x in 𝓝 (0 : ℂ), q n (T x) = x := by
    simpa only [hq0] using hqa.hasStrictDerivAt.eventually_right_inverse hqd0
  have hnz : ∀ᶠ x in 𝓝 (0 : ℂ), f x ≠ 0 :=
    hfa.continuousAt.eventually_ne (by rw [hf0]; exact one_ne_zero)
  filter_upwards [hinv, hnz] with x hx hx0
  have htx : T x = x * f x ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hx0)).mp
    exact hx
  have hpow : (x * f x ^ 2) ^ n = x ^ n * f x ^ (2 * n) := by
    rw [mul_pow, ← pow_mul]
  change phi n (T x) = _
  conv_lhs => rw [phi, htx]
  rw [hpow]

private theorem boundary_deriv_ne_zero (n : ℕ) (hn : 2 ≤ n) (t L : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hL : 1 ≤ L)
    (hphi : phi n (t : ℂ) = (L : ℂ)) : deriv (q n) (t : ℂ) ≠ 0 := by
  have hL0 : L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hL)
  have hLc : (L : ℂ) ≠ 0 := by exact Complex.ofReal_ne_zero.mpr hL0
  have hphi0 : phi n (t : ℂ) ≠ 0 := by exact Ne.symm (ne_of_ne_of_eq (id (Ne.symm hLc)) (id (Eq.symm hphi)))
  rw [(q_hasDerivAt n (by omega) (t : ℂ) hphi0).deriv, hphi]
  have hposq : 0 < (1 - t + (2 * (n : ℝ) - 1) * t ^ n) / L ^ 3 :=
    div_pos (boundary_numerator_pos n hn t ht ht1)
      (pow_pos (lt_of_lt_of_le zero_lt_one hL) 3)
  have heq : (1 - (t : ℂ) + (2 * (n : ℂ) - 1) * (t : ℂ) ^ n) / (L : ℂ) ^ 3 =
      (((1 - t + (2 * (n : ℝ) - 1) * t ^ n) / L ^ 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq]
  exact_mod_cast ne_of_gt hposq


private theorem boundary_inverse (n : ℕ) (hn : 2 ≤ n) (t L R : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hL : 1 ≤ L)
    (hphi : phi n (t : ℂ) = (L : ℂ)) (hq : q n (t : ℂ) = (R : ℂ))
    (T : ℝ → ℂ) (hT : Tendsto T (𝓝[<] R) (𝓝 (t : ℂ)))
    (hrel : ∀ᶠ x : ℝ in 𝓝[<] R, q n (T x) = (x : ℂ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (R : ℂ) ∧
      ∀ᶠ x : ℝ in 𝓝[<] R, g (x : ℂ) = phi n (T x) := by
  have hLc : (L : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hL)
  have hqa := q_analytic n (t : ℂ) (by rw [hphi]; exact hLc)
  have hqd := boundary_deriv_ne_zero n hn t L ht ht1 hL hphi
  let H := hqa.hasStrictDerivAt.localInverse _ _ _ hqd
  have hHa : AnalyticAt ℂ H (R : ℂ) := by
    simpa only [hq] using hqa.analyticAt_localInverse hqd
  refine ⟨fun z => phi n (H z), (phi_analytic n (H (R : ℂ))).comp hHa, ?_⟩
  have hleft : ∀ᶠ z in 𝓝 (t : ℂ), H (q n z) = z :=
    hqa.hasStrictDerivAt.eventually_left_inverse hqd
  filter_upwards [hT.eventually hleft, hrel] with x hx hrelx
  rw [hrelx] at hx
  exact congrArg (phi n) hx

end Inverse


namespace Shared

/-- The OEIS equation; every power is ordinary multiplication of formal series. -/
def SeriesEquation (n : ℕ) (F : PowerSeries ℤ) : Prop :=
  F = 1 + PowerSeries.X * F ^ 2 - PowerSeries.X ^ n * F ^ (2 * n)

/-- The source stops at the first undefined parameter: all earlier terms must exist. -/
def DefinedThrough (N : ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ N →
    ∃ F : PowerSeries ℤ, SeriesEquation n F ∧
      ∃ M : ℕ, (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M)

/-- Infinite length of the source sequence, not infinitely many distinct values. -/
private def commonClaim : Prop :=
  Set.Infinite {N : ℕ | 2 ≤ N ∧ DefinedThrough N}

end Shared

namespace A395835

/-- A395835(n)=M(n), provided the whole source prefix exists. -/
def Term835 (n : ℕ) (a : ℤ) : Prop :=
  2 ≤ n ∧ Shared.DefinedThrough n ∧
    ∃ (F : PowerSeries ℤ) (M : ℕ), Shared.SeriesEquation n F ∧
      (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M) ∧ a = (M : ℤ)

def claim : Prop :=
  Set.Infinite {n : ℕ | ∃ a : ℤ, Term835 n a}

end A395835

namespace A395836

/-- A395836(n) is the absolute value of the first negative coefficient. -/
def Term836 (n : ℕ) (a : ℤ) : Prop :=
  2 ≤ n ∧ Shared.DefinedThrough n ∧
    ∃ (F : PowerSeries ℤ) (M : ℕ), Shared.SeriesEquation n F ∧
      (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M) ∧ a = |PowerSeries.coeff M F|

def claim836 : Prop :=
  Set.Infinite {n : ℕ | ∃ a : ℤ, Term836 n a}

end A395836

namespace A395837

/-- A395837(n) is the coefficient immediately before the first negative one. -/
def Term837 (n : ℕ) (a : ℤ) : Prop :=
  2 ≤ n ∧ Shared.DefinedThrough n ∧
    ∃ (F : PowerSeries ℤ) (M : ℕ), Shared.SeriesEquation n F ∧
      (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M) ∧ a = PowerSeries.coeff (M - 1) F

def claim837 : Prop :=
  Set.Infinite {n : ℕ | ∃ a : ℤ, Term837 n a}

end A395837

namespace A395838

/-- The mathematical first differences M(n+1)-M(n).
The published table prepends M(2) and shifts this tail by one index. -/
def Term838 (n : ℕ) (a : ℤ) : Prop :=
  2 ≤ n ∧ Shared.DefinedThrough (n + 1) ∧
    ∃ (F G : PowerSeries ℤ) (M N : ℕ),
      Shared.SeriesEquation n F ∧ (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M) ∧
      Shared.SeriesEquation (n + 1) G ∧ (IsLeast {m : ℕ | PowerSeries.coeff m G < 0} N) ∧
      a = (N : ℤ) - (M : ℤ)

def claim838 : Prop :=
  Set.Infinite {n : ℕ | ∃ a : ℤ, Term838 n a}

end A395838

set_option autoImplicit false
open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
namespace Inverse
variable {R : Type*} [CommRing R]

private def step (n : ℕ) (F : PowerSeries R) : PowerSeries R :=
  1 + X * F ^ 2 - X ^ n * F ^ (2 * n)

private theorem step_constant (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries R) :
    constantCoeff (step n F) = 1 := by
  simp [step, show n ≠ 0 from Nat.ne_zero_of_lt hn]

private theorem step_contract (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (F G : PowerSeries R) (h : Agree d F G) :
    Agree (d + 1) (step n F) (step n G) := by
  have h1 := agree_X (agree_pow h 2)
  have h2 := agree_X (agree_mul
    (show Agree d ((X : PowerSeries R) ^ (n - 1)) (X ^ (n - 1)) from fun _ _ => rfl)
    (agree_pow h (2 * n)))
  have he (H : PowerSeries R) : X * (X ^ (n - 1) * H ^ (2 * n)) = X ^ n * H ^ (2 * n) := by
    rw [← mul_assoc]
    exact congrArg (fun u : PowerSeries R => u * H ^ (2 * n))
      (by simpa only [pow_one] using pow_mul_pow_sub (X : PowerSeries R) hn)
  intro k hk
  simpa only [step, he, map_sub, map_add] using
    congrArg₂ (fun a b : R => coeff k (1 : PowerSeries R) + a - b) (h1 k hk) (h2 k hk)

private theorem series_exists_unique (n : ℕ) (hn : 1 ≤ n) :
    ∃! F : PowerSeries R, F = 1 + X * F ^ 2 - X ^ n * F ^ (2 * n) := by
  obtain ⟨F, hF0, hF, huniq⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed (R := R)
      (step n) (fun _ _ => step_constant n hn _)
      (by intro d f g hd hf hg h; exact step_contract n hn d f g h)
  refine ⟨F, hF, ?_⟩
  intro G hG
  apply huniq G _ hG
  rw [hG]
  exact step_constant n hn G

private theorem constant_eq_one (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) : coeff 0 F = 1 := by
  change F = step n F at hF
  rw [coeff_zero_eq_constantCoeff, hF]
  exact step_constant n hn F

private theorem firstNegative_pos (n : ℕ) (hn : 2 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) (M : ℕ) (hM : (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M)) :
    0 < M := by
  have hc := constant_eq_one n (by omega) F hF
  have hneg : coeff M F < 0 := hM.1
  by_contra! h
  have : M = 0 := by exact Nat.eq_zero_of_le_zero h
  simp [this, hc] at hneg


private theorem firstNegative_of_negative (F : PowerSeries ℤ) (h : ∃ m, coeff m F < 0) :
    ∃ M, (IsLeast {m : ℕ | PowerSeries.coeff m F < 0} M) := by
  exact ⟨Nat.find h, Nat.isLeast_find h⟩

private theorem common_of_all (hall : ∀ n : ℕ, 2 ≤ n →
    ∃ F : PowerSeries ℤ, Shared.SeriesEquation n F ∧
      ∃ m : ℕ, coeff m F < 0) : Shared.commonClaim := by
  apply (Set.Ici_infinite (2 : ℕ)).mono
  intro N hN
  refine ⟨hN, fun n hn _ => ?_⟩
  obtain ⟨F, hF, hneg⟩ := hall n hn
  exact ⟨F, hF, firstNegative_of_negative F hneg⟩

private theorem all_defined_of_common (h : Shared.commonClaim) :
    ∀ N : ℕ, Shared.DefinedThrough N := by
  intro N n hn hnN
  obtain ⟨K, hK, hNK⟩ := h.exists_gt N
  exact hK.2 n hn (by omega)

private theorem result835_of_common (h : Shared.commonClaim) : A395835.claim := by
  apply h.mono
  intro n hn
  obtain ⟨F, hF, M, hM⟩ := hn.2 n hn.1 le_rfl
  exact ⟨(M : ℤ), hn.1, hn.2, F, M, hF, hM, rfl⟩

private theorem result836_of_common (h : Shared.commonClaim) : A395836.claim836 := by
  apply h.mono
  intro n hn
  obtain ⟨F, hF, M, hM⟩ := hn.2 n hn.1 le_rfl
  exact ⟨|coeff M F|, hn.1, hn.2, F, M, hF, hM, rfl⟩

private theorem result837_of_common (h : Shared.commonClaim) : A395837.claim837 := by
  apply h.mono
  intro n hn
  obtain ⟨F, hF, M, hM⟩ := hn.2 n hn.1 le_rfl
  have hMp := firstNegative_pos n hn.1 F hF M hM
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hMp)
  subst M
  refine ⟨coeff k F, hn.1, hn.2, F, k + 1, hF, hM, ?_⟩
  simp

private theorem result838_of_common (h : Shared.commonClaim) : A395838.claim838 := by
  apply (Set.Ici_infinite (2 : ℕ)).mono
  intro n hn
  have hall := all_defined_of_common h (n + 1)
  obtain ⟨F, hF, M, hM⟩ := hall n hn (by omega)
  obtain ⟨G, hG, N, hN⟩ := hall (n + 1) (Nat.le_trans hn (Nat.le_succ n)) le_rfl
  exact ⟨(N : ℤ) - M, hn, hall, F, G, M, N, hF, hM, hG, hN, rfl⟩

end Inverse


set_option autoImplicit false
open scoped BigOperators Topology
open PowerSeries
namespace Taylor

private def series (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))

private theorem series_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : series f = series g := by
  ext n
  simp only [series, coeff_mk]
  rw [h.iteratedDeriv_eq n]

private theorem series_const (c : ℂ) : series (fun _ => c) = C c := by
  ext n
  cases n with
  | zero => simp [series]
  | succ n => simp [series, iteratedDeriv_const]

private theorem series_id : series (fun z : ℂ => z) = X := by
  ext n
  simp only [series, coeff_mk, iteratedDeriv_fun_id_zero, coeff_X]
  split_ifs with h
  · subst n; simp
  · simp

private theorem series_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series (f + g) = series f + series g := by
  ext n
  simp only [series, coeff_mk, map_add, iteratedDeriv_add hf.contDiffAt hg.contDiffAt, add_div]

private theorem series_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series (f - g) = series f - series g := by
  ext n
  simp only [series, coeff_mk, map_sub, iteratedDeriv_sub hf.contDiffAt hg.contDiffAt, sub_div]

private theorem series_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    series (f * g) = series f * series g := by
  ext n
  simp only [series, coeff_mk, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hfact : (n.choose k : ℂ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hnk : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
  field_simp
  linear_combination (iteratedDeriv k f 0 * iteratedDeriv (n - k) g 0) * hfact

private theorem series_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) :
  series (f ^ k) = series f ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    change series (fun _ : ℂ => 1) = 1
    simpa only [map_one] using series_const (1 : ℂ)
  | succ k ih =>
    rw [pow_succ, series_mul (hf.pow k) hf, ih, pow_succ]

end Taylor


set_option autoImplicit false
open Filter Set FormalMultilinearSeries Inverse
open scoped Topology NNReal ENNReal BigOperators
open D5.S3.Weil.Probability.CanonicalLiNonnegativeConverse
namespace Boundary




private theorem scalar_real (a : ℕ → ℝ) (x : ℝ) :
    (fun z : ℂ => ∑' m, (a m : ℂ) * z ^ m) (x : ℂ) = (((fun x : ℝ => ∑' m, a m * x ^ m) x : ℝ) : ℂ) := by
  simp only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow]

private theorem scalarSeries_sum (a : ℕ → ℝ) : ((FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))).sum = (fun z : ℂ => ∑' m, (a m : ℂ) * z ^ m) := by
  simpa only [FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := ℂ) (fun m => (a m : ℂ)))

private theorem real_summable (a : ℕ → ℝ) (x : ℝ≥0)
    (hx : (x : ℝ≥0∞) < ((FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))).radius) :
    Summable (fun m => a m * (x : ℝ) ^ m) := by
  have hmem : (x : ℂ) ∈ Metric.eball 0 ((FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))).radius := by
    simpa [mem_eball_zero_iff, enorm, Complex.nnnorm_real] using hx
  have hs := ((FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))).summable hmem
  apply Complex.summable_ofReal.mp
  simpa [ofScalars_apply_eq, smul_eq_mul, mul_comm] using hs

private theorem realSum_ge_one (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (ha0 : a 0 = 1)
    (x : ℝ) (hx : 0 ≤ x) (hs : Summable (fun m => a m * x ^ m)) :
    1 ≤ (fun x : ℝ => ∑' m, a m * x ^ m) x := by
  simpa only [ha0, pow_zero, mul_one] using
    hs.le_tsum 0 (fun m _ => mul_nonneg (ha m) (pow_nonneg hx m))

private theorem finite_boundary_obstruction (n : ℕ) (hn : 2 ≤ n)
    (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (ha0 : a 0 = 1)
    (R : ℝ≥0) (hR : 0 < R) (hrad : ((FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))).radius = (R : ℝ≥0∞))
    (hpoly : ∀ x : ℝ, 0 < x → x < R →
      (fun x : ℝ => ∑' m, a m * x ^ m) x = 1 + x * (fun x : ℝ => ∑' m, a m * x ^ m) x ^ 2 - x ^ n * (fun x : ℝ => ∑' m, a m * x ^ m) x ^ (2 * n)) : False := by
  let s := (fun x : ℝ => ∑' m, a m * x ^ m)
  have hRr : (0 : ℝ) < R := hR
  have hsumm (x : ℝ) (hx : 0 ≤ x) (hxR : x < R) : Summable (fun m => a m * x ^ m) := by
    apply real_summable a ⟨x, hx⟩
    rw [hrad]
    exact ENNReal.coe_lt_coe.mpr hxR
  have hsb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) R) :
      1 ≤ s x ∧ s x ≤ 2 ∧ 0 < x * s x ^ 2 ∧ x * s x ^ 2 ≤ 1 := by
    have hs1 := realSum_ge_one a ha ha0 x hx.1.le (hsumm x hx.1.le hx.2)
    have hb := equation_bounds n hn x (s x) hx.1 hs1 (hpoly x hx.1 hx.2)
    exact ⟨hs1, hb.2.2.2, hb.1, hb.2.2.1⟩
  have hmono : MonotoneOn s (Ioo (0 : ℝ) R) := by
    intro x hx y hy hxy
    apply (hsumm x hx.1.le hx.2).tsum_le_tsum _ (hsumm y hy.1.le hy.2)
    intro m
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hxy m) (ha m)
  have hne : (Ioo (0 : ℝ) R).Nonempty := nonempty_Ioo.mpr hRr
  have hbd : BddAbove (s '' Ioo (0 : ℝ) R) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hsb x hx).2.1
  let L := sSup (s '' Ioo (0 : ℝ) R)
  have hlim : Tendsto s (𝓝[<] (R : ℝ)) (𝓝 L) :=
    MonotoneOn.tendsto_nhdsWithin_Ioo_left hne hmono hbd
  have hL1 : 1 ≤ L := by
    obtain ⟨x, hx⟩ := hne
    exact (hsb x hx).1.trans (le_csSup hbd (mem_image_of_mem s hx))
  let t : ℝ := R * L ^ 2
  have htp : 0 < t := mul_pos hRr (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hL1))
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] (R : ℝ)) (𝓝 (R : ℝ)) :=
    continuousAt_id.continuousWithinAt
  have htlim : Tendsto (fun x : ℝ => x * s x ^ 2) (𝓝[<] (R : ℝ)) (𝓝 t) :=
    hid.mul (hlim.pow 2)
  have ht1 : t ≤ 1 := le_of_tendsto htlim (by
    filter_upwards [Ioo_mem_nhdsLT hRr] with x hx
    exact (hsb x hx).2.2.2)
  have hpolyLim : L = 1 + (R : ℝ) * L ^ 2 - (R : ℝ) ^ n * L ^ (2 * n) := by
    apply tendsto_nhds_unique hlim
    exact ((tendsto_const_nhds.add (hid.mul (hlim.pow 2))).sub
      ((hid.pow n).mul (hlim.pow (2 * n)))).congr' (by
        filter_upwards [Ioo_mem_nhdsLT hRr] with x hx
        exact (hpoly x hx.1 hx.2).symm)
  have hphi : phi n (t : ℂ) = (L : ℂ) := by
    have hpow : t ^ n = (R : ℝ) ^ n * L ^ (2 * n) := by
      dsimp only [t]
      rw [mul_pow, ← pow_mul]
    have heq : 1 + t - t ^ n = L := by rw [hpow]; exact hpolyLim.symm
    change 1 + (t : ℂ) - (t : ℂ) ^ n = (L : ℂ)
    exact_mod_cast heq
  have hL0 : L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hL1)
  have hq : q n (t : ℂ) = (R : ℂ) := by
    rw [q, hphi]
    change (((R : ℝ) * L ^ 2 : ℝ) : ℂ) / (L : ℂ) ^ 2 = (R : ℂ)
    push_cast
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (by exact_mod_cast hL0))
  let T := fun x : ℝ => ((x * s x ^ 2 : ℝ) : ℂ)
  have hTlim : Tendsto T (𝓝[<] (R : ℝ)) (𝓝 (t : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htlim
  have hphiT (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) R) : phi n (T x) = ((s x : ℝ) : ℂ) := by
    have hpow : (x * s x ^ 2) ^ n = x ^ n * s x ^ (2 * n) := by rw [mul_pow, ← pow_mul]
    have heq : 1 + x * s x ^ 2 - (x * s x ^ 2) ^ n = s x := by
      rw [hpow]; exact (hpoly x hx.1 hx.2).symm
    dsimp only [phi, T]
    exact_mod_cast heq
  have hrel : ∀ᶠ x : ℝ in 𝓝[<] (R : ℝ), q n (T x) = (x : ℂ) := by
    filter_upwards [Ioo_mem_nhdsLT hRr] with x hx
    have hs0 : s x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hsb x hx).1)
    rw [q, hphiT x hx]
    dsimp only [T]
    push_cast
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (by exact_mod_cast hs0))
  obtain ⟨g, hga, hgeq⟩ := boundary_inverse n hn t L R htp ht1 hL1 hphi hq T hTlim hrel
  have hevent : ∀ᶠ x : ℝ in 𝓝[<] (R : ℝ), g (x : ℂ) = (fun z : ℂ => ∑' m, (a m : ℂ) * z ^ m) (x : ℂ) := by
    filter_upwards [hgeq, Ioo_mem_nhdsLT hRr] with x hx hxi
    rw [hx, hphiT x hxi]
    exact (scalar_real a x).symm
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  apply nonnegative_series_positive_boundary_obstruction a ha R hR hrad g hga
  refine ⟨ε, hε, ?_⟩
  intro x hx hxR hx0
  apply he
  constructor
  · rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_neg (sub_neg.mpr hxR)]
    linarith
  · exact hxR

end Boundary


set_option autoImplicit false
open PowerSeries Inverse Taylor Boundary Filter Set FormalMultilinearSeries
open scoped Topology NNReal ENNReal
namespace Assembly

private theorem mapped_equation (n : ℕ) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) :
    PowerSeries.map (Int.castRingHom ℂ) F =
      1 + X * PowerSeries.map (Int.castRingHom ℂ) F ^ 2 -
        X ^ n * PowerSeries.map (Int.castRingHom ℂ) F ^ (2 * n) := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℂ)) hF
  simpa only [map_sub, map_add, map_one, map_mul, map_pow, PowerSeries.map_X] using h

private theorem taylor_equation (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (heq : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 1 + z * f z ^ 2 - z ^ n * f z ^ (2 * n)) :
    series f = 1 + X * series f ^ 2 - X ^ n * series f ^ (2 * n) := by
  have ht := series_congr heq
  change series f = series ((fun _ : ℂ => 1) + _root_.id * f ^ 2 - _root_.id ^ n * f ^ (2 * n)) at ht
  rw [series_sub (analyticAt_const.add (analyticAt_id.mul (hf.pow 2)))
      ((analyticAt_id.pow n).mul (hf.pow (2 * n))),
    series_add analyticAt_const (analyticAt_id.mul (hf.pow 2)),
    series_mul analyticAt_id (hf.pow 2),
    series_mul (analyticAt_id.pow n) (hf.pow (2 * n)),
    series_pow hf, series_pow hf, series_pow analyticAt_id,
    series_const, map_one] at ht
  have hid : series (_root_.id : ℂ → ℂ) = (X : PowerSeries ℂ) := by
    exact Taylor.series_id
  rw [hid] at ht
  exact ht

private theorem germ_coefficients (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (heq : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 1 + z * f z ^ 2 - z ^ n * f z ^ (2 * n)) :
    series f = PowerSeries.map (Int.castRingHom ℂ) F :=
  (series_exists_unique n hn).unique (taylor_equation n f hf heq) (mapped_equation n F hF)

private theorem convergent_germ (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) :
    ∃ f : ℂ → ℂ, HasFPowerSeriesAt f
      ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), f z = 1 + z * f z ^ 2 - z ^ n * f z ^ (2 * n) := by
  obtain ⟨f, hf, hf0, heq⟩ := zero_germ n hn
  have hcoeff := germ_coefficients n hn F hF f hf heq
  refine ⟨f, ?_, heq⟩
  convert hf.hasFPowerSeriesAt using 1
  apply congrArg (FormalMultilinearSeries.ofScalars ℂ)
  funext m
  have hm := congrArg (PowerSeries.coeff m) hcoeff
  simpa [series, PowerSeries.coeff_map] using hm.symm

end Assembly


set_option autoImplicit false
open PowerSeries Inverse Taylor Boundary Assembly Filter Set FormalMultilinearSeries
open scoped Topology NNReal ENNReal
namespace Global

private theorem scalar_equation_on_disk (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) :
    0 < ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))).radius ∧
    ∀ z : ℂ, z ∈ Metric.eball 0 ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))).radius →
      (fun z : ℂ => ∑' m, ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ) * z ^ m) z =
        1 + z * (fun z : ℂ => ∑' m, ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ) * z ^ m) z ^ 2 -
        z ^ n * (fun z : ℂ => ∑' m, ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ) * z ^ m) z ^ (2 * n) := by
  let a := fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)
  let p := (FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))
  obtain ⟨f, hfp, heq⟩ := convergent_germ n hn F hF
  have hp : 0 < p.radius := hfp.radius_pos
  refine ⟨hp, ?_⟩
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ),
      p.sum z = 1 + z * p.sum z ^ 2 - z ^ n * p.sum z ^ (2 * n) := by
    obtain ⟨r, hr⟩ := hfp
    filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hr.r_pos, heq] with z hz heqz
    have hsum : f z = p.sum z := by simpa only [zero_add] using hr.sum hz
    simpa only [hsum] using heqz
  have ha : AnalyticOnNhd ℂ p.sum (Metric.eball 0 p.radius) := p.analyticOnNhd
  have hb : AnalyticOnNhd ℂ (fun z => 1 + z * p.sum z ^ 2 - z ^ n * p.sum z ^ (2 * n))
      (Metric.eball 0 p.radius) := by
    intro z hz
    exact (analyticAt_const.add (analyticAt_id.mul ((ha z hz).pow 2))).sub
      ((analyticAt_id.pow n).mul ((ha z hz).pow (2 * n)))
  have hext := ha.eqOn_of_preconnected_of_eventuallyEq hb Metric.isPreconnected_eball
    (show (0 : ℂ) ∈ Metric.eball 0 p.radius by simpa using hp) hlocal
  intro z hz
  simpa only [p, scalarSeries_sum] using hext hz

private theorem real_equation_inside (n : ℕ) (hn : 1 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) (x : ℝ≥0)
    (hx : (x : ℝ≥0∞) < ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))).radius) :
    (fun x : ℝ => ∑' m, (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m * x ^ m) x =
      1 + (x : ℝ) * (fun x : ℝ => ∑' m, (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m * x ^ m) x ^ 2 -
        (x : ℝ) ^ n * (fun x : ℝ => ∑' m, (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m * x ^ m) x ^ (2 * n) := by
  have hmem : (x : ℂ) ∈ Metric.eball 0 ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))).radius := by
    simpa [mem_eball_zero_iff, enorm, Complex.nnnorm_real] using hx
  have heq := (scalar_equation_on_disk n hn F hF).2 (x : ℂ) hmem
  simp only [scalar_real] at heq
  exact_mod_cast heq

private theorem radius_le_one (n : ℕ) (hn : 2 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) (hpos : ∀ m, 0 ≤ PowerSeries.coeff m F) :
    ((FormalMultilinearSeries.ofScalars ℂ (fun m => ((fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m : ℂ)))).radius ≤ 1 := by
  by_contra! h
  obtain ⟨x, hx1, hxr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hx1' : (1 : ℝ) < x := by exact_mod_cast hx1
  have ha : ∀ m, (0 : ℝ) ≤ PowerSeries.coeff m F := by exact fun m => Int.cast_nonneg (hpos m)
  have ha0 : ((PowerSeries.coeff 0 F : ℤ) : ℝ) = 1 := by rw [constant_eq_one n (by omega) F hF]; norm_num
  have hs := real_summable (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) x hxr
  have hs1 := realSum_ge_one (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) ha ha0 x x.coe_nonneg hs
  have hb := equation_bounds n hn x ((fun x : ℝ => ∑' m, (fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)) m * x ^ m) x)
    (by linarith) hs1 (real_equation_inside n (by omega) F hF x hxr)
  linarith [hb.2.1, hb.2.2.1]

private theorem has_negative (n : ℕ) (hn : 2 ≤ n) (F : PowerSeries ℤ)
    (hF : Shared.SeriesEquation n F) : ∃ m : ℕ, PowerSeries.coeff m F < 0 := by
  by_contra! hall
  let a := fun m => ((PowerSeries.coeff m F : ℤ) : ℝ)
  let p := (FormalMultilinearSeries.ofScalars ℂ (fun m => (a m : ℂ)))
  have ha : ∀ m, 0 ≤ a m := by exact fun m => Int.cast_nonneg (hall m)
  have ha0 : a 0 = 1 := by
    dsimp only [a]
    rw [constant_eq_one n (by omega) F hF]
    norm_num
  have hp : 0 < p.radius := (scalar_equation_on_disk n (by omega) F hF).1
  have hp1 : p.radius ≤ 1 := radius_le_one n hn F hF hall
  have hptop : p.radius ≠ ∞ := ne_of_lt (lt_of_le_of_lt hp1 (by simp))
  let R := p.radius.toNNReal
  have hrad : p.radius = (R : ℝ≥0∞) := (ENNReal.coe_toNNReal hptop).symm
  have hR : 0 < R := by
    apply ENNReal.coe_pos.mp
    rw [← hrad]
    exact hp
  apply finite_boundary_obstruction n hn a ha ha0 R hR hrad
  intro x hx hxR
  exact real_equation_inside n (by omega) F hF ⟨x, hx.le⟩ (by
    rw [hrad]
    exact ENNReal.coe_lt_coe.mpr hxR)

private theorem common_result : Shared.commonClaim := by
  apply common_of_all
  intro n hn
  obtain ⟨F, hF, _⟩ := series_exists_unique (R := ℤ) n (by omega)
  exact ⟨F, hF, has_negative n hn F hF⟩

end Global
namespace A395835
theorem result : claim := Inverse.result835_of_common Global.common_result
end A395835
namespace A395836
theorem result836 : claim836 := Inverse.result836_of_common Global.common_result
end A395836
namespace A395837
theorem result837 : claim837 := Inverse.result837_of_common Global.common_result
end A395837
namespace A395838
theorem result838 : claim838 := Inverse.result838_of_common Global.common_result
end A395838


end
end D5.S3.Analytic.AlgebraicSeries.HannaA3958Infinitude

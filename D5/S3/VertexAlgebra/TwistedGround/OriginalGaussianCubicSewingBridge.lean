import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
UNCOMPILED SOURCE ATTEMPT. No elaboration, kernel or official acceptance.
The imported cubic supplier is the unchanged manifest-pinned source attempt.

All transport below is private and restricted to the coefficient cone. The
two finite antidiagonals in `chart_mul` are the multiplication witness: the
inner Laurent products are first shifted into ordinary power series. Thus
`sigma_mul` exchanges two FINITE sums, never infinite Laurent sums.

Only the inverse of 2(a-b)^2 is transported as a cone element. The identity
for the moving denominator is obtained afterwards by multiplication by a^2
and native formal-unit cancellation. Neither a^-1 nor (ab-x)^-1 is transported.
No root equation for hb, recurrence or analytic convergence is used.

The order-floor and scalar-inverse proof patterns are adapted from lines
272-284 and 379-401 of the manifest-pinned FinitePrincipalParts input. Its
private declarations are not imported or accessed through private names.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

private def cone (K : AnnulusSeries) : Prop :=
  ∀ d : ℕ, ∀ k : ℤ, k + d < 0 → (PowerSeries.coeff d K).coeff k = 0

private def chart (K : AnnulusSeries) (d t : ℕ) : ℂ :=
  (PowerSeries.coeff d K).coeff ((t : ℤ) - d)

private def rowSeries (K : AnnulusSeries) (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (chart K d)

private lemma chart_add (K L : AnnulusSeries) (d t : ℕ) :
    chart (K + L) d t = chart K d t + chart L d t := by
  simp only [chart, map_add, HahnSeries.coeff_add]

private lemma chart_neg (K : AnnulusSeries) (d t : ℕ) :
    chart (-K) d t = -chart K d t := by
  simp only [chart, map_neg, HahnSeries.coeff_neg]

private def sigma (K : AnnulusSeries) : AnnulusSeries :=
  PowerSeries.mk fun n => HahnSeries.single (-(n : ℤ)) (1 : ℂ) *
    (PowerSeries.mk (fun r : ℕ =>
      (PowerSeries.coeff r K).coeff ((n : ℤ) - r)) : LaurentSeries ℂ)

private lemma cone_sigma (K : AnnulusSeries) : cone (sigma K) := by
  intro d k hk
  rw [sigma, PowerSeries.coeff_mk, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.coeff_coe, if_pos (by omega : k - -(d : ℤ) < 0)]

private lemma chart_sigma (K : AnnulusSeries) (d t : ℕ) :
    chart (sigma K) d t = chart K t d := by
  change (PowerSeries.coeff d (sigma K)).coeff ((t : ℤ) - d) = _
  rw [sigma, PowerSeries.coeff_mk, HahnSeries.coeff_single_mul, one_mul]
  have ht : ((t : ℤ) - d) - -(d : ℤ) = (t : ℤ) := by ring
  rw [ht, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk]
  rfl

private lemma row_reconstruct {K : AnnulusSeries} (hK : cone K) (d : ℕ) :
    PowerSeries.coeff d K = HahnSeries.single (-(d : ℤ)) (1 : ℂ) *
      (rowSeries K d : LaurentSeries ℂ) := by
  ext k
  rw [HahnSeries.coeff_single_mul, one_mul]
  by_cases hk : k - -(d : ℤ) < 0
  · rw [LaurentSeries.coeff_coe, if_pos hk]
    exact hK d k (by omega)
  · rw [LaurentSeries.coeff_coe, if_neg hk, rowSeries, PowerSeries.coeff_mk]
    change (PowerSeries.coeff d K).coeff k =
      (PowerSeries.coeff d K).coeff (((k - -(d : ℤ)).natAbs : ℤ) - d)
    rw [← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ k - -(d : ℤ))]
    congr 1 <;> ring

private lemma chart_ext {K L : AnnulusSeries} (hK : cone K) (hL : cone L)
    (h : ∀ d t : ℕ, chart K d t = chart L d t) : K = L := by
  apply PowerSeries.ext
  intro d
  rw [row_reconstruct hK d, row_reconstruct hL d]
  congr 1
  apply congrArg (fun f : PowerSeries ℂ => (f : LaurentSeries ℂ))
  apply PowerSeries.ext
  intro t
  simpa only [rowSeries, PowerSeries.coeff_mk] using h d t

private lemma cone_add {K L : AnnulusSeries} (hK : cone K) (hL : cone L) :
    cone (K + L) := by
  intro d k hk
  simp only [map_add, HahnSeries.coeff_add, hK d k hk, hL d k hk, add_zero]

private lemma cone_neg {K : AnnulusSeries} (hK : cone K) : cone (-K) := by
  intro d k hk
  simp only [map_neg, HahnSeries.coeff_neg, hK d k hk, neg_zero]

private lemma cone_sub {K L : AnnulusSeries} (hK : cone K) (hL : cone L) :
    cone (K - L) := by
  simpa only [sub_eq_add_neg] using cone_add hK (cone_neg hL)

private lemma laurent_product_floor (f g : LaurentSeries ℂ) (p q : ℤ)
    (hf : ∀ k : ℤ, k < p → f.coeff k = 0)
    (hg : ∀ k : ℤ, k < q → g.coeff k = 0)
    (k : ℤ) (hk : k < p + q) : (f * g).coeff k = 0 := by
  have hf' : (p : WithTop ℤ) ≤ f.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr (fun j hj => hf j (by exact_mod_cast hj))
  have hg' : (q : WithTop ℤ) ≤ g.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr (fun j hj => hg j (by exact_mod_cast hj))
  have hp : ((p + q : ℤ) : WithTop ℤ) ≤ (f * g).orderTop := by
    simpa using (add_le_add hf' hg').trans HahnSeries.orderTop_add_le_mul
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop
    ((show (k : WithTop ℤ) < ((p + q : ℤ) : WithTop ℤ) by exact_mod_cast hk).trans_le hp)

private lemma cone_mul {K L : AnnulusSeries} (hK : cone K) (hL : cone L) :
    cone (K * L) := by
  intro d k hk
  rw [PowerSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro rs hrs
  have hrs' : rs.1 + rs.2 = d := Finset.mem_antidiagonal.mp hrs
  apply laurent_product_floor _ _ (-(rs.1 : ℤ)) (-(rs.2 : ℤ))
  · intro j hj
    exact hK rs.1 j (by omega)
  · intro j hj
    exact hL rs.2 j (by omega)
  · omega

/- This identity converts an actual Hahn product into a finite natural
antidiagonal. Both shifts are justified by the actual cone hypotheses. -/
private lemma chart_row_product {K L : AnnulusSeries} (hK : cone K) (hL : cone L)
    (r s t : ℕ) :
    (PowerSeries.coeff r K * PowerSeries.coeff s L).coeff
        ((t : ℤ) - (r + s : ℕ)) =
      ∑ ij ∈ Finset.antidiagonal t, chart K r ij.1 * chart L s ij.2 := by
  have hm : PowerSeries.coeff r K * PowerSeries.coeff s L =
      HahnSeries.single (-((r + s : ℕ) : ℤ)) (1 : ℂ) *
        ((rowSeries K r * rowSeries L s : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [row_reconstruct hK r, row_reconstruct hL s, LaurentSeries.coe_mul]
    calc
      _ = (HahnSeries.single (-(r : ℤ)) (1 : ℂ) *
          HahnSeries.single (-(s : ℤ)) (1 : ℂ)) *
          ((rowSeries K r : LaurentSeries ℂ) * (rowSeries L s : LaurentSeries ℂ)) := by ring
      _ = _ := by
        rw [HahnSeries.single_mul_single]
        simp only [one_mul, Nat.cast_add, neg_add_rev]
        congr 2 <;> ring
  rw [hm, HahnSeries.coeff_single_mul, one_mul]
  have ht : (t : ℤ) - (r + s : ℕ) - -((r + s : ℕ) : ℤ) = (t : ℤ) := by ring
  rw [ht, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mul]
  simp only [rowSeries, PowerSeries.coeff_mk]

private lemma chart_mul {K L : AnnulusSeries} (hK : cone K) (hL : cone L)
    (d t : ℕ) :
    chart (K * L) d t =
      ∑ rs ∈ Finset.antidiagonal d, ∑ ij ∈ Finset.antidiagonal t,
        chart K rs.1 ij.1 * chart L rs.2 ij.2 := by
  rw [chart, PowerSeries.coeff_mul, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro rs hrs
  have hrs' : rs.1 + rs.2 = d := Finset.mem_antidiagonal.mp hrs
  simpa only [hrs'] using chart_row_product hK hL rs.1 rs.2 t

/- At output [x^d a^(t-d)], the original outer degree is t. If its
outer split is r and inner exponent j, the first shifted inner index is
r+j in [0,d]. Thus swapping the two finite antidiagonals implements exactly
the finite bijection (r,j) -> (r+j,-j); off-cone coefficients vanish. -/
private lemma sigma_mul {K L : AnnulusSeries} (hK : cone K) (hL : cone L) :
    sigma (K * L) = sigma K * sigma L := by
  apply chart_ext (cone_sigma _) (cone_mul (cone_sigma _) (cone_sigma _))
  intro d t
  rw [chart_sigma, chart_mul hK hL, chart_mul (cone_sigma K) (cone_sigma L)]
  simp only [chart_sigma]
  exact Finset.sum_comm

private lemma sigma_add (K L : AnnulusSeries) : sigma (K + L) = sigma K + sigma L := by
  apply chart_ext (cone_sigma _) (cone_add (cone_sigma _) (cone_sigma _))
  intro d t
  simp only [chart_sigma, chart_add]

private lemma sigma_neg (K : AnnulusSeries) : sigma (-K) = -sigma K := by
  apply chart_ext (cone_sigma _) (cone_neg (cone_sigma _))
  intro d t
  simp only [chart_sigma, chart_neg]

private lemma sigma_sub (K L : AnnulusSeries) : sigma (K - L) = sigma K - sigma L := by
  simp only [sub_eq_add_neg, sigma_add, sigma_neg]

private lemma sigma_involutive {K : AnnulusSeries} (hK : cone K) : sigma (sigma K) = K := by
  apply chart_ext (cone_sigma _) hK
  intro d t
  rw [chart_sigma, chart_sigma]

private def liftScalar (f : PowerSeries ℂ) : AnnulusSeries :=
  PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) f

private lemma cone_liftScalar (f : PowerSeries ℂ) : cone (liftScalar f) := by
  intro d k hk
  rw [liftScalar, PowerSeries.coeff_map, HahnSeries.C_apply,
    HahnSeries.coeff_single, if_neg (by omega : k ≠ 0)]

private lemma chart_liftScalar (f : PowerSeries ℂ) (d t : ℕ) :
    chart (liftScalar f) d t = if t = d then PowerSeries.coeff d f else 0 := by
  rw [chart, liftScalar, PowerSeries.coeff_map, HahnSeries.C_apply, HahnSeries.coeff_single]
  by_cases h : t = d
  · subst t
    simp
  · rw [if_neg h, if_neg (by omega : (t : ℤ) - d ≠ 0)]

private lemma sigma_liftScalar (f : PowerSeries ℂ) : sigma (liftScalar f) = liftScalar f := by
  apply chart_ext (cone_sigma _) (cone_liftScalar _)
  intro d t
  rw [chart_sigma, chart_liftScalar, chart_liftScalar]
  by_cases h : d = t
  · subst t
    simp
  · simp [h, Ne.symm h]

private abbrev A : AnnulusSeries := PowerSeries.C (HahnSeries.single 1 (1 : ℂ))
private abbrev AI : AnnulusSeries := PowerSeries.C (HahnSeries.single (-1) (1 : ℂ))
private abbrev B (b : ℂ) : AnnulusSeries := PowerSeries.C (HahnSeries.C b)
private abbrev X : AnnulusSeries := PowerSeries.X
private abbrev Y : AnnulusSeries := X * AI
private abbrev SC : AnnulusSeries := liftScalar scalarCSeries

private lemma AI_A : AI * A = 1 := by
  rw [AI, A, ← map_mul, HahnSeries.single_mul_single]
  norm_num

private lemma A_AI : A * AI = 1 := by rw [mul_comm, AI_A]

private lemma AY : A * Y = X := by
  calc
    _ = X * (A * AI) := by ring
    _ = X := by rw [A_AI, mul_one]

private lemma cone_A : cone A := by
  intro d k hk
  by_cases hd : d = 0
  · subst d
    rw [A, PowerSeries.coeff_zero_C, HahnSeries.coeff_single, if_neg (by omega : k ≠ 1)]
  · rw [A, PowerSeries.coeff_C_of_ne_zero hd]
    simp

private lemma cone_Y : cone Y := by
  intro d k hk
  by_cases hd : d = 1
  · subst d
    simp only [Y, AI, PowerSeries.coeff_mul_C, PowerSeries.coeff_one_X, one_mul]
    rw [HahnSeries.coeff_single, if_neg (by omega : k ≠ -1)]
  · simp only [Y, AI, PowerSeries.coeff_mul_C, PowerSeries.coeff_X, if_neg hd, zero_mul,
      HahnSeries.coeff_zero]

private lemma chart_A (d t : ℕ) : chart A d t = if d = 0 ∧ t = 1 then 1 else 0 := by
  by_cases hd : d = 0
  · subst d
    by_cases ht : t = 1
    · subst t
      simp [chart, A]
    · simp [chart, A, ht, show (t : ℤ) ≠ 1 by omega]
  · simp [chart, A, PowerSeries.coeff_C, hd]

private lemma chart_Y (d t : ℕ) : chart Y d t = if d = 1 ∧ t = 0 then 1 else 0 := by
  by_cases hd : d = 1
  · subst d
    by_cases ht : t = 0
    · subst t
      simp [chart, Y, AI, PowerSeries.coeff_mul_C]
    · simp [chart, Y, AI, PowerSeries.coeff_mul_C, ht,
        show (t : ℤ) - 1 ≠ -1 by omega]
  · simp [chart, Y, AI, PowerSeries.coeff_mul_C, PowerSeries.coeff_X, hd]

private lemma sigma_A : sigma A = Y := by
  apply chart_ext (cone_sigma _) cone_Y
  intro d t
  rw [chart_sigma, chart_A, chart_Y]
  simp only [and_comm]

private lemma cone_B (b : ℂ) : cone (B b) := by
  have he : B b = liftScalar (PowerSeries.C b) := by simp [B, liftScalar]
  rw [he]
  exact cone_liftScalar _

private lemma sigma_B (b : ℂ) : sigma (B b) = B b := by
  have he : B b = liftScalar (PowerSeries.C b) := by simp [B, liftScalar]
  rw [he, sigma_liftScalar]

private lemma cone_one : cone (1 : AnnulusSeries) := by
  simpa [liftScalar] using cone_liftScalar (1 : PowerSeries ℂ)

private lemma sigma_one : sigma (1 : AnnulusSeries) = 1 := by
  simpa [liftScalar] using sigma_liftScalar (1 : PowerSeries ℂ)

private lemma cone_two : cone (2 : AnnulusSeries) := by
  simpa [B] using cone_B (2 : ℂ)

private lemma sigma_two : sigma (2 : AnnulusSeries) = 2 := by
  simpa [B] using sigma_B (2 : ℂ)

private lemma cone_X : cone X := by
  simpa [liftScalar, X] using cone_liftScalar (PowerSeries.X : PowerSeries ℂ)

private lemma sigma_X : sigma X = X := by
  simpa [liftScalar, X] using sigma_liftScalar (PowerSeries.X : PowerSeries ℂ)

private lemma cone_pow {K : AnnulusSeries} (hK : cone K) (n : ℕ) : cone (K ^ n) := by
  induction n with
  | zero => simpa using cone_one
  | succ n ih => simpa only [pow_succ] using cone_mul ih hK

private lemma sigma_sq {K : AnnulusSeries} (hK : cone K) : sigma (K ^ 2) = sigma K ^ 2 := by
  simpa only [pow_two] using sigma_mul hK hK

private lemma cone_coe (f : PowerSeries ℂ) : cone (PowerSeries.C (f : LaurentSeries ℂ)) := by
  intro d k hk
  by_cases hd : d = 0
  · subst d
    rw [PowerSeries.coeff_zero_C, LaurentSeries.coeff_coe, if_pos (by omega : k < 0)]
  · rw [PowerSeries.coeff_C_of_ne_zero hd]
    simp

private lemma coe_inverse (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = (f : LaurentSeries ℂ)⁻¹ := by
  have hm : (f : LaurentSeries ℂ) * ((f⁻¹ : PowerSeries ℂ) : LaurentSeries ℂ) = 1 := by
    rw [← LaurentSeries.coe_mul, PowerSeries.mul_inv_cancel f hf]
    simp
  have hn : (f : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  exact mul_left_cancel₀ hn (hm.trans (mul_inv_cancel₀ hn).symm)

private abbrev DT (b : ℂ) : AnnulusSeries := 2 * (A - B b) ^ 2
private abbrev DU (b : ℂ) : AnnulusSeries := 2 * (A * B b - X) ^ 2
private abbrev NT (b : ℂ) : AnnulusSeries :=
  A * B b * (A + B b) + 2 * (1 + X) * A * B b + X * (A + B b)
private abbrev NU (b : ℂ) : AnnulusSeries :=
  X * (A * B b * (A + B b + 2) + X * (A + B b + 2 * A * B b))
private abbrev PT (b : ℂ) : AnnulusSeries := NT b * (DT b)⁻¹
private abbrev PU (b : ℂ) : AnnulusSeries := NU b * (DU b)⁻¹

private lemma DT_unit (b : ℂ) (hb : b ≠ 0) : PowerSeries.constantCoeff (DT b) ≠ 0 := by
  let f : PowerSeries ℂ := 2 * (PowerSeries.X - PowerSeries.C b) ^ 2
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    simpa [f] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (pow_ne_zero 2 (neg_ne_zero.mpr hb))
  have he : DT b = PowerSeries.C (f : LaurentSeries ℂ) := by
    simp [DT, f, A, B, map_mul, map_sub, map_pow,
      HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C]
  rw [he, PowerSeries.constantCoeff_C]
  intro hz
  have hc := congrArg (fun z : LaurentSeries ℂ => z.coeff 0) hz
  have hzero : PowerSeries.constantCoeff f = 0 := by
    simpa only [LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_zero] using hc
  exact hf hzero

private lemma cone_DT_inverse (b : ℂ) (hb : b ≠ 0) : cone ((DT b)⁻¹) := by
  let f : PowerSeries ℂ := 2 * (PowerSeries.X - PowerSeries.C b) ^ 2
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    simpa [f] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (pow_ne_zero 2 (neg_ne_zero.mpr hb))
  have he : DT b = PowerSeries.C (f : LaurentSeries ℂ) := by
    simp [DT, f, A, B, map_mul, map_sub, map_pow,
      HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C]
  rw [he, PowerSeries.C_inv, ← coe_inverse f hf]
  exact cone_coe f⁻¹

private lemma DU_unit (b : ℂ) (hb : b ≠ 0) : PowerSeries.constantCoeff (DU b) ≠ 0 := by
  have hab : (HahnSeries.single 1 (1 : ℂ) : LaurentSeries ℂ) * HahnSeries.C b =
      HahnSeries.single 1 b := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  simpa [DU, A, B, X, hab] using
    mul_ne_zero (by norm_num : (2 : LaurentSeries ℂ) ≠ 0)
      (pow_ne_zero 2 (HahnSeries.single_ne_zero hb))

private lemma cone_NT (b : ℂ) : cone (NT b) := by
  exact cone_add
    (cone_add (cone_mul (cone_mul cone_A (cone_B b)) (cone_add cone_A (cone_B b)))
      (cone_mul (cone_mul (cone_mul cone_two (cone_add cone_one cone_X)) cone_A) (cone_B b)))
    (cone_mul cone_X (cone_add cone_A (cone_B b)))

private lemma cone_PT (b : ℂ) (hb : b ≠ 0) : cone (PT b) :=
  cone_mul (cone_NT b) (cone_DT_inverse b hb)

private lemma sigma_DT (b : ℂ) : sigma (DT b) = 2 * (Y - B b) ^ 2 := by
  rw [sigma_mul cone_two (cone_pow (cone_sub cone_A (cone_B b)) 2), sigma_two,
    sigma_sq (cone_sub cone_A (cone_B b)), sigma_sub, sigma_A, sigma_B]

/- Compensated inverse transport. The native inverse on the right is not
claimed to be a cone element; a^2 is essential. -/
private lemma sigma_DT_inverse (b : ℂ) (hb : b ≠ 0) :
    sigma ((DT b)⁻¹) = A ^ 2 * (DU b)⁻¹ := by
  have hD : cone (DT b) := cone_mul cone_two (cone_pow (cone_sub cone_A (cone_B b)) 2)
  have hs : sigma ((DT b)⁻¹) * (2 * (Y - B b) ^ 2) = 1 := by
    rw [← sigma_DT b, ← sigma_mul (cone_DT_inverse b hb) hD,
      PowerSeries.inv_mul_cancel (DT b) (DT_unit b hb), sigma_one]
  have hpoly : (2 * (Y - B b) ^ 2) * A ^ 2 = DU b := by
    calc
      _ = 2 * (A * Y - A * B b) ^ 2 := by ring
      _ = DU b := by rw [AY]; dsimp [DU]; ring
  have hmove : sigma ((DT b)⁻¹) * DU b = A ^ 2 := by
    rw [← hpoly]
    calc
      _ = (sigma ((DT b)⁻¹) * (2 * (Y - B b) ^ 2)) * A ^ 2 := by ring
      _ = A ^ 2 := by rw [hs, one_mul]
  exact (PowerSeries.eq_mul_inv_iff_mul_eq (DU_unit b hb)).mpr hmove

private lemma sigma_NT (b : ℂ) :
    sigma (NT b) =
      Y * B b * (Y + B b) + 2 * (1 + X) * Y * B b + X * (Y + B b) := by
  dsimp [NT]
  rw [sigma_add, sigma_add,
    sigma_mul (cone_mul cone_A (cone_B b)) (cone_add cone_A (cone_B b)),
    sigma_mul cone_A (cone_B b),
    sigma_mul (cone_mul (cone_mul cone_two (cone_add cone_one cone_X)) cone_A) (cone_B b),
    sigma_mul (cone_mul cone_two (cone_add cone_one cone_X)) cone_A,
    sigma_mul cone_two (cone_add cone_one cone_X),
    sigma_mul cone_X (cone_add cone_A (cone_B b))]
  simp only [sigma_add, sigma_A, sigma_B, sigma_two, sigma_one, sigma_X]

private lemma sigma_PT (b : ℂ) (hb : b ≠ 0) : sigma (PT b) = PU b := by
  rw [sigma_mul (cone_NT b) (cone_DT_inverse b hb), sigma_NT,
    sigma_DT_inverse b hb]
  have hpoly :
      (Y * B b * (Y + B b) + 2 * (1 + X) * Y * B b + X * (Y + B b)) * A ^ 2 =
        NU b := by
    calc
      _ = (A * Y) ^ 2 * B b + A * (A * Y) * (B b) ^ 2 +
          2 * (1 + X) * A * (A * Y) * B b +
          X * A * (A * Y) + X * A ^ 2 * B b := by ring
      _ = NU b := by rw [AY]; dsimp [NU]; ring
  calc
    _ = ((Y * B b * (Y + B b) + 2 * (1 + X) * Y * B b +
        X * (Y + B b)) * A ^ 2) * (DU b)⁻¹ := by ring
    _ = PU b := by rw [hpoly]

private abbrev W : AnnulusSeries := A * formalOmega

private lemma W_coeff (d : ℕ) : PowerSeries.coeff d W =
    HahnSeries.single (-(d : ℤ)) (halfBinomial d) * (halfSeries : LaurentSeries ℂ) := by
  change PowerSeries.coeff d (PowerSeries.C (HahnSeries.single 1 (1 : ℂ)) * formalOmega) = _
  rw [PowerSeries.coeff_C_mul]
  change HahnSeries.single 1 (1 : ℂ) *
    (HahnSeries.single (-(d : ℤ) - 1) (halfBinomial d) * (halfSeries : LaurentSeries ℂ)) = _
  rw [← mul_assoc, HahnSeries.single_mul_single, one_mul]
  congr 2 <;> ring

private lemma cone_W : cone W := by
  intro d k hk
  rw [W_coeff, HahnSeries.coeff_single_mul, LaurentSeries.coeff_coe,
    if_pos (by omega : k - -(d : ℤ) < 0), mul_zero]

private lemma chart_W (d t : ℕ) : chart W d t = halfBinomial d * halfBinomial t := by
  rw [chart, W_coeff, HahnSeries.coeff_single_mul]
  have ht : ((t : ℤ) - d) - -(d : ℤ) = (t : ℤ) := by ring
  rw [ht, LaurentSeries.coeff_coe_powerSeries]
  rfl

private lemma sigma_W : sigma W = W := by
  apply chart_ext (cone_sigma _) cone_W
  intro d t
  rw [chart_sigma, chart_W, chart_W, mul_comm]

private lemma external_as_lift (b hb : ℂ) : formalExternalOmega b hb =
    liftScalar (PowerSeries.mk fun n => hb * halfBinomial n / b ^ (n + 1)) := by
  ext d
  simp [formalExternalOmega, liftScalar]

private lemma cone_external (b hb : ℂ) : cone (formalExternalOmega b hb) := by
  rw [external_as_lift]
  exact cone_liftScalar _

private lemma sigma_external (b hb : ℂ) : sigma (formalExternalOmega b hb) = formalExternalOmega b hb := by
  rw [external_as_lift, sigma_liftScalar]

private lemma cone_SC : cone SC := cone_liftScalar _
private lemma sigma_SC : sigma SC = SC := sigma_liftScalar _

private lemma literal_TT (b hb : ℂ) :
    cubicTTSeries b hb = formalOmega * formalExternalOmega b hb * (PT b + SC) := by rfl

private lemma literal_UT (b hb : ℂ) :
    cubicUTSeries b hb = -(formalOmega * formalExternalOmega b hb) * (PU b + SC) := by rfl

private lemma cone_A_TT (b hb : ℂ) (hb0 : b ≠ 0) : cone (A * cubicTTSeries b hb) := by
  have he : A * cubicTTSeries b hb = W * formalExternalOmega b hb * (PT b + SC) := by
    rw [literal_TT]
    dsimp [W]
    ring
  rw [he]
  exact cone_mul (cone_mul cone_W (cone_external b hb)) (cone_add (cone_PT b hb0) cone_SC)

private def iota (K : AnnulusSeries) : AnnulusSeries := -AI * sigma (A * K)

private lemma iota_involutive {K : AnnulusSeries} (hK : cone (A * K)) :
    iota (iota K) = K := by
  have hA : A * iota K = -sigma (A * K) := by
    dsimp [iota]
    calc
      _ = -(A * AI) * sigma (A * K) := by ring
      _ = -sigma (A * K) := by rw [A_AI]; ring
  change -AI * sigma (A * iota K) = K
  rw [hA, sigma_neg, sigma_involutive hK]
  calc
    _ = (AI * A) * K := by ring
    _ = K := by rw [AI_A, one_mul]

private lemma iota_TT (b hb : ℂ) (hb0 : b ≠ 0) :
    iota (cubicTTSeries b hb) = cubicUTSeries b hb := by
  have he : A * cubicTTSeries b hb = W * formalExternalOmega b hb * (PT b + SC) := by
    rw [literal_TT]
    dsimp [W]
    ring
  rw [iota, he,
    sigma_mul (cone_mul cone_W (cone_external b hb)) (cone_add (cone_PT b hb0) cone_SC),
    sigma_mul cone_W (cone_external b hb), sigma_W, sigma_external,
    sigma_add, sigma_PT b hb0, sigma_SC, literal_UT]
  dsimp [W]
  calc
    _ = -(AI * A) * (formalOmega * formalExternalOmega b hb) * (PU b + SC) := by ring
    _ = _ := by rw [AI_A]; ring

private lemma iota_UT (b hb : ℂ) (hb0 : b ≠ 0) :
    iota (cubicUTSeries b hb) = cubicTTSeries b hb := by
  rw [← iota_TT b hb hb0]
  exact iota_involutive (cone_A_TT b hb hb0)

/- This last extraction uses a nonnegative original outer degree n+s, not a
truncated degree or a global Laurent substitution. -/
private lemma iota_coefficient (K : AnnulusSeries) (s n : ℕ) :
    (PowerSeries.coeff n (iota K)).coeff ((s : ℤ) - 1) =
      -negativeCoefficient K s (s + n) := by
  have hi : iota K = -(AI * sigma (A * K)) := by dsimp [iota]; ring
  rw [hi, map_neg, HahnSeries.coeff_neg, AI, PowerSeries.coeff_C_mul,
    HahnSeries.coeff_single_mul, one_mul]
  have hs : ((s : ℤ) - 1) - (-1) = (s : ℤ) := by ring
  rw [hs, sigma, PowerSeries.coeff_mk, HahnSeries.coeff_single_mul, one_mul]
  have hsn : (s : ℤ) - -(n : ℤ) = ((s + n : ℕ) : ℤ) := by push_cast; ring
  rw [hsn, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk,
    A, PowerSeries.coeff_C_mul, HahnSeries.coeff_single_mul, one_mul]
  dsimp [negativeCoefficient]
  congr 2
  push_cast
  ring

/-- Intended exact original TT-to-UT signed sewing identity.
SOURCE ONLY: this proof term has not been elaborated or kernel checked. -/
theorem cubic_tt_signed_sewing (b hb : ℂ) (hb0 : b ≠ 0)
    (s : ℕ) (_hs : 1 ≤ s) (n : ℕ) :
    negativeCoefficient (cubicTTSeries b hb) s (s + n) =
      -(PowerSeries.coeff n (cubicUTSeries b hb)).coeff ((s : ℤ) - 1) := by
  have h := iota_coefficient (cubicTTSeries b hb) s n
  rw [iota_TT b hb hb0] at h
  simpa only [neg_neg] using congrArg (fun z : ℂ => -z) h.symm

/-- Intended exact original UT-to-TT signed sewing identity, with arbitrary hb.
SOURCE ONLY: this proof term has not been elaborated or kernel checked. -/
theorem cubic_ut_signed_sewing (b hb : ℂ) (hb0 : b ≠ 0)
    (s : ℕ) (_hs : 1 ≤ s) (n : ℕ) :
    negativeCoefficient (cubicUTSeries b hb) s (s + n) =
      -(PowerSeries.coeff n (cubicTTSeries b hb)).coeff ((s : ℤ) - 1) := by
  have h := iota_coefficient (cubicUTSeries b hb) s n
  rw [iota_UT b hb hb0] at h
  simpa only [neg_neg] using congrArg (fun z : ℂ => -z) h.symm

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicKernel

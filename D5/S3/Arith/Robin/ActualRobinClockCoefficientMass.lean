/- GID: D5/S3/Arith/Robin/ActualRobinClockCoefficientMass
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualRobinClockCoefficientMass
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual shell covariance controls the exact finite coefficient mass. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance

/-!
This is the finite coefficient consumer of the same literal actual clock
kernel. The imported activation integral and harmonic-shell variation are
consumed through `actual_clock_quantitative`, without assumed W/Gamma bounds.
The finite Abel top and lower anchor remain. Empty shifts and invalid blocks
are settled before maxima. Corr certification, CA clock identity and the full
Robin/5040/RH goal remain unfinished.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators Interval Topology
open D5.S3.Arith.Robin.ActualRobinClockCovariance

namespace D5.S3.Arith.Robin.ActualRobinClockCoefficientMass

def covarianceEnvelope (z t : ℝ) : ℝ := 1/(t*(t+z))

private theorem z_h {z t : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    z*covarianceEnvelope z t = 1/t-1/(t+z) := by
  unfold covarianceEnvelope
  have htz : t+z ≠ 0 := ne_of_gt (by linarith)
  field_simp [ne_of_gt ht, htz] <;> ring

private theorem z_difference {z t : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    z*(covarianceEnvelope z t-covarianceEnvelope z (t+1)) =
      1/(t*(t+1))-1/((t+z)*(t+z+1)) := by
  rw [mul_sub, z_h ht hz, z_h (by linarith) hz]
  have h1 : t+1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : t+z ≠ 0 := ne_of_gt (by linarith)
  have h3 : t+z+1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [ne_of_gt ht, h1, h2, h3] <;> ring

private theorem z_difference_mono {t z Z : ℝ}
    (ht : 0 < t) (hz : 0 ≤ z) (hzZ : z ≤ Z) :
    z*(covarianceEnvelope z t-covarianceEnvelope z (t+1)) ≤ Z*(covarianceEnvelope Z t-covarianceEnvelope Z (t+1)) := by
  rw [z_difference ht hz, z_difference ht (hz.trans hzZ)]
  apply sub_le_sub_left
  apply one_div_le_one_div_of_le
  · exact mul_pos (by linarith) (by linarith)
  · exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

private theorem z_h_mono {t z Z : ℝ}
    (ht : 0 < t) (hz : 0 ≤ z) (hzZ : z ≤ Z) :
    z*covarianceEnvelope z t ≤ Z*covarianceEnvelope Z t := by
  rw [z_h ht hz, z_h ht (hz.trans hzZ)]
  exact sub_le_sub_left (one_div_le_one_div_of_le (by linarith) (by linarith)) _

private theorem finite_Abel {L T : ℕ} (hLT : L ≤ T) (f : ℕ → ℝ) :
    (∑ r ∈ Icc L T, (r : ℝ)*(f r-f (r+1))) =
      (L : ℝ)*f L + (∑ r ∈ Icc (L+1) T, f r) - (T : ℝ)*f (T+1) := by
  have H : ∀ n, (∑ i ∈ range n, (f i-f (i+1))) = f 0-f n :=
    fun n => sum_range_sub' f n
  have hs := sum_Ico_by_parts (fun i : ℕ => (i : ℝ))
    (fun i => f i-f (i+1)) (Nat.lt_succ_of_le hLT)
  simp only [H, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, smul_eq_mul, one_mul, sum_sub_distrib, sum_const,
    Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hLT] at hs
  have hshift : (∑ i ∈ Ico L T, f (i+1)) = ∑ r ∈ Icc (L+1) T, f r := by
    rw [sum_Ico_add' f L T (c := 1), Ico_add_one_right_eq_Icc]
  rw [hshift, Ico_add_one_right_eq_Icc] at hs
  linarith

def abelBudget (L T : ℕ) (z : ℝ) : ℝ :=
  z*((L : ℝ)*covarianceEnvelope z L + (∑ r ∈ Icc (L+1) T, covarianceEnvelope z r) -
    (T : ℝ)*covarianceEnvelope z (T+1))

private theorem abelBudget_exact {L T : ℕ} (hLT : L ≤ T) (z : ℝ) :
    (∑ r ∈ Icc L T, (r : ℝ)*z*(covarianceEnvelope z r-covarianceEnvelope z (r+1))) = abelBudget L T z := by
  unfold abelBudget
  have hAbel := finite_Abel hLT (fun r => covarianceEnvelope z r)
  push_cast at hAbel
  rw [← hAbel, mul_sum]
  apply sum_congr rfl
  intro r _
  push_cast
  ring

private theorem h_le_inv_sq {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    covarianceEnvelope z t ≤ (t^2)⁻¹ := by
  unfold covarianceEnvelope
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos ht)
    (by nlinarith : t^2 ≤ t*(t+z))

private theorem abelBudget_budget {L T : ℕ} {z : ℝ}
    (hL : 1 ≤ L) (hLT : L ≤ T) (hz : 0 ≤ z) :
    abelBudget L T z ≤ 2*z/(L : ℝ) := by
  have hL0 : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hT0 : 0 < (T : ℝ)+1 := by positivity
  have heq : Icc (L+1) T = Ioc L T := by
    ext i
    simp only [mem_Icc, mem_Ioc]
    omega
  have htail : (∑ r ∈ Icc (L+1) T, covarianceEnvelope z r) ≤ (L : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ r ∈ Icc (L+1) T, ((r : ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro r hr
        apply h_le_inv_sq _ hz
        exact_mod_cast (show 0 < r by have := (mem_Icc.mp hr).1; omega)
      _ = ∑ r ∈ Ioc L T, ((r : ℝ)^2)⁻¹ := by rw [heq]
      _ ≤ (L : ℝ)⁻¹-(T : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (by omega) hLT
      _ ≤ (L : ℝ)⁻¹ := sub_le_self _ (by positivity)
  have hfirst : (L : ℝ)*covarianceEnvelope z L ≤ (L : ℝ)⁻¹ := by
    calc
      _ ≤ (L : ℝ)*((L : ℝ)^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (h_le_inv_sq hL0 hz) hL0.le
      _ = (L : ℝ)⁻¹ := by field_simp [ne_of_gt hL0] <;> ring
  have htop : 0 ≤ (T : ℝ)*covarianceEnvelope z (T+1) := by
    unfold covarianceEnvelope
    positivity
  have hs : (L : ℝ)*covarianceEnvelope z L + (∑ r ∈ Icc (L+1) T, covarianceEnvelope z r) -
      (T : ℝ)*covarianceEnvelope z (T+1) ≤ 2/(L : ℝ) := by
    rw [div_eq_mul_inv]
    linarith
  unfold abelBudget
  convert mul_le_mul_of_nonneg_left hs hz using 1 <;> first | rfl | ring


def maxShift (Z : Finset ℝ) : ℝ :=
  if hZ : Z.Nonempty then Z.sup' hZ id else 0

def omega {m : ℕ} (A : Fin m → ℝ) (Z : Finset ℝ) (r : ℕ) : ℝ :=
  if hZ : Z.Nonempty then Z.sup' hZ (fun z => z *
    (Gamma A r ((r : ℝ)+z)-Gamma A (r+1) ((r : ℝ)+z+1))) else 0

def kappa_L {m : ℕ} (A : Fin m → ℝ) (Z : Finset ℝ) (L : ℕ) : ℝ :=
  if hZ : Z.Nonempty then Z.sup' hZ (fun z => z*Gamma A L ((L : ℝ)+z)) else 0

def coefficientMass {m : ℕ} (A : Fin m → ℝ) (Z : Finset ℝ) (L T : ℕ) : ℝ :=
  if T < L then 0 else
    (∑ r ∈ Icc L T, (r : ℝ)*omega A Z r)+(L-1 : ℕ)*kappa_L A Z L

private theorem coefficientMass_empty {m : ℕ} (A : Fin m → ℝ) (L T : ℕ) :
    coefficientMass A ∅ L T = 0 := by
  simp [coefficientMass, omega, kappa_L]

-- Settle an invalid block before taking any maximum. Within a valid block
-- the lower anchor remains; an empty tail alone is not an Abel cancellation.
private theorem coefficientMass_tail_empty {m : ℕ} (A : Fin m → ℝ) (Z : Finset ℝ)
    {L T : ℕ} (hTL : T < L) :
    coefficientMass A Z L T = 0 := by
  simp [coefficientMass, hTL]

private theorem actual_mass_bound {m : ℕ} (A : Fin m → ℝ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (Z : Finset ℝ) (hZpos : ∀ z ∈ Z, 0 ≤ z) {L T : ℕ}
    (hL : 1 ≤ L) (hLT : L ≤ T) :
    coefficientMass A Z L T ≤ (m : ℝ)/4 *
      (rangeBudget a b*variationBudget a b*abelBudget L T (maxShift Z) +
       (rangeBudget a b)^2*(L-1 : ℕ)*maxShift Z/((L : ℝ)*(L+maxShift Z))) := by
  by_cases hZ : Z.Nonempty
  · let Zmax := Z.sup' hZ id
    have hmax : maxShift Z = Zmax := by simp [maxShift, hZ, Zmax]
    have hzmax : 0 ≤ Zmax := by
      obtain ⟨z, hz⟩ := hZ
      exact (hZpos z hz).trans (le_sup' id hz)
    have hlemax : ∀ z ∈ Z, z ≤ Zmax := fun z hz => le_sup' id hz
    have hL0 : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
    have hK : 0 ≤ rangeBudget a b := by
      unfold rangeBudget
      have ha0 : 0 < a := by linarith
      have hla := Real.log_pos ha
      have hlab := Real.log_le_log ha0 hab
      exact add_nonneg (Real.log_nonneg ((one_le_div ha0).mpr hab))
        (Real.log_nonneg ((one_le_div hla).mpr hlab))
    have hC : 0 ≤ variationBudget a b := by
      unfold variationBudget
      have hlog := Real.log_nonneg ((one_le_div (by linarith : 0 < a)).mpr hab)
      have hla := Real.log_pos ha
      exact mul_nonneg (by positivity) (by linarith)
    let F := (m : ℝ)*rangeBudget a b*variationBudget a b/4
    let G := (m : ℝ)*(rangeBudget a b)^2/4
    have hF : 0 ≤ F := by dsimp [F]; positivity
    have hG : 0 ≤ G := by dsimp [G]; positivity
    have hweight : ∀ r ∈ Icc L T,
        omega A Z r ≤ F*Zmax*(covarianceEnvelope Zmax r-covarianceEnvelope Zmax ((r : ℝ)+1)) := by
      intro r hr
      have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hL.trans (mem_Icc.mp hr).1
      have hr0 : 0 < (r : ℝ) := by linarith
      simp only [omega, dif_pos hZ]
      apply sup'_le hZ
      intro z hz
      have hz0 := hZpos z hz
      have hactual := (actual_clock_quantitative A ha hab hAa hAb hr1
        (by linarith : (r : ℝ) ≤ r+1) hz0).2.2.2.1
      have hscaled := mul_le_mul_of_nonneg_left hactual hz0
      have hmono := z_difference_mono hr0 hz0 (hlemax z hz)
      have hR : z*(Gamma A r ((r : ℝ)+z)-Gamma A (r+1) ((r : ℝ)+z+1)) ≤
          F*(z*(covarianceEnvelope z r-covarianceEnvelope z ((r : ℝ)+1))) := by
        convert hscaled using 1 <;>
          (try simp only [F, covarianceEnvelope, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]) <;> first | rfl | ring
      calc
        _ ≤ F*(z*(covarianceEnvelope z r-covarianceEnvelope z ((r : ℝ)+1))) := hR
        _ ≤ F*(Zmax*(covarianceEnvelope Zmax r-covarianceEnvelope Zmax ((r : ℝ)+1))) :=
          mul_le_mul_of_nonneg_left hmono hF
        _ = _ := by ring
    have hanchor : kappa_L A Z L ≤ G*Zmax*covarianceEnvelope Zmax L := by
      simp only [kappa_L, dif_pos hZ]
      apply sup'_le hZ
      intro z hz
      have hz0 := hZpos z hz
      -- Real consumer of the public quantitative theorem's actual G-size field.
      have hactual := (actual_clock_quantitative A ha hab hAa hAb
        (by exact_mod_cast hL : 1 ≤ (L : ℝ)) le_rfl hz0).2.1
      have hscaled := mul_le_mul_of_nonneg_left hactual hz0
      have hmono := z_h_mono hL0 hz0 (hlemax z hz)
      calc
        z*Gamma A L ((L : ℝ)+z) ≤ G*(z*covarianceEnvelope z L) := by
          dsimp [G, covarianceEnvelope]
          convert hscaled using 1 <;>
            first | rfl | (field_simp [ne_of_gt hL0, ne_of_gt (by linarith : 0 < (L : ℝ)+z)] <;> ring)
        _ ≤ G*(Zmax*covarianceEnvelope Zmax L) := mul_le_mul_of_nonneg_left hmono hG
        _ = _ := by ring
    have hsum : (∑ r ∈ Icc L T, (r : ℝ)*omega A Z r) ≤ F*abelBudget L T Zmax := by
      calc
        _ ≤ ∑ r ∈ Icc L T, (r : ℝ)*(F*Zmax*(covarianceEnvelope Zmax r-covarianceEnvelope Zmax ((r : ℝ)+1))) :=
          sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hweight r hr) (Nat.cast_nonneg _))
        _ = F*(∑ r ∈ Icc L T, (r : ℝ)*Zmax*(covarianceEnvelope Zmax r-covarianceEnvelope Zmax (r+1))) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro r _
          push_cast
          ring
        _ = _ := by rw [abelBudget_exact hLT]
    have hbottom := mul_le_mul_of_nonneg_left hanchor (Nat.cast_nonneg (L-1))
    unfold coefficientMass
    rw [if_neg (not_lt.mpr hLT), hmax]
    calc
      _ ≤ F*abelBudget L T Zmax + (L-1 : ℕ)*(G*Zmax*covarianceEnvelope Zmax L) := add_le_add hsum hbottom
      _ = _ := by
        dsimp [F, G, covarianceEnvelope]
        field_simp [ne_of_gt hL0, ne_of_gt (by linarith : 0 < (L : ℝ)+Zmax)] <;> ring
  · have hempty : Z = ∅ := not_nonempty_iff_eq_empty.mp hZ
    subst Z
    rw [coefficientMass_empty]
    simp [maxShift, abelBudget]



private theorem actual_mass_coarse {m : ℕ} (A : Fin m → ℝ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (Z : Finset ℝ) (hZpos : ∀ z ∈ Z, 0 ≤ z) {L T : ℕ}
    (hL : 1 ≤ L) (hLT : L ≤ T) :
    coefficientMass A Z L T ≤ (m : ℝ)/4 *
      (rangeBudget a b*variationBudget a b*(2*maxShift Z/(L : ℝ)) +
       (rangeBudget a b)^2*(L-1 : ℕ)*maxShift Z/((L : ℝ)*(L+maxShift Z))) := by
  have hK : 0 ≤ rangeBudget a b := by
    unfold rangeBudget
    have ha0 : 0 < a := by linarith
    have hla := Real.log_pos ha
    have hlab := Real.log_le_log ha0 hab
    exact add_nonneg (Real.log_nonneg ((one_le_div ha0).mpr hab))
      (Real.log_nonneg ((one_le_div hla).mpr hlab))
  have hC : 0 ≤ variationBudget a b := by
    unfold variationBudget
    have hlog := Real.log_nonneg ((one_le_div (by linarith : 0 < a)).mpr hab)
    have hla := Real.log_pos ha
    exact mul_nonneg (by positivity) (by linarith)
  have hzmax : 0 ≤ maxShift Z := by
    unfold maxShift
    split_ifs with hZ
    · obtain ⟨z,hz⟩ := hZ
      exact (hZpos z hz).trans (le_sup' id hz)
    · exact le_rfl
  exact (actual_mass_bound A ha hab hAa hAb Z hZpos hL hLT).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left (abelBudget_budget hL hLT hzmax) (mul_nonneg hK hC)) le_rfl)
      (by positivity))

private theorem actual_mass_nonneg {m : ℕ} (A : Fin m → ℝ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (Z : Finset ℝ) (hZpos : ∀ z ∈ Z, 0 ≤ z) {L T : ℕ}
    (hL : 1 ≤ L) : 0 ≤ coefficientMass A Z L T := by
  by_cases hTL : T < L
  · rw [coefficientMass_tail_empty A Z hTL]
  by_cases hZ : Z.Nonempty
  · obtain ⟨z,hz⟩ := hZ
    have hZ : Z.Nonempty := ⟨z, hz⟩
    have hz0 := hZpos z hz
    have hweights : ∀ r ∈ Icc L T, 0 ≤ omega A Z r := by
      intro r hr
      have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hL.trans (mem_Icc.mp hr).1
      have hgam := (actual_clock_quantitative A ha hab hAa hAb hr1
        (by linarith : (r : ℝ) ≤ r+1) hz0).2.2.1
      have hterm : 0 ≤ z*(Gamma A r ((r : ℝ)+z)-Gamma A (r+1) ((r : ℝ)+z+1)) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
          using mul_nonneg hz0 hgam
      simp only [omega, dif_pos hZ]
      exact hterm.trans (le_sup' (fun z => z *
        (Gamma A r ((r : ℝ)+z)-Gamma A (r+1) ((r : ℝ)+z+1))) hz)
    have hanchor : 0 ≤ kappa_L A Z L := by
      have hgam := (actual_clock_quantitative A ha hab hAa hAb
        (by exact_mod_cast hL : 1 ≤ (L : ℝ)) le_rfl hz0).1
      simp only [kappa_L, dif_pos hZ]
      exact (mul_nonneg hz0 hgam).trans (le_sup' (fun z => z*Gamma A L ((L : ℝ)+z)) hz)
    simp only [coefficientMass, if_neg hTL]
    exact add_nonneg (sum_nonneg (fun r hr =>
      mul_nonneg (Nat.cast_nonneg _) (hweights r hr)))
      (mul_nonneg (Nat.cast_nonneg _) hanchor)
  · have hempty : Z = ∅ := not_nonempty_iff_eq_empty.mp hZ
    subst Z
    rw [coefficientMass_empty]


/-- The exact finite coefficient-mass consumer of the actual activation-shell
variation and range estimates. Empty shifts and invalid blocks are settled
before maxima. The exact Abel budget retains its finite negative top. -/
theorem actual_clock_coefficient_mass {m : ℕ} (A : Fin m → ℝ) {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hAa : ∀ i, a ≤ A i) (hAb : ∀ i, A i ≤ b)
    (Z : Finset ℝ) (hZpos : ∀ z ∈ Z, 0 ≤ z) {L T : ℕ}
    (hL : 1 ≤ L) (hLT : L ≤ T) :
    0 ≤ coefficientMass A Z L T ∧
    coefficientMass A Z L T ≤ (m : ℝ)/4 *
      (rangeBudget a b*variationBudget a b*abelBudget L T (maxShift Z) +
       (rangeBudget a b)^2*(L-1 : ℕ)*maxShift Z/((L : ℝ)*(L+maxShift Z))) ∧
    coefficientMass A Z L T ≤ (m : ℝ)/4 *
      (rangeBudget a b*variationBudget a b*(2*maxShift Z/(L : ℝ)) +
       (rangeBudget a b)^2*(L-1 : ℕ)*maxShift Z/((L : ℝ)*(L+maxShift Z))) := by
  exact ⟨actual_mass_nonneg A ha hab hAa hAb Z hZpos hL,
    actual_mass_bound A ha hab hAa hAb Z hZpos hL hLT,
    actual_mass_coarse A ha hab hAa hAb Z hZpos hL hLT⟩

end D5.S3.Arith.Robin.ActualRobinClockCoefficientMass

#print axioms D5.S3.Arith.Robin.ActualRobinClockCoefficientMass.actual_clock_coefficient_mass

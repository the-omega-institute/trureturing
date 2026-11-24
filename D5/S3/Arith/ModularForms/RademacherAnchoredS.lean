/- GID: D5/S3/Arith/ModularForms/RademacherAnchoredS
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: S invariance of the normalized rectangular Rademacher limit by anchoring at i. -/

import D5.S3.Arith.ModularForms.RademacherRectangularConvergence
import D5.S3.Arith.ModularForms.RademacherSLinearStrips

open Filter
open scoped BigOperators Topology UpperHalfPlane

namespace D5.S3.Arith.ModularForms.RademacherAnchoredS

open RademacherVacuum hiding PrimitiveRow remainderLimit tendstoUniformlyOn_remainderCutoff
open RademacherRectangularConvergence RademacherSLinearStrips

set_option autoImplicit false

noncomputable section

private def exponentConstant : ℂ := 2 * (Real.pi : ℂ) * Complex.I

private def polar (z : ℂ) : ℂ := Complex.exp (-exponentConstant * z)

private def idRow : ℤ × ℤ := (0, 1)

private def positiveRow (p : ℤ × ℤ) : Prop := 0 < p.1 ∧ Int.gcd p.1 p.2 = 1

private def rotate (p : ℤ × ℤ) : ℤ × ℤ :=
  if 0 < p.2 then (p.2, -p.1) else if p.2 < 0 then (-p.2, p.1) else idRow

private theorem first_eq_one {c : ℤ} (hc : 0 < c) (h : Int.gcd c 0 = 1) : c = 1 := by
  have hs : c.natAbs = 1 := by simpa using h
  omega

private theorem rotate_rotate (p : ℤ × ℤ) (hp : p = idRow ∨ positiveRow p) :
    rotate (rotate p) = p := by
  rcases hp with rfl | hp
  · norm_num [rotate, idRow]
  · rcases p with ⟨c, d⟩
    obtain ⟨hc, hprim⟩ := hp
    change 0 < c at hc
    change Int.gcd c d = 1 at hprim
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · simp [rotate, hd, not_lt_of_ge hd.le, hc]
    · rw [first_eq_one hc hprim]
      norm_num [rotate, idRow]
    · simp [rotate, hd, hc, not_lt_of_ge hc.le]

private def withIdentity (s : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := insert idRow s

private theorem mem_withIdentity_cutoff {N : ℕ} {c d : ℤ} :
    (c, d) ∈ withIdentity (cutoffPairs N) ↔
      (c = 0 ∧ d = 1) ∨ (0 < c ∧ c < (N : ℤ) ∧ |d| < (N : ℤ) ^ 2 ∧ Int.gcd c d = 1) := by
  simp only [withIdentity, Finset.mem_insert, idRow, Prod.mk.injEq, mem_cutoffPairs]

private theorem mem_withIdentity_transposed {N : ℕ} {c d : ℤ} :
    (c, d) ∈ withIdentity (transposedPairs N) ↔
      (c = 0 ∧ d = 1) ∨ (0 < c ∧ c < (N : ℤ) ^ 2 ∧ |d| < (N : ℤ) ∧ Int.gcd c d = 1) := by
  simp only [withIdentity, Finset.mem_insert, idRow, Prod.mk.injEq, mem_transposedPairs]

private theorem int_gcd_rotate_pos (c d : ℤ) : Int.gcd d (-c) = Int.gcd c d := by
  simp [Int.gcd, Nat.gcd_comm]

private theorem int_gcd_rotate_neg (c d : ℤ) : Int.gcd (-d) c = Int.gcd c d := by
  simp [Int.gcd, Nat.gcd_comm]

private theorem rotate_mem_cutoffs {N : ℕ} (hN : 2 ≤ N) :
    (∀ p ∈ withIdentity (cutoffPairs N), rotate p ∈ withIdentity (transposedPairs N)) ∧
      (∀ p ∈ withIdentity (transposedPairs N), rotate p ∈ withIdentity (cutoffPairs N)) := by
  have hN' : (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have hsq : (N : ℤ) ≤ (N : ℤ) ^ 2 := Int.le_self_sq _
  constructor
  · rintro ⟨c, d⟩ hp
    rcases mem_withIdentity_cutoff.mp hp with ⟨rfl, rfl⟩ | ⟨hc, hcN, hdN, hprim⟩
    · apply mem_withIdentity_transposed.mpr
      right
      change 0 < (1 : ℤ) ∧ (1 : ℤ) < (N : ℤ) ^ 2 ∧ |(0 : ℤ)| < (N : ℤ) ∧ Int.gcd 1 0 = 1
      norm_num
      omega
    · rcases lt_trichotomy d 0 with hd | rfl | hd
      · rw [abs_of_neg hd] at hdN
        rw [show rotate (c, d) = (-d, c) by simp [rotate, hd, not_lt_of_ge hd.le]]
        exact mem_withIdentity_transposed.mpr (Or.inr
          ⟨by omega, hdN, by simpa only [abs_of_pos hc] using hcN,
            (int_gcd_rotate_neg c d).trans hprim⟩)
      · simp [rotate, idRow, withIdentity]
      · rw [abs_of_pos hd] at hdN
        rw [show rotate (c, d) = (d, -c) by simp [rotate, hd]]
        exact mem_withIdentity_transposed.mpr (Or.inr
          ⟨hd, hdN, by simpa only [abs_neg, abs_of_pos hc] using hcN,
            (int_gcd_rotate_pos c d).trans hprim⟩)
  · rintro ⟨c, d⟩ hp
    rcases mem_withIdentity_transposed.mp hp with ⟨rfl, rfl⟩ | ⟨hc, hcN, hdN, hprim⟩
    · apply mem_withIdentity_cutoff.mpr
      right
      change 0 < (1 : ℤ) ∧ (1 : ℤ) < (N : ℤ) ∧ |(0 : ℤ)| < (N : ℤ) ^ 2 ∧ Int.gcd 1 0 = 1
      norm_num
      omega
    · rcases lt_trichotomy d 0 with hd | rfl | hd
      · rw [abs_of_neg hd] at hdN
        rw [show rotate (c, d) = (-d, c) by simp [rotate, hd, not_lt_of_ge hd.le]]
        exact mem_withIdentity_cutoff.mpr (Or.inr
          ⟨by omega, hdN, by simpa only [abs_of_pos hc] using hcN,
            (int_gcd_rotate_neg c d).trans hprim⟩)
      · simp [rotate, idRow, withIdentity]
      · rw [abs_of_pos hd] at hdN
        rw [show rotate (c, d) = (d, -c) by simp [rotate, hd]]
        exact mem_withIdentity_cutoff.mpr (Or.inr
          ⟨hd, hdN, by simpa only [abs_neg, abs_of_pos hc] using hcN,
            (int_gcd_rotate_pos c d).trans hprim⟩)

private def rowExponential (p : ℤ × ℤ) (τ : ℍ) : ℂ :=
  if p.1 = 0 then polar τ else
    vacuumPhase p.1 p.2 * Complex.exp (vacuumArgument p.1 p.2 τ)

private def anchoredRow (p : ℤ × ℤ) (τ : ℍ) : ℂ :=
  rowExponential p τ - rowExponential p UpperHalfPlane.I

private def fraction (a b c d : ℤ) (τ : ℍ) : ℂ :=
  ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / denominator c d τ

private theorem polar_add_int (z : ℂ) (n : ℤ) : polar (z + n) = polar z := by
  unfold polar
  rw [show -exponentConstant * (z + (n : ℂ)) =
      -exponentConstant * z + ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        simp only [Int.cast_neg, exponentConstant]
        ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A unimodular top row gives the row exponential. Its choice drops out by periodicity. -/
private theorem rowExponential_eq_fraction {a b c d : ℤ}
    (hp : (c = 0 ∧ d = 1) ∨ (0 < c ∧ Int.gcd c d = 1))
    (hdet : a * d - b * c = 1) (τ : ℍ) :
    rowExponential (c, d) τ = polar (fraction a b c d τ) := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨hc, hprim⟩
  · have ha : a = 1 := by simpa using hdet
    subst a
    simpa [rowExponential, fraction, denominator] using (polar_add_int (τ : ℂ) b).symm
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hD : denominator c d τ ≠ 0 := denominator_ne_zero hc d τ
  have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by exact_mod_cast hdet
  have ha' : d * a ≡ 1 [ZMOD c] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-b, by linear_combination -hdet⟩
  have hi := (inverseResidue_spec hc hprim).2.2
  have hmod : inverseResidue c d ≡ a [ZMOD c] := by
    calc
      inverseResidue c d ≡ inverseResidue c d * (d * a) [ZMOD c] := by
        simpa only [mul_one] using ha'.symm.mul_left (inverseResidue c d)
      _ ≡ a * (d * inverseResidue c d) [ZMOD c] := by
        rw [show inverseResidue c d * (d * a) = a * (d * inverseResidue c d) by ring]
      _ ≡ a [ZMOD c] := by simpa only [mul_one] using hi.mul_left a
  obtain ⟨n, hn⟩ := Int.modEq_iff_dvd.mp hmod
  have hnC : (a : ℂ) - (inverseResidue c d : ℂ) = (c : ℂ) * (n : ℂ) := by
    exact_mod_cast hn
  have hfrac : fraction a b c d τ =
      ((inverseResidue c d : ℂ) / (c : ℂ) - 1 / ((c : ℂ) * denominator c d τ)) +
        (n : ℂ) := by
    have hnum : ((a : ℂ) * (τ : ℂ) + (b : ℂ)) * (c : ℂ) =
        (a : ℂ) * denominator c d τ - 1 := by
      simp only [denominator]
      linear_combination -hdetC
    calc
      _ = ((a : ℂ) * denominator c d τ - 1) / ((c : ℂ) * denominator c d τ) := by
        rw [← hnum, fraction, mul_comm (c : ℂ) (denominator c d τ),
          mul_div_mul_right _ _ hcC]
      _ = (a : ℂ) / (c : ℂ) - 1 / ((c : ℂ) * denominator c d τ) := by
        rw [sub_div, mul_div_mul_right _ _ hD]
      _ = _ := by
        have ha : (a : ℂ) = (inverseResidue c d : ℂ) + (c : ℂ) * (n : ℂ) := by
          linear_combination hnC
        rw [ha]
        field_simp [hcC, hD]
        ring
  rw [hfrac, polar_add_int]
  simp only [rowExponential, ite_eq_right hc.ne', vacuumPhase, vacuumArgument,
    polar, exponentConstant, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, Complex.ofReal_intCast, ← Complex.exp_add]
  congr 1
  ring

private theorem coe_S (τ : ℍ) :
    ((ModularGroup.S • τ : ℍ) : ℂ) = (- (τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]

private theorem S_anchor : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [coe_S, UpperHalfPlane.coe_I, inv_neg, Complex.inv_I, neg_neg]

private theorem fraction_S (a b c d : ℤ) (τ : ℍ) :
    fraction a b c d (ModularGroup.S • τ) = fraction b (-a) d (-c) τ := by
  unfold fraction denominator
  simp only [coe_S, inv_neg, Int.cast_neg]
  let z : ℂ := τ
  have hz : z ≠ 0 := τ.ne_zero
  have h (x y : ℂ) : x * -z⁻¹ + y = (y * z + -x) * z⁻¹ := by
    field_simp [hz]
    ring
  rw [h, h, mul_div_mul_right _ _ (inv_ne_zero hz)]

private theorem fraction_neg (a b c d : ℤ) (τ : ℍ) :
    fraction (-a) (-b) (-c) (-d) τ = fraction a b c d τ := by
  unfold fraction denominator
  simp only [Int.cast_neg, neg_mul, ← neg_add, neg_div_neg_eq]

private theorem rowExponential_rotate (p : ℤ × ℤ) (hp : p = idRow ∨ positiveRow p) (τ : ℍ) :
    rowExponential p (ModularGroup.S • τ) = rowExponential (rotate p) τ := by
  rcases hp with rfl | hp
  · have h := fraction_S 1 0 0 1 τ
    norm_num only [neg_zero] at h
    change rowExponential (0, 1) (ModularGroup.S • τ) = rowExponential (1, 0) τ
    rw [rowExponential_eq_fraction (a := 1) (b := 0) (Or.inl ⟨rfl, rfl⟩) (by decide),
      rowExponential_eq_fraction (a := 0) (b := -1) (Or.inr ⟨by decide, by decide⟩) (by decide), h]
  · rcases p with ⟨c, d⟩
    obtain ⟨hc, hprim⟩ := hp
    change 0 < c at hc
    change Int.gcd c d = 1 at hprim
    have hbez : (1 : ℤ) = c * Int.gcdA c d + d * Int.gcdB c d := by
      simpa only [hprim, Nat.cast_one] using Int.gcd_eq_gcd_ab c d
    let a := Int.gcdB c d
    let b := -Int.gcdA c d
    have hdet : a * d - b * c = 1 := by
      dsimp [a, b]
      linear_combination -hbez
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · have hp' : Int.gcd (-d) c = 1 := (int_gcd_rotate_neg c d).trans hprim
      rw [show rotate (c, d) = (-d, c) by simp [rotate, hd, not_lt_of_ge hd.le],
        rowExponential_eq_fraction (Or.inr ⟨hc, hprim⟩) hdet, fraction_S,
        rowExponential_eq_fraction (a := -b) (b := a) (Or.inr ⟨by omega, hp'⟩)
          (by linear_combination hdet)]
      simpa only [neg_neg] using
        congrArg polar (fraction_neg b (-a) d (-c) τ).symm
    · obtain rfl := first_eq_one hc hprim
      change rowExponential (1, 0) (ModularGroup.S • τ) = rowExponential (0, 1) τ
      rw [rowExponential_eq_fraction (a := 0) (b := -1) (Or.inr ⟨by decide, by decide⟩) (by decide),
        fraction_S,
        rowExponential_eq_fraction (a := 1) (b := 0) (Or.inl ⟨rfl, rfl⟩) (by decide)]
      simpa only [neg_neg, neg_zero] using
        congrArg polar (fraction_neg 1 0 0 1 τ)
    · have hp' : Int.gcd d (-c) = 1 := (int_gcd_rotate_pos c d).trans hprim
      rw [show rotate (c, d) = (d, -c) by simp [rotate, hd],
        rowExponential_eq_fraction (Or.inr ⟨hc, hprim⟩) hdet, fraction_S,
        rowExponential_eq_fraction (a := b) (b := -a) (Or.inr ⟨hd, hp'⟩)
          (by linear_combination hdet)]

private theorem anchoredRow_rotate (p : ℤ × ℤ) (hp : p = idRow ∨ positiveRow p) (τ : ℍ) :
    anchoredRow p (ModularGroup.S • τ) = anchoredRow (rotate p) τ := by
  unfold anchoredRow
  rw [rowExponential_rotate p hp τ, ← rowExponential_rotate p hp UpperHalfPlane.I, S_anchor]

private theorem normalized_of_mem {s : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hs : ∀ q ∈ s, positiveRow q) (hp : p ∈ withIdentity s) : p = idRow ∨ positiveRow p :=
  (Finset.mem_insert.mp hp).imp id (hs p)

private theorem cutoff_positive (N : ℕ) (p : ℤ × ℤ) (hp : p ∈ cutoffPairs N) : positiveRow p := by
  rcases p with ⟨c, d⟩
  obtain ⟨hc, _, _, hcd⟩ := mem_cutoffPairs.mp hp
  exact ⟨hc, hcd⟩

private theorem transposed_positive (N : ℕ) (p : ℤ × ℤ) (hp : p ∈ transposedPairs N) :
    positiveRow p := by
  rcases p with ⟨c, d⟩
  obtain ⟨hc, _, _, hcd⟩ := mem_transposedPairs.mp hp
  exact ⟨hc, hcd⟩

private theorem sum_anchoredRow_S {N : ℕ} (hN : 2 ≤ N) (τ : ℍ) :
    (∑ p ∈ withIdentity (cutoffPairs N), anchoredRow p (ModularGroup.S • τ)) =
      ∑ p ∈ withIdentity (transposedPairs N), anchoredRow p τ := by
  obtain ⟨h₁, h₂⟩ := rotate_mem_cutoffs hN
  exact Finset.sum_nbij' rotate rotate h₁ h₂
    (fun p hp => rotate_rotate p (normalized_of_mem (cutoff_positive N) hp))
    (fun p hp => rotate_rotate p (normalized_of_mem (transposed_positive N) hp))
    (fun p hp => anchoredRow_rotate p (normalized_of_mem (cutoff_positive N) hp) τ)

/-- The quadratic remainders summed over a finite set of positive rows. -/
def quadraticSum (s : Finset (ℤ × ℤ)) (τ : ℍ) : ℂ :=
  ∑ p ∈ s, quadraticRemainder p.1 p.2 τ

private theorem sum_anchoredRow_eq {s : Finset (ℤ × ℤ)}
    (hs : ∀ p ∈ s, positiveRow p) (τ : ℍ) :
    (∑ p ∈ withIdentity s, anchoredRow p τ) =
      polar τ - polar Complex.I + anchoredLinearSum s τ +
        (quadraticSum s τ - quadraticSum s UpperHalfPlane.I) := by
  have hi : idRow ∉ s := by
    intro h
    have := (hs idRow h).1
    norm_num [idRow] at this
  have hsplit (p : ℤ × ℤ) (hp : p ∈ s) :
      anchoredRow p τ =
        (linearSummand p.1 p.2 τ - linearSummand p.1 p.2 UpperHalfPlane.I) +
        (quadraticRemainder p.1 p.2 τ - quadraticRemainder p.1 p.2 UpperHalfPlane.I) := by
    simp only [anchoredRow, rowExponential, ite_eq_right (hs p hp).1.ne',
      linearSummand, quadraticRemainder]
    ring
  rw [withIdentity, Finset.sum_insert hi, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hidentity : anchoredRow idRow τ = polar τ - polar Complex.I := rfl
  have hquadratic :
      (∑ p ∈ s, (quadraticRemainder p.1 p.2 τ - quadraticRemainder p.1 p.2 UpperHalfPlane.I)) =
        quadraticSum s τ - quadraticSum s UpperHalfPlane.I :=
    Finset.sum_sub_distrib _ _
  rw [hidentity, hquadratic]
  exact (add_assoc _ _ _).symm

private theorem original_anchoredCutoff_eq (N : ℕ) (τ : ℍ) :
    rademacherCutoff N τ - rademacherCutoff N UpperHalfPlane.I =
      ∑ p ∈ withIdentity (cutoffPairs N), anchoredRow p τ := by
  rw [sum_anchoredRow_eq (cutoff_positive N), rademacherCutoff_eq, rademacherCutoff_eq]
  simp only [anchoredLinearSum, Finset.sum_sub_distrib, quadraticSum, remainderCutoff,
    linearCutoff, polar, exponentConstant, Complex.ofReal_mul, Complex.ofReal_ofNat,
    UpperHalfPlane.coe_I, neg_mul]
  abel

private theorem cutoff_S_sub {N : ℕ} (hN : 2 ≤ N) (τ : ℍ) :
    rademacherCutoff N (ModularGroup.S • τ) - rademacherCutoff N τ =
      (anchoredLinearSum (transposedPairs N \ cutoffPairs N) τ -
        anchoredLinearSum (cutoffPairs N \ transposedPairs N) τ) +
      ((quadraticSum (transposedPairs N) τ - quadraticSum (transposedPairs N) UpperHalfPlane.I) -
        (remainderCutoff N τ - remainderCutoff N UpperHalfPlane.I)) := by
  have h := (original_anchoredCutoff_eq N (ModularGroup.S • τ)).trans (sum_anchoredRow_S hN τ)
  rw [sum_anchoredRow_eq (transposed_positive N)] at h
  have horig := original_anchoredCutoff_eq N τ
  rw [sum_anchoredRow_eq (cutoff_positive N)] at horig
  have hlin :
      anchoredLinearSum (transposedPairs N \ cutoffPairs N) τ -
          anchoredLinearSum (cutoffPairs N \ transposedPairs N) τ =
        anchoredLinearSum (transposedPairs N) τ - anchoredLinearSum (cutoffPairs N) τ := by
    unfold anchoredLinearSum
    exact Finset.sum_sdiff_sub_sum_sdiff
  have hrem (z : ℍ) : quadraticSum (cutoffPairs N) z = remainderCutoff N z := rfl
  rw [hrem τ, hrem UpperHalfPlane.I] at horig
  calc
    _ = (rademacherCutoff N (ModularGroup.S • τ) - rademacherCutoff N UpperHalfPlane.I) -
          (rademacherCutoff N τ - rademacherCutoff N UpperHalfPlane.I) := by abel
    _ = _ := by rw [h, horig, hlin]; abel

private def transposedRows (N : ℕ) : Finset PrimitiveRow :=
  (transposedPairs N).subtype (fun p => 0 < p.1 ∧ Int.gcd p.1 p.2 = 1)

private theorem tendsto_transposedRows : Tendsto transposedRows atTop atTop := by
  refine tendsto_atTop.2 (fun s => ?_)
  have h : ∀ᶠ N in atTop, ∀ p ∈ s, p ∈ transposedRows N :=
    s.eventually_all.2 (fun p _ => by
      rcases p with ⟨⟨c, d⟩, hc, hprim⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (max c |d|)
      filter_upwards [eventually_ge_atTop n] with N hN
      have hcast : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      have hmax := hn.trans_le hcast
      apply Finset.mem_subtype.mpr
      exact mem_transposedPairs.mpr
        ⟨hc, ((le_max_left _ _).trans_lt hmax).trans_le (Int.le_self_sq _),
          (le_max_right _ _).trans_lt hmax, hprim⟩)
  exact h.mono (fun _ hN p hp => hN p hp)

/-- The transposed remainder has the same compact-uniform limit as the original remainder. -/
theorem tendstoUniformlyOn_transposedRemainder {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N => quadraticSum (transposedPairs N)) remainderLimit atTop K := by
  obtain ⟨C, _, hsum, hbound⟩ := quadraticRemainder_compact_majorant hK
  have hM := tendstoUniformlyOn_tsum
    (f := fun (p : PrimitiveRow) (τ : ℍ) => quadraticRemainder p.val.1 p.val.2 τ)
    (s := K) (hsum.subtype positiveRow)
    (fun p τ hτ => hbound τ hτ p.val.1 p.val.2 p.property.1)
  have hcut : TendstoUniformlyOn
      (fun N τ => ∑ p ∈ transposedRows N, quadraticRemainder p.val.1 p.val.2 τ)
      remainderLimit atTop K :=
    fun u hu => tendsto_transposedRows.eventually (hM u hu)
  apply hcut.congr
  refine Eventually.of_forall (fun N τ _ => ?_)
  exact Finset.sum_subtype_of_mem (fun p : ℤ × ℤ => quadraticRemainder p.1 p.2 τ)
    (fun p hp => transposed_positive N p hp)

/-- The anchored quadratic difference vanishes uniformly on compact sets. -/
theorem tendstoUniformlyOn_anchoredRemainder_difference {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N τ =>
        (quadraticSum (transposedPairs N) τ - quadraticSum (transposedPairs N) UpperHalfPlane.I) -
          (remainderCutoff N τ - remainderCutoff N UpperHalfPlane.I))
      (fun _ => 0) atTop K := by
  have hKI : IsCompact (insert UpperHalfPlane.I K) := hK.insert _
  have hsub : K ⊆ insert UpperHalfPlane.I K := fun _ h => Set.mem_insert_of_mem _ h
  have hi : UpperHalfPlane.I ∈ insert UpperHalfPlane.I K := Set.mem_insert _ _
  have ht := tendstoUniformlyOn_transposedRemainder hKI
  have hr := tendstoUniformlyOn_remainderCutoff hKI
  have ha := (ht.mono hsub).sub ((ht.tendsto_at hi).tendstoUniformlyOn_const K)
  have hb := (hr.mono hsub).sub ((hr.tendsto_at hi).tendstoUniformlyOn_const K)
  exact (ha.sub hb).congr_right fun τ _ => sub_self _

/-- Reindexing by S changes the analytic cutoff by a compact-uniform vanishing error. -/
theorem tendstoUniformlyOn_rademacherCutoff_S_sub {K : Set ℍ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N τ => rademacherCutoff N (ModularGroup.S • τ) - rademacherCutoff N τ)
      (fun _ => 0) atTop K := by
  obtain ⟨hshort, hlong⟩ := tendstoUniformlyOn_anchoredLinearSum_strips hK
  have h := (hshort.sub hlong).add (tendstoUniformlyOn_anchoredRemainder_difference hK)
  refine (h.congr ?_).congr_right ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN τ _
    exact (cutoff_S_sub hN τ).symm
  · intro τ _
    simp

/-- The actual normalized rectangular Rademacher limit is invariant under S. -/
theorem rademacherLimit_S_smul (τ : ℍ) :
    rademacherLimit (ModularGroup.S • τ) = rademacherLimit τ := by
  have hlimit (z : ℍ) := (tendstoUniformlyOn_rademacherCutoff_sub_twelve
    (isCompact_singleton (x := z))).tendsto_at (Set.mem_singleton z)
  have hs := (hlimit (ModularGroup.S • τ)).sub (hlimit τ)
  have h₁ : Tendsto
      (fun N => rademacherCutoff N (ModularGroup.S • τ) - rademacherCutoff N τ)
      atTop (𝓝 (rademacherLimit (ModularGroup.S • τ) - rademacherLimit τ)) := by
    have heq (a b : ℂ) : (a - 12) - (b - 12) = a - b := by abel
    simpa only [heq] using hs
  have h₀ := (tendstoUniformlyOn_rademacherCutoff_S_sub
    (isCompact_singleton (x := τ))).tendsto_at (Set.mem_singleton τ)
  exact sub_eq_zero.mp (tendsto_nhds_unique h₁ h₀)

end

end D5.S3.Arith.ModularForms.RademacherAnchoredS

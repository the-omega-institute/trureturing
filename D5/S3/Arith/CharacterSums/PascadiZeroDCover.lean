/- GID: D5/S3/Arith/CharacterSums/PascadiZeroDCover
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiZeroDCover
   mirror-E: none(waiver:zero-dixon-root-relevant-cover)
   anchors: []
   utility: none
   digest: Zero Dixon singular pencils have a root-relevant factor cover at sixth height. -/

import D5.S3.Arith.CharacterSums.PascadiZeroDQuadratic

/-! Localization keeps every irreducible factor root-relevant. The constant
complement transfer and mixed resultant argument are reused from the actual
seventh-height cover, with zero Dixon residuals and the sixth-height quadratic
elimination replacing its seventh-height hypotheses. No rank or nonalignment
condition is imposed. -/

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

open private padded_rational_resultant_zero localized_common_of_constant_complement from
  D5.S3.Arith.CharacterSums.PascadiSeventhHeightCover
open private bracket from D5.S3.Arith.CharacterSums.PascadiPrimeCubeSingularCover

/-- All nonzero-reduction singular pencils with zero actual triple Dixon
residuals admit at most three primitive irreducible root-relevant factors at
sixth height. The chosen reference and every covered pencil use the actual
LQ carrier. Constant baseline leading data and zero baseline resultant are
included without a rank assumption or a supplied factor cover. -/
theorem actual_zero_dixon_singular_factor_cover {ι : Type*}
    (l m q r s : Option ι → ℤ) (i₀ : ι) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (I J H : ℝ) (hJI : J ≤ I) (hJ : 1 ≤ J) (hH : 1 ≤ H)
    (hl : ∀ i, |(l i : ℝ)| ≤ 3 * I) (hm : ∀ i, |(m i : ℝ)| ≤ 3 * J)
    (hq : ∀ i, |(q i : ℝ)| ≤ I ^ 2)
    (hr : ∀ i, |(r i : ℝ)| ≤ 2 * I * J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J ^ 2)
    (hunit : IsUnit (((l none + b * m none : ℤ) : ZMod p)))
    (hred : ∀ i, (familyPolynomial l m q r s i).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hdeg : ∀ i, (familyPolynomial l m q r s i).natDegree ≤ 3)
    (hcoeff : ∀ i, ∀ j ≤ (familyPolynomial l m q r s i).natDegree,
      |((familyPolynomial l m q r s i).coeff j : ℝ)| ≤ H * I ^ (3 - j) * J ^ j)
    (hroot : ∀ i, (p : ℤ) ^ 3 ∣ (familyPolynomial l m q r s i).eval b)
    (hderiv : ∀ i, (p : ℤ) ∣ (familyPolynomial l m q r s i).derivative.eval b)
    (hzero : ∀ i j, residual
      ![l none, l (some i), l (some j)] ![m none, m (some i), m (some j)]
      ![q none, q (some i), q (some j)] ![r none, r (some i), r (some j)]
      ![s none, s (some i), s (some j)] = 0)
    (hgap : max 6804 (24 * (8 * H) ^ 4) * (I * J) ^ 6 < (p : ℝ) ^ 5) :
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧ f ∣ familyPolynomial l m q r s i₀ ∧
        ((f.eval b : ℤ) : ZMod p) = 0 ∧ f.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ i, ∃ f ∈ F, f ∣ familyPolynomial l m q r s i) := by
  classical
  have hI : 1 ≤ I := hJ.trans hJI
  have hgapQ : 6804 * I ^ 6 * J ^ 4 < (p : ℝ) ^ 5 := by
    calc
      _ ≤ 6804 * (I * J) ^ 6 := by
        rw [mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hJ (by decide : 4 ≤ 6))
          (by positivity : 0 ≤ 6804 * I ^ 6)
      _ ≤ max 6804 (24 * (8 * H) ^ 4) * (I * J) ^ 6 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ < _ := hgap
  have hgapMixed : 24 * (8 * H) ^ 4 * (I * J) ^ 6 < (p : ℝ) ^ 5 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans_lt hgap
  let P := familyPolynomial l m q r s
  have hlocal := fun i => localized_factor_cube (P i) p b (hred i) (hdeg i)
    (hroot i) (hderiv i) I J H hJI hJ (by linarith) (hcoeff i)
  choose R U hRU hprim hUnit hRed hRoot hDeriv hDeg hRel hCoeff using hlocal
  have hPn (i : ι) : P i ≠ 0 := by
    intro h
    apply hred i
    change (P i).map (Int.castRingHom (ZMod p)) = 0
    rw [h, Polynomial.map_zero]
  have hUn (i : ι) : U i ≠ 0 := by
    intro hz
    apply hPn i
    rw [hRU i, hz, mul_zero]
  have hOriginalDeg (i : ι) : (P i).natDegree = 2 ∨ (P i).natDegree = 3 := by
    have hd := natDegree_le_of_dvd ⟨U i, hRU i⟩ (hPn i)
    have hr := hDeg i
    have hp : (P i).natDegree ≤ 3 := hdeg i
    omega
  have hComplement (i : ι) (heq : (P i).natDegree = (R i).natDegree) :
      (U i).natDegree = 0 := by
    have hh := natDegree_mul (hprim i).ne_zero (hUn i)
    rw [← hRU i, heq] at hh
    omega
  have hres (i j : ι) : (P i).resultant (P j) 3 3 = 0 := by
    change (pair ![l none, l (some i), l (some j)]
      ![m none, m (some i), m (some j)] ![q none, q (some i), q (some j)]
      ![r none, r (some i), r (some j)] ![s none, s (some i), s (some j)] 1).resultant
      (pair ![l none, l (some i), l (some j)]
      ![m none, m (some i), m (some j)] ![q none, q (some i), q (some j)]
      ![r none, r (some i), r (some j)] ![s none, s (some i), s (some j)] 2) 3 3 = 0
    rw [actual_residual_resultant, hzero i j, mul_zero]
  have hquadratic (i j : ι) (hi : (P i).natDegree = 2) (hj : (P j).natDegree = 2) :
      (P i).resultant (P j) 2 2 = 0 := by
    let L : Fin 3 → ℤ := ![l none, l (some i), l (some j)]
    let M : Fin 3 → ℤ := ![m none, m (some i), m (some j)]
    let Q : Fin 3 → ℤ := ![q none, q (some i), q (some j)]
    let A : Fin 3 → ℤ := ![r none, r (some i), r (some j)]
    let B : Fin 3 → ℤ := ![s none, s (some i), s (some j)]
    exact zero_dixon_quadratic_resultant_zero L M Q A B p b I J hI hJ
      (by intro k; fin_cases k <;> simp [L, hl])
      (by intro k; fin_cases k <;> simp [M, hm])
      (by intro k; fin_cases k <;> simp [Q, hq])
      (by intro k; fin_cases k <;> simp [A, hr])
      (by intro k; fin_cases k <;> simp [B, hs]) hi hj
      (hred i) (hroot i) (hroot j) (hderiv i) (hderiv j)
      hunit (hzero i j) hgapQ
  have inj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hreverse (i j : ι)
      (hz : ((R j).map (Int.castRingHom ℚ)).resultant ((R i).map (Int.castRingHom ℚ)) = 0) :
      ((R i).map (Int.castRingHom ℚ)).resultant ((R j).map (Int.castRingHom ℚ)) = 0 := by
    apply Polynomial.resultant_eq_zero_iff.mpr
    refine ⟨Or.inl ((Polynomial.map_ne_zero_iff inj).mpr (hprim i).ne_zero), ?_⟩
    intro hc
    exact (Polynomial.resultant_eq_zero_iff.mp hz).2 hc.symm
  have hmixed (i j : ι) (hPi : (P i).natDegree = 3)
      (hi : (R i).natDegree = 2) (hj : (R j).natDegree = 2) :
      ((R i).map (Int.castRingHom ℚ)).resultant ((R j).map (Int.castRingHom ℚ)) = 0 := by
    have hdiv := quadratic_resultant_dvd_fifth (R i) (R j) b (p : ℤ) hi hj
      (hRoot i) (hRoot j) (hDeriv i) (hDeriv j)
    rw [hi, hj] at hdiv
    have hbnd := cubic_quadratic_mixed_resultant_height (P i) (R i) (U i) (R j)
      (hRU i) hPi hi hj I J H hJI hJ (by linarith) (hcoeff i) (hCoeff j)
    have hz : (R i).resultant (R j) 2 2 = 0 := by
      by_contra hn
      have hv := Int.le_abs_of_dvd hn hdiv
      have hv' : (p : ℝ) ^ 5 ≤ |(((R i).resultant (R j) 2 2 : ℤ) : ℝ)| := by
        exact_mod_cast hv
      exact (not_lt_of_ge hv') (hbnd.trans_lt hgapMixed)
    simp only [natDegree_map_eq_of_injective inj, hi, hj, resultant_map_map, hz, map_zero]
  have hresR (i j : ι) : ((R i).map (Int.castRingHom ℚ)).resultant
      ((R j).map (Int.castRingHom ℚ)) = 0 := by
    by_cases hi : (R i).natDegree = 3
    · have hPi : (P i).natDegree = 3 := by
        have hr := natDegree_le_of_dvd ⟨U i, hRU i⟩ (hPn i)
        have hp : (P i).natDegree ≤ 3 := hdeg i
        omega
      exact localized_common_of_constant_complement (P i) (P j) (R i) (U i) (R j) (U j)
        p b (hPn i) (hRU i) (hRU j) (hprim i)
        (hComplement i (hPi.trans hi.symm)) (hRel i) (hUnit j)
        (padded_rational_resultant_zero (P i) (P j) 3 (hPn i) hPi (hdeg j) (hres i j))
    by_cases hj : (R j).natDegree = 3
    · apply hreverse i j
      have hPj : (P j).natDegree = 3 := by
        have hr := natDegree_le_of_dvd ⟨U j, hRU j⟩ (hPn j)
        have hp : (P j).natDegree ≤ 3 := hdeg j
        omega
      exact localized_common_of_constant_complement (P j) (P i) (R j) (U j) (R i) (U i)
        p b (hPn j) (hRU j) (hRU i) (hprim j)
        (hComplement j (hPj.trans hj.symm)) (hRel j) (hUnit i)
        (padded_rational_resultant_zero (P j) (P i) 3 (hPn j) hPj (hdeg i) (hres j i))
    have hd : (R i).natDegree = 2 := (hDeg i).resolve_right hi
    have he : (R j).natDegree = 2 := (hDeg j).resolve_right hj
    by_cases hPi : (P i).natDegree = 3
    · exact hmixed i j hPi hd he
    by_cases hPj : (P j).natDegree = 3
    · exact hreverse i j (hmixed j i hPj he hd)
    have hPi2 := (hOriginalDeg i).resolve_right hPi
    have hPj2 := (hOriginalDeg j).resolve_right hPj
    exact localized_common_of_constant_complement (P i) (P j) (R i) (U i) (R j) (U j)
      p b (hPn i) (hRU i) (hRU j) (hprim i)
      (hComplement i (hPi2.trans hd.symm)) (hRel i) (hUnit j)
      (padded_rational_resultant_zero (P i) (P j) 2 (hPn i) hPi2 hPj2.le
        (hquadratic i j hPi2 hPj2))
  let Fq := (normalizedFactors ((R i₀).map (Int.castRingHom ℚ))).toFinset
  have hFq (t : ℚ[X]) (ht : t ∈ Fq) :
      Irreducible t ∧ t ∣ (R i₀).map (Int.castRingHom ℚ) :=
    ⟨irreducible_of_normalized_factor t (Multiset.mem_toFinset.mp ht),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp ht)⟩
  have hcard : Fq.card ≤ 3 := by
    have hc := rational_factor_card_le ((R i₀).map (Int.castRingHom ℚ))
      ((Polynomial.map_ne_zero_iff inj).mpr (hprim i₀).ne_zero)
    rw [natDegree_map_eq_of_injective inj] at hc
    exact hc.trans (by have := hDeg i₀; omega)
  have hlift := fun t : {t // t ∈ Fq} => lift_primitive_rational_factor (R i₀) (hprim i₀) t.val
    (hFq t.val t.property).1 (hFq t.val t.property).2
  choose L hLirr hLprim hLdvd hLassoc using hlift
  refine ⟨Fq.attach.image L, Finset.card_image_le.trans (by simpa using hcard), ?_, ?_⟩
  · intro f hf
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    refine ⟨hLirr t, hLprim t, (hLdvd t).trans ⟨U i₀, hRU i₀⟩,
      hRel i₀ _ (hLirr t) (hLdvd t), ?_⟩
    intro hz
    obtain ⟨V, hV⟩ := hLdvd t
    apply hRed i₀
    rw [hV, Polynomial.map_mul, hz, zero_mul]
  · intro i
    obtain ⟨t, ht, _, _, htR⟩ := rational_common_factor_of_resultant_zero
      ((R i₀).map (Int.castRingHom ℚ)) ((R i).map (Int.castRingHom ℚ))
      ((Polynomial.map_ne_zero_iff inj).mpr (hprim i₀).ne_zero) (hresR i₀ i)
    let x : {t // t ∈ Fq} := ⟨t, ht⟩
    refine ⟨L x, Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hq : (L x).map (Int.castRingHom ℚ) ∣ (R i).map (Int.castRingHom ℚ) :=
      (hLassoc x).symm.dvd.trans htR
    have hz := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (hLprim x)).mpr hq
    exact hz.trans ⟨U i, hRU i⟩

-- A rank-one L projection and a zero leading baseline yield repeated T².
-- All assumptions of the cover are checked at I=J=H=1, p=37, b=0.
example :
    let l : Option (Fin 2) → ℤ := fun _ => 1
    let m : Option (Fin 2) → ℤ := fun _ => 0
    let q : Option (Fin 2) → ℤ := fun _ => 1
    let r : Option (Fin 2) → ℤ := fun _ => 0
    let s : Option (Fin 2) → ℤ := fun i => match i with | none => 0 | some _ => 1
    m none = 0 ∧ s none = 0 ∧
      (∀ i, familyPolynomial l m q r s i = (X : ℤ[X]) ^ 2) ∧
      ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
        (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧
          f ∣ familyPolynomial l m q r s 0 ∧ ((f.eval 0 : ℤ) : ZMod 37) = 0 ∧
          f.map (Int.castRingHom (ZMod 37)) ≠ 0) ∧
        (∀ i, ∃ f ∈ F, f ∣ familyPolynomial l m q r s i) := by
  dsimp only
  let l : Option (Fin 2) → ℤ := fun _ => 1
  let m : Option (Fin 2) → ℤ := fun _ => 0
  let q : Option (Fin 2) → ℤ := fun _ => 1
  let r : Option (Fin 2) → ℤ := fun _ => 0
  let s : Option (Fin 2) → ℤ := fun i => match i with | none => 0 | some _ => 1
  have hP (i : Fin 2) : familyPolynomial l m q r s i = (X : ℤ[X]) ^ 2 := by
    simp [familyPolynomial, linear, quadratic, l, m, q, r, s]
  refine ⟨rfl, rfl, hP, ?_⟩
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply actual_zero_dixon_singular_factor_cover l m q r s 0 37 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num)
  · intro i; norm_num [l]
  · intro i; norm_num [m]
  · intro i; norm_num [q]
  · intro i; norm_num [r]
  · intro i; cases i <;> norm_num [s]
  · norm_num [l, m]
  · intro i; rw [hP i]; simp
  · intro i; rw [hP i]; norm_num
  · intro i j hj
    rw [hP i] at hj ⊢
    norm_num at hj
    interval_cases j <;> norm_num
  · intro i; rw [hP i]; simp
  · intro i; rw [hP i]; simp
  · intro i j
    simp [residual, residualMatrix, bracket, Matrix.det_fin_three, l, m, q, r, s]
  · norm_num

end

end D5.S3.Arith.CharacterSums.PrimeCube

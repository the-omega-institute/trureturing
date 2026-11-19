/- GID: D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSeventhHeightCover
   mirror-E: none(waiver:actual-prime-cube-factor-cover)
   anchors: []
   utility: none
   digest: The actual prime-cube singular pencil has a factor cover using only seventh height. -/

import D5.S3.Arith.CharacterSums.PascadiActualQuadraticResultant
import D5.S3.Arith.CharacterSums.PascadiCubicQuadraticHeight

/-! The original prime-cube cover used an eighth-weight bound for two localized
quadratic factors. Here two actual quadratic pencils use their structural seventh-weight
elimination; a quadratic factor of a genuine cubic uses its stronger sixth-weight mixed
resultant bound. The cubic localized-factor branch retains the existing residual proof.
The finite root-relevant cover construction is adapted from actual_singular_factor_cover.
This does not itself assert a larger final tuple-count range. -/

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.PrimeCube

noncomputable section

private theorem padded_rational_resultant_zero (P Q : ℤ[X]) (n : ℕ)
    (hP : P ≠ 0) (hdP : P.natDegree = n) (hdQ : Q.natDegree ≤ n)
    (hz : P.resultant Q n n = 0) :
    (P.map (Int.castRingHom ℚ)).resultant (Q.map (Int.castRingHom ℚ)) = 0 := by
  have inj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hPQ : P.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff inj).mpr hP
  have hqdeg : (Q.map (Int.castRingHom ℚ)).natDegree ≤ n := by
    simpa only [natDegree_map_eq_of_injective inj] using hdQ
  have hqpd : (P.map (Int.castRingHom ℚ)).natDegree = n := by
    simpa only [natDegree_map_eq_of_injective inj] using hdP
  have heq := Polynomial.resultant_add_right_deg
    (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) n
    (Q.map (Int.castRingHom ℚ)).natDegree
    (n - (Q.map (Int.castRingHom ℚ)).natDegree) le_rfl
  rw [Nat.add_sub_of_le hqdeg] at heq
  have hzQ : (P.map (Int.castRingHom ℚ)).resultant
      (Q.map (Int.castRingHom ℚ)) n n = 0 := by
    rw [resultant_map_map, hz, map_zero]
  rw [hzQ] at heq
  have hlc : (P.map (Int.castRingHom ℚ)).coeff n ≠ 0 := by
    rw [← hqpd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hPQ
  rw [hqpd]
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hlc)

private theorem localized_common_of_constant_complement
    (P Q R U S V : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P ≠ 0) (hPU : P = R * U) (hQV : Q = S * V)
    (hR : R.IsPrimitive) (hUd : U.natDegree = 0)
    (hrel : ∀ f : ℤ[X], Irreducible f → f ∣ R → ((f.eval b : ℤ) : ZMod p) = 0)
    (hV : IsUnit ((V.eval b : ℤ) : ZMod p))
    (hz : (P.map (Int.castRingHom ℚ)).resultant (Q.map (Int.castRingHom ℚ)) = 0) :
    (R.map (Int.castRingHom ℚ)).resultant (S.map (Int.castRingHom ℚ)) = 0 := by
  have hU : U ≠ 0 := by intro h; simp [hPU, h] at hP
  have inj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hPQ : P.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff inj).mpr hP
  have hUQ : U.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff inj).mpr hU
  have hu : IsUnit (U.map (Int.castRingHom ℚ)) := by
    apply Polynomial.isUnit_iff_degree_eq_zero.mpr
    rw [degree_eq_natDegree hUQ, natDegree_map_eq_of_injective inj, hUd]
    rfl
  obtain ⟨t, _, ht, htP, htQ⟩ := rational_common_factor_of_resultant_zero
    (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) hPQ hz
  have htR : t ∣ R.map (Int.castRingHom ℚ) := by
    rw [hPU, Polynomial.map_mul] at htP
    rcases (irreducible_iff_prime.mp ht).dvd_mul.mp htP with h | h
    · exact h
    · exact False.elim (ht.not_isUnit (isUnit_iff_dvd_one.mpr (h.trans hu.dvd)))
  obtain ⟨f, hfi, hfp, hfR, ha⟩ := lift_primitive_rational_factor R hR t ht htR
  have hfQ : f ∣ Q := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f Q hfp).mpr
    (ha.symm.dvd.trans htQ)
  have hfS : f ∣ S := by
    rw [hQV] at hfQ
    rcases (irreducible_iff_prime.mp hfi).dvd_mul.mp hfQ with h | h
    · exact h
    · obtain ⟨W, hW⟩ := h
      have he := hrel f hfi hfR
      have hvz : ((V.eval b : ℤ) : ZMod p) = 0 := by
        rw [hW, eval_mul, Int.cast_mul, he, zero_mul]
      exact False.elim (hV.ne_zero hvz)
  apply Polynomial.resultant_eq_zero_iff.mpr
  refine ⟨Or.inl ((Polynomial.map_ne_zero_iff inj).mpr hR.ne_zero), ?_⟩
  intro hc
  exact ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfp).mp hfi).not_isUnit
    (hc.isUnit_of_dvd' (Polynomial.map_dvd (Int.castRingHom ℚ) hfR)
      (Polynomial.map_dvd (Int.castRingHom ℚ) hfS))

private theorem singular_quadratic_leading_unit (P : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (b : ℤ) (hred : P.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hd : P.natDegree = 2) (hv : (p : ℤ) ^ 3 ∣ P.eval b)
    (hderiv : (p : ℤ) ∣ P.derivative.eval b) : ((P.coeff 2 : ℤ) : ZMod p) ≠ 0 := by
  let f := P.map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := hred
  have hvp : (p : ℤ) ∣ P.eval b := by
    simpa only [pow_one] using (pow_dvd_pow (p : ℤ) (by decide : 1 ≤ 3)).trans hv
  have hr0 : f.IsRoot (b : ZMod p) := by
    simpa [f, Polynomial.IsRoot, Polynomial.eval_intCast_map] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (P.eval b) p).mpr hvp
  have hr1 : f.derivative.IsRoot (b : ZMod p) := by
    simpa [f, Polynomial.IsRoot, Polynomial.derivative_map, Polynomial.eval_intCast_map] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (P.derivative.eval b) p).mpr hderiv
  have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨hr0, hr1⟩
  have hdn := Polynomial.natDegree_le_of_dvd (Polynomial.pow_rootMultiplicity_dvd f (b : ZMod p)) hf
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdn
  have hfdeg : f.natDegree = 2 := by
    have hle : f.natDegree ≤ P.natDegree := natDegree_map_le
    omega
  have hn : f.coeff 2 ≠ 0 := by
    rw [← hfdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf
  simpa [f] using hn

/-- The actual prime-cube singular pencil admits at most three primitive,
root-relevant irreducible factors under one seventh-weight height condition.
The coefficient bounds are the literal LQ bounds; no factor-height hypothesis
is substituted for the actual pencil structure. -/
theorem actual_seventh_height_singular_factor_cover {ι : Type*}
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
    (hgap : max (10368 * (3 : ℝ) ^ 9) (max 14256 (24 * (8 * H) ^ 4)) * (I * J) ^ 7 <
      (p : ℝ) ^ 5) :
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧ f ∣ familyPolynomial l m q r s i₀ ∧
        ((f.eval b : ℤ) : ZMod p) = 0 ∧ f.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ i, ∃ f ∈ F, f ∣ familyPolynomial l m q r s i) := by
  classical
  have hI : 1 ≤ I := hJ.trans hJI
  have hB : 1 ≤ I * J := one_le_mul_of_one_le_of_one_le hI hJ
  have hgapR : 10368 * (3 : ℝ) ^ 9 * (I * J) ^ 7 < (p : ℝ) ^ 5 := by
    calc
      _ ≤ max (10368 * (3 : ℝ) ^ 9) (max 14256 (24 * (8 * H) ^ 4)) * (I * J) ^ 7 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ < _ := hgap
  have hgapQ : 14256 * (I * J) ^ 7 < (p : ℝ) ^ 5 := by
    calc
      _ ≤ max (10368 * (3 : ℝ) ^ 9) (max 14256 (24 * (8 * H) ^ 4)) * (I * J) ^ 7 :=
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
      _ < _ := hgap
  have hgapMixed : 24 * (8 * H) ^ 4 * (I * J) ^ 6 < (p : ℝ) ^ 5 := by
    calc
      _ ≤ 24 * (8 * H) ^ 4 * (I * J) ^ 7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by decide : 6 ≤ 7)) (by positivity)
      _ ≤ max (10368 * (3 : ℝ) ^ 9) (max 14256 (24 * (8 * H) ^ 4)) * (I * J) ^ 7 :=
        mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      _ < _ := hgap
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
    let L : Fin 3 → ℤ := ![l none, l (some i), l (some j)]
    let M : Fin 3 → ℤ := ![m none, m (some i), m (some j)]
    let Q : Fin 3 → ℤ := ![q none, q (some i), q (some j)]
    let A : Fin 3 → ℤ := ![r none, r (some i), r (some j)]
    let B : Fin 3 → ℤ := ![s none, s (some i), s (some j)]
    exact actual_pair_resultant_zero L M Q A B p b I J 3 hI hJ (by norm_num)
      (by intro k; fin_cases k <;> simp [L, hl])
      (by intro k; fin_cases k <;> simp [M, hm])
      (by intro k; fin_cases k <;> simp [Q]; all_goals exact (hq _).trans (by nlinarith [sq_nonneg I]))
      (by intro k; fin_cases k <;> simp [A]; all_goals exact (hr _).trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ I) (by linarith : 0 ≤ J)]))
      (by intro k; fin_cases k <;> simp [B]; all_goals exact (hs _).trans (by nlinarith [sq_nonneg J]))
      hunit (hroot i) (hroot j) (hderiv i) (hderiv j) hgapR
  have hquadratic (i j : ι) (hi : (P i).natDegree = 2) (hj : (P j).natDegree = 2) :
      (P i).resultant (P j) 2 2 = 0 := by
    let L : Fin 3 → ℤ := ![l none, l (some i), l (some j)]
    let M : Fin 3 → ℤ := ![m none, m (some i), m (some j)]
    let Q : Fin 3 → ℤ := ![q none, q (some i), q (some j)]
    let A : Fin 3 → ℤ := ![r none, r (some i), r (some j)]
    let B : Fin 3 → ℤ := ![s none, s (some i), s (some j)]
    exact actual_quadratic_pair_resultant_zero L M Q A B p b I J hI hJ
      (by intro k; fin_cases k <;> simp [L, hl])
      (by intro k; fin_cases k <;> simp [M, hm])
      (by intro k; fin_cases k <;> simp [Q, hq])
      (by intro k; fin_cases k <;> simp [A, hr])
      (by intro k; fin_cases k <;> simp [B, hs]) hi hj
      (hroot i) (hroot j) (hderiv i) (hderiv j)
      (singular_quadratic_leading_unit (P i) p b (hred i) hi (hroot i) (hderiv i))
      hunit hgapQ
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

end

end D5.S3.Arith.CharacterSums.PrimeCube

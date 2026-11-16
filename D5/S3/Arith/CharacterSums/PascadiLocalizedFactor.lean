/- GID: D5/S3/Arith/CharacterSums/PascadiLocalizedFactor
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiLocalizedFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive local factors retain the actual residue root and weighted height. -/
/- Provenance: integrated from the completed 2026-11-16 singular-cover research archive.
Original source SHA256: 3f4fdb232cd07f365c10aa8b032bf2f35396742aa6cbc4a51772a83494541b9f.
Canonical integration preserves the archived proofs; see the Pascadi Library note. -/

import D5.S3.Arith.CharacterSums.PascadiSingularFactorCover
import D5.S3.Arith.AbsoluteValues.Heights.Gelfond
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-! Primitive root selection and coefficient bounds for actual cubic factors. -/

open Polynomial UniqueFactorizationMonoid
open scoped BigOperators
namespace D5.S3.Arith.CharacterSums
noncomputable section

private theorem primitive_root_split (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ∃ R U : ℤ[X], P = R * U ∧ R.IsPrimitive ∧
      ((U.eval b : ℤ) : ZMod p) ≠ 0 ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ R → ((q.eval b : ℤ) : ZMod p) = 0) := by
  classical
  let ev : ℤ[X] →+* ZMod p :=
    (Polynomial.evalRingHom (b : ZMod p)).comp (Polynomial.mapRingHom (Int.castRingHom _))
  have hev (f : ℤ[X]) : ev f = ((f.eval b : ℤ) : ZMod p) := by
    simp [ev, Polynomial.eval_intCast_map]
  let M := normalizedFactors P.primPart
  let A := M.filter (fun f => ev f = 0)
  let B := M.filter (fun f => ev f ≠ 0)
  have hsplit : A + B = M := Multiset.filter_add_not _ _
  have hPP : P.primPart ≠ 0 := P.primPart_ne_zero
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hPP
  change M.prod * (u : ℤ[X]) = P.primPart at hu
  have hAB : P.primPart = A.prod * (B.prod * (u : ℤ[X])) := by
    rw [← hu, ← hsplit, Multiset.prod_add]; ring
  have hdiv : A.prod ∣ P.primPart := ⟨_, hAB⟩
  have hc : ev (C P.content) ≠ 0 := by
    intro hz
    apply hP
    rw [P.eq_C_content_mul_primPart, Polynomial.map_mul]
    have hz' : (P.content : ZMod p) = 0 := by simpa [ev] using hz
    rw [Polynomial.map_C]
    change Polynomial.C ((P.content : ℤ) : ZMod p) * _ = 0
    rw [hz', Polynomial.C_0, zero_mul]
  have hB : ev B.prod ≠ 0 := by
    rw [map_multiset_prod]
    apply Multiset.prod_ne_zero
    intro hx
    obtain ⟨f, hf, hz⟩ := Multiset.mem_map.mp hx
    exact (Multiset.mem_filter.mp hf).2 hz
  have hu0 : ev (u : ℤ[X]) ≠ 0 := (u.isUnit.map ev).ne_zero
  refine ⟨A.prod, B.prod * (u : ℤ[X]) * C P.content, ?_,
    isPrimitive_of_dvd P.isPrimitive_primPart hdiv, ?_, ?_⟩
  · calc P = C P.content * P.primPart := P.eq_C_content_mul_primPart
         _ = _ := by rw [hAB]; ring
  · rw [← hev, map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hB hu0) hc
  · intro q hq hqR
    obtain ⟨f, hf, hqf⟩ := exists_associated_mem_of_dvd_prod (irreducible_iff_prime.mp hq)
      (fun f hf => UniqueFactorizationMonoid.prime_of_normalized_factor f
        (Multiset.mem_filter.mp hf).1) hqR
    have hf0 := (Multiset.mem_filter.mp hf).2
    obtain ⟨v, hv⟩ := hqf
    have hq0 : ev q = 0 := by
      have heq := congrArg ev hv
      rw [map_mul, hf0] at heq
      exact (mul_eq_zero.mp heq).resolve_right (v.isUnit.map ev).ne_zero
    rwa [hev] at hq0

/-- The factor is constructed from the original polynomial, preserving exact singularity data. -/
theorem primitive_localized_factor (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0) (hd : P.natDegree ≤ 3)
    (hv : (p : ℤ) ^ 2 ∣ P.eval b) (hdv : (p : ℤ) ∣ P.derivative.eval b) :
    ∃ R U : ℤ[X], P = R * U ∧ R.IsPrimitive ∧
      IsUnit ((U.eval b : ℤ) : ZMod p) ∧ R.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      (p : ℤ) ^ 2 ∣ R.eval b ∧ (p : ℤ) ∣ R.derivative.eval b ∧
      (R.natDegree = 2 ∨ R.natDegree = 3) ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ R → ((q.eval b : ℤ) : ZMod p) = 0) := by
  obtain ⟨R, U, hRU, hprim, hU, hrel⟩ := primitive_root_split P p b hP
  have hRn : R.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro hz
    apply hP
    rw [hRU, Polynomial.map_mul, hz, zero_mul]
  have hcop : IsCoprime (p : ℤ) (U.eval b) :=
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).coprime_iff_not_dvd.mpr
      (by simpa only [← ZMod.intCast_zmod_eq_zero_iff_dvd] using hU)
  have hvR : (p : ℤ) ^ 2 ∣ R.eval b := by
    rw [hRU, eval_mul] at hv
    exact (hcop.pow_left (m := 2)).dvd_of_dvd_mul_right hv
  have hpR : (p : ℤ) ∣ R.eval b := dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hvR
  have hdR : (p : ℤ) ∣ R.derivative.eval b := by
    rw [hRU, derivative_mul, eval_add, eval_mul, eval_mul] at hdv
    apply hcop.dvd_of_dvd_mul_right
    simpa using dvd_sub hdv (hpR.mul_right (U.derivative.eval b))
  have hRdeg : R.natDegree ≤ 3 :=
    (natDegree_le_of_dvd ⟨U, hRU⟩ (by intro hz; simp [hz] at hP)).trans hd
  have hdeg2 : 2 ≤ R.natDegree := by
    let r := R.map (Int.castRingHom (ZMod p))
    have hr : r ≠ 0 := hRn
    have hr0 : r.IsRoot (b : ZMod p) := by
      simpa [r, Polynomial.IsRoot, Polynomial.eval_intCast_map] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (R.eval b) p).mpr hpR
    have hr1 : r.derivative.IsRoot (b : ZMod p) := by
      simpa [r, Polynomial.IsRoot, Polynomial.derivative_map, Polynomial.eval_intCast_map] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (R.derivative.eval b) p).mpr hdR
    have hm := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hr).mpr ⟨hr0, hr1⟩
    have hdvd := Polynomial.pow_rootMultiplicity_dvd r (b : ZMod p)
    have hdn := Polynomial.natDegree_le_of_dvd hdvd hr
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hdn
    exact (Nat.succ_le_iff.mpr hm).trans (hdn.trans Polynomial.natDegree_map_le)
  exact ⟨R, U, hRU, hprim, isUnit_iff_ne_zero.mpr hU, hRn, hvR, hdR,
    by omega, hrel⟩

private theorem weighted_scale_cancel (J₁ J₂ : ℝ) (h₂ : J₂ ≠ 0)
    (j : ℕ) (hj : j ≤ 3) :
    J₁ ^ (3 - j) * J₂ ^ j * (J₁ / J₂) ^ j = J₁ ^ 3 := by
  interval_cases j <;> norm_num <;> field_simp

private theorem weighted_factor_coeff (P R U : ℤ[X]) (hP : P ≠ 0)
    (hRU : P = R * U) (hd : P.natDegree ≤ 3)
    (J₁ J₂ C : ℝ) (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C)
    (hb : ∀ j ≤ P.natDegree, |(P.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    ∀ j ≤ R.natDegree, |(R.coeff j : ℝ)| ≤ 8 * C * J₁ ^ (3 - j) * J₂ ^ j := by
  have h₂p : 0 < J₂ := lt_of_lt_of_le zero_lt_one h₂
  have h₁p : 0 < J₁ := h₂p.trans_le h₁₂
  let l : ℝ := J₁ / J₂
  have hl : 1 ≤ l := (one_le_div h₂p).mpr h₁₂
  have hlp : 0 < l := lt_of_lt_of_le zero_lt_one hl
  let t : ℂ[X] := Polynomial.C (l : ℂ) * Polynomial.X
  let F (f : ℤ[X]) : ℂ[X] := (f.map (Int.castRingHom ℂ)).comp t
  have hnorm (f : ℤ[X]) (j : ℕ) :
      ‖(F f).coeff j‖ = |(f.coeff j : ℝ)| * l ^ j := by
    simp [F, t, comp_C_mul_X_coeff, norm_pow, Complex.norm_intCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlp]
  have hdeg (f : ℤ[X]) : (F f).natDegree ≤ f.natDegree := by
    calc (F f).natDegree ≤ (f.map (Int.castRingHom ℂ)).natDegree * t.natDegree :=
          natDegree_comp_le
         _ ≤ f.natDegree * 1 := Nat.mul_le_mul natDegree_map_le
          ((natDegree_C_mul_le _ _).trans natDegree_X_le)
         _ = _ := Nat.mul_one _
  have hmul : F P = F R * F U := by simp [F, hRU, Polynomial.map_mul, mul_comp]
  have hU : U ≠ 0 := by intro hz; simp [hRU, hz] at hP
  have hR : R ≠ 0 := by intro hz; simp [hRU, hz] at hP
  have hds : (F R).natDegree + (F U).natDegree ≤ 3 := by
    have heq := Polynomial.natDegree_mul hR hU
    rw [← hRU] at heq
    have := Nat.add_le_add (hdeg R) (hdeg U)
    omega
  have hUs : 1 ≤ (F U).supNorm := by
    have hc : (1 : ℝ) ≤ |(U.coeff U.natDegree : ℝ)| := by
      rw [coeff_natDegree]
      exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hU)
    calc (1 : ℝ) ≤ |(U.coeff U.natDegree : ℝ)| * l ^ U.natDegree :=
          one_le_mul_of_one_le_of_one_le hc (one_le_pow₀ hl)
         _ = ‖(F U).coeff U.natDegree‖ := (hnorm U _).symm
         _ ≤ (F U).supNorm := (F U).le_supNorm _
  have hPs : (F P).supNorm ≤ C * J₁ ^ 3 := by
    obtain ⟨j, hj⟩ := (F P).exists_eq_supNorm
    rw [hj, hnorm]
    by_cases hjd : j ≤ P.natDegree
    · calc |(P.coeff j : ℝ)| * l ^ j ≤ (C * J₁ ^ (3 - j) * J₂ ^ j) * l ^ j := by
            gcongr; exact hb j hjd
           _ = C * J₁ ^ 3 := by
            rw [show (C * J₁ ^ (3 - j) * J₂ ^ j) * l ^ j =
              C * (J₁ ^ (3 - j) * J₂ ^ j * (J₁/J₂) ^ j) by dsimp [l]; ring]
            rw [weighted_scale_cancel J₁ J₂ h₂p.ne' j (hjd.trans hd)]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [Int.cast_zero, abs_zero, zero_mul]
      positivity
  have hRs : (F R).supNorm ≤ 8 * C * J₁ ^ 3 := by
    have hg := Polynomial.supNorm_mul_supNorm_le_two_pow (F R) (F U)
    rw [← hmul] at hg
    have hpow : (2 : ℝ) ^ ((F R).natDegree + (F U).natDegree) ≤ 8 := by
      calc (2 : ℝ) ^ ((F R).natDegree + (F U).natDegree) ≤ (2 : ℝ) ^ 3 :=
            pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hds
           _ = _ := by norm_num
    calc (F R).supNorm ≤ (F R).supNorm * (F U).supNorm :=
          le_mul_of_one_le_right (F R).supNorm_nonneg hUs
         _ ≤ _ := hg
         _ ≤ 8 * (C * J₁ ^ 3) :=
          mul_le_mul hpow hPs (F P).supNorm_nonneg (by norm_num)
         _ = _ := by ring
  intro j hj
  have hj3 : j ≤ 3 := hj.trans ((natDegree_le_of_dvd ⟨U, hRU⟩ hP).trans hd)
  apply (mul_le_mul_iff_left₀ (pow_pos hlp j)).mp
  calc |(R.coeff j : ℝ)| * l ^ j = ‖(F R).coeff j‖ := (hnorm R j).symm
       _ ≤ (F R).supNorm := (F R).le_supNorm _
       _ ≤ 8 * C * J₁ ^ 3 := hRs
       _ = (8 * C * J₁ ^ (3 - j) * J₂ ^ j) * l ^ j := by
        rw [show (8 * C * J₁ ^ (3 - j) * J₂ ^ j) * l ^ j =
          (8 * C) * (J₁ ^ (3 - j) * J₂ ^ j * (J₁/J₂) ^ j) by dsimp [l]; ring]
        rw [weighted_scale_cancel J₁ J₂ h₂p.ne' j hj3]

/-- Weighted height is inherited by the primitive factor selected at the actual residue root. -/
theorem weighted_primitive_localized_factor (P : ℤ[X]) (p : ℕ) [Fact p.Prime] (b : ℤ)
    (hP : P.map (Int.castRingHom (ZMod p)) ≠ 0) (hd : P.natDegree ≤ 3)
    (hv : (p : ℤ) ^ 2 ∣ P.eval b) (hdv : (p : ℤ) ∣ P.derivative.eval b)
    (J₁ J₂ C : ℝ) (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 0 ≤ C)
    (hb : ∀ j ≤ P.natDegree, |(P.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j) :
    ∃ R U : ℤ[X], P = R * U ∧ R.IsPrimitive ∧
      IsUnit ((U.eval b : ℤ) : ZMod p) ∧ R.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      (p : ℤ) ^ 2 ∣ R.eval b ∧ (p : ℤ) ∣ R.derivative.eval b ∧
      (R.natDegree = 2 ∨ R.natDegree = 3) ∧
      (∀ q : ℤ[X], Irreducible q → q ∣ R → ((q.eval b : ℤ) : ZMod p) = 0) ∧
      (∀ j ≤ R.natDegree, |(R.coeff j : ℝ)| ≤ 8 * C * J₁ ^ (3 - j) * J₂ ^ j) := by
  obtain ⟨R,U,heq,hprim,hU,hRn,hvR,hdR,hdeg,hrel⟩ :=
    primitive_localized_factor P p b hP hd hv hdv
  refine ⟨R,U,heq,hprim,hU,hRn,hvR,hdR,hdeg,hrel,?_⟩
  exact weighted_factor_coeff P R U (by intro hz; simp [hz] at hP)
    heq hd J₁ J₂ C h₁₂ h₂ hC hb
theorem lift_primitive_rational_factor (R : ℤ[X]) (hR : R.IsPrimitive)
    (q : ℚ[X]) (hq : Irreducible q) (hqR : q ∣ R.map (Int.castRingHom ℚ)) :
    ∃ Q : ℤ[X], Irreducible Q ∧ Q.IsPrimitive ∧ Q ∣ R ∧
      Associated q (Q.map (Int.castRingHom ℚ)) := by
  classical
  let M := normalizedFactors R
  have hp (f : ℤ[X]) (hf : f ∈ M) : f.IsPrimitive :=
    isPrimitive_of_dvd hR (dvd_of_mem_normalizedFactors hf)
  have hprime : ∀ r ∈ M.map (Polynomial.map (Int.castRingHom ℚ)), Prime r := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp hr
    exact irreducible_iff_prime.mp
      ((Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hp f hf)).mp
        (irreducible_of_normalized_factor f hf))
  have ha : Associated (M.map (Polynomial.map (Int.castRingHom ℚ))).prod
      (R.map (Int.castRingHom ℚ)) := by
    rw [← Polynomial.map_multiset_prod]
    exact (prod_normalizedFactors hR.ne_zero).map (Polynomial.mapRingHom (Int.castRingHom ℚ))
  obtain ⟨r, hr, hqr⟩ := exists_associated_mem_of_dvd_prod (irreducible_iff_prime.mp hq)
    hprime (ha.dvd_iff_dvd_right.mpr hqR)
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hr
  exact ⟨Q, irreducible_of_normalized_factor Q hQ, hp Q hQ,
    dvd_of_mem_normalizedFactors hQ, hqr⟩

/-- The cover consists of primitive integer factors of actual original polynomials,
and every chosen factor vanishes at the actual residue root. -/
theorem weighted_localized_factor_cover (S : Set ℤ[X]) (P₀ : ℤ[X]) (h₀ : P₀ ∈ S)
    (p : ℕ) [Fact p.Prime] (b : ℤ) (J₁ J₂ C : ℝ)
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂) (hC : 1 ≤ C)
    (hred : ∀ P ∈ S, P.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hdeg : ∀ P ∈ S, P.natDegree ≤ 3)
    (hcoeff : ∀ P ∈ S, ∀ j ≤ P.natDegree,
      |(P.coeff j : ℝ)| ≤ C * J₁ ^ (3 - j) * J₂ ^ j)
    (hroot : ∀ P ∈ S, (p : ℤ) ^ 2 ∣ P.eval b)
    (hderiv : ∀ P ∈ S, (p : ℤ) ∣ P.derivative.eval b)
    (hgap : 720 * (8 * C) ^ 6 * (J₁ * J₂) ^ 9 < (p : ℝ) ^ 4) :
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ q ∈ F, Irreducible q ∧ q.IsPrimitive ∧ q ∣ P₀ ∧
        ((q.eval b : ℤ) : ZMod p) = 0 ∧ q.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ P ∈ S, ∃ q ∈ F, q ∣ P) := by
  classical
  have hlocal := fun f : S => weighted_primitive_localized_factor f.val p b
    (hred f.val f.property) (hdeg f.val f.property)
    (hroot f.val f.property) (hderiv f.val f.property)
    J₁ J₂ C h₁₂ h₂ (by linarith) (hcoeff f.val f.property)
  choose R U hRU hprim hUnit hRed hRoot hDeriv hDeg hRel hCoeff using hlocal
  let T : Set ℤ[X] := Set.range R
  let a : S := ⟨P₀, h₀⟩
  have ha : R a ∈ T := ⟨a, rfl⟩
  obtain ⟨Fq, hcard, hFq, hcover⟩ := weighted_singular_factor_cover T (R a) ha
    b (p : ℤ) J₁ J₂ (8 * C) (h₂.trans h₁₂) h₂ (by linarith)
    (by rintro _ ⟨f, rfl⟩; exact hDeg f)
    (by rintro _ ⟨f, rfl⟩; exact hCoeff f)
    (by rintro _ ⟨f, rfl⟩; exact hRoot f)
    (by rintro _ ⟨f, rfl⟩; exact hDeriv f)
    (by exact_mod_cast hgap)
  have hlift := fun q : {q // q ∈ Fq} =>
    lift_primitive_rational_factor (R a) (hprim a) q.val
      (hFq q.val q.property).1 (hFq q.val q.property).2
  choose L hLirr hLprim hLdvd hLassoc using hlift
  refine ⟨Fq.attach.image L, (Finset.card_image_le.trans ?_), ?_, ?_⟩
  · simpa using hcard
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨hLirr x, hLprim x, (hLdvd x).trans ⟨U a, hRU a⟩,
      hRel a _ (hLirr x) (hLdvd x), ?_⟩
    intro hz
    obtain ⟨V, hV⟩ := hLdvd x
    apply hRed a
    rw [hV, Polynomial.map_mul, hz, zero_mul]
  · intro P hP
    let f : S := ⟨P, hP⟩
    obtain ⟨q, hq, hqR⟩ := hcover (R f) ⟨f, rfl⟩
    let x : {q // q ∈ Fq} := ⟨q, hq⟩
    refine ⟨L x, Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have hdQ : (L x).map (Int.castRingHom ℚ) ∣ (R f).map (Int.castRingHom ℚ) :=
      (hLassoc x).symm.dvd.trans hqR
    have hdZ := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (hLprim x)).mpr hdQ
    exact hdZ.trans ⟨U f, hRU f⟩


end
end D5.S3.Arith.CharacterSums

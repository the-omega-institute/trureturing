/- GID: D5/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/FiniteFrobeniusDiscriminantSign
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact characteristic-discriminant sign moments on actual finite determinant fibers. -/

import D5.S3.Factorization.QuadraticIdeals.FiniteTraceDeterminantMass

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Factorization.QuadraticIdeals.FiniteFrobeniusDiscriminantSign
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev RootPair (c : F) := {p : F × F // p.2^2 = p.1^2-c}

private def rootEquivSigma (c : F) :
    RootPair c ≃ Σ t : F, {x : F // x^2=t^2-c} where
  toFun q := ⟨q.1.1, ⟨q.1.2,q.2⟩⟩
  invFun q := ⟨(q.1,q.2.1),q.2.2⟩
  left_inv := by rintro ⟨⟨_,_⟩,_⟩; rfl
  right_inv := by rintro ⟨_,⟨_,_⟩⟩; rfl

private def rootEquivUnits (c : F) (hc : c ≠ 0) (h2 : (2:F) ≠ 0) :
    RootPair c ≃ {v : F // v ≠ 0} where
  toFun q := ⟨q.1.1-q.1.2, fun hz => hc (by
    have h : q.1.1=q.1.2 := sub_eq_zero.mp hz
    linear_combination q.2 + (q.1.1+q.1.2)*h)⟩
  invFun v := ⟨((v.1+c/v.1)/2,(c/v.1-v.1)/2), by
    field_simp [v.2]
    ring⟩
  left_inv := by
    intro q
    have hp : (q.1.1-q.1.2)*(q.1.1+q.1.2)=c := by
      linear_combination -q.2
    have hv : q.1.1-q.1.2 ≠ 0 := left_ne_zero_of_mul (hp ▸ hc)
    have hdiv : c / (q.1.1-q.1.2) = q.1.1+q.1.2 := (div_eq_iff hv).2 (by
      rw [mul_comm]
      exact hp.symm)
    apply Subtype.ext
    change (((q.1.1-q.1.2)+c/(q.1.1-q.1.2))/2,
      (c/(q.1.1-q.1.2)-(q.1.1-q.1.2))/2)=q.1
    rw [hdiv]
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv := by
    intro v
    apply Subtype.ext
    change (v.1+c/v.1)/2-(c/v.1-v.1)/2 = v.1
    field_simp [v.2, h2]
    ring

/-- For any nonzero c over an odd finite field the shifted-square
character sum is minus one. The proof counts the roots via the hyperbola. -/
theorem sum_character_shifted_square (c : F) (hc : c ≠ 0)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (∑ t : F, quadraticChar F (t^2-c)) = -1 := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hh (t : F) : (Fintype.card {x : F // x^2=t^2-c} : ℤ) =
      quadraticChar F (t^2-c) + 1 := by
    rw [Fintype.card_subtype]
    simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hchar (t^2-c)
  have hs : Fintype.card {v : F // v ≠ 0} = Fintype.card F-1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have he := congrArg (fun n : ℕ => (n:ℤ)) ((Fintype.card_congr
    (rootEquivSigma c).symm).trans (Fintype.card_congr (rootEquivUnits c hc h2)))
  rw [Fintype.card_sigma, hs] at he
  push_cast [Nat.cast_sub hq] at he
  simp only [hh, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at he
  linarith

private theorem char_four_mul (d : F) (h2 : (2:F) ≠ 0) :
    quadraticChar F (4*d) = quadraticChar F d := by
  have h4 : (4:F) ≠ 0 := by
    rw [show (4:F)=2*2 by ring]
    exact mul_ne_zero h2 h2
  have hsq : IsSquare (4:F) := ⟨2, by ring⟩
  rw [map_mul, (quadraticChar_one_iff_isSquare h4).mpr hsq, one_mul]

/-- Every zero discriminant contributes exactly one to the root count
of the fixed constant 4d. -/
theorem discriminant_zero_card (d : F) (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (Fintype.card {t : F // t^2=4*d} : ℤ) = 1 + quadraticChar F d := by
  rw [Fintype.card_subtype, add_comm, ← char_four_mul d h2]
  simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hchar (4*d)

/-- The second moment of the discriminant sign equals the number of
nonzero discriminants, including the exact correction from determinant squareclass. -/
theorem sum_discriminant_character_sq (d : F)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (∑ t : F, quadraticChar F (t^2-4*d)^2) =
      (Fintype.card F : ℤ) - (1 + quadraticChar F d) := by
  have H (t : F) : quadraticChar F (t^2-4*d)^2 =
      1 - (if t^2=4*d then (1:ℤ) else 0) := by
    by_cases h : t^2=4*d
    · simp [h]
    · rw [quadraticChar_sq_one (sub_ne_zero.mpr h), ite_eq_right h, sub_zero]
  simp_rw [H, Finset.sum_sub_distrib]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Fintype.card_subtype, discriminant_zero_card d hchar h2]

open D5.S3.Factorization.QuadraticIdeals.FiniteTraceDeterminantMass

/-- Actual fixed-determinant trace mass, as a rational probability. -/
def traceMass (t d : F) : ℚ :=
  (Fintype.card (TraceDetFiber t d) : ℚ) / (Fintype.card (DetFiber d) : ℚ)

private theorem char_cube (x : F) :
    (quadraticChar F x : ℚ)^3 = (quadraticChar F x : ℚ) := by
  by_cases h : x=0
  · subst x
    rw [quadraticChar_zero]
    norm_num
  · rcases quadraticChar_dichotomy h with hp|hn
    · rw [hp]; norm_num
    · rw [hn]; norm_num

/-- Exact determinant-conditioned discriminant-sign moments, weighted by the
actual finite matrix trace-fiber count, not uniformly by trace values. -/
theorem discriminant_sign_moments (d : F) (hd : d ≠ 0)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    let q : ℚ := Fintype.card F
    let ch (t : F) : ℚ := quadraticChar F (t^2-4*d)
    (∑ t : F, traceMass t d * ch t) = -(1 + (quadraticChar F d : ℚ))/(q^2-1) ∧
    (∑ t : F, traceMass t d * ch t^2) = 1-q*(1 + (quadraticChar F d : ℚ))/(q^2-1) := by
  dsimp only
  let q : ℚ := Fintype.card F
  let ch (t : F) : ℚ := quadraticChar F (t^2-4*d)
  let z : ℚ := 1 + (quadraticChar F d : ℚ)
  have h4 : (4:F) ≠ 0 := by
    rw [show (4:F)=2*2 by ring]
    exact mul_ne_zero h2 h2
  have hS : (∑ t : F, ch t) = -1 := by
    dsimp [ch]
    exact_mod_cast sum_character_shifted_square (4*d) (mul_ne_zero h4 hd) hchar h2
  have hSS : (∑ t : F, ch t^2) = q-z := by
    dsimp [ch,q,z]
    exact_mod_cast sum_discriminant_character_sq d hchar h2
  have C (t : F) : ch t^3 = ch t := char_cube _
  have H (t : F) : traceMass t d = (q+ch t)/(q^2-1) :=
    uniform_trace_mass t d hd hchar h2
  have hq : (1:ℚ) < q := by
    have hv : 1 < Fintype.card F := Fintype.one_lt_card
    dsimp [q]
    exact_mod_cast hv
  have hQ : q^2-1 ≠ 0 := by nlinarith
  change (∑ t : F, traceMass t d * ch t) = -z/(q^2-1) ∧
    (∑ t : F, traceMass t d * ch t^2) = 1-q*z/(q^2-1)
  constructor
  · simp_rw [H, div_mul_eq_mul_div, add_mul, ← pow_two, div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hS, hSS]
    ring
  · have E (t : F) : ((q+ch t)*ch t^2) = q*ch t^2 + ch t := by
      rw [add_mul, ← pow_succ', C]
    simp_rw [H, div_mul_eq_mul_div, E, div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hSS, hS]
    field_simp
    ring

/-- The exact trace histogram sums to one at each nonzero determinant. -/
theorem traceMass_sum (d : F) (hd : d ≠ 0)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    (∑ t : F, traceMass t d) = 1 := by
  let q : ℚ := Fintype.card F
  let ch (t : F) : ℚ := quadraticChar F (t^2-4*d)
  have h4 : (4:F) ≠ 0 := by
    rw [show (4:F)=2*2 by ring]
    exact mul_ne_zero h2 h2
  have hS : (∑ t : F, ch t) = -1 := by
    dsimp [ch]
    exact_mod_cast sum_character_shifted_square (4*d) (mul_ne_zero h4 hd) hchar h2
  have H (t : F) : traceMass t d = (q+ch t)/(q^2-1) :=
    uniform_trace_mass t d hd hchar h2
  have hq : (1:ℚ) < q := by
    have hv : 1 < Fintype.card F := Fintype.one_lt_card
    dsimp [q]
    exact_mod_cast hv
  have hQ : q^2-1 ≠ 0 := by nlinarith
  simp_rw [H, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hS,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (q*q + -1)*(q^2-1)⁻¹ = 1
  rw [show q*q + -1 = q^2-1 by ring, mul_inv_cancel₀ hQ]

/-- The determinant-conditioned discriminant sign is an exactly fair bit
at a nonsquare determinant, with the mass on actual matrices. -/
theorem nonsquare_det_sign_fair (d : F) (hd : d ≠ 0) (hnd : ¬ IsSquare d)
    (hchar : ringChar F ≠ 2) (h2 : (2:F) ≠ 0) :
    let ch (t : F) : ℚ := quadraticChar F (t^2-4*d)
    (∑ t : F, if ch t = 1 then traceMass t d else 0) = 1/2 ∧
    (∑ t : F, if ch t = -1 then traceMass t d else 0) = 1/2 ∧
    ∀ t : F, ch t ≠ 0 := by
  dsimp only
  let ch (t : F) : ℚ := quadraticChar F (t^2-4*d)
  have Hdz := quadraticChar_neg_one_iff_not_isSquare.mpr hnd
  have Mom := discriminant_sign_moments d hd hchar h2
  dsimp only at Mom
  rw [Hdz] at Mom
  norm_num at Mom
  have hmean : (∑ t : F, traceMass t d * ch t) = 0 := Mom.1
  have hg (t : F) : t^2-4*d ≠ 0 := by
    intro hz
    apply hnd
    refine ⟨t/2, ?_⟩
    have ht := sub_eq_zero.mp hz
    field_simp
    linear_combination -ht
  have hpm (t : F) : ch t = 1 ∨ ch t = -1 := by
    obtain hp|hn := quadraticChar_dichotomy (hg t)
    · left
      dsimp [ch]
      rw [hp]
      norm_num
    · right
      dsimp [ch]
      rw [hn]
      norm_num
  have A (t : F) : (if ch t = 1 then traceMass t d else 0) =
      (traceMass t d + traceMass t d * ch t) / 2 := by
    obtain h | h := hpm t
    · rw [h]; norm_num
    · rw [h]; norm_num
  have B (t : F) : (if ch t = -1 then traceMass t d else 0) =
      (traceMass t d - traceMass t d * ch t) / 2 := by
    obtain h | h := hpm t
    · rw [h]; norm_num
    · rw [h]; norm_num
  change (∑ t : F, if ch t = 1 then traceMass t d else 0) = 1/2 ∧
    (∑ t : F, if ch t = -1 then traceMass t d else 0) = 1/2 ∧
    ∀ t : F, ch t ≠ 0
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [A, div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, traceMass_sum d hd hchar h2, hmean]
    norm_num
  · simp_rw [B, div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, traceMass_sum d hd hchar h2, hmean]
    norm_num
  · intro t
    obtain h | h := hpm t <;> rw [h] <;> norm_num

end D5.S3.Factorization.QuadraticIdeals.FiniteFrobeniusDiscriminantSign

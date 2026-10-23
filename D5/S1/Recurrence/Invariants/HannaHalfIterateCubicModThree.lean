/- GID: D5/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaHalfIterateCubicModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integral half-iteration and ternary support prove Hanna's A107099 conjecture. -/

/-
result: proof_shape: content; escape_witness: half_mod_three_support.
admission_basis: open-problem-resolution (#18858; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19129.
Direct frozen dependencies: CompositionalSquareDyadicDenominators.Agree,
composition_top, agree_subst, residual, residual_four, C_dvd_iff_coeff;
CubicFifteenSubstitutionParity.prime_power_subst.
Declaration classifications (same-delivery proofs inlined):
IsGF: definition; consumers: claim, rational_integral_equation.
claim: definition; consumers: result.
half_unique: proof_shape: content; escape_witness: half_unique; consumers: half_odd, result.
residual: definition; consumers: residual_agree, residual_div_four, correction, extend_correct, approximation_spec, integral_equation.
residual_agree: proof_shape: bind-only; consumers: extend_correct, integral_equation.
residual_div_four: proof_shape: bind-only; consumers: extend_correct.
correction: definition; consumers: extend, extend_even, extend_correct.
extend: definition; consumers: extend_agree, extend_normal, extend_even, extend_correct, approximation.
extend_agree: proof_shape: bind-only; consumers: extend_normal, extend_correct, approximation_stable.
extend_normal: proof_shape: bind-only; consumers: extend_correct, approximation_spec.
extend_even: proof_shape: bind-only; consumers: approximation_spec.
extend_correct: proof_shape: bind-only; consumers: approximation_spec.
approximation: definition; consumers: approximation_spec, approximation_stable, integralSeries, integral_agree, integral_equation.
approximation_spec: proof_shape: content; escape_witness: approximation_spec; consumers: integral_equation.
approximation_stable: proof_shape: content; escape_witness: approximation_stable; consumers: integral_agree.
integralSeries: definition; consumers: integral_agree, integral_equation, integer_reduction_support, rational_integral_equation, result.
integral_agree: proof_shape: content; escape_witness: approximation_stable; consumers: integral_equation.
integral_equation: proof_shape: content; escape_witness: integral_equation; consumers: integer_reduction_support, rational_integral_equation.
power_three_support: proof_shape: bind-only; consumers: substitution_three_support.
substitution_three_support: proof_shape: bind-only; consumers: half_mod_three_support.
half_mod_three_support: proof_shape: content; escape_witness: half_mod_three_support; consumers: integer_reduction_support.
integer_reduction_support: proof_shape: content; escape_witness: half_mod_three_support; consumers: result.
half_odd: proof_shape: content; escape_witness: half_unique; consumers: rational_integral_equation.
rational_integral_equation: proof_shape: content; escape_witness: integral_equation; consumers: result.
result: proof_shape: content; escape_witness: half_mod_three_support; consumers: terminal result.

All dependencies are reused at their original owners. The exact rational-series
predicate and coefficient claim are those of OEIS A107099. No formula for the
residues at powers of three or coefficient-growth estimate is asserted.
Utility is none: all statements concern unbounded symbolic constructions,
uniqueness, integrality and support, without certified finite computation.
-/

-- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19870.

import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree

open PowerSeries

/-- OEIS A107099, Name (unpaginated): "G.f. satisfies A(A(x)) = x + 4*x^3, where A(x) = Sum_{n>=0} a(n)*x^(2*n+1)." With
a(0) = 1 (offset 0). -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  (∀ n : ℕ, coeff (2 * n) A = 0) ∧ coeff 1 A = 1 ∧ PowerSeries.subst A A = X + 4 * X ^ 3

/-- OEIS A107099, Comments (unpaginated): "Coefficients [x^n] A(x) = 0 (mod 3) except at n = 3^k (conjecture)."
The coefficients are integers. -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, ∃ m : ℤ, coeff n A = m ∧ ((¬ ∃ k : ℕ, n = 3 ^ k) → m ≡ 0 [ZMOD 3])

end D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree
namespace D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree
open PowerSeries
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

section Triangular
variable {R : Type*} [CommRing R]

theorem half_unique [NoZeroDivisors R] (h2 : (2 : R) ≠ 0)
    {f g t : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (hf : f.subst f = t) (hg : g.subst g = t) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ht := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.composition_top hf0 hg0 hf1 hg1 ih
    rw [hf,hg,sub_self] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht.symm).resolve_left h2)

end Triangular


private noncomputable def residual (f : PowerSeries ℤ) : PowerSeries ℤ :=
  f.subst f - X - 4 * X^3

private theorem residual_agree {n : ℕ} {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree n f g) : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree n (residual f) (residual g) := by
  have hs := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.agree_subst hf hg h h
  intro i hi
  simp only [residual, map_sub, hs i hi]

private theorem residual_div_four {f : PowerSeries ℤ} (hf : constantCoeff f = 0)
    (he : ∃ b : PowerSeries ℤ, f = X + 2*b) (n : ℕ) :
    4 ∣ coeff n (residual f) := by
  obtain ⟨b,hb⟩ := he
  have hc2 : C (2 : ℤ) ∣ f-X := by
    refine ⟨b,?_⟩
    rw [hb]
    change X+2*b-X=2*b
    ring
  have hfour : 4 ∣ coeff n (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.residual f) :=
    (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.C_dvd_iff_coeff (4 : ℤ) (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.residual f)).mp (D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.residual_four hf hc2) n
  have heq : residual f = D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.residual f + 4*(X*f-X^3) := by
    change (f.subst f-X-4*X^3)=(f.subst f-X-4*X*f)+4*(X*f-X^3)
    ring
  rw [heq,map_add]
  apply dvd_add hfour
  rw [← map_ofNat C 4,coeff_C_mul]
  exact dvd_mul_right _ _

private noncomputable def correction (n : ℕ) (f : PowerSeries ℤ) : ℤ :=
  -(coeff n (residual f) / 4)

private noncomputable def extend (n : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  f + C (2 * correction n f) * X^n

private theorem extend_agree (n : ℕ) (f : PowerSeries ℤ) : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree n (extend n f) f := by
  intro k hk
  simp only [extend, map_add, coeff_C_mul_X_pow,
    ite_eq_right (Nat.ne_of_lt hk), add_zero]

private theorem extend_normal {n : ℕ} {f : PowerSeries ℤ}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1) :
    constantCoeff (extend n f) = 0 ∧ coeff 1 (extend n f) = 1 := by
  constructor
  · simpa only [coeff_zero_eq_constantCoeff, hf] using extend_agree n f 0 (by omega)
  · simpa only [hf1] using extend_agree n f 1 hn

private theorem extend_even (n : ℕ) (f : PowerSeries ℤ)
    (hf : ∃ b : PowerSeries ℤ, f = X + 2*b) :
    ∃ b : PowerSeries ℤ, extend n f = X + 2*b := by
  obtain ⟨b,hb⟩ := hf
  refine ⟨b + C (correction n f)*X^n, ?_⟩
  simp only [extend, hb, map_mul, map_ofNat]
  ring

private theorem extend_correct {n : ℕ} {f : PowerSeries ℤ}
    (hn : 1 < n) (hf : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (heven : ∃ b : PowerSeries ℤ, f = X+2*b)
    (he : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree n (residual f) 0) :
    D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree (n+1) (residual (extend n f)) 0 := by
  have hz := extend_normal hn hf hf1
  have ht := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.composition_top hz.1 hf hz.2 hf1 (extend_agree n f)
  have hc : 4 * correction n f = -coeff n (residual f) := by
    dsimp [correction]
    rw [mul_neg, Int.mul_ediv_cancel' (residual_div_four hf heven n)]
  have hcoeff : coeff n (extend n f)-coeff n f = 2*correction n f := by
    simp only [extend, map_add, coeff_C_mul_X_pow, ↓reduceIte]
    ring
  rw [hcoeff] at ht
  intro k hk
  by_cases hkn : k < n
  · exact (residual_agree hz.1 hf (extend_agree n f) k hkn).trans (he k hkn)
  · have hkn : k = n := Nat.eq_of_lt_succ_of_not_lt hk hkn
    subst k
    simp only [map_zero, residual, map_sub]
    dsimp [residual] at hc
    simp only [map_sub] at hc
    linear_combination ht + hc

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => X
  | j+1 => extend (j+2) (approximation j)

private theorem approximation_spec (j : ℕ) :
    constantCoeff (approximation j) = 0 ∧ coeff 1 (approximation j) = 1 ∧
    (∃ b : PowerSeries ℤ, approximation j = X+2*b) ∧
    D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree (j+2) (residual (approximation j)) 0 := by
  induction j with
  | zero =>
    refine ⟨by simp [approximation], by simp [approximation], ⟨0, by simp [approximation]⟩, ?_⟩
    intro k hk
    simp only [approximation, residual, subst_X (HasSubst.X'), sub_self, zero_sub,
      map_neg, map_zero, ← map_ofNat C 4, coeff_C_mul, coeff_X_pow,
      ite_eq_right (show k ≠ 3 by omega), mul_zero, neg_zero]
  | succ j ih =>
    have hz := extend_normal (by omega : 1 < j+2) ih.1 ih.2.1
    exact ⟨hz.1,hz.2,extend_even _ _ ih.2.2.1,
      extend_correct (by omega) ih.1 ih.2.1 ih.2.2.1 ih.2.2.2⟩

private theorem approximation_stable {j k : ℕ} (hjk : j ≤ k) :
    D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree (j+2) (approximation k) (approximation j) := by
  induction k, hjk using Nat.le_induction with
  | base => intro i hi; rfl
  | succ k hk ih =>
    intro i hi
    exact (extend_agree (k+2) (approximation k) i (by omega)).trans (ih i hi)

private noncomputable def integralSeries : PowerSeries ℤ :=
  mk fun n => coeff n (approximation n)

private theorem integral_agree (j : ℕ) : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree (j+2) integralSeries (approximation j) := by
  intro n hn
  simp only [integralSeries, coeff_mk]
  by_cases hnj : n ≤ j
  · exact (approximation_stable hnj n (by omega)).symm
  · exact approximation_stable (by omega : j ≤ n) n hn

private theorem integral_equation : constantCoeff integralSeries = 0 ∧
    coeff 1 integralSeries = 1 ∧ integralSeries.subst integralSeries = X+4*X^3 := by
  have hz : constantCoeff integralSeries = 0 := by
    simpa only [coeff_zero_eq_constantCoeff, approximation, constantCoeff_X] using
      integral_agree 0 0 (by omega)
  have h1 : coeff 1 integralSeries = 1 := by
    simpa only [approximation, coeff_one_X] using integral_agree 0 1 (by omega)
  refine ⟨hz,h1,?_⟩
  have he : residual integralSeries = 0 := by
    ext n
    exact (residual_agree hz (approximation_spec n).1 (integral_agree n) n (by omega)).trans
      ((approximation_spec n).2.2.2 n (by omega))
  dsimp [residual] at he
  linear_combination he

private theorem power_three_support {f : PowerSeries (ZMod 3)}
    (hf : ∀ n : ℕ, (¬ ∃ k : ℕ, n=3^k) → coeff n f = 0) :
    ∀ k n : ℕ, (¬ ∃ j : ℕ, n=3^j) → coeff n (f^(3^k)) = 0 := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro n hn
    rw [pow_succ, pow_mul,
      D5.S1.Recurrence.Invariants.CubicFifteenSubstitutionParity.prime_power_subst,
      coeff_subst_X_pow (by decide : 3 ≠ 0)]
    split_ifs with hd
    · apply ih
      rintro ⟨j,hj⟩
      apply hn
      refine ⟨j+1, ?_⟩
      rw [pow_succ, ← hj, Nat.div_mul_cancel hd]
    · rfl

private theorem substitution_three_support {f g : PowerSeries (ZMod 3)}
    (hg0 : constantCoeff g = 0)
    (hf : ∀ n : ℕ, (¬ ∃ k : ℕ, n=3^k) → coeff n f = 0)
    (hg : ∀ n : ℕ, (¬ ∃ k : ℕ, n=3^k) → coeff n g = 0)
    (n : ℕ) (hn : ¬ ∃ k : ℕ, n=3^k) : coeff n (f.subst g)=0 := by
  classical
  rw [coeff_subst' (.of_constantCoeff_zero hg0)]
  have he : (fun k : ℕ => coeff k f • coeff n (g^k)) = fun _ => (0 : ZMod 3) := by
    funext k
    by_cases hk : ∃ j : ℕ, k=3^j
    · obtain ⟨j,rfl⟩ := hk
      rw [power_three_support hg j n hn, smul_zero]
    · rw [hf k hk, zero_smul]
  rw [he]
  simp

private theorem half_mod_three_support (f : PowerSeries (ZMod 3))
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f=1)
    (he : f.subst f=X+X^3) :
    ∀ n : ℕ, (¬ ∃ k : ℕ, n=3^k) → coeff n f=0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hn1 : n ≠ 1 := by intro e; exact hn ⟨0,by simp [e]⟩
    have hn3 : n ≠ 3 := by intro e; exact hn ⟨1,by simp [e]⟩
    by_cases hn0 : n=0
    · subst n; simpa only [coeff_zero_eq_constantCoeff] using hf0
    let t : PowerSeries (ZMod 3) := trunc n f
    have ht0 : constantCoeff t=0 := by
      simpa only [coeff_zero_eq_constantCoeff, hf0] using
        (coeff_coe_trunc_of_lt (f := f) (Nat.pos_of_ne_zero hn0))
    have ht1 : coeff 1 t=1 :=
      (coeff_coe_trunc_of_lt (f := f) (by omega : 1 < n)).trans hf1
    have ha : D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.Agree n f t := by
      intro i hi
      exact (coeff_coe_trunc_of_lt (f := f) hi).symm
    have hts : ∀ i : ℕ, (¬ ∃ k : ℕ, i=3^k) → coeff i t=0 := by
      intro i hi
      change coeff i (trunc n f : PowerSeries (ZMod 3)) = 0
      rw [Polynomial.coeff_coe, coeff_trunc]
      split_ifs with hlt
      · exact ih i hlt hi
      · rfl
    have hcomp := substitution_three_support ht0 hts hts n hn
    have htop := D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.composition_top hf0 ht0 hf1 ht1 ha
    have hfn : coeff n (f.subst f)=0 := by rw [he]; simp [coeff_X,hn1,hn3]
    have htn : coeff n t=0 := hts n hn
    simp only [hfn,hcomp,htn,sub_zero,sub_self] at htop
    exact (mul_eq_zero.mp htop.symm).resolve_left (by decide : (2 : ZMod 3) ≠ 0)

private theorem integer_reduction_support (n : ℕ) (hn : ¬ ∃ k : ℕ, n=3^k) :
    ((coeff n integralSeries : ℤ) : ZMod 3)=0 := by
  let hom := Int.castRingHom (ZMod 3)
  let f : PowerSeries (ZMod 3) := integralSeries.map hom
  have hf0 : constantCoeff f=0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_map,coeff_zero_eq_constantCoeff,integral_equation.1,map_zero]
  have hf1 : coeff 1 f=1 := by
    rw [coeff_map,integral_equation.2.1,map_one]
  have he : f.subst f=X+X^3 := by
    have h := congrArg (PowerSeries.map hom) integral_equation.2.2
    rw [show PowerSeries.map hom (integralSeries.subst integralSeries) =
        (integralSeries.map hom).subst (integralSeries.map hom) from
      map_subst (.of_constantCoeff_zero integral_equation.1) _] at h
    have hfour : (4 : PowerSeries (ZMod 3))=1 := ext (congrFun rfl)
    simpa only [map_add,map_mul,map_pow,map_X,map_ofNat,hfour,one_mul] using h
  exact half_mod_three_support f hf0 hf1 he n hn

private theorem half_odd (f : PowerSeries ℚ) (hf0 : constantCoeff f=0)
    (hf1 : coeff 1 f=1) (hf : PowerSeries.subst f f=X+4*X^3) :
    ∀ n : ℕ, coeff (2*n) f=0 := by
  let u : PowerSeries ℚ := -X
  let g : PowerSeries ℚ := -(PowerSeries.subst u f)
  have hu0 : constantCoeff u=0 := by simp [u]
  have hu : HasSubst u := .of_constantCoeff_zero hu0
  have hfS : HasSubst f := .of_constantCoeff_zero hf0
  have hneg : ∀ {a b : PowerSeries ℚ}, HasSubst b →
      PowerSeries.subst b (-a) = -(PowerSeries.subst b a) := by
    intro a b hb
    rw [← coe_substAlgHom (R:=ℚ) hb]
    exact map_neg (substAlgHom (R:=ℚ) hb) a
  have hg0 : constantCoeff g=0 := by
    have hfu0 : constantCoeff (PowerSeries.subst u f)=0 :=
      constantCoeff_subst_eq_zero hu0 f hf0
    change -(constantCoeff (PowerSeries.subst u f))=0
    rw [hfu0,neg_zero]
  have hgS : HasSubst g := .of_constantCoeff_zero hg0
  have hfu : PowerSeries.subst u f=rescale (-1 : ℚ) f := by
    simpa only [u,neg_one_smul] using (rescale_eq_subst (-1 : ℚ) f).symm
  have hg1 : coeff 1 g=1 := by simp [g,hfu,coeff_rescale,hf1]
  have hgu : PowerSeries.subst g u = -g := by
    change PowerSeries.subst g (-X) = -g
    rw [hneg hgS,subst_X hgS]
  have hgg : PowerSeries.subst g g=X+4*X^3 := by
    calc
      PowerSeries.subst g g = -(PowerSeries.subst g (PowerSeries.subst u f)) := hneg hgS
      _ = -(PowerSeries.subst (PowerSeries.subst g u) f) := by
        rw [subst_comp_subst_apply hu hgS f]
      _ = -(PowerSeries.subst (PowerSeries.subst u f) f) := by
        rw [hgu]; simp only [g,neg_neg]
      _ = -(PowerSeries.subst u (PowerSeries.subst f f)) := by
        rw [subst_comp_subst_apply hfS hu f]
      _ = -(PowerSeries.subst u (X+4*X^3 : PowerSeries ℚ)) := by rw [hf]
      _ = X+4*X^3 := by
        have hfour : PowerSeries.subst u (4 : PowerSeries ℚ)=4 := by
          rw [← coe_substAlgHom (R:=ℚ) hu]
          exact map_ofNat (substAlgHom (R:=ℚ) hu) 4
        rw [subst_add hu,subst_mul hu,subst_pow hu,subst_X hu,hfour]
        dsimp [u]
        ring
  have heq := half_unique (by norm_num : (2 : ℚ) ≠ 0) hf0 hg0 hf1 hg1 hf hgg
  intro n
  have hc := congrArg (coeff (2*n)) heq
  simp only [g,hfu,map_neg,coeff_rescale,pow_mul,neg_one_sq,one_pow,one_mul] at hc
  linarith

private theorem rational_integral_equation : IsGF (integralSeries.map (Int.castRingHom ℚ)) := by
  let hom := Int.castRingHom ℚ
  let f : PowerSeries ℚ := integralSeries.map hom
  have hf0 : constantCoeff f=0 := by
    rw [← coeff_zero_eq_constantCoeff,coeff_map,coeff_zero_eq_constantCoeff,integral_equation.1,map_zero]
  have hf1 : coeff 1 f=1 := by rw [coeff_map,integral_equation.2.1,map_one]
  have he : f.subst f=X+4*X^3 := by
    have h := congrArg (PowerSeries.map hom) integral_equation.2.2
    rw [show PowerSeries.map hom (integralSeries.subst integralSeries) =
        (integralSeries.map hom).subst (integralSeries.map hom) from
      map_subst (.of_constantCoeff_zero integral_equation.1) _] at h
    simpa only [map_add,map_mul,map_pow,map_X,map_ofNat] using h
  exact ⟨half_odd f hf0 hf1 he,hf1,he⟩

theorem result : claim := by
  refine ⟨⟨_,rational_integral_equation⟩,?_⟩
  intro f hf n
  have hf0 : constantCoeff f=0 := by simpa only [Nat.mul_zero,coeff_zero_eq_constantCoeff] using hf.1 0
  have hr := rational_integral_equation
  have hr0 : constantCoeff (integralSeries.map (Int.castRingHom ℚ))=0 := by
    simpa only [Nat.mul_zero,coeff_zero_eq_constantCoeff] using hr.1 0
  have he := half_unique (by norm_num : (2 : ℚ) ≠ 0) hf0 hr0 hf.2.1 hr.2.1 hf.2.2 hr.2.2
  refine ⟨coeff n integralSeries,?_,?_⟩
  · rw [he,coeff_map]; rfl
  · intro hn
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (integer_reduction_support n hn)
    exact Int.modEq_zero_iff_dvd.mpr hdiv


end D5.S1.Recurrence.Invariants.HannaHalfIterateCubicModThree

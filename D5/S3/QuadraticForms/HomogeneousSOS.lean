/- GID: D5/S3/QuadraticForms/HomogeneousSOS
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/HomogeneousSOS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous square representatives for native real sums of squares. -/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Tactic

/-! The native `IsSumSq` predicate allows squares of arbitrary polynomials.
For a homogeneous form of degree `2*d`, homogeneous degree `d` squares
suffice. The proof eliminates every smaller homogeneous component by
positivity over the reals before extracting degree `2*d`. -/

open scoped BigOperators
open MvPolynomial

namespace D5.S3.QuadraticForms.HomogeneousSOS

noncomputable section

private lemma finite_squares {R : Type*} [CommSemiring R] {p : R}
    (hp : IsSumSq p) : ∃ (m : ℕ) (q : Fin m → R), p = ∑ i, q i * q i := by
  induction hp with
  | zero => exact ⟨0,Fin.elim0,by simp⟩
  | @sq_add a s hs ih =>
    obtain ⟨m,q,hq⟩ := ih
    exact ⟨m+1,Fin.cons a q,by simpa only [Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ] using congrArg (a*a + ·) hq⟩

private lemma sum_squares_zero {σ J : Type*} [Fintype J]
    (q : J → MvPolynomial σ ℝ) (hq : ∑ i, q i * q i = 0) : ∀ i, q i = 0 := by
  intro i
  apply MvPolynomial.funext
  intro x
  have he := congrArg (MvPolynomial.eval x) hq
  simp only [map_sum, map_mul, map_zero] at he
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset J)) => mul_self_nonneg
      (MvPolynomial.eval x (q j)))).mp he i (Finset.mem_univ i)
  simpa only [map_zero] using (mul_self_eq_zero.mp hz)

private lemma component_square {σ : Type*} (q : MvPolynomial σ ℝ) (d : ℕ)
    (hlo : ∀ k < d, homogeneousComponent k q = 0) :
    homogeneousComponent (2*d) (q*q) = homogeneousComponent d q * homogeneousComponent d q := by
  classical
  have hc0 (a : σ →₀ ℕ) (ha : a.degree < d) : q.coeff a = 0 := by
    have hh := congrArg (fun p : MvPolynomial σ ℝ => p.coeff a) (hlo a.degree ha)
    simpa only [coeff_homogeneousComponent, ite_true, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using hh
  ext c
  by_cases hc : c.degree = 2*d
  · rw [coeff_homogeneousComponent, if_pos hc, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hadd : ab.1 + ab.2 = c := Finset.mem_antidiagonal.mp hab
    have hdeg : ab.1.degree + ab.2.degree = 2*d := by
      rw [← map_add, hadd, hc]
    by_cases ha : ab.1.degree = d
    · have hb : ab.2.degree = d := by omega
      simp only [coeff_homogeneousComponent, ha, hb, ite_true]
    · have hsmall : ab.1.degree < d ∨ ab.2.degree < d := by omega
      rcases hsmall with hsmall | hsmall
      · simp only [hc0 ab.1 hsmall, coeff_homogeneousComponent,
          if_neg (ne_of_lt hsmall), zero_mul]
      · simp only [hc0 ab.2 hsmall, coeff_homogeneousComponent,
          if_neg (ne_of_lt hsmall), mul_zero]
  · rw [coeff_homogeneousComponent, if_neg hc]
    symm
    exact ((homogeneousComponent_isHomogeneous d q).mul
      (homogeneousComponent_isHomogeneous d q)).coeff_eq_zero (by omega)

/-- A real homogeneous polynomial is a native sum of squares exactly when
it is a finite sum of squares of homogeneous half-degree polynomials.
Zero forms and degree zero are included. -/
theorem homogeneous_sos_iff {σ : Type*} (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous (2*d)) :
    IsSumSq p ↔ ∃ (m : ℕ) (q : Fin m → MvPolynomial σ ℝ),
      (∀ i, (q i).IsHomogeneous d) ∧ p = ∑ i, q i * q i := by
  constructor
  · intro hs
    obtain ⟨m,q,hq⟩ := finite_squares hs
    have hlo : ∀ k < d, ∀ i, homogeneousComponent k (q i) = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        have hzero : (∑ i, homogeneousComponent k (q i) *
            homogeneousComponent k (q i)) = 0 := by
          calc
            _ = ∑ i, homogeneousComponent (2*k) (q i * q i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (component_square (q i) k (fun j hj => ih j hj (by omega) i)).symm
            _ = homogeneousComponent (2*k) p := by rw [hq, map_sum]
            _ = 0 := by
              rw [homogeneousComponent_of_mem hp, if_neg (by omega)]
        exact sum_squares_zero _ hzero
    refine ⟨m,fun i => homogeneousComponent d (q i),
      fun i => homogeneousComponent_isHomogeneous d (q i),?_⟩
    calc
      p = homogeneousComponent (2*d) p := (homogeneousComponent_eq_self hp).symm
      _ = ∑ i, homogeneousComponent (2*d) (q i * q i) := by rw [hq, map_sum]
      _ = _ := Finset.sum_congr rfl fun i _ => component_square (q i) d (fun k hk => hlo k hk i)
  · rintro ⟨m,q,_,rfl⟩
    exact IsSumSq.sum_mul_self Finset.univ q

#print axioms homogeneous_sos_iff

section Parity

variable {σ Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]

private lemma sum_components (w : σ → Γ) (q : MvPolynomial σ ℝ) :
    (∑ a : Γ, weightedHomogeneousComponent w a q) = q := by
  simpa only [finsum_eq_sum_of_fintype] using sum_weightedHomogeneousComponent w q

private lemma zero_component_square (w : σ → Γ) (hΓ : ∀ a : Γ, a + a = 0)
    (q : MvPolynomial σ ℝ) :
    weightedHomogeneousComponent w 0 (q * q) =
      ∑ a : Γ, weightedHomogeneousComponent w a q * weightedHomogeneousComponent w a q := by
  have hterm (a b : Γ) :
      weightedHomogeneousComponent w 0
        (weightedHomogeneousComponent w a q * weightedHomogeneousComponent w b q) =
        if a = b then weightedHomogeneousComponent w a q *
          weightedHomogeneousComponent w b q else 0 := by
    have hh := (weightedHomogeneousComponent_isWeightedHomogeneous a q (w := w)).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous b q (w := w))
    by_cases hab : a = b
    · subst b
      rw [if_pos rfl]
      simpa only [hΓ a] using hh.weightedHomogeneousComponent_same
    · rw [if_neg hab]
      apply hh.weightedHomogeneousComponent_ne
      intro hz
      exact hab (add_right_cancel (hz.symm.trans (hΓ b).symm))
  calc
    _ = weightedHomogeneousComponent w 0
        ((∑ a : Γ, weightedHomogeneousComponent w a q) *
          (∑ a : Γ, weightedHomogeneousComponent w a q)) := by rw [sum_components]
    _ = ∑ a : Γ, ∑ b : Γ, weightedHomogeneousComponent w 0
        (weightedHomogeneousComponent w a q * weightedHomogeneousComponent w b q) := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private lemma component_homogeneous (w : σ → Γ) (a : Γ)
    (q : MvPolynomial σ ℝ) (d : ℕ) (hq : q.IsHomogeneous d) :
    (weightedHomogeneousComponent w a q).IsHomogeneous d := by
  intro c hc
  apply hq
  intro hz
  exact hc (by simp only [coeff_weightedHomogeneousComponent, hz, ite_self])

/-- In a finite parity grading, a real homogeneous sum of squares of degree
`2*d` has square representatives that are simultaneously homogeneous of
degree `d` and contained in individual parity sectors. No SOS hypothesis is
added: the left side is the native unrestricted polynomial predicate. -/
theorem homogeneous_parity_sos_iff (w : σ → Γ) (hΓ : ∀ a : Γ, a + a = 0)
    (p : MvPolynomial σ ℝ) (d : ℕ) (hp : p.IsHomogeneous (2 * d))
    (hzero : p.IsWeightedHomogeneous w 0) :
    IsSumSq p ↔ ∃ (m : ℕ) (q : Fin m → Γ → MvPolynomial σ ℝ),
      (∀ i a, (q i a).IsHomogeneous d ∧ (q i a).IsWeightedHomogeneous w a) ∧
        p = ∑ i, ∑ a, q i a * q i a := by
  constructor
  · intro hs
    obtain ⟨m,q,hq,he⟩ := (homogeneous_sos_iff p d hp).mp hs
    refine ⟨m,fun i a => weightedHomogeneousComponent w a (q i),?_,?_⟩
    · intro i a
      exact ⟨component_homogeneous w a (q i) d (hq i),
        weightedHomogeneousComponent_isWeightedHomogeneous a (q i)⟩
    · calc
        p = weightedHomogeneousComponent w 0 p :=
          hzero.weightedHomogeneousComponent_same.symm
        _ = ∑ i, weightedHomogeneousComponent w 0 (q i * q i) := by rw [he,map_sum]
        _ = _ := Finset.sum_congr rfl fun i _ => zero_component_square w hΓ (q i)
  · rintro ⟨m,q,_,rfl⟩
    exact IsSumSq.sum (fun i _ => IsSumSq.sum_mul_self Finset.univ (q i))

#print axioms homogeneous_parity_sos_iff

end Parity

private def halfExponent {σ : Type*} (c : σ →₀ ℕ) : σ →₀ ℕ :=
  c.mapRange (fun k => k / 2) (by decide)

private def oddExponent {σ : Type*} (c : σ →₀ ℕ) : σ →₀ ℕ :=
  c.mapRange (fun k => k % 2) (by decide)

private lemma exponent_split {σ : Type*} (c : σ →₀ ℕ) :
    oddExponent c + 2 • halfExponent c = c := by
  ext i
  simp only [oddExponent,halfExponent,Finsupp.add_apply,Finsupp.mapRange_apply,
    Finsupp.smul_apply,smul_eq_mul]
  omega

private lemma parity_factor {σ : Type*} (p : MvPolynomial σ ℝ) (α : σ →₀ ℕ)
    (hpar : ∀ c ∈ p.support, oddExponent c = α) (d : ℕ) (hp : p.IsHomogeneous d) :
    ∃ q : MvPolynomial σ ℝ, q.IsHomogeneous ((d - α.degree) / 2) ∧
      p = monomial α 1 * expand 2 q := by
  classical
  let q : MvPolynomial σ ℝ := ∑ c ∈ p.support, monomial (halfExponent c) (p.coeff c)
  have hexp (c : σ →₀ ℕ) (hc : c ∈ p.support) : α + 2 • halfExponent c = c := by
    rw [← hpar c hc]
    exact exponent_split c
  refine ⟨q,?_,?_⟩
  · apply IsHomogeneous.sum
    intro c hc
    apply isHomogeneous_monomial
    have hdeg : α.degree + 2 * (halfExponent c).degree = d := by
      have hd : c.degree = d := by
        by_contra h
        exact (mem_support_iff.mp hc) (hp.coeff_eq_zero h)
      have hh := congrArg Finsupp.degree (hexp c hc)
      simpa [map_add,map_nsmul,nsmul_eq_mul,hd] using hh
    omega
  · calc
      p = ∑ c ∈ p.support, monomial c (p.coeff c) := p.as_sum
      _ = monomial α 1 * expand 2 q := by
        simp only [q,map_sum,Finset.mul_sum,expand_monomial,monomial_mul,one_mul]
        apply Finset.sum_congr rfl
        intro c hc
        rw [hexp c hc]

section BinaryParity

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

private def parityWeight (i : σ) : σ → ZMod 2 := Pi.single i 1

private lemma parityWeight_apply (c : σ →₀ ℕ) (i : σ) :
    (Finsupp.weight parityWeight c) i = (c i : ZMod 2) := by
  classical
  simp only [Finsupp.weight_eq_sum,Finset.sum_apply,Pi.smul_apply,parityWeight,
    Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji,Ne.symm hji]
  · simp

private def binaryExponent (a : σ → ZMod 2) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

private lemma sector_oddExponent (p : MvPolynomial σ ℝ) (a : σ → ZMod 2)
    (hp : p.IsWeightedHomogeneous parityWeight a) (c : σ →₀ ℕ) (hc : c ∈ p.support) :
    oddExponent c = binaryExponent a := by
  ext i
  have hh := congrFun (hp (mem_support_iff.mp hc)) i
  rw [parityWeight_apply] at hh
  change c i % 2 = (a i).val
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hh

private lemma expand_homogeneous (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.IsHomogeneous d) : (expand 2 p).IsHomogeneous (2 * d) := by
  intro c hc
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp
    (support_expand_subset p (mem_support_iff.mpr hc))
  rw [map_nsmul,hp (mem_support_iff.mp hb),nsmul_eq_mul]
  norm_num

private lemma expand_parity_zero (p : MvPolynomial σ ℝ) :
    (expand 2 p).IsWeightedHomogeneous parityWeight 0 := by
  intro c hc
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp
    (support_expand_subset p (mem_support_iff.mpr hc))
  ext i
  rw [parityWeight_apply]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [Finsupp.smul_apply,smul_eq_mul,htwo]

private lemma expand_square_factor (α : σ →₀ ℕ) (q : MvPolynomial σ ℝ) :
    expand 2 (monomial α 1 * (q * q)) =
      (monomial α 1 * expand 2 q) * (monomial α 1 * expand 2 q) := by
  rw [map_mul,map_mul,expand_monomial]
  have hm : monomial (2 • α) (1 : ℝ) = monomial α 1 * monomial α 1 := by
    rw [monomial_mul_monomial,one_mul,two_nsmul]
  rw [hm]
  ring

/-- The homogeneous even-form SOS decomposition of GNP Proposition 8.10.
The left side is the unrestricted native SOS predicate after the genuine
substitution `Xᵢ ↦ Xᵢ²`. The right side uses binary square-free monomials
times squares, with the exact degree relation on every nonzero summand.
No SOS or tensor-moment characterization is assumed as a hypothesis. -/
theorem even_form_sos_iff (p : MvPolynomial σ ℝ) (r : ℕ)
    (hp : p.IsHomogeneous r) :
    IsSumSq (expand 2 p) ↔
      ∃ (m : ℕ) (α : Fin m → σ →₀ ℕ) (d : Fin m → ℕ)
        (q : Fin m → MvPolynomial σ ℝ),
        (∀ i, (∀ j, α i j ≤ 1) ∧ (q i).IsHomogeneous (d i) ∧
          (q i = 0 ∨ (α i).degree + 2 * d i = r)) ∧
        p = ∑ i, monomial (α i) 1 * (q i * q i) := by
  constructor
  · intro hs
    obtain ⟨m,f,hf,he⟩ := (homogeneous_parity_sos_iff parityWeight
      (fun a => by ext j; exact CharTwo.add_self_eq_zero _) (expand 2 p) r
      (expand_homogeneous p r hp) (expand_parity_zero p)).mp hs
    have hfactor (i : Fin m) (a : σ → ZMod 2) := parity_factor (f i a)
      (binaryExponent a) (fun c hc => sector_oddExponent (f i a) a (hf i a).2 c hc)
      r (hf i a).1
    choose q hq hfact using hfactor
    let J := Fin m × (σ → ZMod 2)
    let e := Fintype.equivFin J
    refine ⟨Fintype.card J,fun j => binaryExponent (e.symm j).2,
      fun j => (r - (binaryExponent (e.symm j).2).degree) / 2,
      fun j => q (e.symm j).1 (e.symm j).2,?_,?_⟩
    · intro j
      let i := (e.symm j).1
      let a := (e.symm j).2
      refine ⟨fun k => ?_,hq i a,?_⟩
      · change (a k).val ≤ 1
        have hh := (a k).val_lt
        omega
      · by_cases hz : f i a = 0
        · left
          have hh := hfact i a
          rw [hz] at hh
          have hm : (monomial (binaryExponent a) (1 : ℝ)) ≠ 0 := by simp
          exact (expand_eq_zero (by decide : 0 < 2)).mp
            ((mul_eq_zero.mp hh.symm).resolve_left hm)
        · right
          obtain ⟨c,hc⟩ := MvPolynomial.exists_coeff_ne_zero hz
          have hodd := sector_oddExponent (f i a) a (hf i a).2 c
            (mem_support_iff.mpr hc)
          have hh := congrArg Finsupp.degree (exponent_split c)
          have hd : c.degree = r := by
            by_contra h
            exact hc ((hf i a).1.coeff_eq_zero h)
          simp [hodd,map_add,map_nsmul,nsmul_eq_mul,hd] at hh
          change (binaryExponent a).degree +
            2 * ((r - (binaryExponent a).degree) / 2) = r
          omega
    · apply expand_injective (by decide : 0 < 2)
      rw [map_sum]
      calc
        expand 2 p = ∑ i, ∑ a, f i a * f i a := he
        _ = ∑ j : J, f j.1 j.2 * f j.1 j.2 :=
          (Fintype.sum_prod_type (fun j : J => f j.1 j.2 * f j.1 j.2)).symm
        _ = ∑ j : Fin (Fintype.card J),
            f (e.symm j).1 (e.symm j).2 * f (e.symm j).1 (e.symm j).2 :=
          (e.symm.sum_comp _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [expand_square_factor,← hfact]
  · rintro ⟨m,α,d,q,_,rfl⟩
    rw [map_sum]
    simp_rw [expand_square_factor]
    exact IsSumSq.sum_mul_self Finset.univ _

#print axioms even_form_sos_iff

end BinaryParity

end
end D5.S3.QuadraticForms.HomogeneousSOS

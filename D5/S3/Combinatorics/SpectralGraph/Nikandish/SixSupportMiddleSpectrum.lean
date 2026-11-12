/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportMiddleSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact three middle-exponent regimes of the actual endpoint-one spectrum. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointOneSpectrum

/-! Source: endpoint-one-middle-root and endpoint-one-root-hierarchy notes,
revision 6d491f77b35dec808fc777b69939c56cdae5dc02, original blobs
8d35abb385270112d7865471ded1d756f109f76b and
6cb0e2bc4ef2fd8743678dc996645e3c4bb0b5d5. The proof consumes the full
actual six-support spectrum, including every algebraic multiplicity.
Real root location does not assert integer exponent-point existence. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportMiddleSpectrum
open Polynomial
open D5.S3.Combinatorics.SpectralGraph
open SixSupportClassificationAlgebra SixSupportEndpointOneArithmetic

/-- A fully split factorization of the actual endpoint-one residual,
with one low root and all three high roots counted with multiplicity. -/
theorem factor_roots (a b c : ℝ) (ha : 2+Real.sqrt 3 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (h1 : h a b c 1 = 0) :
    ∃ μ x y z : ℝ,
      quartic a b c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) ∧
      a < μ ∧ μ < min c (a+b) ∧
      a+b+c < x ∧ a+b+c < y ∧ a+b+c < z := by
  classical
  obtain ⟨μ,r,hr,hcard,hμa,hμU,hhigh⟩ :=
    SixSupportEndpointOneSpectrum.result a b c ha hab hbc h1
  obtain ⟨x,y,z,hrxyz⟩ := Multiset.card_eq_three.mp hcard
  have hmon : (quartic a b c).Monic := by unfold quartic; monicity!
  have hdeg : (quartic a b c).natDegree = 4 := by unfold quartic; compute_degree!
  have hall : (quartic a b c).roots.card = (quartic a b c).natDegree := by
    rw [hr,Multiset.card_add,Multiset.card_singleton,hcard,hdeg]
  have hf := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hall
  rw [hr,hrxyz] at hf
  have hfactor : quartic a b c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hf.symm
  refine ⟨μ,x,y,z,hfactor,hμa,hμU,?_,?_,?_⟩ <;>
    apply hhigh <;> rw [hrxyz] <;> simp

/-- Throughout the complete real endpoint-one domain, the sign of
c+a-b(b+2) is exactly the sign of the unique low residual root minus b.
The other three residual roots remain strictly above s, including ties. -/
theorem result (a b c : ℝ) (ha : 2+Real.sqrt 3 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (h1 : h a b c 1 = 0) :
    ∃ μ x y z : ℝ,
      quartic a b c = (X-C μ)*(X-C x)*(X-C y)*(X-C z) ∧
      a < μ ∧ μ < min c (a+b) ∧
      a+b+c < x ∧ a+b+c < y ∧ a+b+c < z ∧
      (0 < c+a-b*(b+2) ↔ b < μ) ∧
      (c+a-b*(b+2) = 0 ↔ μ = b) ∧
      (c+a-b*(b+2) < 0 ↔ μ < b) := by
  obtain ⟨μ,x,y,z,hf,hμa,hμU,hx,hy,hz⟩ := factor_roots a b c ha hab hbc h1
  have ha2 : 2 < a := by have := Real.sqrt_nonneg (3 : ℝ); linarith
  have hb1 : 1 < b := by linarith
  have habc : 0 < (a*b*c)^2 := by
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hc0 : 0 < c := by linarith
    positivity
  have hbx : b-x < 0 := by linarith
  have hby : b-y < 0 := by linarith
  have hbz : b-z < 0 := by linarith
  have hneg : (b-x)*(b-y)*(b-z) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hbx hby) hbz
  have hpos : 0 < -(b-1)*((b-x)*(b-y)*(b-z)) :=
    mul_pos_of_neg_of_neg (by linarith) hneg
  have he := congrArg (fun f : ℝ[X] => f.eval b) (factorization a b c)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C,h1,zero_mul,add_zero] at he
  change h a b c b = (b-1)*(quartic a b c).eval b at he
  rw [(exponent_value a b c).2.1,hf] at he
  simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  have hrel : (a*b*c)^2*(c+a-b*(b+2)) =
      (-(b-1)*((b-x)*(b-y)*(b-z)))*(μ-b) := by nlinarith only [he]
  have hsgn : (0 < c+a-b*(b+2) ↔ b < μ) := by
    constructor
    · intro hp
      have hp' := mul_pos habc hp
      rw [hrel] at hp'
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hpos).mp hp')
    · intro hp
      have hp' := mul_pos hpos (sub_pos.mpr hp)
      rw [← hrel] at hp'
      exact (mul_pos_iff_of_pos_left habc).mp hp'
  have heq : (c+a-b*(b+2) = 0 ↔ μ = b) := by
    constructor
    · intro he0
      rw [he0,mul_zero] at hrel
      exact sub_eq_zero.mp ((mul_eq_zero.mp hrel.symm).resolve_left hpos.ne')
    · intro hμ
      rw [hμ,sub_self,mul_zero] at hrel
      exact (mul_eq_zero.mp hrel).resolve_left habc.ne'
  have hsgn' : (c+a-b*(b+2) < 0 ↔ μ < b) := by
    constructor
    · intro hn
      have hn' := mul_neg_of_pos_of_neg habc hn
      rw [hrel] at hn'
      exact sub_neg.mp (neg_of_mul_neg_right hn' hpos.le)
    · intro hn
      have hn' := mul_neg_of_pos_of_neg hpos (sub_neg.mpr hn)
      rw [← hrel] at hn'
      exact neg_of_mul_neg_right hn' habc.le
  exact ⟨μ,x,y,z,hf,hμa,hμU,hx,hy,hz,hsgn,heq,hsgn'⟩

#print axioms factor_roots
#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportMiddleSpectrum

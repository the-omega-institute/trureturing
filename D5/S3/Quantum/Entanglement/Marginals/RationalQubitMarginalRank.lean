/- GID: D5/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rational positive two-qubit marginals admit a rational extension of rank at most three. -/

import D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix Complex
open scoped ComplexOrder ComplexConjugate Matrix Kronecker
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank

private def direction (x y : ℂ) : Bool → ℂ
  | false => x
  | true => y

private theorem rational_conj {z : ℂ} (hz : RationalEntry z) : RationalEntry (conj z) :=
  (rationalConjugate ⟨z, hz⟩).property

private theorem decompose_qubit (P : Matrix Bool Bool ℂ) (hP : P.PosSemidef) :
    ∃ (s t : ℂ) (x y : Bool → ℂ),
      x false = 1 ∧ y true = 1 ∧ 0 ≤ s ∧ 0 ≤ t ∧ P = s • vecMulVec x (star x) + t • vecMulVec y (star y) ∧
      ((∀ i j, RationalEntry (P i j)) →
        RationalEntry s ∧ RationalEntry t ∧ (∀ i, RationalEntry (x i)) ∧
          ∀ i, RationalEntry (y i)) := by
  let a := P false false
  let c := P false true
  let d := P true true
  have ha : 0 ≤ a := hP.diag_nonneg
  have ha' : conj a = a := hP.isHermitian.apply _ _
  have hc : conj c = P true false := hP.isHermitian.apply _ _
  have hd : 0 ≤ d := hP.diag_nonneg
  have hdet := (hP.submatrix finTwoEquiv).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  change 0 ≤ a * d - c * P true false at hdet
  rw [← hc] at hdet
  by_cases hz : a = 0
  · have hcz : c = 0 := by
      rw [hz, zero_mul, zero_sub, neg_nonneg, Complex.mul_conj] at hdet
      exact normSq_eq_zero.mp (le_antisymm (by exact_mod_cast hdet) (normSq_nonneg _))
    refine ⟨0, d, direction 1 0, direction 0 1, rfl, rfl, le_rfl, hd, ?_, ?_⟩
    · ext i j
      cases i <;> cases j <;> simp [direction, Matrix.vecMulVec_apply]
      · exact hz
      · exact hcz
      · simpa [hcz] using hc.symm
      · rfl
    · intro h
      refine ⟨rationalComplex.zero_mem, h true true, ?_, ?_⟩
      · intro i
        cases i
        · exact rationalComplex.one_mem
        · exact rationalComplex.zero_mem
      · intro i
        cases i
        · exact rationalComplex.zero_mem
        · exact rationalComplex.one_mem
  · let t := d - c * conj c / a
    let x := direction 1 (conj c / a)
    let y := direction 0 1
    have ht : 0 ≤ t := by
      have han : 0 ≤ a⁻¹ := by
        rw [Complex.nonneg_iff] at ha ⊢
        simp [Complex.inv_re, Complex.inv_im, ← ha.2,
          div_nonneg ha.1 (Complex.normSq_nonneg _)]
      have hmul := mul_nonneg hdet han
      have he : (a * d - c * conj c) * a⁻¹ = t := by
        dsimp [t]
        field_simp
      rwa [he] at hmul
    refine ⟨a, t, x, y, rfl, rfl, ha, ht, ?_, ?_⟩
    · ext i j
      cases i <;> cases j <;>
        simp [x, y, t, direction, Matrix.vecMulVec_apply, ← hc,
          ← show P false true = c by rfl, d, ha'] <;>
        first
        | rfl
        | field_simp
      all_goals ring
    · intro h
      have haQ : a ∈ rationalComplex := h false false
      have hcQ : c ∈ rationalComplex := h false true
      have hdQ : d ∈ rationalComplex := h true true
      have hcc : conj c ∈ rationalComplex := rational_conj hcQ
      refine ⟨haQ, rationalComplex.sub_mem hdQ
        (rationalComplex.div_mem (rationalComplex.mul_mem hcQ hcc) haQ), ?_, ?_⟩
      · intro i
        cases i
        · exact rationalComplex.one_mem
        · exact rationalComplex.div_mem hcc haQ
      · intro i
        cases i
        · exact rationalComplex.zero_mem
        · exact rationalComplex.one_mem

private theorem three_weights (a a' b b' : ℝ)
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b') (ht : a + a' = b + b')
    (haQ : RationalEntry (a : ℂ)) (haQ' : RationalEntry (a' : ℂ))
    (hbQ : RationalEntry (b : ℂ)) (hbQ' : RationalEntry (b' : ℂ)) :
    ∃ p q r s : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ 0 ≤ r ∧ 0 ≤ s ∧
      p + q = a ∧ r + s = a' ∧ p + r = b ∧ q + s = b' ∧ (q = 0 ∨ r = 0) ∧
      RationalEntry (p : ℂ) ∧ RationalEntry (q : ℂ) ∧
      RationalEntry (r : ℂ) ∧ RationalEntry (s : ℂ) := by
  rcases le_total a b with he | he
  · refine ⟨a, 0, b - a, b', ha, le_rfl, sub_nonneg.mpr he, hb', by ring, by linarith,
      by ring, by ring, Or.inl rfl, haQ, ?_, ?_, hbQ'⟩
    · exact rationalComplex.zero_mem
    · change ((b - a : ℝ) : ℂ) ∈ rationalComplex
      rw [Complex.ofReal_sub]
      exact rationalComplex.sub_mem hbQ haQ
  · refine ⟨b, a - b, 0, a', hb, sub_nonneg.mpr he, le_rfl, ha', by ring, by ring,
      by ring, by linarith, Or.inr rfl, hbQ, ?_, ?_, haQ'⟩
    · change ((a - b : ℝ) : ℂ) ∈ rationalComplex
      rw [Complex.ofReal_sub]
      exact rationalComplex.sub_mem haQ hbQ
    · exact rationalComplex.zero_mem

private theorem normalize_atom (s : ℂ) (hs : 0 ≤ s) (x : Bool → ℂ) (hx : x ≠ 0)
    (hsQ : RationalEntry s) (hxQ : ∀ i, RationalEntry (x i)) :
    ∃ (a : ℝ) (A : Matrix Bool Bool ℂ) (y : Bool → ℂ),
      0 ≤ a ∧ RationalEntry (a : ℂ) ∧ A.trace = 1 ∧
      (∀ i j, RationalEntry (A i j)) ∧ A = vecMulVec y (star y) ∧
      (a : ℂ) • A = s • vecMulVec x (star x) := by
  let T := vecMulVec x (star x)
  have hp : T.PosSemidef := Matrix.posSemidef_vecMulVec_self_star x
  have htrace0 : T.trace ≠ 0 := by
    intro h
    have hmat := hp.trace_eq_zero_iff.mp h
    apply hx
    funext i
    have hd := congrFun (congrFun hmat i) i
    change x i * conj (x i) = 0 at hd
    rw [Complex.mul_conj] at hd
    exact normSq_eq_zero.mp (Complex.ofReal_eq_zero.mp hd)
  have ht := Complex.nonneg_iff.mp hp.trace_nonneg
  let t := T.trace.re
  have htC : (t : ℂ) = T.trace := by
    apply Complex.ext <;> simp [t, ← ht.2]
  have htpos : 0 < t := by
    refine lt_of_le_of_ne ht.1 ?_
    intro h
    apply htrace0
    rw [← htC, ← h, Complex.ofReal_zero]
  let A := T.trace⁻¹ • T
  let y := fun i => ((t.sqrt)⁻¹ : ℝ) • x i
  have hA : ∀ i j, RationalEntry (A i j) := by
    have hT (i j : Bool) : T i j ∈ rationalComplex :=
      rationalComplex.mul_mem (hxQ i) (rational_conj (hxQ j))
    have htr : T.trace ∈ rationalComplex :=
      rationalComplex.sum_mem fun i _ => hT i i
    exact fun i j => rationalComplex.mul_mem (rationalComplex.inv_mem htr) (hT i j)
  have hsC : (s.re : ℂ) = s := by
    apply Complex.ext <;> simp [← (Complex.nonneg_iff.mp hs).2]
  have hcoef : ((s.re * t : ℝ) : ℂ) = s * T.trace := by
    rw [Complex.ofReal_mul, hsC, htC]
  refine ⟨s.re * t, A, y, mul_nonneg (Complex.nonneg_iff.mp hs).1 htpos.le, ?_, ?_, hA, ?_, ?_⟩
  · rw [hcoef]
    have hT (i : Bool) : T i i ∈ rationalComplex :=
      rationalComplex.mul_mem (hxQ i) (rational_conj (hxQ i))
    exact rationalComplex.mul_mem hsQ (rationalComplex.sum_mem fun i _ => hT i)
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htrace0]
  · have hroot : (t.sqrt)⁻¹ * (t.sqrt)⁻¹ = t⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt htpos.le]
    ext i j
    simp only [A, T, y, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.real_smul, RCLike.star_def, map_mul, Complex.conj_ofReal, smul_eq_mul]
    rw [← htC, ← Complex.ofReal_inv, ← hroot, Complex.ofReal_mul]
    ring
  · rw [hcoef, smul_smul, mul_assoc, mul_inv_cancel₀ htrace0, mul_one]

private abbrev atom (u : Bool → ℂ) := vecMulVec u (star u)

private theorem two_atoms (P : Matrix Bool Bool ℂ) (hP : P.PosSemidef)
    (hQ : ∀ i j, RationalEntry (P i j)) :
    ∃ (a a' : ℝ) (u u' : Bool → ℂ),
      0 ≤ a ∧ 0 ≤ a' ∧ RationalEntry (a : ℂ) ∧ RationalEntry (a' : ℂ) ∧
      (atom u).trace = 1 ∧ (atom u').trace = 1 ∧
      (∀ i j, RationalEntry (atom u i j)) ∧
      (∀ i j, RationalEntry (atom u' i j)) ∧
      P = (a : ℂ) • atom u + (a' : ℂ) • atom u' := by
  obtain ⟨s, t, x, y, hx, hy, hs, ht, hP', hR⟩ := decompose_qubit P hP
  obtain ⟨hsQ, htQ, hxQ, hyQ⟩ := hR hQ
  have hx0 : x ≠ 0 := by
    intro h
    have e := congrFun h false
    rw [hx] at e
    exact one_ne_zero e
  have hy0 : y ≠ 0 := by
    intro h
    have e := congrFun h true
    rw [hy] at e
    exact one_ne_zero e
  obtain ⟨a, A, u, ha, haQ, hAtr, hAQ, rfl, hA⟩ := normalize_atom s hs x hx0 hsQ hxQ
  obtain ⟨a', A', u', ha', haQ', hAtr', hAQ', rfl, hA'⟩ := normalize_atom t ht y hy0 htQ hyQ
  exact ⟨a, a', u, u', ha, ha', haQ, haQ', hAtr, hAtr', hAQ, hAQ',
    by rw [hA, hA', ← hP']⟩

private theorem trace_two_atoms {P : Matrix Bool Bool ℂ} {a a' : ℝ}
    {u u' : Bool → ℂ} (h : P = (a : ℂ) • atom u + (a' : ℂ) • atom u')
    (h1 : (atom u).trace = 1) (h2 : (atom u').trace = 1) :
    P.trace.re = a + a' := by
  simp [h, Matrix.trace_add, Matrix.trace_smul, h1, h2, Complex.add_re]

private theorem kronecker_atom (x y : Bool → ℂ) :
    atom x ⊗ₖ atom y =
      let z := fun k : Bool × Bool => x k.1 * y k.2
      vecMulVec z (star z) := by
  ext i j
  simp [Matrix.vecMulVec_apply, Pi.star_apply]
  ring

private theorem scale_outer {n : Type*} (a : ℝ) (ha : 0 ≤ a) (x : n → ℂ) :
    (a : ℂ) • vecMulVec x (star x) =
      let z := fun i => (a.sqrt : ℂ) * x i
      vecMulVec z (star z) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply,
    RCLike.star_def, map_mul, Complex.conj_ofReal]
  have he : (a.sqrt : ℂ) * (a.sqrt : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  calc
    _ = ((a.sqrt : ℂ) * (a.sqrt : ℂ)) * (x i * conj (x j)) := by rw [he]
    _ = _ := by ring

private theorem rank_outer_sum3 {n : Type*} [Fintype n] (x y z : n → ℂ) :
    (vecMulVec x (star x) + vecMulVec y (star y) + vecMulVec z (star z)).rank ≤ 3 := by
  let M : Matrix n (Fin 3) ℂ := fun i j => ![x i, y i, z i] j
  have hM : M * Mᴴ = vecMulVec x (star x) + vecMulVec y (star y) + vecMulVec z (star z) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [Matrix.conjTranspose_apply]
    simp [M, Matrix.vecMulVec_apply, Pi.star_apply, add_assoc]
  rw [← hM]
  exact (rank_mul_le_left M Mᴴ).trans (by simpa using rank_le_card_width M)

private theorem term_positive (x y : Bool → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ((a : ℂ) • (atom x ⊗ₖ atom y)).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · exact (Matrix.posSemidef_vecMulVec_self_star x).kronecker
      (Matrix.posSemidef_vecMulVec_self_star y)
  · exact_mod_cast ha

private theorem term_rational {a : ℝ} {x y : Bool → ℂ} (h : RationalEntry (a : ℂ))
    (hx : ∀ i j, RationalEntry (atom x i j)) (hy : ∀ i j, RationalEntry (atom y i j)) :
    ∀ i j, RationalEntry (((a : ℂ) • (atom x ⊗ₖ atom y)) i j) := by
  intro i j
  exact rationalComplex.mul_mem h (rationalComplex.mul_mem (hx _ _) (hy _ _))

private theorem term_left (x y : Bool → ℂ) (a : ℝ) (h : (atom y).trace = 1) :
    partialTraceRight ((a : ℂ) • (atom x ⊗ₖ atom y)) = (a : ℂ) • atom x := by
  have he :
      (a : ℂ) • (atom x ⊗ₖ atom y) = (((a : ℂ) • atom x) ⊗ₖ atom y) :=
    (smul_kronecker _ _ _).symm
  rw [he]
  change partialTraceRight (kronecker ((a : ℂ) • atom x) (atom y)) = _
  rw [partialTraceRight_kronecker, h, one_smul]

private theorem term_right (x y : Bool → ℂ) (a : ℝ) (h : (atom x).trace = 1) :
    partialTraceLeft ((a : ℂ) • (atom x ⊗ₖ atom y)) = (a : ℂ) • atom y := by
  have he :
      (a : ℂ) • (atom x ⊗ₖ atom y) = (atom x ⊗ₖ ((a : ℂ) • atom y)) :=
    (kronecker_smul _ _ _).symm
  rw [he]
  change partialTraceLeft (kronecker (atom x) ((a : ℂ) • atom y)) = _
  rw [partialTraceLeft_kronecker, h, one_smul]

private theorem rank_three_atoms (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (x y u v w z : Bool → ℂ) :
    ((a : ℂ) • (atom x ⊗ₖ atom y) + (b : ℂ) • (atom u ⊗ₖ atom v) +
      (c : ℂ) • (atom w ⊗ₖ atom z)).rank ≤ 3 := by
  rw [kronecker_atom, kronecker_atom, kronecker_atom,
    scale_outer a ha, scale_outer b hb, scale_outer c hc]
  exact rank_outer_sum3 _ _ _

/-- Two rational positive qubit marginals of equal trace admit a rational joint
positive matrix of rank at most three. -/
private theorem construct_rational_extension (L R : Matrix Bool Bool ℂ)
    (hL : L.PosSemidef) (hR : R.PosSemidef) (htrace : L.trace = R.trace)
    (hLQ : ∀ i j, RationalEntry (L i j)) (hRQ : ∀ i j, RationalEntry (R i j)) :
    ∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      S.PosSemidef ∧ partialTraceRight S = L ∧ partialTraceLeft S = R ∧
      S.rank ≤ 3 ∧ ∀ i j, RationalEntry (S i j) := by
  obtain ⟨a, a', x, x', ha, ha', haQ, haQ', hx, hx', hxQ, hxQ', hLe⟩ := two_atoms L hL hLQ
  obtain ⟨b, b', y, y', hb, hb', hbQ, hbQ', hy, hy', hyQ, hyQ', hRe⟩ := two_atoms R hR hRQ
  have ht : a + a' = b + b' :=
    (trace_two_atoms hLe hx hx').symm.trans
      ((congrArg Complex.re htrace).trans (trace_two_atoms hRe hy hy'))
  obtain ⟨p, q, r, s, hp, hq, hr, hs, hpa, hraa, hpb, hqbb, hzero, hpQ, hqQ, hrQ, hsQ⟩ :=
    three_weights a a' b b' ha ha' hb hb' ht haQ haQ' hbQ hbQ'
  let E := (p : ℂ) • (atom x ⊗ₖ atom y)
  let F := (q : ℂ) • (atom x ⊗ₖ atom y')
  let G := (r : ℂ) • (atom x' ⊗ₖ atom y)
  let H := (s : ℂ) • (atom x' ⊗ₖ atom y')
  refine ⟨E + F + G + H, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((term_positive x y p hp).add (term_positive x y' q hq)).add
      (term_positive x' y r hr)).add (term_positive x' y' s hs)
  · simp only [partialTraceRight_add, E, F, G, H, term_left _ _ _ hy, term_left _ _ _ hy']
    rw [hLe, add_assoc ((p : ℂ) • atom x + (q : ℂ) • atom x),
      ← add_smul, ← Complex.ofReal_add, hpa, ← add_smul, ← Complex.ofReal_add, hraa]
  · simp only [partialTraceLeft_add, E, F, G, H, term_right _ _ _ hx, term_right _ _ _ hx']
    rw [hRe, add_right_comm ((p : ℂ) • atom y), add_assoc, ← add_smul,
      ← Complex.ofReal_add, hpb, ← add_smul, ← Complex.ofReal_add, hqbb]
  · rcases hzero with h | h
    · simpa [E, F, G, H, h] using rank_three_atoms p r s hp hr hs x y x' y x' y'
    · simpa [E, F, G, H, h] using rank_three_atoms p q s hp hq hs x y x y' x' y'
  · intro i j
    exact rationalComplex.add_mem
      (rationalComplex.add_mem
        (rationalComplex.add_mem
          (term_rational hpQ hxQ hyQ i j)
          (term_rational hqQ hxQ hyQ' i j))
        (term_rational hrQ hxQ' hyQ i j))
      (term_rational hsQ hxQ' hyQ' i j)

/-- The two endpoint matrices admit a rational positive joint matrix of rank at most
three exactly when they are rational, positive semidefinite, and have equal trace. -/
theorem rational_endpoint_rank_le_three (L R : Matrix Bool Bool ℂ) :
    (∃ S : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      S.PosSemidef ∧ partialTraceRight S = L ∧ partialTraceLeft S = R ∧
        S.rank ≤ 3 ∧ ∀ i j, RationalEntry (S i j)) ↔
      L.PosSemidef ∧ R.PosSemidef ∧ L.trace = R.trace ∧
        (∀ i j, RationalEntry (L i j)) ∧ ∀ i j, RationalEntry (R i j) := by
  constructor
  · rintro ⟨S, hS, rfl, rfl, _, hQ⟩
    refine ⟨partialTraceRight_posSemidef hS, partialTraceLeft_posSemidef hS,
      (trace_partialTraceRight S).trans (trace_partialTraceLeft S).symm, ?_, ?_⟩
    · intro i j
      exact rationalComplex.sum_mem fun k _ => hQ (i, k) (j, k)
    · intro i j
      exact rationalComplex.sum_mem fun k _ => hQ (k, i) (k, j)
  · rintro ⟨hL, hR, ht, hLQ, hRQ⟩
    exact construct_rational_extension L R hL hR ht hLQ hRQ

end D5.S3.Quantum.Entanglement.Marginals.RationalQubitMarginalRank

/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalTwoVertexLoop
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalTwoVertexLoop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint absolute convergence of the literal fixed-sector two-vertex occupation loop. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutScalar
import Batteries.Tactic.OpenPrivate

/-! Factorial contraction of the two original mixed occupation kernels. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalTwoVertexLoop

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial LatticeAllStateField
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents FieldNormalProduct
open CanonicalOccupationSewing
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open scoped BigOperators VertexOperator

open private wordCoeff from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private factorialEnvelope factorialEnvelope_nonneg factorialEnvelope_summable
  factorialEnvelope_mul canonical_basis_input_expansion
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
open private mixedEnvelope mixedEnvelope_nonneg overlapBinomial chooseKernel chooseKernel_eq
  translationEnvelope
  mixedConstant mixedRadius mixedEnergy mixedConstant_nonneg mixed_descendant_bound
  from D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutOccupation
open private factorialEnvelope_prod factorial_binomial_cancel overlap_cancellation
  radial_polynomial_bound from D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutScalar

noncomputable section

private theorem envelope_pos (D : LatticeData) (B : ℝ) (hB : 0 < B) (d : Occ D) :
    0 < factorialEnvelope D B d := by
  classical
  rw [factorialEnvelope_prod D B d d.support (by rfl)]
  exact Finset.prod_pos (fun x hx => div_pos (pow_pos (div_pos hB (by positivity)) _)
    (by positivity))

private theorem envelope_mono (D : LatticeData) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (d : Occ D) : factorialEnvelope D A d ≤ factorialEnvelope D B d := by
  classical
  rw [factorialEnvelope_prod D A d d.support (by rfl),
    factorialEnvelope_prod D B d d.support (by rfl)]
  apply Finset.prod_le_prod₀
  · intro x hx; positivity
  · intro x hx
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg hA (by positivity))
        (div_le_div_of_nonneg_right hAB (by positivity)) _) (by positivity)

/-- The finite factorial convolution, including every retained occupation.
This is the binomial contraction used by the two reverse kernels. -/
private theorem envelope_convolution (D : LatticeData) (A B : ℝ) (d : Occ D) :
    (∑ u ∈ Finset.Iic d, factorialEnvelope D B u * factorialEnvelope D A (d-u)) =
      factorialEnvelope D (B+A) d := by
  classical
  have hsub (u : Occ D) (hu : u ≤ d) : u.support ⊆ d.support := by
    intro x hx
    simp only [Finsupp.mem_support_iff] at hx ⊢
    have hh := hu x
    omega
  have hdiff (u : Occ D) : (d-u).support ⊆ d.support := by
    intro x hx
    simp only [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hx ⊢
    omega
  have hi : Finset.Iic d = d.support.finsupp (fun x => Finset.range (d x+1)) := by
    ext u
    rw [Finset.mem_Iic, Finset.mem_finsupp_iff]
    constructor
    · intro hu
      exact ⟨hsub u hu, fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (hu x))⟩
    · rintro ⟨hu,h⟩ x
      by_cases hx : x ∈ d.support
      · exact Nat.le_of_lt_succ (Finset.mem_range.mp (h x hx))
      · have hz : u x = 0 := Finsupp.notMem_support_iff.mp (fun hh => hx (hu hh))
        simp [hz]
  calc
    _ = ∑ u ∈ Finset.Iic d, ∏ x ∈ d.support,
        (B / (x.2+1 : ℝ)) ^ u x / ((u x).factorial : ℝ) *
          ((A / (x.2+1 : ℝ)) ^ (d x-u x) / ((d x-u x).factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [factorialEnvelope_prod D B u d.support (hsub u (Finset.mem_Iic.mp hu)),
        factorialEnvelope_prod D A (d-u) d.support (hdiff u), ← Finset.prod_mul_distrib]
      simp only [Finsupp.tsub_apply]
    _ = ∏ x ∈ d.support, ∑ n ∈ Finset.range (d x+1),
        (B / (x.2+1 : ℝ)) ^ n / (n.factorial : ℝ) *
          ((A / (x.2+1 : ℝ)) ^ (d x-n) / ((d x-n).factorial : ℝ)) := by
      rw [hi, Finset.finsupp, Finset.sum_map, Finset.prod_sum]
      simp only [Function.Embedding.coeFn_mk]
      apply Finset.sum_congr
      · ext f
        simp only [Finset.mem_pi]
      · intro f hf
        conv_lhs => rw [← Finset.prod_attach]
        apply Finset.prod_congr rfl
        intro x hx
        simp [Finsupp.indicator_of_mem x.2]
    _ = factorialEnvelope D (B+A) d := by
      rw [factorialEnvelope_prod D (B+A) d d.support (by rfl)]
      apply Finset.prod_congr rfl
      intro x hx
      have hn (n : ℕ) (hn : n ∈ Finset.range (d x+1)) :
          (B / (x.2+1 : ℝ)) ^ n / (n.factorial : ℝ) *
            ((A / (x.2+1 : ℝ)) ^ (d x-n) / ((d x-n).factorial : ℝ)) =
          ((B / (x.2+1 : ℝ)) ^ n * (A / (x.2+1 : ℝ)) ^ (d x-n) *
            ((d x).choose n : ℝ)) / ((d x).factorial : ℝ) := by
        have hle : n ≤ d x := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have hfact : ((d x).choose n : ℝ) * (n.factorial : ℝ) *
            ((d x-n).factorial : ℝ) = ((d x).factorial : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
        field_simp
        rw [← hfact]
        ring
      rw [Finset.sum_congr rfl hn, ← Finset.sum_div, ← add_pow, ← add_div]

private theorem degree_le_level (D : LatticeData) (d : Occ D) : d.degree ≤ level D d := by
  classical
  simp only [Finsupp.degree_apply, level, LatticePositiveEnergy.oscillatorEnergy,
    Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  apply Finset.sum_le_sum
  intro x hx
  exact Nat.le_mul_of_pos_right _ (by omega)

/-- An actual factorial Schur estimate for the source mixed kernel. Only the
input radius is damped. No factor involving T enters its contraction ratio. -/
private theorem mixed_schur (D : LatticeData) (A T B ρ : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hB : 0 < B) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hclose : ρ * B + A ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d e : Occ D,
      ρ ^ level D e * mixedEnvelope D A T d e * factorialEnvelope D B e ≤
        C * factorialEnvelope D B d := by
  classical
  let f := fun w : Occ D => ρ ^ level D w * factorialEnvelope D (B*T) w
  have hf : Summable f := by
    simpa [f, abs_of_nonneg hρ] using factorialEnvelope_summable D (B*T)
      (mul_nonneg hB.le hT) (ρ : ℂ) (by simpa [abs_of_nonneg hρ] using hρ1)
  have hf0 (w : Occ D) : 0 ≤ f w := mul_nonneg (pow_nonneg hρ _)
    (factorialEnvelope_nonneg D _ (mul_nonneg hB.le hT) _)
  let C := ∑' w, f w
  have hC : 0 ≤ C := tsum_nonneg hf0
  refine ⟨C,hC,fun d e => ?_⟩
  let S := (Finset.Iic d).filter (fun u : Occ D => u ≤ e)
  have hterm (u : Occ D) (hu : u ∈ S) :
      ρ ^ level D e * (overlapBinomial D e u * T^(e-u).degree *
        factorialEnvelope D A (d-u)) * factorialEnvelope D B e ≤
      C * (factorialEnvelope D (ρ*B) u * factorialEnvelope D A (d-u)) := by
    have hud : u ≤ d := Finset.mem_Iic.mp (Finset.mem_filter.mp hu).1
    have hue : u ≤ e := (Finset.mem_filter.mp hu).2
    have hd : u+(d-u)=d := add_tsub_cancel_of_le hud
    have he : u+(e-u)=e := add_tsub_cancel_of_le hue
    have hc := overlap_cancellation D 1 B A T u (d-u) (e-u)
    rw [hd,he] at hc
    simp only [one_pow, one_mul, translationEnvelope, chooseKernel_eq D e u hue] at hc
    have hl : level D e = level D u + level D (e-u) := by
      have hh : level D (u+(e-u)) = level D u + level D (e-u) := by
        simp only [level, LatticePositiveEnergy.oscillatorEnergy, map_add]
      exact (congrArg (level D) he).symm.trans hh
    have hb : f (e-u) ≤ C := hf.le_tsum (e-u) (fun _ _ => hf0 _)
    calc
      _ = (ρ ^ level D u * factorialEnvelope D B u * factorialEnvelope D A (d-u)) *
          f (e-u) := by
        rw [hl,pow_add]
        dsimp [f]
        linear_combination (ρ ^ level D u * ρ ^ level D (e-u)) * hc
      _ ≤ (ρ ^ u.degree * factorialEnvelope D B u * factorialEnvelope D A (d-u)) * C := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ hρ1.le
              (degree_le_level D u)) (factorialEnvelope_nonneg D B hB.le _))
            (factorialEnvelope_nonneg D A hA _)
        · exact hb
        · exact hf0 _
        · exact mul_nonneg (mul_nonneg (pow_nonneg hρ _)
            (factorialEnvelope_nonneg D B hB.le _)) (factorialEnvelope_nonneg D A hA _)
      _ = _ := by rw [factorialEnvelope_mul]; ring
  calc
    _ = ∑ u ∈ S, ρ ^ level D e * (overlapBinomial D e u * T^(e-u).degree *
        factorialEnvelope D A (d-u)) * factorialEnvelope D B e := by
      simp only [mixedEnvelope, S, Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ u ∈ S, C * (factorialEnvelope D (ρ*B) u * factorialEnvelope D A (d-u)) :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ u ∈ Finset.Iic d,
        C * (factorialEnvelope D (ρ*B) u * factorialEnvelope D A (d-u)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      intro u hu hn
      exact mul_nonneg hC (mul_nonneg
        (factorialEnvelope_nonneg D _ (mul_nonneg hρ hB.le) _)
        (factorialEnvelope_nonneg D A hA _))
    _ = C * factorialEnvelope D (ρ*B+A) d := by
      rw [← Finset.mul_sum, envelope_convolution]
    _ ≤ C * factorialEnvelope D B d := mul_le_mul_of_nonneg_left
      (envelope_mono D (by positivity) hclose d) hC

private theorem cyclic_envelope_summable (D : LatticeData) (A T : ℝ)
    (hA : 1 ≤ A) (hT : 0 ≤ T) (r1 r2 : ℝ)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hr1' : r1 < 1) (hr2' : r2 < 1) :
    Summable (fun z : Occ D × Occ D => r1 ^ level D z.1 * r2 ^ level D z.2 *
      mixedEnvelope D A T z.1 z.2 * mixedEnvelope D A T z.2 z.1) := by
  let ρ := (1+max r1 r2)/2
  have hρ : 0 < ρ := by dsimp [ρ]; have := le_max_left r1 r2; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := max_lt hr1' hr2'; linarith
  have h1ρ : r1 < ρ := by dsimp [ρ]; have := le_max_left r1 r2; linarith
  have h2ρ : r2 < ρ := by dsimp [ρ]; have := le_max_right r1 r2; linarith
  let B := (A+1)/(1-ρ)
  have hB : 0 < B := div_pos (by linarith) (by linarith)
  have hclose : ρ*B+A ≤ B := by
    have heq : B*(1-ρ)=A+1 := by dsimp [B]; field_simp
    nlinarith
  obtain ⟨C,hC,hschur⟩ := mixed_schur D A T B ρ (by linarith) hT hB hρ.le hρ1 hclose
  have hcycle (d e : Occ D) :
      ρ ^ level D d * ρ ^ level D e * mixedEnvelope D A T d e *
        mixedEnvelope D A T e d ≤ C*C := by
    have hh := mul_le_mul (hschur d e) (hschur e d)
      (mul_nonneg (mul_nonneg (pow_nonneg hρ.le _) (mixedEnvelope_nonneg D A T
        (by linarith) hT e d)) (envelope_pos D B hB d).le)
      (mul_nonneg hC (envelope_pos D B hB d).le)
    have hp := mul_pos (envelope_pos D B hB d) (envelope_pos D B hB e)
    apply (mul_le_mul_iff_left₀ hp).mp
    convert hh using 1 <;> ring
  have hs (r : ℝ) (hr : 0 ≤ r) (hrρ : r < ρ) :
      Summable (fun d : Occ D => (r/ρ)^level D d) := by
    have hh : ‖(r/ρ : ℝ)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hρ.le)]
      exact (div_lt_one hρ).mpr hrρ
    have hh' : ‖((r/ρ : ℝ) : ℂ)‖ < 1 := by simpa using hh
    simpa [signedIntegerMonomial, integerEnergy, level,
      LatticePositiveEnergy.oscillatorEnergy, norm_mul, norm_pow,
      abs_of_nonneg hr, abs_of_pos hρ] using
      summable_norm_signed_integer_occupations (Fin D.rank) hh'
  have hs1 := hs r1 hr1 h1ρ
  have hs2 := hs r2 hr2 h2ρ
  have hsum := (hs1.mul_of_nonneg hs2 (fun _ => by positivity)
    (fun _ => by positivity)).mul_left (C*C)
  refine hsum.of_nonneg_of_le (fun z : Occ D × Occ D => by
    exact mul_nonneg (mul_nonneg (by positivity)
      (mixedEnvelope_nonneg D A T (by linarith) hT _ _))
      (mixedEnvelope_nonneg D A T (by linarith) hT _ _)) ?_
  rintro ⟨d,e⟩
  calc
    _ = ((r1/ρ)^level D d * (r2/ρ)^level D e) *
        (ρ^level D d * ρ^level D e * mixedEnvelope D A T d e *
          mixedEnvelope D A T e d) := by
      simp only [div_pow]
      field_simp
    _ ≤ ((r1/ρ)^level D d * (r2/ρ)^level D e) * (C*C) :=
      mul_le_mul_of_nonneg_left (hcycle d e) (by positivity)
    _ = _ := by ring

private theorem word_loop_summable (D : LatticeData) (a b : Charge D)
    (ω ν : List (Index D)) (r s : ℤ) (q1 q2 : ℂ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Occ D × Occ D =>
      ‖q1^level D z.1 * q2^level D z.2 *
        wordCoeff D a (-a+b) ω (r+(level D z.2 : ℤ)-(level D z.1 : ℤ)) z.1 z.2 *
        wordCoeff D (-a) b ν (s+(level D z.1 : ℤ)-(level D z.2 : ℤ)) z.2 z.1‖) := by
  classical
  let A : ℝ := 1+∑ i : Fin D.rank, ‖(a i : ℂ)‖
  let T : ℝ := 1+∑ i : Fin D.rank, ‖(bilinear D a (unitCharge D i) : ℂ)‖
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have hT : 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have ha (i : Fin D.rank) : ‖(a i : ℂ)‖ ≤ A := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ => norm_nonneg (a j : ℂ))
      (Finset.mem_univ i)
    dsimp [A]; linarith
  have ht (i : Fin D.rank) : ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ =>
      norm_nonneg (bilinear D a (unitCharge D j) : ℂ)) (Finset.mem_univ i)
    dsimp [T]; linarith
  have hna (i : Fin D.rank) : ‖((-a) i : ℂ)‖ ≤ A := by simpa using ha i
  have hnt (i : Fin D.rank) : ‖(bilinear D (-a) (unitCharge D i) : ℂ)‖ ≤ T := by
    simpa [bilinear_neg_left] using ht i
  let C := mixedConstant D a (-a+b) A T ω * mixedConstant D (-a) b A T ν
  let J := mixedRadius D ω + mixedRadius D ν
  have hC : 0 ≤ C := mul_nonneg (mixedConstant_nonneg D a (-a+b) ω A T hA hT)
    (mixedConstant_nonneg D (-a) b ν A T hA hT)
  have hCω := mixedConstant_nonneg D a (-a+b) ω A T hA hT
  let ρ1 := (1+‖q1‖)/2
  let ρ2 := (1+‖q2‖)/2
  obtain ⟨C1,hC1,hb1⟩ := radial_polynomial_bound J ‖q1‖ (norm_nonneg _) hq1
  obtain ⟨C2,hC2,hb2⟩ := radial_polynomial_bound J ‖q2‖ (norm_nonneg _) hq2
  have hsum := (cyclic_envelope_summable D A T hA (by linarith) ρ1 ρ2
    (by dsimp [ρ1]; positivity) (by dsimp [ρ2]; positivity)
    (by dsimp [ρ1]; linarith) (by dsimp [ρ2]; linarith)).mul_left (C*C1*C2)
  refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨d,e⟩
  have hM := mixedEnvelope_nonneg D A T (by linarith) (by linarith) d e
  have hM' := mixedEnvelope_nonneg D A T (by linarith) (by linarith) e d
  have henergy : mixedEnergy D d e ≤ (1+(level D d : ℝ))*(1+(level D e : ℝ)) := by
    dsimp [mixedEnergy]
    have := Nat.cast_nonneg (α := ℝ) (level D d)
    have := Nat.cast_nonneg (α := ℝ) (level D e)
    nlinarith
  have hbound :
      ‖wordCoeff D a (-a+b) ω (r+(level D e : ℤ)-(level D d : ℤ)) d e‖ *
        ‖wordCoeff D (-a) b ν (s+(level D d : ℤ)-(level D e : ℤ)) e d‖ ≤
      C * ((1+(level D d : ℝ))^J * (1+(level D e : ℝ))^J) *
        mixedEnvelope D A T d e * mixedEnvelope D A T e d := by
    calc
      _ ≤ (mixedConstant D a (-a+b) A T ω * mixedEnergy D d e ^ mixedRadius D ω *
          mixedEnvelope D A T d e) *
        (mixedConstant D (-a) b A T ν * mixedEnergy D e d ^ mixedRadius D ν *
          mixedEnvelope D A T e d) :=
        mul_le_mul (mixed_descendant_bound D a (-a+b) A T hA hT ha ht ω _ d e)
          (mixed_descendant_bound D (-a) b A T hA hT hna hnt ν _ e d)
          (norm_nonneg _) (mul_nonneg (mul_nonneg hCω
            (pow_nonneg (by dsimp [mixedEnergy]; positivity) _)) hM)
      _ = C * mixedEnergy D d e ^ J * mixedEnvelope D A T d e *
          mixedEnvelope D A T e d := by
        have he : mixedEnergy D e d = mixedEnergy D d e := by dsimp [mixedEnergy]; ring
        rw [he]
        dsimp [C,J]
        rw [pow_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hM'
        apply mul_le_mul_of_nonneg_right _ hM
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [mul_pow] using pow_le_pow_left₀ (by dsimp [mixedEnergy]; positivity) henergy J
  simp only [norm_mul,norm_pow]
  calc
    _ = (‖q1‖^level D d * ‖q2‖^level D e) *
        (‖wordCoeff D a (-a+b) ω (r+(level D e : ℤ)-(level D d : ℤ)) d e‖ *
          ‖wordCoeff D (-a) b ν (s+(level D d : ℤ)-(level D e : ℤ)) e d‖) := by ring
    _ ≤ (‖q1‖^level D d * ‖q2‖^level D e) *
        (C*((1+(level D d : ℝ))^J * (1+(level D e : ℝ))^J) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = C * (‖q1‖^level D d * (1+(level D d : ℝ))^J) *
        (‖q2‖^level D e * (1+(level D e : ℝ))^J) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d := by ring
    _ ≤ C * (C1*ρ1^level D d) * (C2*ρ2^level D e) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d := by
      apply mul_le_mul_of_nonneg_right _ hM'
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb1 (level D d)) hC)
        (hb2 (level D e)) (by positivity) (by positivity)
    _ = _ := by ring

/-- Joint absolute summability of the literal two-vertex loop in the fixed
charge sector b. Both occupations are unrestricted, including zero radii. -/
theorem canonical_two_vertex_loop_summable (D : LatticeData) (a b : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Occ D × Occ D =>
      ‖q1^level D z.1 * q2^level D z.2 *
        (canonical D a (-a+b) u
          (r+(level D z.2 : ℤ)-(level D z.1 : ℤ))
          (CanonicalOccupationSewing.b D z.2)).coeff z.1 *
        (canonical D (-a) b v
          (s+(level D z.1 : ℤ)-(level D z.2 : ℤ))
          (CanonicalOccupationSewing.b D z.1)).coeff z.2‖) := by
  classical
  have hs : Summable (fun z : Occ D × Occ D =>
      ∑ U ∈ u.support, ∑ V ∈ v.support,
        ‖(u.coeff U * v.coeff V) *
          (q1^level D z.1 * q2^level D z.2 *
            wordCoeff D a (-a+b) (occurrences D U)
              (r+(level D z.2 : ℤ)-(level D z.1 : ℤ)) z.1 z.2 *
            wordCoeff D (-a) b (occurrences D V)
              (s+(level D z.1 : ℤ)-(level D z.2 : ℤ)) z.2 z.1)‖) := by
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    simpa only [norm_mul] using
      (word_loop_summable D a b (occurrences D U) (occurrences D V) r s q1 q2 hq1 hq2).mul_left
        ‖u.coeff U * v.coeff V‖
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨d,e⟩
  have heq : q1^level D d * q2^level D e *
      (canonical D a (-a+b) u (r+(level D e : ℤ)-(level D d : ℤ))
        (CanonicalOccupationSewing.b D e)).coeff d *
      (canonical D (-a) b v (s+(level D d : ℤ)-(level D e : ℤ))
        (CanonicalOccupationSewing.b D d)).coeff e =
      ∑ U ∈ u.support, ∑ V ∈ v.support,
        (u.coeff U * v.coeff V) *
          (q1^level D d * q2^level D e *
            wordCoeff D a (-a+b) (occurrences D U)
              (r+(level D e : ℤ)-(level D d : ℤ)) d e *
            wordCoeff D (-a) b (occurrences D V)
              (s+(level D d : ℤ)-(level D e : ℤ)) e d) := by
    simp only [canonical_basis_input_expansion, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    ring
  rw [heq]
  apply norm_sum_le_of_le
  intro U hU
  exact norm_sum_le _ _

end
end D5.S3.VertexAlgebra.CanonicalTwoVertexLoop

#print axioms D5.S3.VertexAlgebra.CanonicalTwoVertexLoop.canonical_two_vertex_loop_summable

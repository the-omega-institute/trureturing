/- GID: D5/S3/Quantum/Magic/QuquintFiniteMaximum
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintFiniteMaximum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Magic/QuquintStrictDecrease.directional_decrease; premises=D5/S3/Quantum/Magic/QuquintCertificateAssembly.all_branches_negative; result=D5/S3/Quantum/Magic/QuquintFiniteMaximum.second_variation_negative
   digest: The exact finite sign maximum and both directions of the negativity criterion. -/

import D5.S3.Quantum.Magic.QuquintCertificateBridge
import D5.S3.Quantum.Magic.QuquintCertificateAssembly

noncomputable section
open Matrix
open scoped BigOperators
open D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
open D5.S3.Quantum.Magic.QuquintCertificateData (base zeroQ branch)
open D5.S3.Quantum.Magic.QuquintCertificateBridge
open D5.S3.Quantum.Magic.QuquintCertificateAssembly
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000

namespace D5.S3.Quantum.Magic.QuquintFiniteMaximum

def signPattern (s : Fin 32) (i : Fin 5) : Bool :=
  decide (s.val / 2 ^ (4 - i.val) % 2 ≠ 0)

def signValue (s : Fin 32) (i : Fin 5) : ℝ :=
  if signPattern s i then 1 else -1

def secondVariation (v : State) : ℝ :=
  (∑ qp ∈ (Finset.univ \ zeroPoints),
    (SignType.sign (wigner psi qp.1 qp.2) : ℝ) * wigner v qp.1 qp.2) +
    (∑ qp ∈ zeroPoints, |wigner v qp.1 qp.2|) - lOne psi * ‖v‖ ^ 2

def branchMaximum (a : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun s : Fin 32 => a ⬝ᵥ (branch s *ᵥ a))

private theorem signPattern_surjective : Function.Surjective signPattern := by decide

private theorem signValue_eq (s : Fin 32) (i : Fin 5) : signValue s i =
    if s.val / 2 ^ (4 - i.val) % 2 = 0 then -1 else 1 := by
  by_cases h : s.val / 2 ^ (4 - i.val) % 2 = 0
  · simp [signValue, signPattern, h]
  · simp [signValue, signPattern, h]

private theorem signed_le_abs (s : Fin 32) (i : Fin 5) (x : ℝ) :
    signValue s i * x ≤ |x| := by
  unfold signValue
  split <;> simp only [one_mul, neg_mul, one_mul]
  · exact le_abs_self x
  · exact neg_le_abs x

private theorem exists_maximizing_signs (x : Fin 5 → ℝ) :
    ∃ s : Fin 32, ∀ i, signValue s i * x i = |x i| := by
  obtain ⟨s, hs⟩ := signPattern_surjective (fun i => decide (0 ≤ x i))
  refine ⟨s, fun i => ?_⟩
  simp only [signValue, hs]
  by_cases hx : 0 ≤ x i
  · simp [hx, abs_of_nonneg hx]
  · simp [hx, abs_of_neg (lt_of_not_ge hx)]

private theorem zeroIndex_injective : Function.Injective zeroIndex := by decide

private theorem zero_sum (f : Fin 5 × Fin 5 → ℝ) :
    ∑ qp ∈ zeroPoints, f qp = ∑ i : Fin 5, f (zeroIndex i) := by
  rw [← zeroIndex_image, Finset.sum_image]
  exact fun _ _ _ _ h => zeroIndex_injective h

private theorem base_eval (a : Fin 4 → ℝ) :
    a ⬝ᵥ (base *ᵥ a) =
      (∑ qp ∈ (Finset.univ \ zeroPoints),
        (SignType.sign (wigner psi qp.1 qp.2) : ℝ) *
          wigner (tangentEquiv a : State) qp.1 qp.2) -
        lOne psi * ‖(tangentEquiv a : State)‖ ^ 2 := by
  rw [base_eq]
  simp only [sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum,
    smul_mulVec, dotProduct_smul, smul_eq_mul, phaseForm_eval, gram_eval]

theorem branch_eval (s : Fin 32) (a : Fin 4 → ℝ) :
    a ⬝ᵥ (branch s *ᵥ a) = a ⬝ᵥ (base *ᵥ a) +
      ∑ i : Fin 5, signValue s i * (a ⬝ᵥ (zeroQ i *ᵥ a)) := by
  simp only [branch, add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum,
    smul_mulVec, dotProduct_smul, smul_eq_mul, signValue_eq]

theorem secondVariation_coordinates (a : Fin 4 → ℝ) :
    secondVariation (tangentEquiv a : State) = a ⬝ᵥ (base *ᵥ a) +
      ∑ i : Fin 5, |a ⬝ᵥ (zeroQ i *ᵥ a)| := by
  simp only [secondVariation, base_eval, zeroQ_eq, phaseForm_eval]
  rw [zero_sum]
  ring

theorem finite_sign_maximum (a : Fin 4 → ℝ) :
    secondVariation (tangentEquiv a : State) = branchMaximum a := by
  rw [secondVariation_coordinates]
  apply le_antisymm
  · obtain ⟨s, hs⟩ := exists_maximizing_signs (fun i => a ⬝ᵥ (zeroQ i *ᵥ a))
    calc
      _ = a ⬝ᵥ (branch s *ᵥ a) := by rw [branch_eval]; simp only [hs]
      _ ≤ branchMaximum a := Finset.le_sup'
        (fun t : Fin 32 => a ⬝ᵥ (branch t *ᵥ a)) (Finset.mem_univ s)
  · apply Finset.sup'_le
    intro s _
    rw [branch_eval]
    exact add_le_add_right (Finset.sum_le_sum fun i _ => signed_le_abs s i _) _

theorem finite_sign_maximum_tangent (v : tangent) :
    secondVariation (v : State) = branchMaximum (tangentEquiv.symm v) := by
  simpa only [tangentEquiv.apply_symm_apply] using
    finite_sign_maximum (tangentEquiv.symm v)

private theorem branch_hermitian (s : Fin 32) : (branch s).IsHermitian := by
  have hb : base.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [base, conjTranspose_apply]
  have hq (k : Fin 5) : (zeroQ k).IsHermitian := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [zeroQ, conjTranspose_apply]
  unfold branch Matrix.IsHermitian
  simp only [conjTranspose_add, conjTranspose_sum, conjTranspose_smul,
    star_trivial, hb.eq, (hq _).eq]

theorem negativity_iff :
    (∀ v : tangent, v ≠ 0 → secondVariation (v : State) < 0) ↔
      ∀ s : Fin 32, Matrix.PosDef (-branch s) := by
  constructor
  · intro h s
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (branch_hermitian s).neg
    intro a ha
    have hv : tangentEquiv a ≠ 0 := by
      intro hz
      exact ha (tangentEquiv.injective (by simpa using hz))
    have hm := h (tangentEquiv a) hv
    rw [finite_sign_maximum] at hm
    have hb : a ⬝ᵥ (branch s *ᵥ a) < 0 :=
      lt_of_le_of_lt (Finset.le_sup'
        (fun t : Fin 32 => a ⬝ᵥ (branch t *ᵥ a)) (Finset.mem_univ s)) hm
    simpa only [star_trivial, neg_mulVec, dotProduct_neg, neg_pos] using hb
  · intro h v hv
    rw [finite_sign_maximum_tangent]
    apply (Finset.sup'_lt_iff _).mpr
    intro s _
    have ha : tangentEquiv.symm v ≠ 0 := by
      intro hz
      exact hv (tangentEquiv.symm.injective (by simpa using hz))
    have hb := (h s).dotProduct_mulVec_pos ha
    simpa only [star_trivial, neg_mulVec, dotProduct_neg, neg_pos] using hb

theorem second_variation_negative (v : tangent) (hv : v ≠ 0) :
    secondVariation (v : State) < 0 :=
  negativity_iff.mpr all_branches_negative v hv

def integerWitness (s : Fin 32) : Fin 4 → ℤ :=
  match s.val with
  | 0 => ![-4,0,4,1]
  | 1 => ![-3,4,-1,4]
  | 2 => ![-4,-1,-2,4]
  | 3 => ![-4,2,-1,3]
  | 4 => ![-4,-1,0,4]
  | 5 => ![-2,-3,-4,4]
  | 6 => ![-4,-3,-2,4]
  | 7 => ![-3,4,4,-2]
  | 8 => ![-4,-4,4,-4]
  | 9 => ![-3,-4,3,-4]
  | 10 => ![-4,-3,4,-3]
  | 11 => ![-4,2,1,1]
  | 12 => ![-4,-3,4,-4]
  | 13 => ![-4,-4,3,-4]
  | 14 => ![-4,-2,2,-1]
  | 15 => ![-4,-3,3,-3]
  | 16 => ![-3,-1,-4,2]
  | 17 => ![-4,-3,-4,3]
  | 18 => ![-4,-1,-4,4]
  | 19 => ![-4,-2,-4,4]
  | 20 => ![-4,-4,-4,-4]
  | 21 => ![-4,-4,-4,-1]
  | 22 => ![-4,-4,-2,4]
  | 23 => ![-4,-4,-4,3]
  | 24 => ![-3,-4,4,-4]
  | 25 => ![-2,-4,1,-3]
  | 26 => ![-4,-4,4,-3]
  | 27 => ![-4,1,-2,2]
  | 28 => ![-4,-4,-2,-4]
  | 29 => ![-4,-4,-2,-3]
  | 30 => ![-4,-4,0,1]
  | _ => ![-4,-4,-1,1]

private theorem radical_intervals :
    (3804226 / 1000000 : ℝ) < QuquintCertificateData.radical ∧
    QuquintCertificateData.radical < 3804227 / 1000000 ∧
    (14472135 / 1000000 : ℝ) < QuquintCertificateData.radical ^ 2 ∧
    QuquintCertificateData.radical ^ 2 < 14472136 / 1000000 ∧
    (550552 / 10000 : ℝ) < QuquintCertificateData.radical ^ 3 ∧
    QuquintCertificateData.radical ^ 3 < 550554 / 10000 := by
  let r := QuquintCertificateData.radical
  have hsq : r ^ 2 = 10 + 2 * Real.sqrt 5 := QuquintCertificateData.radical_sq
  have hf := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hfp := Real.sqrt_nonneg 5
  have hr : 0 < r := by dsimp [r, QuquintCertificateData.radical]; positivity
  have hlo : (14472135 / 1000000 : ℝ) < r ^ 2 := by nlinarith
  have hhi : r ^ 2 < (14472136 / 1000000 : ℝ) := by nlinarith
  have hrl : (3804226 / 1000000 : ℝ) < r := by nlinarith
  have hrh : r < (3804227 / 1000000 : ℝ) := by nlinarith
  refine ⟨hrl, hrh, hlo, hhi, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hlo hr]
  · nlinarith [mul_lt_mul_of_pos_left hhi hr]

theorem integerWitness_signs (s : Fin 32) (i : Fin 5) :
    0 < signValue s i *
      ((fun j => (integerWitness s j : ℝ)) ⬝ᵥ
        (zeroQ i *ᵥ (fun j => (integerWitness s j : ℝ)))) := by
  obtain ⟨hrl, hrh, hsql, hsqh, hcbl, hcbh⟩ := radical_intervals
  fin_cases s <;> fin_cases i
  all_goals norm_num [signValue, signPattern, integerWitness, zeroQ,
    dotProduct, mulVec, Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals linarith only [hrl, hrh, hsql, hsqh, hcbl, hcbh]

theorem sign_patterns_attained (s : Fin 32) :
    ∃ a : Fin 4 → ℝ, (∀ j, ∃ n : ℤ, a j = (n : ℝ)) ∧ a ≠ 0 ∧
      ∀ i : Fin 5, 0 < signValue s i *
        wigner (tangentEquiv a : State) (zeroIndex i).1 (zeroIndex i).2 := by
  refine ⟨fun j => (integerWitness s j : ℝ),
    (fun j => ⟨integerWitness s j, rfl⟩), ?_, ?_⟩
  · intro hz
    have h := integerWitness_signs s 0
    rw [hz] at h
    simp at h
  · intro i
    rw [← phaseForm_eval, ← zeroQ_eq]
    exact integerWitness_signs s i

#print axioms branch_eval
#print axioms secondVariation_coordinates
#print axioms finite_sign_maximum
#print axioms finite_sign_maximum_tangent
#print axioms negativity_iff
#print axioms second_variation_negative
#print axioms integerWitness_signs
#print axioms sign_patterns_attained
end D5.S3.Quantum.Magic.QuquintFiniteMaximum

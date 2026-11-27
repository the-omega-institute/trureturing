/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Ambient degree of the literal Pauli readout. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeRotation

/-! Ambient degrees of native adjacent Pauli readouts before restricting to a spectral fiber. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSHorizontalNativeDegree

open MvPolynomial
open scoped BigOperators Matrix Kronecker
open SevenSiteTraceBase (Word wordPolynomial)
open SevenSiteCriticalCertificate (wordTrace rotationIndex sliceBlock)
open PeriodicMPSUniformNativeSliceReadout
  (alignedMoment alignedMoment_eq_transferPower pauliInsertion rawSlicePolynomial)
open PeriodicMPSUniformAntisymmetricTransfer (BondMatrix mixedTransfer)
open PeriodicMPSUniformHardCoreTransferRecurrence (TwoBits)
open UniformNativeRotation (rotationPolynomial)

open private form from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
open private alignedWord map_alignedWord map_pauliInsertionCoeff from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.UniformNativeSliceReadout
open private sliceAffine term_eval_degree from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCertificate
open private normalForm traceTerms evalTerms evalTerms_append evalTerms_raiseD evalTerms_raiseE
  evalTerms_raiseK evalTerms_scale traceTerms_fits Fits Term.eval Term.degree
  NormalForm.one NormalForm.a NormalForm.b NormalForm.ab from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalTrace

noncomputable section

variable {R σ : Type*} [CommRing R]

private theorem eval_normalForm (d k e : R) (w : List (Fin 2)) :
    let f := normalForm w
    form 1 0 d e k w =
      (evalTerms d k e (NormalForm.one f), evalTerms d k e (NormalForm.a f),
        evalTerms d k e (NormalForm.b f), evalTerms d k e (NormalForm.ab f)) := by
  induction w with
  | nil => simp [form, normalForm, evalTerms, Term.eval]
  | cons i w ih =>
    dsimp only at ih
    by_cases hi : i = 0
    · simp [form, normalForm, hi, ih, evalTerms_append, evalTerms_raiseD]
    · simp [form, normalForm, hi, ih, evalTerms_append, evalTerms_raiseE,
        evalTerms_raiseK, evalTerms_scale, sub_eq_add_neg, add_assoc]

/-- The unrestricted word recursion agrees with the aligned trace-term recurrence. -/
theorem wordPolynomial_aligned_eq_wordTrace (d k e : R) (w : List (Fin 2)) :
    wordPolynomial 1 0 d e k w = wordTrace d k e w := by
  simp [wordPolynomial, wordTrace, traceTerms, eval_normalForm, evalTerms_append,
    evalTerms_scale, evalTerms_raiseK, add_assoc]

/-- Trace alignment turns the existing weight filtration into an ordinary degree bound. -/
theorem wordPolynomial_aligned_totalDegree (z : Fin 3 → MvPolynomial σ R)
    (hz : ∀ i, (z i).totalDegree ≤ 1) (w : List (Fin 2)) :
    (wordPolynomial 1 0 (z 0) (z 2) (z 1) w).totalDegree ≤ w.length / 2 := by
  rw [wordPolynomial_aligned_eq_wordTrace]
  have hfit := traceTerms_fits w
  unfold wordTrace
  generalize traceTerms w = terms at hfit ⊢
  have h (m) (hm : m ∈ terms) :
      (Term.eval (z 0) (z 1) (z 2) m).totalDegree ≤
        w.length / 2 := by
    have hweight := (hfit m hm).1
    exact (term_eval_degree m z hz).trans (by omega)
  unfold evalTerms
  clear hfit
  induction terms with
  | nil => simp
  | cons m terms ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (totalDegree_add _ _).trans (max_le (h m (by simp))
      (ih (fun n hn => h n (List.mem_cons_of_mem _ hn))))

private theorem alignedWord_totalDegree (z : Fin 3 → MvPolynomial σ R)
    (hz : ∀ i, (z i).totalDegree ≤ 1) {n : ℕ} (w : Word n) :
    (alignedWord z w).totalDegree ≤ n / 2 := by
  simpa only [alignedWord, List.length_ofFn] using
    wordPolynomial_aligned_totalDegree z hz (List.ofFn w)

/-- The exact native readout has a bound at every residual transfer power. -/
theorem alignedMoment_totalDegree (r : ℕ) (ι : R) (ket bra : Fin 3 → MvPolynomial σ R)
    (hk : ∀ i, (ket i).totalDegree ≤ 1) (hb : ∀ i, (bra i).totalDegree ≤ 1)
    (ab : Fin 4 × Fin 4) :
    (alignedMoment r (C ι) ket bra ab).totalDegree ≤ 2 * ((2 + r) / 2) := by
  unfold alignedMoment
  apply totalDegree_finsetSum_le
  intro q _
  apply totalDegree_finsetSum_le
  intro p _
  have hC := (map_pauliInsertionCoeff (C : R →+* MvPolynomial σ R) ι ab p q).symm
  rw [hC]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply totalDegree_finsetSum_le
  intro w _
  exact (totalDegree_mul _ _).trans
    ((Nat.add_le_add (alignedWord_totalDegree ket hk (Fin.append ![p.1, p.2] w))
      (alignedWord_totalDegree bra hb (Fin.append ![q.1, q.2] w))).trans (by omega))

/-- A partial lowers the total-degree budget by one, with truncation at zero. -/
theorem pderiv_totalDegree_le {p : MvPolynomial σ R} (j : σ) :
    (pderiv j p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  nth_rw 1 [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [pderiv_monomial]
  by_cases hj : s j = 0
  · simp [hj]
  have htotal := le_totalDegree hs
  have hsum : (s - Finsupp.single j 1).sum (fun _ e => e) + 1 =
      s.sum (fun _ e => e) := by
    conv_rhs => rw [← Finsupp.sub_add_single_one_cancel hj]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  apply (totalDegree_monomial_le _ _).trans
  change (s - Finsupp.single j 1).sum (fun _ e => e) ≤ p.totalDegree - 1
  omega

/-- Independent ambient coordinates in order `(d, db, e, eb, k)`, with a shared mixed trace. -/
def ambientMoment (r : ℕ) (ι : R) (ab : Fin 4 × Fin 4) : MvPolynomial (Fin 5) R :=
  alignedMoment r (C ι) ![X 0, X 4, X 2] ![X 1, X 4, X 3] ab

/-- Evaluation in the five ambient coordinates is the literal mixed-transfer moment. -/
theorem eval_ambientMoment_eq_transferPower (r : ℕ) (ι : R)
    (ket bra : Fin 2 → BondMatrix R)
    (hk₀ : (ket 0).trace = 1) (hk₁ : (ket 1).trace = 0)
    (hb₀ : (bra 0).trace = 1) (hb₁ : (bra 1).trace = 0)
    (hk : (ket 0 * ket 1).trace = (bra 0 * bra 1).trace) (ab : Fin 4 × Fin 4) :
    eval ![(ket 0).det, (bra 0).det, (ket 1).det, (bra 1).det, (ket 0 * ket 1).trace]
        (ambientMoment r ι ab) =
      (pauliInsertion ι ket bra ab * mixedTransfer ket bra ^ r).trace := by
  let v : Fin 5 → R :=
    ![(ket 0).det, (bra 0).det, (ket 1).det, (bra 1).det, (ket 0 * ket 1).trace]
  let f := eval v
  have hket : f ∘ (![X 0, X 4, X 2] : Fin 3 → MvPolynomial (Fin 5) R) =
      ![(ket 0).det, (ket 0 * ket 1).trace, (ket 1).det] := by
    funext i
    fin_cases i <;> simp [f, v]
  have hbra : f ∘ (![X 1, X 4, X 3] : Fin 3 → MvPolynomial (Fin 5) R) =
      ![(bra 0).det, (bra 0 * bra 1).trace, (bra 1).det] := by
    funext i
    fin_cases i <;> simp [f, v, hk]
  rw [← alignedMoment_eq_transferPower r ι ket bra hk₀ hk₁ hb₀ hb₁ ab]
  change f (ambientMoment r ι ab) = _
  simp only [ambientMoment, alignedMoment, map_sum, map_mul, map_pauliInsertionCoeff,
    map_alignedWord, hket, hbra, f, eval_C]

theorem ambientMoment_totalDegree (r : ℕ) [Nontrivial R] (ι : R) (ab : Fin 4 × Fin 4) :
    (ambientMoment r ι ab).totalDegree ≤ 2 * ((2 + r) / 2) := by
  apply alignedMoment_totalDegree
  all_goals intro i; fin_cases i <;> simp

theorem ambientMoment_totalDegree_le_eight {r : ℕ} (hr : r ≤ 7) [Nontrivial R]
    (ι : R) (ab : Fin 4 × Fin 4) :
    (ambientMoment r ι ab).totalDegree ≤ 8 :=
  (ambientMoment_totalDegree r ι ab).trans (by omega)

theorem ambientPartial_totalDegree_le_seven {r : ℕ} (hr : r ≤ 7) [Nontrivial R]
    (ι : R) (ab : Fin 4 × Fin 4) (j : Fin 5) :
    (pderiv j (ambientMoment r ι ab)).totalDegree ≤ 7 :=
  (pderiv_totalDegree_le j).trans
    (Nat.sub_le_sub_right (ambientMoment_totalDegree_le_eight hr ι ab) 1)

/-- A row combination with coefficients in the base ring preserves the ambient degree.
This includes the complex-linear changes of rotation basis. -/
theorem linearCombination_totalDegree {τ : Type*} [Fintype τ]
    (a : τ → R) (p : τ → MvPolynomial σ R) {n : ℕ}
    (h : ∀ i, (p i).totalDegree ≤ n) :
    (∑ i, C (a i) * p i).totalDegree ≤ n := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using h i)

/-- Eight fixed Hermite coefficients give the pre-restriction observation entry. -/
def ambientHermiteMoment (c : Fin 8 → R) (ι : R) (ab : Fin 4 × Fin 4) :
    MvPolynomial (Fin 5) R :=
  ∑ r, C (c r) * ambientMoment r.val ι ab

theorem ambientHermiteMoment_totalDegree [Nontrivial R]
    (c : Fin 8 → R) (ι : R) (ab : Fin 4 × Fin 4) :
    (ambientHermiteMoment c ι ab).totalDegree ≤ 8 :=
  linearCombination_totalDegree c _ (fun r =>
    ambientMoment_totalDegree_le_eight (by omega : r.val ≤ 7) ι ab)

theorem ambientHermitePartial_totalDegree [Nontrivial R]
    (c : Fin 8 → R) (ι : R) (ab : Fin 4 × Fin 4) (j : Fin 5) :
    (pderiv j (ambientHermiteMoment c ι ab)).totalDegree ≤ 7 :=
  (pderiv_totalDegree_le j).trans (Nat.sub_le_sub_right (ambientHermiteMoment_totalDegree c ι ab) 1)

private theorem pauliRotation_totalDegree
    (p : Fin 4 × Fin 4 → MvPolynomial σ R) {n : ℕ} (hp : ∀ ab, (p ab).totalDegree ≤ n)
    (j : Fin 3) (ab : Fin 4 × Fin 4) :
    let a := rotationIndex j ab.1
    let b := rotationIndex j ab.2
    (((a.1 : MvPolynomial σ R) * p (a.2, ab.2)) +
      ((b.1 : MvPolynomial σ R) * p (ab.1, b.2))).totalDegree ≤ n := by
  dsimp only
  apply (totalDegree_add _ _).trans
  apply max_le
  all_goals
    apply (totalDegree_mul _ _).trans
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C, zero_add]
    apply hp

/-- The signed action on each Pauli index, applied to the ambient Hermite moment. -/
def ambientHermiteRotation (c : Fin 8 → R) (ι : R) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    MvPolynomial (Fin 5) R :=
  let a := rotationIndex j ab.1
  let b := rotationIndex j ab.2
  (a.1 : MvPolynomial (Fin 5) R) * ambientHermiteMoment c ι (a.2, ab.2) +
    (b.1 : MvPolynomial (Fin 5) R) * ambientHermiteMoment c ι (ab.1, b.2)

theorem ambientHermiteRotation_totalDegree [Nontrivial R]
    (c : Fin 8 → R) (ι : R) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    (ambientHermiteRotation c ι j ab).totalDegree ≤ 8 :=
  pauliRotation_totalDegree _ (ambientHermiteMoment_totalDegree c ι) j ab

/-- In particular the coefficients may involve `Complex.I`, as in the paper's rotation basis. -/
theorem ambientHermiteMixedRotation_totalDegree
    (c : Fin 8 → ℂ) (a : Fin 3 → ℂ) (ab : Fin 4 × Fin 4) :
    (∑ j, C (a j) * ambientHermiteRotation c Complex.I j ab).totalDegree ≤ 8 :=
  linearCombination_totalDegree a _ fun j => ambientHermiteRotation_totalDegree c Complex.I j ab

theorem rawSlicePolynomial_totalDegree (r : ℕ) (ab : Fin 4 × Fin 4) :
    (rawSlicePolynomial r ab).totalDegree ≤ 2 * ((2 + r) / 2) :=
  alignedMoment_totalDegree r Complex.I _ _ (sliceAffine Complex.I true)
    (sliceAffine Complex.I false) ab

theorem rotationPolynomial_totalDegree (r : ℕ) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    (rotationPolynomial r j ab).totalDegree ≤ 2 * ((2 + r) / 2) :=
  pauliRotation_totalDegree _ (rawSlicePolynomial_totalDegree r) j ab

end

end D5.S3.Quantum.TensorNetworks.UniformMPSHorizontalNativeDegree

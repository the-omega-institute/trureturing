/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalTrace]
   utility: none
   digest: Each literal critical cofactor is divisible by the mixed trace with quotient of total degree at most 46. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalTrace
import Batteries.Tactic.OpenPrivate

/-! Pauli observations, Euler identities, and the mixed-trace factor for
the literal seven-site critical cofactors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Matrix

open scoped BigOperators

open private Term Term.coeff Term.d Term.k Term.e Term.degree Term.phase Term.eval traceTerms evalTerms Bond joinedWord
  term_degree pairWeight term_phase
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalTrace

section Observation

variable {R : Type*} [CommRing R]

private def pauli (ι : R) : Fin 4 → Bond R :=
  ![1, !![0, 1; 1, 0], !![0, -ι; ι, 0], !![1, 0; 0, -1]]

private def readout (ι : R) (ab : Fin 4 × Fin 4) (p q : Pair) : R :=
  pauli ι ab.1 q.1 p.1 * pauli ι ab.2 q.2 p.2

/-- Row order of the norm, one-site Pauli vector and upper two-site Pauli triangle. -/
def observedRow : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0), (1,0), (2,0), (3,0), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]

/-- Pauli contraction with independent arguments in the two trace blocks. -/
def observation (ι : R) (plus minus : Fin 3 → R) (ab : Fin 4 × Fin 4) : R :=
  ∑ p : Pair, ∑ q : Pair, readout ι ab p q * rawGram plus minus p q

/-- Sum a function of the ket and bra monomials over the literal suffix contraction. -/
private def contract (f : Pair → Pair → Term → Term → R) : R :=
  ∑ p : Pair, ∑ q : Pair, ∑ s : Fin 5 → Fin 2,
    ((traceTerms (joinedWord p s)).map fun m =>
      ((traceTerms (joinedWord q s)).map (f p q m)).sum).sum

private theorem contract_observation (ι : R) (plus minus : Fin 3 → R)
    (ab : Fin 4 × Fin 4) :
    contract (fun p q m n => readout ι ab p q *
      (Term.eval (plus 0) (plus 1) (plus 2) m * Term.eval (minus 0) (minus 1) (minus 2) n)) =
      observation ι plus minus ab := by
  unfold contract observation rawGram wordTrace evalTerms
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro s _
  rw [← List.sum_map_mul_right, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m _
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]

/-- Apply `6 - E₊ - E₋` to the raw observation before identifying the two blocks. -/
def radialEuler (ι : R) (plus minus : Fin 3 → R) (ab : Fin 4 × Fin 4) : R :=
  contract fun p q m n => readout ι ab p q * (6 - (Term.degree m : R) - (Term.degree n : R)) *
    (Term.eval (plus 0) (plus 1) (plus 2) m * Term.eval (minus 0) (minus 1) (minus 2) n)

/-- Apply `E₊ - E₋` to the raw observation before identifying the two blocks. -/
def differenceEuler (ι : R) (plus minus : Fin 3 → R) (ab : Fin 4 × Fin 4) : R :=
  contract fun p q m n => readout ι ab p q * ((Term.degree m : R) - (Term.degree n : R)) *
    (Term.eval (plus 0) (plus 1) (plus 2) m * Term.eval (minus 0) (minus 1) (minus 2) n)

/-- Keep the two mixed traces independent until the argument substitution here. -/
def sliceBlock (ι : R) (x : Fin 5 → R) (ket : Bool) : Fin 3 → R :=
  let j := if ket then ι else -ι
  ![x 0 + j * x 3, x 1, x 2 + j * x 4]

/-- The five slice variables are `Re d, k, Re e, Im d, Im e`. -/
def slicedObservation (ι : R) (x : Fin 5 → R) (ab : Fin 4 × Fin 4) : R :=
  observation ι (sliceBlock ι x true) (sliceBlock ι x false) ab

end Observation

section Degree

open MvPolynomial

variable {R σ : Type*} [CommRing R]

private theorem contract_degree {f : Pair → Pair → Term → Term → MvPolynomial σ R} {N : ℕ}
    (h : ∀ (p q : Pair) (s : Fin 5 → Fin 2) (m n : Term),
      m ∈ traceTerms (joinedWord p s) → n ∈ traceTerms (joinedWord q s) →
      (f p q m n).totalDegree ≤ N) :
    (contract f).totalDegree ≤ N := by
  have sum_degree (l : List Term) (g : Term → MvPolynomial σ R)
      (hg : ∀ a ∈ l, (g a).totalDegree ≤ N) :
      ((l.map g).sum).totalDegree ≤ N := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (totalDegree_add _ _).trans (max_le (hg a (by simp)) (ih
        (fun b hb => hg b (by simp [hb]))))
  unfold contract
  apply totalDegree_finsetSum_le
  intro p _
  apply totalDegree_finsetSum_le
  intro q _
  apply totalDegree_finsetSum_le
  intro s _
  apply sum_degree
  intro m hm
  apply sum_degree
  intro n hn
  exact h p q s m n hm hn

private theorem term_eval_degree (m : Term) (a : Fin 3 → MvPolynomial σ R)
    (ha : ∀ i, (a i).totalDegree ≤ 1) :
    (Term.eval (a 0) (a 1) (a 2) m).totalDegree ≤ Term.degree m := by
  have hp (i : Fin 3) (t : ℕ) : (a i ^ t).totalDegree ≤ t :=
    (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left t (ha i))
  unfold Term.eval Term.degree
  have hc : (((Term.coeff m) : MvPolynomial σ R)).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R)]
    exact totalDegree_C _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add
    ((totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_mul _ _).trans (by rw [hc, zero_add]; exact hp 0 (Term.d m)))
      (hp 1 (Term.k m)))) (hp 2 (Term.e m)))

private theorem weighted_degree (c : R) (plus minus : Fin 3 → MvPolynomial σ R)
    (hp : ∀ i, (plus i).totalDegree ≤ 1) (hm : ∀ i, (minus i).totalDegree ≤ 1)
    (m n : Term) :
    (C c * (Term.eval (plus 0) (plus 1) (plus 2) m *
      Term.eval (minus 0) (minus 1) (minus 2) n)).totalDegree ≤ Term.degree m + Term.degree n :=
  (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add (term_eval_degree m plus hp) (term_eval_degree n minus hm)))

private theorem readout_C (ι : R) (ab : Fin 4 × Fin 4) (p q : Pair) :
    readout (C ι : MvPolynomial σ R) ab p q = C (readout ι ab p q) := by
  have h (a : Fin 4) (i j : Fin 2) : pauli (C ι : MvPolynomial σ R) a i j =
      C (pauli ι a i j) := by
    fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauli]
  simp only [readout, h, map_mul]

/-- Raw observations have degree at most six under any affine substitution into the
split blocks, including the five-variable real slice and its transverse lines. -/
theorem observation_totalDegree (ι : R) (plus minus : Fin 3 → MvPolynomial σ R)
    (hp : ∀ i, (plus i).totalDegree ≤ 1) (hm : ∀ i, (minus i).totalDegree ≤ 1)
    (ab : Fin 4 × Fin 4) :
    (observation (C ι) plus minus ab).totalDegree ≤ 6 := by
  rw [← contract_observation]
  apply contract_degree
  intro p q s m n hmem hn
  rw [readout_C]
  exact (weighted_degree _ plus minus hp hm m n).trans
    (Nat.add_le_add (term_degree p s hmem) (term_degree q s hn))

/-- Both Euler combinations annihilate the unique possible degree-six block,
whose ket and bra degrees are each three. -/
theorem euler_totalDegree (ι : R) (plus minus : Fin 3 → MvPolynomial σ R)
    (hp : ∀ i, (plus i).totalDegree ≤ 1) (hm : ∀ i, (minus i).totalDegree ≤ 1)
    (ab : Fin 4 × Fin 4) :
    (radialEuler (C ι) plus minus ab).totalDegree ≤ 5 ∧
    (differenceEuler (C ι) plus minus ab).totalDegree ≤ 5 := by
  constructor <;> simp only [radialEuler, differenceEuler]
  all_goals
    apply contract_degree
    intro p q s m n hmem hn
    have h₁ := term_degree p s hmem
    have h₂ := term_degree q s hn
    by_cases h : Term.degree m + Term.degree n ≤ 5
    · rw [readout_C]
      simp only [← map_natCast C, ← map_ofNat C, ← map_sub, ← map_mul]
      exact (weighted_degree _ plus minus hp hm m n).trans h
    · have h₃ : Term.degree m = 3 := by omega
      have h₄ : Term.degree n = 3 := by omega
      simp [h₃, h₄, show (6 : MvPolynomial σ R) - 3 - 3 = 0 by ring]

end Degree

section CriticalMatrix

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The two-site Pauli coordinates transform by this infinitesimal action on
each Pauli index. Index zero is the identity. -/
def rotationIndex : Fin 3 → Fin 4 → ℤ × Fin 4 :=
  ![![(0,0), (0,0), (-1,3), (1,2)],
    ![(0,0), (1,3), (0,0), (-1,1)],
    ![(0,0), (-1,2), (1,1), (0,0)]]

/-- Physical rotation on the Pauli vector and on each of the two tensor indices. -/
def rotationObservation (ι : R) (x : Fin 5 → R) (j : Fin 3)
    (ab : Fin 4 × Fin 4) : R :=
  let a := rotationIndex j ab.1
  let b := rotationIndex j ab.2
  (a.1 : R) * slicedObservation ι x (a.2, ab.2) +
    (b.1 : R) * slicedObservation ι x (ab.1, b.2)

noncomputable section

/-- The polynomial ring in the five real slice variables, with a chosen coefficient ring. -/
abbrev Slice (R : Type*) [CommRing R] := MvPolynomial (Fin 5) R

/-- The five-variable polynomial giving a single Pauli readout. -/
def V (ι : R) (ab : Fin 4 × Fin 4) : Slice R :=
  slicedObservation (C ι) X ab

private theorem sliceAffine (ι : R) (ket : Bool) (i : Fin 3) :
    (sliceBlock (C ι) (X : Fin 5 → Slice R) ket i).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (sliceBlock (C ι) X ket i) (0 : Slice R), totalDegree_zero]
    decide
  have h (s t : Fin 5) (a : R) : (X s + C a * X t : Slice R).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_C])
  cases ket
  · fin_cases i
    · change (X 0 + -(C ι) * X 3 : Slice R).totalDegree ≤ 1
      rw [← map_neg]
      exact h 0 3 (-ι)
    · exact (totalDegree_X (R := R) (1 : Fin 5)).le
    · change (X 2 + -(C ι) * X 4 : Slice R).totalDegree ≤ 1
      rw [← map_neg]
      exact h 2 4 (-ι)
  · fin_cases i
    · exact h 0 3 ι
    · exact (totalDegree_X (R := R) (1 : Fin 5)).le
    · exact h 2 4 ι

private theorem V_degree (ι : R) (ab : Fin 4 × Fin 4) : (V ι ab).totalDegree ≤ 6 :=
  observation_totalDegree ι _ _ (sliceAffine ι true) (sliceAffine ι false) ab

private theorem rotation_degree (ι : R) (j : Fin 3) (ab : Fin 4 × Fin 4) :
    (rotationObservation (C ι) X j ab).totalDegree ≤ 6 := by
  unfold rotationObservation
  apply (totalDegree_add _ _).trans
  apply max_le
  all_goals
    apply (totalDegree_mul _ _).trans
    rw [← map_intCast (C : R →+* Slice R), totalDegree_C, zero_add]
    apply V_degree

private theorem diff_degree {p : Slice R} (hp : p.totalDegree ≤ 6) (i : Fin 5) :
    (pderiv i p).totalDegree ≤ 5 := by
  nth_rw 1 [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [pderiv_monomial]
  by_cases hi : s i = 0
  · simp [hi]
  have htotal := (le_totalDegree hs).trans hp
  have hsum : (s - Finsupp.single i 1).sum (fun _ e => e) + 1 =
      s.sum (fun _ e => e) := by
    conv_rhs => rw [← Finsupp.sub_add_single_one_cancel hi]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  apply (totalDegree_monomial_le _ _).trans
  change (s - Finsupp.single i 1).sum (fun _ e => e) ≤ 5
  omega

/-- The unnormalized projective rank matrix after deleting the indicated Pauli row.
The five slice partials come first, then the value and the three rotations. -/
def criticalMatrix (ι : R) (deleted : Fin 10) : Matrix (Fin 9) (Fin 9) (Slice R) :=
  fun i j =>
    let ab := observedRow (deleted.succAbove i)
    if h : j.val < 5 then pderiv ⟨j.val, h⟩ (V ι ab)
    else if j = 5 then V ι ab
    else rotationObservation (C ι) X ⟨j.val - 6, by omega⟩ ab

/-- The Euler column replacements with the two unmodified rotation columns. -/
def reducedCriticalMatrix (ι : R) (deleted : Fin 10) : Matrix (Fin 9) (Fin 9) (Slice R) :=
  fun i j =>
    let ab := observedRow (deleted.succAbove i)
    if j = 5 then radialEuler (C ι) (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab
    else if j = 8 then C ι *
      differenceEuler (C ι) (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab
    else criticalMatrix ι deleted i j

private def columnDegree (j : Fin 9) : ℕ := if j.val = 6 ∨ j.val = 7 then 6 else 5

private theorem reduced_column_degree (ι : R) (deleted : Fin 10) (i j : Fin 9) :
    (reducedCriticalMatrix ι deleted i j).totalDegree ≤ columnDegree j := by
  let ab := observedRow (deleted.succAbove i)
  have he := euler_totalDegree ι _ _ (sliceAffine ι true) (sliceAffine ι false) ab
  by_cases h₅ : j = 5
  · subst j
    exact he.1
  by_cases h₈ : j = 8
  · subst j
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact he.2
  rw [reducedCriticalMatrix, ite_eq_right h₅, ite_eq_right h₈, criticalMatrix]
  by_cases h : j.val < 5
  · rw [dite_eq_left h, columnDegree, ite_eq_right (by omega)]
    exact diff_degree (V_degree _ _) _
  · rw [dite_eq_right h, ite_eq_right h₅, columnDegree, ite_eq_left (by omega)]
    exact rotation_degree _ _ _

/-- The two Euler replacements lower the total degree of every selected determinant to 47. -/
theorem reduced_cofactor_totalDegree (ι : R) (deleted : Fin 10) :
    (reducedCriticalMatrix ι deleted).det.totalDegree ≤ 47 := by
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro p _
  apply (totalDegree_mul _ _).trans
  have hsign : ((Equiv.Perm.sign p : Slice R)).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* Slice R), totalDegree_C]
  rw [hsign, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ j : Fin 9, columnDegree j := Finset.sum_le_sum fun j _ =>
      reduced_column_degree ι deleted _ j
    _ = 47 := by decide +kernel

private abbrev Dir (R : Type*) [CommRing R] := Derivation R (Slice R) (Slice R)

private theorem contract_map {S : Type*} [CommRing S] (D : S →+ S)
    (f : Pair → Pair → Term → Term → S) :
    D (contract f) = contract (fun p q m n => D (f p q m n)) := by
  simp only [contract, map_sum]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
    Finset.sum_congr rfl (fun s _ => ?_)))
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro m _
  rw [Function.comp_apply, map_list_sum, List.map_map]
  rfl

private theorem contract_sub {S : Type*} [CommRing S]
    (f g : Pair → Pair → Term → Term → S) :
    contract (fun p q m n => f p q m n - g p q m n) = contract f - contract g := by
  have list_sub (l : List Term) (u v : Term → S) :
      (l.map fun m => u m - v m).sum = (l.map u).sum - (l.map v).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel
  simp_rw [contract, ← Finset.sum_sub_distrib, ← list_sub]

private theorem contract_mul {S : Type*} [CommRing S] (c : S)
    (f : Pair → Pair → Term → Term → S) :
    contract (fun p q m n => c * f p q m n) = c * contract f := by
  simp [contract, Finset.mul_sum, List.sum_map_mul_left]

private theorem contract_congr {S : Type*} [CommRing S]
    {f g : Pair → Pair → Term → Term → S}
    (h : ∀ (p q : Pair) (s : Fin 5 → Fin 2) (m n : Term),
      m ∈ traceTerms (joinedWord p s) → n ∈ traceTerms (joinedWord q s) →
      f p q m n = g p q m n) :
    contract f = contract g := by
  unfold contract
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
    Finset.sum_congr rfl (fun s _ => ?_)))
  congr 1
  apply List.map_congr_left
  intro m hm
  congr 1
  apply List.map_congr_left
  intro n hn
  exact h p q s m n hm hn

private theorem deriv_mul (D : Dir R) (p q : Slice R) :
    D (p * q) = D p * q + p * D q := by
  exact (D.leibniz p q).trans (by simp [smul_eq_mul, mul_comm, add_comm])

private theorem deriv_scaled_pow (D : Dir R) {x a : Slice R} (h : D x = a * x)
    (n : ℕ) : D (x ^ n) = (n : Slice R) * a * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, deriv_mul, ih, h, Nat.cast_succ]
    ring

private def monomialWeight (v : Fin 3 → Slice R) (m : Term) : Slice R :=
  ((Term.d m) : Slice R) * v 0 + ((Term.k m) : Slice R) * v 1 + ((Term.e m) : Slice R) * v 2

private theorem deriv_term (D : Dir R) (a v : Fin 3 → Slice R)
    (h : ∀ i, D (a i) = v i * a i) (m : Term) :
    D (Term.eval (a 0) (a 1) (a 2) m) = monomialWeight v m * Term.eval (a 0) (a 1) (a 2) m := by
  simp only [Term.eval, monomialWeight, deriv_mul, deriv_scaled_pow D (h _),
    Derivation.map_intCast, zero_mul, zero_add]
  ring

private def slicedTerm (ι : R) (b : Bool) (m : Term) : Slice R :=
  let x := sliceBlock (C ι) X b
  Term.eval (x 0) (x 1) (x 2) m

private def atom (ι : R) (ab : Fin 4 × Fin 4) (p q : Pair) (m n : Term) : Slice R :=
  C (readout ι ab p q) * (slicedTerm ι true m * slicedTerm ι false n)

private theorem V_eq_contract (ι : R) (ab : Fin 4 × Fin 4) : V ι ab = contract (atom ι ab) := by
  rw [V, slicedObservation, ← contract_observation]
  simp only [readout_C]
  rfl

private theorem deriv_atom (ι : R) (D : Dir R) (plus minus : Fin 3 → Slice R)
    (hp : ∀ j, D (sliceBlock (C ι) X true j) = plus j * sliceBlock (C ι) X true j)
    (hm : ∀ j, D (sliceBlock (C ι) X false j) = minus j * sliceBlock (C ι) X false j)
    (ab : Fin 4 × Fin 4) (p q : Pair) (m n : Term) :
    D (atom ι ab p q m n) = (monomialWeight plus m + monomialWeight minus n) *
      atom ι ab p q m n := by
  simp only [atom, slicedTerm, deriv_mul, derivation_C, zero_mul, zero_add,
    deriv_term D _ _ hp, deriv_term D _ _ hm]
  ring

private theorem derivAlong_eq_sum (v : Fin 5 → Slice R) (p : Slice R) :
    mkDerivation R v p = ∑ i, v i * pderiv i p := by
  have sum_apply (s : Finset (Fin 5)) (f : Fin 5 → Dir R) (q : Slice R) :
      (∑ i ∈ s, f i) q = ∑ i ∈ s, f i q := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih]
  let D : Dir R := ∑ i, v i • pderiv i
  have h : mkDerivation R v = D := by
    apply derivation_ext
    intro i
    simp [D, mkDerivation_X, sum_apply, Pi.single_apply]
  rw [h]
  simp [D, sum_apply, smul_eq_mul]

private def diagonalCorrection : Fin 5 → Slice R := ![-X 3, 0, X 4, X 0, -X 2]

private def eRotation : Fin 5 → Slice R := ![0, 0, -2 * X 4, 0, 2 * X 2]

private theorem radial_column (ι : R) (ab : Fin 4 × Fin 4) :
    radialEuler (C ι) (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab =
      6 * V ι ab - mkDerivation R X (V ι ab) := by
  have h (b : Bool) (j : Fin 3) : mkDerivation R X (sliceBlock (C ι) X b j) =
      (1 : Slice R) * sliceBlock (C ι) X b j := by
    cases b <;> fin_cases j <;>
      simp [sliceBlock, mkDerivation_X, derivation_C]
  have hD (p q : Pair) (m n : Term) :
      mkDerivation R X (atom ι ab p q m n) =
        ((Term.degree m : Slice R) + (Term.degree n : Slice R)) * atom ι ab p q m n := by
    rw [deriv_atom ι _ (fun _ => 1) (fun _ => 1) (h true) (h false)]
    simp [monomialWeight, Term.degree, Nat.cast_add]
  rw [V_eq_contract, ← contract_mul,
    show mkDerivation R X (contract (atom ι ab)) =
        contract (fun p q m n => mkDerivation R X (atom ι ab p q m n)) from
      contract_map (mkDerivation R X).toLinearMap.toAddMonoidHom _]
  rw [← contract_sub]
  unfold radialEuler
  apply contract_congr
  intro p q s m n _ _
  rw [hD]
  simp only [atom, slicedTerm, readout_C]
  ring

private theorem contract_add {S : Type*} [CommRing S]
    (f g : Pair → Pair → Term → Term → S) :
    contract (fun p q m n => f p q m n + g p q m n) = contract f + contract g := by
  simpa only [sub_neg_eq_add, neg_one_mul] using
    (contract_sub f (fun p q m n => (-1 : S) * g p q m n)).trans
      (congrArg (contract f - ·) (contract_mul (-1) g))

private theorem pauli_phase (ι : R) (hι : ι ^ 2 = -1) (a : Fin 4) (p q : Fin 2) :
    ((rotationIndex 2 a).1 : R) * pauli ι (rotationIndex 2 a).2 q p =
      ι * ((p.val : R) - (q.val : R)) * pauli ι a q p := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp [rotationIndex, pauli, mul_neg, neg_mul, hι, ← pow_two]

private theorem readout_phase (ι : R) (hι : ι ^ 2 = -1)
    (ab : Fin 4 × Fin 4) (p q : Pair) :
    ((rotationIndex 2 ab.1).1 : R) * readout ι ((rotationIndex 2 ab.1).2, ab.2) p q +
      ((rotationIndex 2 ab.2).1 : R) * readout ι (ab.1, (rotationIndex 2 ab.2).2) p q =
      ι * ((pairWeight p : R) - (pairWeight q : R)) * readout ι ab p q := by
  unfold readout pairWeight
  rw [← mul_assoc, mul_left_comm (((rotationIndex 2 ab.2).1 : R))]
  simp only [pauli_phase ι hι, Nat.cast_add]
  ring

private theorem rotation_phase_column (ι : R) (hι : ι ^ 2 = -1) (ab : Fin 4 × Fin 4) :
    rotationObservation (C ι) X 2 ab =
      contract (fun p q m n => C ι * ((Term.phase m : Slice R) - (Term.phase n : Slice R)) *
        atom ι ab p q m n) := by
  change (↑(rotationIndex 2 ab.1).1 : Slice R) * V ι ((rotationIndex 2 ab.1).2, ab.2) +
    (↑(rotationIndex 2 ab.2).1 : Slice R) * V ι (ab.1, (rotationIndex 2 ab.2).2) = _
  rw [V_eq_contract, V_eq_contract, ← contract_mul, ← contract_mul, ← contract_add]
  apply contract_congr
  intro p q s m n hm hn
  have he : (Term.phase m : Slice R) - (Term.phase n : Slice R) =
      (pairWeight p : Slice R) - (pairWeight q : Slice R) := by
    rw [term_phase p s hm, term_phase q s hn, Nat.cast_add, Nat.cast_add]
    ring
  rw [he]
  have hmap := congrArg (C : R →+* Slice R) (readout_phase ι hι ab p q)
  simp only [map_add, map_mul, map_sub, map_natCast, map_intCast] at hmap
  unfold atom
  linear_combination (norm := ring_nf) (slicedTerm ι true m * slicedTerm ι false n) * hmap

private theorem diagonal_column (ι : R) (hι : ι ^ 2 = -1) (ab : Fin 4 × Fin 4) :
    C ι * differenceEuler (C ι) (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab =
      rotationObservation (C ι) X 2 ab + mkDerivation R diagonalCorrection (V ι ab) := by
  have hsquare : (C ι : Slice R) ^ 2 = -1 := by
    rw [← map_pow, hι, map_neg, map_one]
  let vp : Fin 3 → Slice R := ![C ι, 0, -C ι]
  let vm : Fin 3 → Slice R := ![-C ι, 0, C ι]
  have hp (j : Fin 3) : mkDerivation R diagonalCorrection (sliceBlock (C ι) X true j) =
      vp j * sliceBlock (C ι) X true j := by
    fin_cases j <;> simp [sliceBlock, diagonalCorrection, vp, mkDerivation_X, derivation_C,
      mul_add] <;>
      first | linear_combination -X 3 * hsquare | linear_combination X 4 * hsquare
  have hm (j : Fin 3) : mkDerivation R diagonalCorrection (sliceBlock (C ι) X false j) =
      vm j * sliceBlock (C ι) X false j := by
    fin_cases j <;> simp [sliceBlock, diagonalCorrection, vm, mkDerivation_X, derivation_C,
      mul_add] <;>
      first | linear_combination -X 3 * hsquare | linear_combination X 4 * hsquare
  rw [rotation_phase_column ι hι, V_eq_contract,
    show mkDerivation R diagonalCorrection (contract (atom ι ab)) =
        contract (fun p q m n => mkDerivation R diagonalCorrection (atom ι ab p q m n)) from
      contract_map (mkDerivation R diagonalCorrection).toLinearMap.toAddMonoidHom _]
  rw [← contract_add]
  unfold differenceEuler
  rw [← contract_mul]
  apply contract_congr
  intro p q s m n _ _
  rw [deriv_atom ι _ vp vm hp hm]
  simp [monomialWeight, vp, vm, Term.phase, Term.degree, atom, slicedTerm, readout_C,
    Nat.cast_add, Nat.cast_mul]
  ring

private def derivativeColumn (i : Fin 5) : Fin 9 := ⟨i.val, by omega⟩

private theorem det_update_derivative_sum (M : Matrix (Fin 9) (Fin 9) (Slice R))
    (j : Fin 9) (hj : 5 ≤ j.val) (v : Fin 5 → Slice R) :
    (M.updateCol j (∑ i : Fin 5, v i • (fun k => M k (derivativeColumn i)))).det = 0 := by
  have h (s : Finset (Fin 5)) :
      (M.updateCol j (∑ i ∈ s, v i • (fun k => M k (derivativeColumn i)))).det = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      apply Matrix.det_eq_zero_of_column_eq_zero j
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ih,
        Matrix.det_updateCol_eq_zero (show derivativeColumn a ≠ j by
          intro he; have he' := congrArg Fin.val he; change a.val = j.val at he'; have ha' := a.isLt; omega),
        mul_zero, add_zero]
  exact h Finset.univ

private theorem critical_partial (ι : R) (deleted : Fin 10) (i : Fin 9) (j : Fin 5) :
    criticalMatrix ι deleted i (derivativeColumn j) =
      pderiv j (V ι (observedRow (deleted.succAbove i))) := by
  have h : (derivativeColumn j).val < 5 := j.isLt
  rw [criticalMatrix, dite_eq_left h]
  rfl

/-- The two replacements preserve the original cofactor up to the constant six.
The diagonal replacement is scaled by the square root of minus one. -/
theorem reduced_cofactor_eq_six (ι : R) (hι : ι ^ 2 = -1) (deleted : Fin 10) :
    (reducedCriticalMatrix ι deleted).det = 6 * (criticalMatrix ι deleted).det := by
  let M := criticalMatrix ι deleted
  let Dr : Fin 9 → Slice R := fun i =>
    mkDerivation R X (V ι (observedRow (deleted.succAbove i)))
  let Dz : Fin 9 → Slice R := fun i =>
    mkDerivation R diagonalCorrection (V ι (observedRow (deleted.succAbove i)))
  let M₁ := M.updateCol 5 ((6 : Slice R) • (fun i => M i 5) - Dr)
  have h₁ : M₁.det = 6 * M.det := by
    unfold M₁
    rw [sub_eq_add_neg, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
      Matrix.updateCol_eq_self]
    have hDr : Dr = ∑ j : Fin 5, (X j : Slice R) • (fun i => M i (derivativeColumn j)) := by
      funext i
      simp only [Dr, derivAlong_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        M, critical_partial]
    rw [hDr, ← neg_one_smul (R := Slice R), Matrix.det_updateCol_smul,
      det_update_derivative_sum M 5 (by decide), mul_zero, add_zero]
  have h₂ : (M₁.updateCol 8 ((fun i => M₁ i 8) + Dz)).det = M₁.det := by
    rw [Matrix.det_updateCol_add, Matrix.updateCol_eq_self]
    have hDz : Dz = ∑ j : Fin 5, (diagonalCorrection j : Slice R) •
        (fun i => M₁ i (derivativeColumn j)) := by
      funext i
      simp only [Dz, derivAlong_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hj : derivativeColumn j ≠ 5 := by
        intro he
        have he' := congrArg Fin.val he
        change j.val = 5 at he'
        have hj' := j.isLt
        omega
      simp only [M₁, Matrix.updateCol_ne hj, M, critical_partial]
    rw [hDz, det_update_derivative_sum M₁ 8 (by decide), add_zero]
  rw [← h₁, ← h₂]
  congr 1
  apply Matrix.ext
  intro i j
  let ab := observedRow (deleted.succAbove i)
  by_cases hj₅ : j = 5
  · subst j
    have hv : M i 5 = V ι ab := rfl
    change radialEuler (C ι) (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab = _
    rw [Matrix.updateCol_ne (by decide : (5 : Fin 9) ≠ 8)]
    simp only [M₁, Matrix.updateCol_self,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv]
    exact radial_column ι ab
  · by_cases hj₈ : j = 8
    · subst j
      have hz : M i 8 = rotationObservation (C ι) X 2 ab := rfl
      change C ι * differenceEuler (C ι)
        (sliceBlock (C ι) X true) (sliceBlock (C ι) X false) ab = _
      simp only [Matrix.updateCol_self, Pi.add_apply, M₁, Matrix.updateCol_ne
        (by decide : (8 : Fin 9) ≠ 5), hz]
      exact diagonal_column ι hι ab
    · simp only [reducedCriticalMatrix, ite_eq_right hj₅, ite_eq_right hj₈,
        Matrix.updateCol_ne hj₈, M₁, Matrix.updateCol_ne hj₅, M]

/-- The original cofactors have total degree at most 47 when six is regular,
in particular over the complex numbers and modulo 1009. -/
theorem critical_cofactor_totalDegree [IsDomain R] (ι : R)
    (hι : ι ^ 2 = -1) (h₆ : (6 : R) ≠ 0) (deleted : Fin 10) :
    (criticalMatrix ι deleted).det.totalDegree ≤ 47 := by
  have h := reduced_cofactor_totalDegree ι deleted
  by_cases hz : (criticalMatrix ι deleted).det = 0
  · simp [hz]
  rw [reduced_cofactor_eq_six ι hι, ← map_ofNat (C : R →+* Slice R),
    totalDegree_mul_of_isDomain (C_ne_zero.mpr h₆) hz, totalDegree_C, zero_add] at h
  exact h


private def kPhasePart (ι : R) (ab : Fin 4 × Fin 4) : Slice R :=
  contract fun p q m n => C ι * (((Term.k m) : Slice R) - ((Term.k n) : Slice R)) * atom ι ab p q m n

private theorem phase_split (ι : R) (hι : ι ^ 2 = -1) (ab : Fin 4 × Fin 4) :
    rotationObservation (C ι) X 2 ab =
      mkDerivation R eRotation (V ι ab) + kPhasePart ι ab := by
  have hsquare : (C ι : Slice R) ^ 2 = -1 := by
    rw [← map_pow, hι, map_neg, map_one]
  let vp : Fin 3 → Slice R := ![0, 0, 2 * C ι]
  let vm : Fin 3 → Slice R := ![0, 0, -2 * C ι]
  have hp (j : Fin 3) : mkDerivation R eRotation (sliceBlock (C ι) X true j) =
      vp j * sliceBlock (C ι) X true j := by
    fin_cases j <;> simp [sliceBlock, eRotation, vp, mkDerivation_X, derivation_C]
    linear_combination -2 * X 4 * hsquare
  have hm (j : Fin 3) : mkDerivation R eRotation (sliceBlock (C ι) X false j) =
      vm j * sliceBlock (C ι) X false j := by
    fin_cases j <;> simp [sliceBlock, eRotation, vm, mkDerivation_X, derivation_C]
    linear_combination -2 * X 4 * hsquare
  rw [rotation_phase_column ι hι, V_eq_contract,
    show mkDerivation R eRotation (contract (atom ι ab)) =
        contract (fun p q m n => mkDerivation R eRotation (atom ι ab p q m n)) from
      contract_map (mkDerivation R eRotation).toLinearMap.toAddMonoidHom _]
  rw [kPhasePart, ← contract_add]
  apply contract_congr
  intro p q s m n _ _
  rw [deriv_atom ι _ vp vm hp hm]
  simp [monomialWeight, vp, vm, Term.phase, Nat.cast_add, Nat.cast_mul]
  ring

private theorem slicedTerm_dvd (ι : R) (b : Bool) (m : Term) (hm : (Term.k m) ≠ 0) :
    X 1 ∣ slicedTerm ι b m := by
  simp only [slicedTerm, Term.eval]
  have h : sliceBlock (C ι) (X : Fin 5 → Slice R) b 1 = X 1 := by cases b <;> rfl
  rw [h]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ hm) _) _

private theorem kPhasePart_dvd (ι : R) (ab : Fin 4 × Fin 4) :
    X 1 ∣ kPhasePart ι ab := by
  unfold kPhasePart contract
  apply Finset.dvd_sum
  intro p _
  apply Finset.dvd_sum
  intro q _
  apply Finset.dvd_sum
  intro s _
  apply List.dvd_sum
  intro a ha
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
  apply List.dvd_sum
  intro a ha
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp ha
  by_cases hm : (Term.k m) = 0
  · by_cases hn : (Term.k n) = 0
    · simp [hm, hn]
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right (slicedTerm_dvd ι false n hn) _) _) _
  · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (slicedTerm_dvd ι true m hm) _) _) _

/-- Every original cofactor has the common factor (k). -/
theorem critical_cofactor_dvd_k (ι : R) (hι : ι ^ 2 = -1) (deleted : Fin 10) :
    X 1 ∣ (criticalMatrix ι deleted).det := by
  let M := criticalMatrix ι deleted
  let ab := fun i => observedRow (deleted.succAbove i)
  let De : Fin 9 → Slice R := fun i => mkDerivation R eRotation (V ι (ab i))
  have hD : De = ∑ j : Fin 5, (eRotation j : Slice R) • (fun i => M i (derivativeColumn j)) := by
    funext i
    simp only [De, ab, derivAlong_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      M, critical_partial]
  choose q hq using fun i : Fin 9 => kPhasePart_dvd ι (ab i)
  have hz : (fun i => M i 8) = De + (X 1 : Slice R) • q := by
    funext i
    change rotationObservation (C ι) X 2 (ab i) = _
    rw [phase_split ι hι]
    simp only [De, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq i]
  change X 1 ∣ M.det
  rw [← Matrix.updateCol_eq_self M 8, hz, Matrix.det_updateCol_add,
    Matrix.det_updateCol_smul, hD, det_update_derivative_sum _ _ (by decide),
    zero_add]
  exact dvd_mul_right _ _

/-- Each critical cofactor is a multiple of (k) with a quotient of total degree at most 46. -/
theorem critical_cofactor_quotient [IsDomain R] (ι : R)
    (hι : ι ^ 2 = -1) (h₆ : (6 : R) ≠ 0) (deleted : Fin 10) :
    ∃ p : Slice R, (criticalMatrix ι deleted).det = X 1 * p ∧ p.totalDegree ≤ 46 := by
  obtain ⟨p, hp⟩ := critical_cofactor_dvd_k ι hι deleted
  refine ⟨p, hp, ?_⟩
  by_cases hz : p = 0
  · simp [hz]
  have h := critical_cofactor_totalDegree ι hι h₆ deleted
  rw [hp, totalDegree_mul_of_isDomain (X_ne_zero 1) hz, totalDegree_X] at h
  omega

end

end CriticalMatrix

section Evaluation

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem map_pauli (f : R →+* S) (ι : R) (a : Fin 4) (p q : Fin 2) :
    f (pauli ι a p q) = pauli (f ι) a p q := by
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    simp [pauli, Matrix.cons_val', Matrix.of_apply]

/-- The literal observation commutes with specialization of its scalar arguments. -/
theorem map_slicedObservation (f : R →+* S) (ι : R) (x : Fin 5 → R)
    (ab : Fin 4 × Fin 4) :
    f (slicedObservation ι x ab) = slicedObservation (f ι) (fun j => f (x j)) ab := by
  have hs (ket : Bool) (j : Fin 3) :
      f (sliceBlock ι x ket j) = sliceBlock (f ι) (fun i => f (x i)) ket j := by
    cases ket <;> fin_cases j <;> simp [sliceBlock]
  simp only [slicedObservation, observation, readout, rawGram, wordTrace, evalTerms, Term.eval,
    map_sum, map_mul, map_list_sum, List.map_map, Function.comp_def, map_pow, map_intCast,
    map_pauli, hs]
  rfl

/-- Rotation also commutes with specialization. -/
theorem map_rotationObservation (f : R →+* S) (ι : R) (x : Fin 5 → R)
    (j : Fin 3) (ab : Fin 4 × Fin 4) :
    f (rotationObservation ι x j ab) =
      rotationObservation (f ι) (fun i => f (x i)) j ab := by
  simp [rotationObservation, map_slicedObservation]

theorem observation_totalDegree_slice (ι : R) (ab : Fin 4 × Fin 4) :
    (V ι ab).totalDegree ≤ 6 := V_degree ι ab

theorem partial_totalDegree_slice (ι : R) (ab : Fin 4 × Fin 4) (i : Fin 5) :
    (MvPolynomial.pderiv i (V ι ab)).totalDegree ≤ 5 := diff_degree (V_degree ι ab) i

end Evaluation

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

#print axioms D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate.wordTrace_eq_matrixTrace
#print axioms D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate.rawGram_eq_rawTwo
#print axioms D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate.reduced_cofactor_eq_six
#print axioms D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate.critical_cofactor_quotient

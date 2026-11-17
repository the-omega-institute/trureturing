/- GID: D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary external derivatives and full native affine row coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators ContDiff

namespace D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient
open OriginalGaussianSourceGerm
section ExternalJets
open MvPolynomial NativeAffineTransport
open FactorialFockMetric (weight weight_pos)
set_option backward.isDefEq.respectTransparency true
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Ordinary differentiation in a single external coordinate. -/
def coordinateDerivative (i : I) (f : (I → ℂ) → ℂ) (x : I → ℂ) : ℂ :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- Finite ordered partial derivatives. The empty word evaluates the function. -/
def coordinateJet : List I → ((I → ℂ) → ℂ) → (I → ℂ) → ℂ
  | [], f => f
  | i :: l, f => coordinateJet l (coordinateDerivative i f)

private def polynomialJet : List I → MvPolynomial I ℂ → MvPolynomial I ℂ
  | [], p => p
  | i :: l, p => polynomialJet l (pderiv i p)

/-- Multiplicities of the external coordinates differentiated by a word. -/
def jetOccupation : List I → I →₀ ℕ
  | [] => 0
  | i :: l => jetOccupation l + Finsupp.single i 1

private theorem jet_degree (l : List I) : (jetOccupation l).degree = l.length := by
  induction l with
  | nil => simp [jetOccupation]
  | cons i l ih => simp [jetOccupation, ih]

private theorem hasDerivAt_eval_update (p : MvPolynomial I ℂ) (x : I → ℂ) (i : I) :
    HasDerivAt (fun t => eval (Function.update x i t) p)
      (eval x (pderiv i p)) (x i) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (x i) c
  | add p q hp hq => simpa only [map_add, Pi.add_apply] using hp.fun_add hq
  | mul_X p j hp =>
    have hj : HasDerivAt (fun t => Function.update x i t j)
        (if j = i then (1 : ℂ) else 0) (x i) := by
      by_cases h : j = i
      · subst j
        simpa using hasDerivAt_id' (x i)
      · simpa [Function.update_of_ne h, h] using hasDerivAt_const (x i) (x j)
    convert hp.fun_mul hj using 1 <;>
      simp [map_mul, pderiv_mul, pderiv_X, Pi.single_apply, eq_comm,
        Function.update_eq_self, ite_mul, apply_ite] <;> split_ifs <;> simp_all <;> ring

private theorem coordinateDerivative_eval (i : I) (p : MvPolynomial I ℂ) :
    coordinateDerivative i (fun x => eval x p) = fun x => eval x (pderiv i p) := by
  funext x
  exact (hasDerivAt_eval_update p x i).deriv

private theorem coordinateJet_eval (l : List I) (p : MvPolynomial I ℂ) :
    coordinateJet l (fun x => eval x p) = fun x => eval x (polynomialJet l p) := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih =>
    simp only [coordinateJet, polynomialJet, coordinateDerivative_eval, ih]

private theorem coordinateDerivative_exp_mul (i : I) (p r : MvPolynomial I ℂ) :
    coordinateDerivative i (fun x => Complex.exp (eval x p) * eval x r) =
      fun x => Complex.exp (eval x p) * eval x (pderiv i p * r + pderiv i r) := by
  funext x
  have h := ((hasDerivAt_eval_update p x i).cexp).fun_mul (hasDerivAt_eval_update r x i)
  rw [coordinateDerivative, h.deriv]
  simp only [Function.update_eq_self, map_add, map_mul]
  ring

private theorem polynomialJet_add (l : List I) (p q : MvPolynomial I ℂ) :
    polynomialJet l (p + q) = polynomialJet l p + polynomialJet l q := by
  induction l generalizing p q with
  | nil => rfl
  | cons i l ih => simp only [polynomialJet, map_add, ih]

private theorem polynomialJet_smul (l : List I) (c : ℂ) (p : MvPolynomial I ℂ) :
    polynomialJet l (c • p) = c • polynomialJet l p := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih => simp only [polynomialJet, Derivation.map_smul, ih]

private theorem polynomialJet_vanish (l : List I) (p r : MvPolynomial I ℂ)
    (hp : eval (0 : I → ℂ) p = 0) (k : ℕ) (hk : l.length < k) :
    eval (0 : I → ℂ) (polynomialJet l (p ^ k * r)) = 0 := by
  induction l generalizing k r with
  | nil =>
    simp only [polynomialJet, map_mul, map_pow, hp, zero_pow (by omega : k ≠ 0), zero_mul]
  | cons i l ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by simp only [List.length_cons] at hk; omega)
    have he : pderiv i (p ^ (m+1) * r) =
        (m+1 : ℂ) • (p ^ m * (pderiv i p * r)) + p ^ (m+1) * pderiv i r := by
      rw [pderiv_mul, pderiv_pow]
      simp only [Nat.add_sub_cancel, smul_eq_C_mul]
      have hc : ((m+1 : ℕ) : MvPolynomial I ℂ) = C (m+1 : ℂ) := by simp
      rw [hc]
      ring
    rw [polynomialJet, he, polynomialJet_add, polynomialJet_smul]
    simp only [map_add, smul_eq_C_mul, map_mul, eval_C]
    rw [ih (pderiv i p * r) m (by simp only [List.length_cons] at hk; omega),
      ih (pderiv i r) (m+1) (by simp only [List.length_cons] at hk; omega)]
    ring

private theorem expCut_succ (p : MvPolynomial I ℂ) (m : ℕ) :
    expCut p (m+1) = expCut p m + ((m+1).factorial : ℂ)⁻¹ • p^(m+1) := by
  exact Finset.sum_range_succ _ _

/-- Every finite ordinary external jet is determined by the full-degree
exponential Taylor cutoff. No external degree is omitted. -/
private theorem external_jet_expCut_aux (l : List I) (p r : MvPolynomial I ℂ)
    (hp : p.coeff 0 = 0) (N : ℕ) (hN : l.length ≤ N) :
    coordinateJet l (fun x => Complex.exp (eval x p) * eval x r) 0 =
      eval (0 : I → ℂ) (polynomialJet l (expCut p N * r)) := by
  have hp' : eval (0 : I → ℂ) p = 0 := by simpa only [eval_zero, constantCoeff_eq] using hp
  induction l generalizing N r with
  | nil =>
    have he : eval (0 : I → ℂ) (expCut p N) = 1 := by
      simp only [expCut, map_sum, smul_eq_C_mul, map_mul, eval_C, map_pow, hp']
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        simp only [eval_zero, constantCoeff_eq, hp, zero_pow hk0, mul_zero]
      · simp
    simp only [coordinateJet, polynomialJet, hp', Complex.exp_zero, one_mul, map_mul, he]
  | cons i l ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := N) (by simp only [List.length_cons] at hN; omega)
    rw [coordinateJet, coordinateDerivative_exp_mul, ih _ m (by simpa using hN)]
    have he : pderiv i (expCut p (m+1) * r) =
        expCut p m * (pderiv i p * r + pderiv i r) +
        ((m+1).factorial : ℂ)⁻¹ • (p^(m+1) * pderiv i r) := by
      rw [pderiv_mul, pderiv_expCut, expCut_succ]
      simp only [smul_eq_C_mul]
      ring
    rw [polynomialJet, he, polynomialJet_add, polynomialJet_smul, map_add, smul_eq_C_mul, map_mul, eval_C,
      polynomialJet_vanish l p (pderiv i r) hp' (m+1) (by simp only [List.length_cons] at hN; omega)]
    simp

private theorem polynomialJet_constant (l : List I) (p : MvPolynomial I ℂ) :
    eval (0 : I → ℂ) (polynomialJet l p) =
      (weight (jetOccupation l) : ℂ) * p.coeff (jetOccupation l) := by
  induction l generalizing p with
  | nil => simp [polynomialJet, jetOccupation, weight, constantCoeff_eq]
  | cons i l ih =>
    rw [polynomialJet, ih, coeff_pderiv]
    simp only [jetOccupation]
    rw [show (weight (jetOccupation l + Finsupp.single i 1) : ℂ) =
      ((jetOccupation l) i+1 : ℂ) * (weight (jetOccupation l) : ℂ) by
        exact_mod_cast FactorialFockMetric.weight_add_single (jetOccupation l) i]
    ring

/-- A full-degree exponential Taylor polynomial has exactly the same finite
ordinary external jet as the original exponential times its polynomial factor. -/
theorem external_jet_expCut (l : List I) (p r : MvPolynomial I ℂ)
    (hp : p.coeff 0 = 0) (N : ℕ) (hN : l.length ≤ N) :
    coordinateJet l (fun x => Complex.exp (eval x p) * eval x r) 0 =
      coordinateJet l (fun x => eval x (expCut p N * r)) 0 := by
  rw [coordinateJet_eval]
  exact external_jet_expCut_aux l p r hp N hN

/-- The ordinary multivariate external coefficient of the actual affine
exponential is the native affineCoefficient. The normalization is the product
of coordinate factorials; the Taylor cutoff bounds the whole occupation. -/
theorem native_affine_external_jet (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (l : List I) (N : ℕ) (hN : (jetOccupation l).degree ≤ N) :
    coordinateJet l (fun x => Complex.exp (eval x (affineExponent A mu))) 0 /
        (weight (jetOccupation l) : ℂ) =
      OriginalChargedRowSource.affineCoefficient A mu (jetOccupation l) := by
  have h := external_jet_expCut l (affineExponent A mu) 1 (affineExponent_constant A mu)
    N (by simpa only [jet_degree] using hN)
  simp only [map_one, mul_one] at h
  rw [h, coordinateJet_eval]
  dsimp only
  rw [polynomialJet_constant, native_affine_eq_taylor A mu hs,
    taylorCoefficient_cut A mu (jetOccupation l) N hN]
  have hw : (weight (jetOccupation l) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (weight_pos (jetOccupation l)))
  exact mul_div_cancel_left₀ _ hw

private theorem jetOccupation_multiset (l : List I) :
    jetOccupation l = (l : Multiset I).toFinsupp := by
  induction l with
  | nil => simp [jetOccupation]
  | cons i l ih =>
    ext j
    simp [jetOccupation, ih, Multiset.toFinsupp_apply, List.count_cons, Finsupp.single_apply, add_comm]

private def occupationWord (d : I →₀ ℕ) : List I := d.toMultiset.toList

private theorem occupationWord_spec (d : I →₀ ℕ) :
    jetOccupation (occupationWord d) = d := by
  rw [jetOccupation_multiset]
  simp [occupationWord]

/-- Ordinary multivariate coefficient extraction by finite coordinate derivatives. -/
def externalCoefficient (d : I →₀ ℕ) (f : (I → ℂ) → ℂ) : ℂ :=
  coordinateJet (occupationWord d) f 0 / (weight d : ℂ)

/-- Every external occupation, including the empty occupation, is extracted
at its full total degree from the actual affine exponential. -/
theorem native_affine_external_coefficient (A : Matrix I I ℂ) (mu : I → ℂ)
    (hs : ∀ i j, A i j = A j i) (d : I →₀ ℕ) (N : ℕ) (hN : d.degree ≤ N) :
    externalCoefficient d (fun x => Complex.exp (eval x (affineExponent A mu))) =
      OriginalChargedRowSource.affineCoefficient A mu d := by
  have h := native_affine_external_jet A mu hs (occupationWord d) N
  rw [occupationWord_spec] at h
  exact h hN

theorem coordinateJet_const_mul (l : List I) (c : ℂ) (f : (I → ℂ) → ℂ) :
    coordinateJet l (fun x => c * f x) = fun x => c * coordinateJet l f x := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    have he : coordinateDerivative i (fun x => c * f x) =
        fun x => c * coordinateDerivative i f x := by
      ext x
      exact deriv_const_mul_field c
    rw [coordinateJet, he, ih]
    rfl

theorem coordinateJet_append (l k : List I) (f : (I → ℂ) → ℂ) :
    coordinateJet (l ++ k) f = coordinateJet k (coordinateJet l f) := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih => simpa only [List.cons_append, coordinateJet] using ih (coordinateDerivative i f)

variable {J : Type*} [Fintype J] [DecidableEq J]

private theorem coordinateJet_inl (l : List I) (f : ((I ⊕ J) → ℂ) → ℂ)
    (x : I → ℂ) (y : J → ℂ) :
    coordinateJet l (fun u => f (Sum.elim u y)) x =
      coordinateJet (l.map Sum.inl) f (Sum.elim x y) := by
  induction l generalizing f x with
  | nil => rfl
  | cons i l ih =>
    have he : coordinateDerivative i (fun u => f (Sum.elim u y)) =
        fun u => coordinateDerivative (Sum.inl i) f (Sum.elim u y) := by
      ext u
      simp only [coordinateDerivative, Sum.elim_inl, ← Sum.update_elim_inl]
    simp only [coordinateJet, List.map_cons, he]
    exact ih _ x

private theorem coordinateJet_inr (l : List J) (f : ((I ⊕ J) → ℂ) → ℂ)
    (x : I → ℂ) (y : J → ℂ) :
    coordinateJet l (fun v => f (Sum.elim x v)) y =
      coordinateJet (l.map Sum.inr) f (Sum.elim x y) := by
  induction l generalizing f y with
  | nil => rfl
  | cons i l ih =>
    have he : coordinateDerivative i (fun v => f (Sum.elim x v)) =
        fun v => coordinateDerivative (Sum.inr i) f (Sum.elim x v) := by
      ext v
      simp only [coordinateDerivative, Sum.elim_inr, ← Sum.update_elim_inr]
    simp only [coordinateJet, List.map_cons, he]
    exact ih _ y

private theorem jetOccupation_join (l : List I) (k : List J) :
    jetOccupation (l.map Sum.inl ++ k.map Sum.inr) =
      (jetOccupation l).sumElim (jetOccupation k) := by
  induction l with
  | nil =>
    induction k with
    | nil => ext (i | i) <;> simp [jetOccupation]
    | cons j k ih =>
      simp only [List.map_nil, List.nil_append, List.map_cons, jetOccupation] at ih ⊢
      rw [ih]
      ext (i | i) <;> simp [Finsupp.single_apply]
  | cons i l ih =>
    simp only [List.map_cons, List.cons_append, jetOccupation, ih]
    ext (j | j) <;> simp [Finsupp.single_apply]

private theorem affineExponent_split (C : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (m : I ⊕ J → ℂ) (hs : ∀ i j, C i j = C j i) (u : I → ℂ) (x : J → ℂ) :
    eval (Sum.elim u x) (affineExponent C m) = externalExponent C m x +
      eval u (affineExponent (C.submatrix Sum.inl Sum.inl) (mixedMean C m x)) := by
  simp only [affineExponent, FactorialFockQuadraticEstimate.quadratic, map_add,
    map_sum, smul_eq_C_mul, map_mul, eval_C, eval_X, Matrix.submatrix_apply,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, externalExponent, mixedMean,
    Finset.sum_add_distrib, add_mul, Finset.sum_mul, Finset.mul_sum]
  have hc : (∑ i : J, ∑ j : I, C (.inr i) (.inl j) * (x i * u j)) =
      ∑ j : I, ∑ i : J, C (.inl j) (.inr i) * (u j * x i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs (.inr i) (.inl j), mul_comm (x i)]
  rw [hc]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have ht : (∑ i : I, (∑ j : J, C (.inl i) (.inr j) * x j) * u i) =
      ∑ i : I, ∑ j : J, C (.inl i) (.inr j) * u i * x j := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [ht]
  ring

/-- Internal extraction followed by the ordinary external coefficient gives
the native coefficient of the full row. Both occupations contribute to the
Taylor degree; no identity of source arrays is assumed. -/
theorem native_mixed_external_coefficient (C : Matrix (I ⊕ J) (I ⊕ J) ℂ)
    (m : I ⊕ J → ℂ) (hs : ∀ i j, C i j = C j i) (d : I →₀ ℕ) (h : J →₀ ℕ) :
    externalCoefficient h (fun x => Complex.exp (externalExponent C m x) *
      OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
        (mixedMean C m x) d) =
      OriginalChargedRowSource.affineCoefficient C m (d.sumElim h) := by
  let l := occupationWord d
  let k := occupationWord h
  let F := fun v => Complex.exp (eval v (affineExponent C m))
  have hi (x : J → ℂ) : coordinateJet (l.map Sum.inl) F (Sum.elim 0 x) =
      (weight d : ℂ) * (Complex.exp (externalExponent C m x) *
        OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
          (mixedMean C m x) d) := by
    rw [← coordinateJet_inl]
    simp only [F, affineExponent_split C m hs, Complex.exp_add]
    rw [coordinateJet_const_mul]
    have hh := native_affine_external_jet (C.submatrix Sum.inl Sum.inl)
      (mixedMean C m x) (fun i j => hs (.inl i) (.inl j)) l d.degree (by simp only [l, occupationWord_spec]; exact le_rfl)
    rw [show jetOccupation l = d from occupationWord_spec d] at hh
    have hw : (weight d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (weight_pos d))
    dsimp only
    rw [(div_eq_iff hw).mp hh]
    ring
  have he := native_affine_external_jet C m hs (l.map Sum.inl ++ k.map Sum.inr)
    (d.sumElim h).degree (by simp only [jetOccupation_join, l, k, occupationWord_spec]; exact le_rfl)
  rw [jetOccupation_join, show jetOccupation l = d from occupationWord_spec d,
    show jetOccupation k = h from occupationWord_spec h, coordinateJet_append] at he
  have hz : (0 : (I ⊕ J) → ℂ) = Sum.elim (0 : I → ℂ) (0 : J → ℂ) := by
    ext (i | i) <;> rfl
  rw [hz] at he
  change coordinateJet (k.map Sum.inr) (coordinateJet (l.map Sum.inl) F) (Sum.elim 0 0) /
    (weight (d.sumElim h) : ℂ) = _ at he
  rw [← coordinateJet_inr (I := I) k (coordinateJet (l.map Sum.inl) F) 0 0] at he
  simp only [hi, coordinateJet_const_mul] at he
  have hw : (weight d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (weight_pos d))
  have hv : (weight h : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (weight_pos h))
  have hprod : (weight (d.sumElim h) : ℂ) = (weight d : ℂ) * (weight h : ℂ) := by
    simp [weight, Finsupp.prod_sumElim, Nat.cast_mul]
  rw [hprod] at he
  change _ / (weight h : ℂ) = _
  convert he using 1 <;> field_simp <;> ring

/-- Equality on an open external neighborhood is preserved by every finite
ordinary coordinate jet. -/
theorem coordinateJet_congrOn (l : List I) {f g : (I → ℂ) → ℂ} {U : Set (I → ℂ)}
    (hU : IsOpen U) (h : Set.EqOn f g U) : Set.EqOn (coordinateJet l f) (coordinateJet l g) U := by
  induction l generalizing f g with
  | nil => exact h
  | cons i l ih =>
    apply ih
    intro x hx
    have ht : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
      simpa only [id_eq, Function.update_eq_self] using ((continuous_const (y := x)).update i continuous_id).tendsto (x i)
    have he : (fun t => f (Function.update x i t)) =ᶠ[nhds (x i)]
        (fun t => g (Function.update x i t)) := by
      filter_upwards [ht.eventually (hU.mem_nhds hx)] with t ht
      exact h ht
    exact he.deriv_eq

private theorem norm_update_lt (x : I → ℂ) (i : I) (t : ℂ) (r : ℝ)
    (hx : ‖x‖ < r) (ht : ‖t‖ < r) : ‖Function.update x i t‖ < r := by
  rw [pi_norm_lt_iff (lt_of_le_of_lt (norm_nonneg _) hx)]
  intro j
  by_cases hj : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hj] using (norm_le_pi_norm x j).trans_lt hx

private theorem coordinateDerivative_bound (f : (I → ℂ) → ℂ) (i : I) (M r : ℝ)
    (hr : 0 < r) (hf : ∀ x, Differentiable ℂ (fun t => f (Function.update x i t)))
    (hb : ∀ x, ‖x‖ < r → ‖f x‖ ≤ M) (x : I → ℂ) (hx : ‖x‖ < r/2) :
    ‖coordinateDerivative i f x‖ ≤ M / (r/4) := by
  let g := fun t => f (Function.update x i t)
  rw [coordinateDerivative, ← Complex.cderiv_eq_deriv isOpen_univ
    (hf x).differentiableOn (by positivity : 0 < r/4) (by simp)]
  apply Complex.norm_cderiv_le (by positivity)
  intro t ht
  apply hb
  apply norm_update_lt x i t r (by linarith)
  have hd : ‖t - x i‖ = r/4 := mem_sphere_iff_norm.mp ht
  calc
    ‖t‖ ≤ ‖t - x i‖ + ‖x i‖ := by simpa using norm_add_le (t - x i) (x i)
    _ ≤ r/4 + ‖x‖ := by rw [hd]; exact add_le_add_right (norm_le_pi_norm x i) _
    _ < r := by linarith

private theorem coordinateDerivative_tsum {K : Type*} (F : K → (I → ℂ) → ℂ)
    (i : I) (M : K → ℝ) (hM : Summable M) (r : ℝ) (hr : 0 < r)
    (hf : ∀ k x, Differentiable ℂ (fun t => F k (Function.update x i t)))
    (hb : ∀ k x, ‖x‖ < r → ‖F k x‖ ≤ M k)
    (x : I → ℂ) (hx : ‖x‖ < r) :
    HasSum (fun k => coordinateDerivative i (F k) x)
      (coordinateDerivative i (fun y => ∑' k, F k y) x) := by
  change HasSum (fun k => deriv (fun t => F k (Function.update x i t)) (x i))
    (deriv (fun t => ∑' k, F k (Function.update x i t)) (x i))
  apply Complex.hasSum_deriv_of_summable_norm hM
    (fun k => (hf k x).differentiableOn) Metric.isOpen_ball
    (fun k t ht => hb k _ (norm_update_lt x i t r hx (mem_ball_zero_iff.mp ht)))
    (mem_ball_zero_iff.mpr ((norm_le_pi_norm x i).trans_lt hx))

/-- Every fixed finite external derivative passes through a normally bounded
sum of entire coordinate jets. The positive neighborhood can shrink with the
jet order; its radius is unrelated to any source cutoff limit. -/
theorem coordinateJet_tsum_normal {K : Type*} (F : K → (I → ℂ) → ℂ)
    (M : K → ℝ) (hM : Summable M) (R : ℝ) (hR : 0 < R)
    (hf : ∀ k l i x, Differentiable ℂ (fun t => coordinateJet l (F k) (Function.update x i t)))
    (hb : ∀ k x, ‖x‖ < R → ‖F k x‖ ≤ M k) (l : List I) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : K → ℝ, Summable B ∧
      (∀ k x, ‖x‖ < r → ‖coordinateJet l (F k) x‖ ≤ B k) ∧
      (∀ x, ‖x‖ < r → HasSum (fun k => coordinateJet l (F k) x)
        (coordinateJet l (fun y => ∑' k, F k y) x)) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨R, hR, M, hM, hb, ?_⟩
    intro x hx
    exact (Summable.of_norm (hM.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hb k x hx))).hasSum
  | append_singleton l i ih =>
    obtain ⟨r, hr, B, hB, hb, he⟩ := ih
    refine ⟨r/2, by positivity, (fun k => B k / (r/4)), hB.div_const _, ?_, ?_⟩
    · intro k x hx
      simpa only [coordinateJet_append, coordinateJet] using
        coordinateDerivative_bound (coordinateJet l (F k)) i (B k) r hr
          (hf k l i) (hb k) x hx
    · intro x hx
      have hx' : ‖x‖ < r := by linarith
      have hs := coordinateDerivative_tsum (fun k => coordinateJet l (F k)) i B hB r hr
        (fun k => hf k l i) hb x hx'
      have ht : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
        simpa only [id_eq, Function.update_eq_self] using ((continuous_const (y := x)).update i continuous_id).tendsto (x i)
      have hh : (fun t => coordinateJet l (fun y => ∑' k, F k y) (Function.update x i t)) =ᶠ[nhds (x i)]
          (fun t => ∑' k, coordinateJet l (F k) (Function.update x i t)) := by
        filter_upwards [ht.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds hx')] with t ht
        exact (he _ ht).tsum_eq.symm
      simpa only [coordinateJet_append, coordinateJet, coordinateDerivative, hh.deriv_eq] using hs

private theorem coordinateJet_normal_family {K T : Type*} (F : K → T → (I → ℂ) → ℂ)
    (M : K → ℝ) (hM : Summable M) (R : ℝ) (hR : 0 < R)
    (hf : ∀ k v l i x, Differentiable ℂ (fun t => coordinateJet l (F k v) (Function.update x i t)))
    (hb : ∀ k v x, ‖x‖ < R → ‖F k v x‖ ≤ M k) (l : List I) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : K → ℝ, Summable B ∧
      (∀ k v x, ‖x‖ < r → ‖coordinateJet l (F k v) x‖ ≤ B k) ∧
      (∀ v x, ‖x‖ < r → HasSum (fun k => coordinateJet l (F k v) x)
        (coordinateJet l (fun y => ∑' k, F k v y) x)) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨R, hR, M, hM, hb, ?_⟩
    intro v x hx
    exact (Summable.of_norm (hM.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hb k v x hx))).hasSum
  | append_singleton l i ih =>
    obtain ⟨r, hr, B, hB, hb, he⟩ := ih
    refine ⟨r/2, by positivity, (fun k => B k / (r/4)), hB.div_const _, ?_, ?_⟩
    · intro k v x hx
      simpa only [coordinateJet_append, coordinateJet] using
        coordinateDerivative_bound (coordinateJet l (F k v)) i (B k) r hr
          (hf k v l i) (hb k v) x hx
    · intro v x hx
      have hx' : ‖x‖ < r := by linarith
      have hs := coordinateDerivative_tsum (fun k => coordinateJet l (F k v)) i B hB r hr
        (fun k => hf k v l i) (fun k => hb k v) x hx'
      have ht : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
        simpa only [id_eq, Function.update_eq_self] using ((continuous_const (y := x)).update i continuous_id).tendsto (x i)
      have hh : (fun t => coordinateJet l (fun y => ∑' k, F k v y) (Function.update x i t)) =ᶠ[nhds (x i)]
          (fun t => ∑' k, coordinateJet l (F k v) (Function.update x i t)) := by
        filter_upwards [ht.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds hx')] with t ht
        exact (he v _ ht).tsum_eq.symm
      simpa only [coordinateJet_append, coordinateJet, coordinateDerivative, hh.deriv_eq] using hs


private theorem coordinateDerivative_fderiv {f : (I → ℂ) → ℂ} (i : I) (x : I → ℂ)
    (hf : DifferentiableAt ℂ f x) :
    coordinateDerivative i f x = fderiv ℂ f x (Pi.single i 1) := by
  have hu : HasDerivAt (fun t => Function.update x i t) (Pi.single i 1) (x i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hasDerivAt_id' (x i)
    · simpa [Function.update_of_ne hj, Pi.single_apply, hj] using hasDerivAt_const (x i) (x j)
  have hf' : HasFDerivAt f (fderiv ℂ f x) (Function.update x i (x i)) := by simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x i) hu).deriv

private theorem coordinateJet_contDiff (f : (I → ℂ) → ℂ)
    (hf : ContDiff ℂ (⊤ : ℕ∞ω) f) (l : List I) :
    ContDiff ℂ (⊤ : ℕ∞ω) (coordinateJet l f) := by
  induction l generalizing f with
  | nil => exact hf
  | cons i l ih =>
    apply ih
    have he : coordinateDerivative i f = fun x => fderiv ℂ f x (Pi.single i 1) := by
      ext x
      exact coordinateDerivative_fderiv i x (hf.differentiable (by simp) x)
    rw [he]
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem powerCoefficient_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E → Matrix I I ℂ) (hA : ∀ i j, ContDiff ℂ (⊤ : ℕ∞ω) (fun x => A x i j))
    (k : ℕ) (d : I →₀ ℕ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fun x => (FactorialFockQuadraticEstimate.quadratic (A x) ^ k).coeff d) := by
  induction k generalizing d with
  | zero => simp only [pow_zero]; exact contDiff_const
  | succ k ih =>
    simp only [pow_succ, coeff_mul]
    apply ContDiff.sum
    intro p hp
    apply (ih p.1).mul
    simp only [FactorialFockQuadraticEstimate.quadratic, coeff_smul, coeff_sum, smul_eq_mul]
    fun_prop

private theorem affineCoefficient_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E → Matrix I I ℂ) (m : E → I → ℂ)
    (hA : ∀ i j, ContDiff ℂ (⊤ : ℕ∞ω) (fun x => A x i j))
    (hm : ∀ i, ContDiff ℂ (⊤ : ℕ∞ω) (fun x => m x i)) (d : I →₀ ℕ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fun x => OriginalChargedRowSource.affineCoefficient (A x) (m x) d) := by
  have ha : ∀ i j, ContDiff ℂ (⊤ : ℕ∞ω)
      (fun x => OriginalChargedRowSource.affineKernel (A x) (m x) i j) := by
    intro i j
    cases i <;> cases j <;>
      simp only [OriginalChargedRowSource.affineKernel, ElementaryGaussianContraction.leftKernel,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply,
        Matrix.zero_apply]
    · exact hA _ _
    · exact hm _
    · exact hm _
    · exact contDiff_const
  simp only [OriginalChargedRowSource.affineCoefficient,
    FactorialFockQuadraticEstimate.gaussianCoefficient,
    FactorialFockQuadraticEstimate.gaussianPiece, coeff_smul, smul_eq_mul]
  apply ContDiff.sum
  intro k hk
  exact contDiff_const.mul (powerCoefficient_contDiff _ ha _ _)

/-- Ordinary fixed multivariate coefficient extraction commutes with a
normally bounded sum, with its complete external factorial normalization. -/
theorem externalCoefficient_tsum {K : Type*} (F : K → (I → ℂ) → ℂ)
    (M : K → ℝ) (hM : Summable M) (R : ℝ) (hR : 0 < R)
    (hf : ∀ k l i x, Differentiable ℂ (fun t => coordinateJet l (F k) (Function.update x i t)))
    (hb : ∀ k x, ‖x‖ < R → ‖F k x‖ ≤ M k) (d : I →₀ ℕ) :
    HasSum (fun k => externalCoefficient d (F k))
      (externalCoefficient d (fun x => ∑' k, F k x)) := by
  obtain ⟨r, hr, B, hB, hb, he⟩ := coordinateJet_tsum_normal F M hM R hR hf hb (occupationWord d)
  exact (he 0 (by simpa using hr)).div_const _

private theorem externalCoefficient_const_mul (d : I →₀ ℕ) (c : ℂ) (f : (I → ℂ) → ℂ) :
    externalCoefficient d (fun x => c * f x) = c * externalCoefficient d f := by
  simp only [externalCoefficient, coordinateJet_const_mul]
  ring

private theorem externalCoefficient_mul_const (d : I →₀ ℕ) (f : (I → ℂ) → ℂ) (c : ℂ) :
    externalCoefficient d (fun x => f x * c) = externalCoefficient d f * c := by
  simp_rw [mul_comm _ c]
  rw [externalCoefficient_const_mul, mul_comm]

/-- Consecutive ordinary extraction of the two actual external row families. -/
def externalPairCoefficient (h : I →₀ ℕ) (k : J →₀ ℕ)
    (F : (I → ℂ) → (J → ℂ) → ℂ) : ℂ :=
  externalCoefficient k (fun y => externalCoefficient h (fun x => F x y))

private theorem externalPairCoefficient_jet (h : I →₀ ℕ) (k : J →₀ ℕ)
    (F : (I → ℂ) → (J → ℂ) → ℂ) :
    externalPairCoefficient h k F =
      coordinateJet ((occupationWord h).map Sum.inl ++ (occupationWord k).map Sum.inr)
        (fun v => F (v ∘ Sum.inl) (v ∘ Sum.inr)) 0 /
        ((weight h : ℂ) * (weight k : ℂ)) := by
  unfold externalPairCoefficient externalCoefficient
  rw [coordinateJet_append]
  have hz : (0 : (I ⊕ J) → ℂ) = Sum.elim (0 : I → ℂ) (0 : J → ℂ) := by ext (i | i) <;> rfl
  rw [hz, ← coordinateJet_inr]
  have hi (y : J → ℂ) :
      coordinateJet (List.map Sum.inl (occupationWord h))
        (fun v => F (v ∘ Sum.inl) (v ∘ Sum.inr)) (Sum.elim 0 y) =
      coordinateJet (occupationWord h) (fun x => F x y) 0 := by
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (coordinateJet_inl (occupationWord h)
        (fun v => F (v ∘ Sum.inl) (v ∘ Sum.inr)) (0 : I → ℂ) y).symm
  simp_rw [hi]
  simp only [div_eq_mul_inv]
  simp_rw [mul_comm _ (weight h : ℂ)⁻¹]
  rw [coordinateJet_const_mul]
  dsimp only
  ring

private theorem externalPair_product (h : I →₀ ℕ) (k : J →₀ ℕ)
    (f : (I → ℂ) → ℂ) (g : (J → ℂ) → ℂ) (c : ℂ) :
    externalPairCoefficient h k (fun x y => c * f x * g y) =
      c * externalCoefficient h f * externalCoefficient k g := by
  simp only [externalPairCoefficient, externalCoefficient_mul_const,
    externalCoefficient_const_mul]

theorem externalPair_affine (C : Matrix (I ⊕ J) (I ⊕ J) ℂ) (m : I ⊕ J → ℂ)
    (hs : ∀ i j, C i j = C j i) (h : I →₀ ℕ) (k : J →₀ ℕ) (c : ℂ) :
    externalPairCoefficient h k (fun x y => c * Complex.exp (eval (Sum.elim x y) (affineExponent C m))) =
      c * OriginalChargedRowSource.affineCoefficient C m (h.sumElim k) := by
  have he (y : J → ℂ) : externalCoefficient h
      (fun x => c * Complex.exp (eval (Sum.elim x y) (affineExponent C m))) =
      c * (Complex.exp (externalExponent C m y) *
        OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m y) h) := by
    simp only [affineExponent_split C m hs, Complex.exp_add, ← mul_assoc]
    rw [externalCoefficient_const_mul,
      native_affine_external_coefficient (C.submatrix Sum.inl Sum.inl) (mixedMean C m y)
        (fun i j => hs (.inl i) (.inl j)) h h.degree le_rfl]
  simp only [externalPairCoefficient, he, externalCoefficient_const_mul,
    native_mixed_external_coefficient C m hs]

/-- Uniform normal bounds survive fixed ordinary extraction in both external
families. The parameter family has no topology and no common source radius
is inferred from this result. -/
theorem externalPair_normal_family {K T : Type*}
    (F : K → T → (I → ℂ) → (J → ℂ) → ℂ)
    (M : K → ℝ) (hM : Summable M) (R : ℝ) (hR : 0 < R)
    (hf : ∀ k v, ContDiff ℂ (⊤ : ℕ∞ω)
      (fun x : (I ⊕ J) → ℂ => F k v (x ∘ Sum.inl) (x ∘ Sum.inr)))
    (hb : ∀ k v x, ‖x‖ < R → ‖F k v (x ∘ Sum.inl) (x ∘ Sum.inr)‖ ≤ M k)
    (h : I →₀ ℕ) (k : J →₀ ℕ) :
    ∃ B : K → ℝ, Summable B ∧
      (∀ v d, ‖externalPairCoefficient h k (F d v)‖ ≤ B d) ∧
      ∀ v, HasSum (fun d => externalPairCoefficient h k (F d v))
        (externalPairCoefficient h k (fun x y => ∑' d, F d v x y)) := by
  let G := fun d v (x : (I ⊕ J) → ℂ) => F d v (x ∘ Sum.inl) (x ∘ Sum.inr)
  have hd d v l i x : Differentiable ℂ
      (fun t => coordinateJet l (G d v) (Function.update x i t)) := by
    apply ((coordinateJet_contDiff _ (hf d v) l).differentiable (by simp)).comp
    apply differentiable_pi.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simpa using differentiable_id
    · simpa [Function.update_of_ne hj] using differentiable_const (x j)
  obtain ⟨r, hr, B, hB, hb', he⟩ := coordinateJet_normal_family G M hM R hR hd hb
    ((occupationWord h).map Sum.inl ++ (occupationWord k).map Sum.inr)
  refine ⟨fun d => B d / ‖(weight h : ℂ) * (weight k : ℂ)‖, hB.div_const _, ?_, ?_⟩
  · intro v d
    rw [externalPairCoefficient_jet, norm_div]
    exact div_le_div_of_nonneg_right (hb' d v 0 (by simpa using hr)) (norm_nonneg _)
  · intro v
    simpa only [externalPairCoefficient_jet] using
      (he v 0 (by simpa using hr)).div_const ((weight h : ℂ) * (weight k : ℂ))

/-- Equality on an actual external neighborhood preserves both finite
ordinary coefficient extractions, including empty occupations. -/
theorem externalPair_congr_ball (h : I →₀ ℕ) (k : J →₀ ℕ)
    (F G : (I → ℂ) → (J → ℂ) → ℂ) {R : ℝ} (hR : 0 < R)
    (he : ∀ v : (I ⊕ J) → ℂ, ‖v‖ < R →
      F (v ∘ Sum.inl) (v ∘ Sum.inr) = G (v ∘ Sum.inl) (v ∘ Sum.inr)) :
    externalPairCoefficient h k F = externalPairCoefficient h k G := by
  simp only [externalPairCoefficient_jet]
  congr 1
  exact coordinateJet_congrOn _
    (U := {v : (I ⊕ J) → ℂ | ‖v‖ < R})
    (isOpen_lt continuous_norm continuous_const)
    (fun v hv => he v hv) (by simpa using hR)

/-- Finite ordinary extraction of the two mixed affine rows keeps exactly
one internal factorial and the full two row occupations. -/
theorem externalPair_mixed {H : Type*} [Fintype H] [DecidableEq H]
    (C : Matrix (H ⊕ I) (H ⊕ I) ℂ) (E : Matrix (H ⊕ J) (H ⊕ J) ℂ)
    (m : H ⊕ I → ℂ) (l : H ⊕ J → ℂ)
    (hs : ∀ i j, C i j = C j i) (ht : ∀ i j, E i j = E j i)
    (d : H →₀ ℕ) (h : I →₀ ℕ) (k : J →₀ ℕ) :
    externalPairCoefficient h k (fun x y =>
      Complex.exp (externalExponent C m x + externalExponent E l y) *
      (weight d : ℂ) *
      OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
        (mixedMean C m x) d *
      OriginalChargedRowSource.affineCoefficient (E.submatrix Sum.inl Sum.inl)
        (mixedMean E l y) d) =
      (weight d : ℂ) * OriginalChargedRowSource.affineCoefficient C m (d.sumElim h) *
        OriginalChargedRowSource.affineCoefficient E l (d.sumElim k) := by
  have he : (fun x y =>
      Complex.exp (externalExponent C m x + externalExponent E l y) *
      (weight d : ℂ) *
      OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
        (mixedMean C m x) d *
      OriginalChargedRowSource.affineCoefficient (E.submatrix Sum.inl Sum.inl)
        (mixedMean E l y) d) =
      (fun x y => (weight d : ℂ) *
        (Complex.exp (externalExponent C m x) *
          OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
            (mixedMean C m x) d) *
        (Complex.exp (externalExponent E l y) *
          OriginalChargedRowSource.affineCoefficient (E.submatrix Sum.inl Sum.inl)
            (mixedMean E l y) d)) := by
    funext x y
    rw [Complex.exp_add]
    ring
  rw [he, externalPair_product, native_mixed_external_coefficient C m hs,
    native_mixed_external_coefficient E l ht]

set_option backward.isDefEq.respectTransparency false

/-- The actual mixed affine occupation term is entire in its external
coordinates. Matrix and mean entries are fixed in this assertion. -/
theorem mixed_external_contDiff {H : Type*} [Fintype H] [DecidableEq H]
    (C : Matrix (H ⊕ I) (H ⊕ I) ℂ) (E : Matrix (H ⊕ J) (H ⊕ J) ℂ)
    (m : H ⊕ I → ℂ) (l : H ⊕ J → ℂ) (d : H →₀ ℕ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fun v : (I ⊕ J) → ℂ =>
      Complex.exp (externalExponent C m (v ∘ Sum.inl) +
        externalExponent E l (v ∘ Sum.inr)) * (weight d : ℂ) *
      OriginalChargedRowSource.affineCoefficient (C.submatrix Sum.inl Sum.inl)
        (mixedMean C m (v ∘ Sum.inl)) d *
      OriginalChargedRowSource.affineCoefficient (E.submatrix Sum.inl Sum.inl)
        (mixedMean E l (v ∘ Sum.inr)) d) := by
  have hv (i : I ⊕ J) : ContDiff ℂ (⊤ : ℕ∞ω) (fun v : (I ⊕ J) → ℂ => v i) :=
    contDiff_apply ℂ (fun _ : I ⊕ J => ℂ) i
  have hexL : ContDiff ℂ (⊤ : ℕ∞ω) (fun v : (I ⊕ J) → ℂ =>
      externalExponent C m (v ∘ Sum.inl)) := by
    unfold externalExponent
    apply ContDiff.add
    · apply ContDiff.mul contDiff_const
      apply ContDiff.sum
      intro i hi
      apply ContDiff.sum
      intro j hj
      exact (contDiff_const.mul (hv (.inl i))).mul (hv (.inl j))
    · apply ContDiff.sum
      intro i hi
      exact contDiff_const.mul (hv (.inl i))
  have hexR : ContDiff ℂ (⊤ : ℕ∞ω) (fun v : (I ⊕ J) → ℂ =>
      externalExponent E l (v ∘ Sum.inr)) := by
    unfold externalExponent
    apply ContDiff.add
    · apply ContDiff.mul contDiff_const
      apply ContDiff.sum
      intro i hi
      apply ContDiff.sum
      intro j hj
      exact (contDiff_const.mul (hv (.inr i))).mul (hv (.inr j))
    · apply ContDiff.sum
      intro i hi
      exact contDiff_const.mul (hv (.inr i))
  have hc := (hexL.add hexR).cexp
  have hm : ∀ i, ContDiff ℂ (⊤ : ℕ∞ω)
      (fun v : (I ⊕ J) → ℂ => mixedMean C m (v ∘ Sum.inl) i) := by
    intro i
    unfold mixedMean
    apply ContDiff.add contDiff_const
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (hv (.inl j))
  have hl : ∀ i, ContDiff ℂ (⊤ : ℕ∞ω)
      (fun v : (I ⊕ J) → ℂ => mixedMean E l (v ∘ Sum.inr) i) := by
    intro i
    unfold mixedMean
    apply ContDiff.add contDiff_const
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (hv (.inr j))
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact hc.mul contDiff_const
    · exact affineCoefficient_contDiff
        (fun _ : (I ⊕ J) → ℂ => C.submatrix Sum.inl Sum.inl)
        (fun v => mixedMean C m (v ∘ Sum.inl))
        (fun _ _ => contDiff_const) hm d
  · exact affineCoefficient_contDiff
      (fun _ : (I ⊕ J) → ℂ => E.submatrix Sum.inl Sum.inl)
      (fun v => mixedMean E l (v ∘ Sum.inr))
      (fun _ _ => contDiff_const) hl d

end ExternalJets

end D5.S3.VertexAlgebra.TwistedGround.NativeAffineExternalCoefficient

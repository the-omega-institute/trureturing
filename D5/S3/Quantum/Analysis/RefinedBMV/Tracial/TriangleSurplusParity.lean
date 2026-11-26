/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusParity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Soundness of parity-separated packed sign checks on the shifted spectral quadrant. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusExpansion
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusPacking
import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Batteries.Tactic.OpenPrivate

/-! The parity-polynomial coefficients are the original bivariate coefficients
with the exponents encoded in a mixed radix. -/

namespace RefinedBMV.Tracial.TriangleSurplus

open Polynomial DimThree.PackedCheck
open RefinedBMV.DividedDifference.SparseExpansion
open private packed_repunit from D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate

private def digit (t : Term) : ℕ := t.exponents.x / 2 + 409 * t.exponents.y

private def parity (t : Term) : ℕ := t.exponents.x % 2

private noncomputable def parityPoly (r : ℕ) (ts : List Term) : Polynomial ℤ :=
  (ts.map fun t => if parity t = r then monomial (digit t) t.coefficient else 0).sum

private theorem parityPoly_bound (r i : ℕ) (ts : List Term) :
    |(parityPoly r ts).coeff i| ≤ coeffMass ts := by
  induction ts with
  | nil => simp [parityPoly, coeffMass]
  | cons t ts ih =>
    change |((if parity t = r then monomial (digit t) t.coefficient else 0) +
      parityPoly r ts).coeff i| ≤ |t.coefficient| + coeffMass ts
    rw [coeff_add]
    apply (abs_add_le _ _).trans (add_le_add ?_ ih)
    split
    · rw [coeff_monomial]
      split <;> simp
    · simp

private theorem parityPoly_degree (r : ℕ) (ts : List Term)
    (h : ∀ t ∈ ts, t.exponents.x ≤ 816 ∧ t.exponents.y ≤ 918) :
    (parityPoly r ts).natDegree < 409 * 919 := by
  suffices (parityPoly r ts).natDegree ≤ 375870 by omega
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  induction ts with
  | nil => simp [parityPoly]
  | cons t ts ih =>
    have ht := h t List.mem_cons_self
    have hk : digit t < 409 * 919 := by unfold digit; omega
    change ((if parity t = r then monomial (digit t) t.coefficient else 0) +
      parityPoly r ts).coeff i = 0
    rw [coeff_add, ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    split
    · simp [coeff_monomial, show digit t ≠ i by omega]
    · simp

private def decodedPower (r i : ℕ) (u v : ℝ) : ℝ :=
  u ^ (2 * (i % 409) + r) * v ^ (i / 409)

private theorem decodedPower_digit (t : Term) (hx : t.exponents.x ≤ 816)
    (u v : ℝ) :
    decodedPower (parity t) (digit t) u v = u ^ t.exponents.x * v ^ t.exponents.y := by
  have hx' : t.exponents.x / 2 < 409 := by omega
  have hm : digit t % 409 = t.exponents.x / 2 := by
    simp [digit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
  have hd : digit t / 409 = t.exponents.y := by
    rw [digit, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hx', zero_add]
  unfold decodedPower parity
  rw [hm, hd, show 2 * (t.exponents.x / 2) + t.exponents.x % 2 = t.exponents.x by omega]

private noncomputable def readPoly (p : Polynomial ℤ) (r : ℕ) (u v : ℝ) : ℝ :=
  p.sum (fun i c => (c : ℝ) * decodedPower r i u v)

private theorem readPoly_add (p q : Polynomial ℤ) (r : ℕ) (u v : ℝ) :
    readPoly (p + q) r u v = readPoly p r u v + readPoly q r u v := by
  exact sum_add_index _ _ _ (by simp) (by simp [add_mul])

private theorem readPoly_monomial (n : ℕ) (c : ℤ) (r : ℕ) (u v : ℝ) :
    readPoly (monomial n c) r u v = (c : ℝ) * decodedPower r n u v :=
  sum_monomial_index _ _ (by simp)

@[simp] private theorem readPoly_zero (r : ℕ) (u v : ℝ) :
    readPoly 0 r u v = 0 := by simp [readPoly]

private theorem eval_split (ts : List Term) (u v : ℝ)
    (hx : ∀ t ∈ ts, t.exponents.x ≤ 816) :
    evalTerms (1 : ℝ) u v 1 1 ts =
      readPoly (parityPoly 0 ts) 0 u v + readPoly (parityPoly 1 ts) 1 u v := by
  induction ts with
  | nil => simp [evalTerms, parityPoly, readPoly]
  | cons t ts ih =>
    have he := decodedPower_digit t (hx t List.mem_cons_self) u v
    have htail := ih (fun u hu => hx u (List.mem_cons_of_mem _ hu))
    have hp : parity t = 0 ∨ parity t = 1 := by unfold parity; omega
    simp only [evalTerms, List.map_cons, List.sum_cons] at htail ⊢
    rw [htail]
    rcases hp with h | h <;>
      simp [parityPoly, h, readPoly_add, readPoly_monomial,
        h ▸ he, Term.eval, add_assoc, add_left_comm]

private theorem readPoly_pos (p : Polynomial ℤ) (r : ℕ) (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v) (h : ∀ i, 0 ≤ p.coeff i) (hne : p ≠ 0) :
    0 < readPoly p r u v := by
  classical
  simp only [readPoly, Polynomial.sum_def]
  apply Finset.sum_pos'
    (fun i _ => mul_nonneg (Int.cast_nonneg (h i)) (by unfold decodedPower; positivity))
  have hi := Polynomial.natDegree_mem_support_of_nonzero hne
  have hc : 0 < p.coeff p.natDegree := lt_of_le_of_ne' (h _) (mem_support_iff.mp hi)
  exact ⟨_, hi, mul_pos (Int.cast_pos.mpr hc) (by unfold decodedPower; positivity)⟩

noncomputable def packedPolynomial (e : Fin 3) (r : ℕ) : Polynomial ℤ :=
  parityPoly r (select e expansion).terms

private theorem pos_of_parity_checks (e : Fin 3) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (h : ∀ r : Fin 2,
      let p := packedPolynomial e r
      let m := polynomialMask 1983 (409 * 919)
      ((p.eval (2 ^ 1984) + ↑m).toNat &&& m = m) ∧ p.eval (2 ^ 1984) ≠ 0) :
    0 < select e (surplus (1 + u) (1 + v)) := by
  rw [← eval_selected_expansion]
  change 0 < evalTerms (1 : ℝ) u v 1 1 (select e expansion).terms
  rw [eval_split _ _ _ (fun t ht => (expansion_term_bounds e t ht).1)]
  have hcoeff (r : Fin 2) (i : ℕ) : 0 ≤ (packedPolynomial e r).coeff i := by
    apply coeff_nonneg_of_polynomial_mask (packedPolynomial e r)
      (parityPoly_degree _ _ (expansion_term_bounds e))
    · intro j
      have hj := (parityPoly_bound r j (select e expansion).terms).trans_lt (expansion_mass e)
      change |(packedPolynomial e r).coeff j| < (2 : ℤ) ^ 1983 at hj
      exact ⟨(abs_lt.mp hj).1.le, (abs_lt.mp hj).2⟩
    · exact (h r).1
  have hne (r : Fin 2) : packedPolynomial e r ≠ 0 := by
    intro hz
    exact (h r).2 (by rw [hz, eval_zero])
  exact add_pos
    (readPoly_pos _ _ _ _ hu hv (hcoeff 0) (hne 0))
    (readPoly_pos _ _ _ _ hu hv (hcoeff 1) (hne 1))

private theorem sqrt_pow (B : ℤ) (n : ℕ) :
    (Zsqrtd.sqrtd (d := B)) ^ n =
      if n % 2 = 0 then ⟨B ^ (n / 2), 0⟩ else ⟨0, B ^ (n / 2)⟩ := by
  calc
    _ = ((Zsqrtd.sqrtd (d := B)) ^ 2) ^ (n / 2) * Zsqrtd.sqrtd ^ (n % 2) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ = _ := by
      rw [pow_two, Zsqrtd.dmuld, ← Int.cast_pow]
      have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h with h | h <;> ext <;> simp [h, -Int.cast_pow]

private theorem packed_term (B : ℤ) (t : Term) :
    t.eval (1 : Zsqrtd B) Zsqrtd.sqrtd (↑(B ^ (409 : ℕ)) : Zsqrtd B) 1 1 =
      if parity t = 0 then ⟨t.coefficient * B ^ digit t, 0⟩
      else ⟨0, t.coefficient * B ^ digit t⟩ := by
  simp only [Term.eval, one_pow, one_mul, mul_one, sqrt_pow]
  have hy : ((↑(B ^ (409 : ℕ)) : Zsqrtd B) ^ t.exponents.y) =
      ↑(B ^ (409 * t.exponents.y)) := by rw [← Int.cast_pow, ← pow_mul]
  rw [hy]
  have hb : B ^ digit t = B ^ (t.exponents.x / 2) * B ^ (409 * t.exponents.y) := by
    rw [digit, pow_add]
  by_cases h : parity t = 0
  · have h' : t.exponents.x % 2 = 0 := h
    simp only [h, h', hb, ite_true]
    ext <;> simp [-Int.cast_pow]
  · have h' : t.exponents.x % 2 ≠ 0 := h
    simp only [h, h', hb, ite_false]
    ext <;> simp [-Int.cast_pow]

private theorem coeff_part_eval (B : ℤ) (r : Fin 2) (ts : List Term) :
    (parityPoly r ts).eval B =
      let z := evalTerms (1 : Zsqrtd B) Zsqrtd.sqrtd (↑(B ^ (409 : ℕ)) : Zsqrtd B) 1 1 ts
      if r.val = 0 then z.re else z.im := by
  induction ts with
  | nil => fin_cases r <;> simp [parityPoly, evalTerms, Zsqrtd.re_zero, Zsqrtd.im_zero]
  | cons t ts ih =>
    have hp : parity t = 0 ∨ parity t = 1 := by unfold parity; omega
    unfold parityPoly at ⊢
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, evalTerms]
    let t' := t.eval (1 : Zsqrtd B) Zsqrtd.sqrtd (↑(B ^ (409 : ℕ)) : Zsqrtd B) 1 1
    let ts' := evalTerms (1 : Zsqrtd B) Zsqrtd.sqrtd (↑(B ^ (409 : ℕ)) : Zsqrtd B) 1 1 ts
    change _ = if r.val = 0 then (t' + ts').re else (t' + ts').im
    dsimp only [t']
    rw [packed_term]
    change (if parity t = (r : ℕ) then monomial (digit t) t.coefficient else 0).eval B +
      (parityPoly r ts).eval B = _
    rw [ih]
    fin_cases r <;> rcases hp with h | h <;>
      simp [h, eval_monomial, ts']

private theorem fastMask_eq (w n : Nat) :
    fastMask (w + 1) n = polynomialMask w n := by
  let B := 2 ^ (w + 1)
  have hB : 0 < B := Nat.two_pow_pos _
  have hdiv : 0 < B - 1 := by
    dsimp [B]
    rw [pow_succ]
    have h := Nat.two_pow_pos w
    omega
  have hgeom : (B - 1) ∣ B ^ n - 1 := by
    refine ⟨packDigits B (List.replicate n 1), ?_⟩
    simpa only [Nat.one_mul, mul_comm (B - 1)] using (packed_repunit n B 1 hB).symm
  unfold fastMask polynomialMask
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.shiftLeft_eq, Nat.add_sub_cancel, pow_mul]
  change (B ^ n - 1) / (B - 1) * 2 ^ w = packDigits B (List.replicate n (2 ^ w))
  rw [mul_comm, ← Nat.mul_div_assoc _ hgeom, ← packed_repunit n B (2 ^ w) hB,
    Nat.mul_div_cancel _ hdiv]

private theorem polynomial_eval_eq (w : Nat) (e : Fin 3) (r : Fin 2) :
    (packedPolynomial e r).eval ↑((1 : Nat) <<< w) =
      let s := select e (packedSurplus w)
      if r.val = 0 then s.re else s.im := by
  unfold packedPolynomial
  rw [coeff_part_eval]
  change (if r.val = 0 then
    (evalExpansion Zsqrtd.sqrtd _ (select e expansion)).re
    else (evalExpansion Zsqrtd.sqrtd _ (select e expansion)).im) = _
  rw [eval_selected_expansion]
  unfold packedSurplus
  have hX : (1 : Zsqrtd (↑((1 : Nat) <<< w) : ℤ)) + Zsqrtd.sqrtd = ⟨1, 1⟩ := by
    rfl
  have hY : (1 : Zsqrtd (↑((1 : Nat) <<< w) : ℤ)) +
      (↑((↑((1 : Nat) <<< w) : ℤ) ^ (409 : ℕ)) :
        Zsqrtd (↑((1 : Nat) <<< w) : ℤ)) = ⟨1 + ↑((1 : Nat) <<< (w * 409)), 0⟩ := by
    have hs : (↑((1 : Nat) <<< (w * 409)) : ℤ) =
        (↑((1 : Nat) <<< w) : ℤ) ^ (409 : ℕ) := by
      simp only [Nat.one_shiftLeft, pow_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hs, ← Zsqrtd.intCast_val, ← Int.cast_one, ← Int.cast_add]
  rw [hX, hY]

private theorem check_sound (w : Nat) (e : Fin 3) (r : Fin 2)
    (h : packedCheck w e.val (r.val != 0) = true) :
    let v := (packedPolynomial e r).eval ↑((1 : Nat) <<< w)
    let m := fastMask w (409 * 919)
    ((v + ↑m).toNat &&& m = m) ∧ v ≠ 0 := by
  rw [polynomial_eval_eq]
  fin_cases r <;>
    simpa only [packedCheck, select, Fin.reduceFinMk, Nat.reduceEqDiff, ite_true, ite_false,
      Bool.false_eq_true, Bool.true_eq_false, Bool.and_eq_true_iff, beq_iff_eq, bne_iff_ne,
      Bool.not_false, Bool.not_true, bne_self_eq_false, beq_self_eq_true, ne_eq,
      Nat.one_ne_zero, not_false_eq_true] using h

/-- A sign check with a nonzero encoded component for each parity gives strict
surplus positivity throughout the open shifted quadrant. -/
theorem pos_of_packedChecks (e : Fin 3) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (heven : packedCheck 1984 e.val false = true)
    (hodd : packedCheck 1984 e.val true = true) :
    0 < select e (surplus (1 + u) (1 + v)) := by
  apply pos_of_parity_checks e u v hu hv
  intro r
  have h (r : Fin 2) : packedCheck 1984 e.val (r.val != 0) = true := by
    fin_cases r
    · exact heven
    · exact hodd
  simpa only [Nat.one_shiftLeft, Nat.cast_pow, Nat.cast_ofNat, fastMask_eq 1983]
    using check_sound 1984 e r (h r)

#print axioms pos_of_packedChecks

end RefinedBMV.Tracial.TriangleSurplus

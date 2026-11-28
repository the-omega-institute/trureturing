/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPackedPolynomial
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact packed comparison of polynomial witnesses for the compact BMV certificate. -/

import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Int.Bitwise

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate

/-! Packed integer multiplication checks for sparse polynomial witnesses. -/

open scoped BigOperators

namespace RefinedBMV

private theorem coeff_eq_zero_of_sum_range_eq_zero {base : Int} (hbase : 0 < base)
    {n : Nat} {coeff : Nat → Int} (hcoeff : ∀ i < n, |coeff i| < base)
    (hsum : (∑ i ∈ Finset.range n, coeff i * base ^ i) = 0) :
    ∀ i < n, coeff i = 0 := by
  induction n generalizing coeff with
  | zero =>
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  | succ n ih =>
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_succ, ← mul_assoc, pow_zero, mul_one] at hsum
    rw [← Finset.sum_mul] at hsum
    have hmod : coeff 0 % base = 0 := by
      simpa only [Int.mul_add_emod_self_right, Int.zero_emod] using
        congrArg (fun z : Int => z % base) hsum
    have hhead : coeff 0 = 0 :=
      Int.eq_zero_of_abs_lt_dvd (Int.dvd_of_emod_eq_zero hmod) (hcoeff 0 (Nat.zero_lt_succ n))
    rw [hhead, add_zero] at hsum
    have htail : (∑ i ∈ Finset.range n, coeff (i + 1) * base ^ i) = 0 :=
      (mul_eq_zero.mp hsum).resolve_right hbase.ne'
    intro i hi
    cases i with
    | zero => exact hhead
    | succ i =>
      exact ih (fun j hj => hcoeff (j + 1) (Nat.succ_lt_succ hj)) htail i
        (Nat.lt_of_succ_lt_succ hi)

/-- A positive-base evaluation determines an integer polynomial among candidates whose
coefficient differences are strictly smaller in absolute value than the base. -/
theorem eq_of_eval_eq_of_coeff_sub_abs_lt {P Q : Polynomial Int} {n : Nat} {base : Int}
    (hbase : 0 < base) (hP : P.natDegree < n) (hQ : Q.natDegree < n)
    (hcoeff : ∀ i < n, |(P - Q).coeff i| < base)
    (heval : P.eval base = Q.eval base) : P = Q := by
  have hdegree : (P - Q).natDegree < n :=
    (Polynomial.natDegree_sub_le P Q).trans_lt (max_lt_iff.mpr ⟨hP, hQ⟩)
  have hsum : (∑ i ∈ Finset.range n, (P - Q).coeff i * base ^ i) = 0 := by
    rw [← Polynomial.eval_eq_sum_range' hdegree base, Polynomial.eval_sub, heval, sub_self]
  apply sub_eq_zero.mp
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < n
  · exact coeff_eq_zero_of_sum_range_eq_zero hbase hcoeff hsum i hi
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hi))

end RefinedBMV

namespace RefinedBMV.DimThree.Certificate

def packedIndex (width : ℕ) (a : Term) : ℕ :=
  a.exponents.1 + width * a.exponents.2.1 + width ^ 2 * a.exponents.2.2

private noncomputable def packedPolynomial (width : ℕ) (xs : List Term) : Polynomial ℤ :=
  (xs.map fun a ↦ Polynomial.monomial (packedIndex width a) a.coefficient).sum

private theorem packed_eval (width : ℕ) (b : ℤ) (xs : List Term) :
    (packedPolynomial width xs).eval b = evalTerms b (b ^ width) (b ^ width ^ 2) xs := by
  induction xs with
  | nil => simp [packedPolynomial, evalTerms]
  | cons a xs ih =>
    change (Polynomial.monomial (packedIndex width a) a.coefficient +
      packedPolynomial width xs).eval b = a.eval b (b ^ width) (b ^ width ^ 2) +
        evalTerms b (b ^ width) (b ^ width ^ 2) xs
    rw [Polynomial.eval_add, Polynomial.eval_monomial, ih]
    simp only [Term.eval, packedIndex, pow_add, pow_mul, Int.cast_id]
    ring

def termMass (xs : List Term) : ℕ :=
  (xs.map fun a ↦ a.coefficient.natAbs).sum

private theorem coefficient_abs_le_mass (width : ℕ) (xs : List Term) (i : ℕ) :
    |(packedPolynomial width xs).coeff i| ≤ (termMass xs : ℤ) := by
  induction xs with
  | nil => simp [packedPolynomial, termMass]
  | cons a xs ih =>
    change |(Polynomial.monomial (packedIndex width a) a.coefficient +
      packedPolynomial width xs).coeff i| ≤ ((a.coefficient.natAbs + termMass xs : ℕ) : ℤ)
    rw [Polynomial.coeff_add, Nat.cast_add]
    refine (abs_add_le ..).trans (add_le_add ?_ ih)
    simp only [Polynomial.coeff_monomial]
    split
    · exact Int.natCast_natAbs _ ▸ le_rfl
    · simp

private theorem degree_lt_of_packed_indices {width bound : ℕ} {xs : List Term}
    (hb : 0 < bound) (hxs : ∀ a ∈ xs, packedIndex width a < bound) :
    (packedPolynomial width xs).natDegree < bound := by
  induction xs with
  | nil => simpa [packedPolynomial] using hb
  | cons a xs ih =>
    change (Polynomial.monomial (packedIndex width a) a.coefficient +
      packedPolynomial width xs).natDegree < bound
    apply (Polynomial.natDegree_add_le _ _).trans_lt
    exact max_lt ((Polynomial.natDegree_monomial_le a.coefficient).trans_lt (hxs a (by simp)))
      (ih fun b hb ↦ hxs b (by simp [hb]))

private theorem decode_index (width : ℕ) (a : Term)
    (h₁ : a.exponents.1 < width) (h₂ : a.exponents.2.1 < width) :
    let i := packedIndex width a
    (i % width, i / width % width, i / width / width) = a.exponents := by
  obtain ⟨⟨ex, ey, ez⟩, c⟩ := a
  change ex < width at h₁
  change ey < width at h₂
  dsimp only
  have hw := Nat.zero_lt_of_lt h₁
  have he : packedIndex width ⟨(ex, ey, ez), c⟩ = ex + width * (ey + width * ez) := by
    change ex + width * ey + width ^ 2 * ez = _
    ring
  rw [he]
  change ((ex + width * (ey + width * ez)) % width,
    (ex + width * (ey + width * ez)) / width % width,
    (ex + width * (ey + width * ez)) / width / width) = (ex, ey, ez)
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂,
    Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt h₁, Nat.div_eq_of_lt h₂, zero_add]

private theorem decoded_eval {width bound : ℕ} (s t u : ℝ) {xs : List Term}
    (h₁ : ∀ a ∈ xs, a.exponents.1 < width) (h₂ : ∀ a ∈ xs, a.exponents.2.1 < width)
    (hkey : ∀ a ∈ xs, packedIndex width a < bound) :
    (∑ i ∈ Finset.range bound, ((packedPolynomial width xs).coeff i : ℝ) *
      s ^ (i % width) * t ^ (i / width % width) * u ^ (i / width / width)) =
      evalTerms s t u xs := by
  induction xs with
  | nil => simp [packedPolynomial, evalTerms]
  | cons a xs ih =>
    have hk := hkey a (by simp)
    have hdec := decode_index width a (h₁ a (by simp)) (h₂ a (by simp))
    change (∑ i ∈ Finset.range bound,
      (((Polynomial.monomial (packedIndex width a) a.coefficient +
        packedPolynomial width xs).coeff i : ℤ) : ℝ) *
        s ^ (i % width) * t ^ (i / width % width) * u ^ (i / width / width)) =
      a.eval s t u + evalTerms s t u xs
    simp only [Polynomial.coeff_add, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [ih (fun a ha ↦ h₁ a (by simp [ha])) (fun a ha ↦ h₂ a (by simp [ha]))
      (fun a ha ↦ hkey a (by simp [ha]))]
    congr 1
    rw [Finset.sum_eq_single_of_mem (packedIndex width a) (Finset.mem_range.mpr hk)]
    · simp only [Polynomial.coeff_monomial, ite_true, Term.eval]
      simpa only using congrArg (fun i : ℕ × ℕ × ℕ ↦
        (a.coefficient : ℝ) * s ^ i.1 * t ^ i.2.1 * u ^ i.2.2) hdec
    · intro i _ hi
      simp [Polynomial.coeff_monomial, hi, Ne.symm hi]

/-- Equality at a sufficiently large integer encoding implies equality as real functions. -/
theorem evalTerms_eq_of_packed {width bound : ℕ} {base : ℤ} {xs ys : List Term}
    (hbase : 0 < base) (hbound : 0 < bound)
    (hkeyX : ∀ a ∈ xs, packedIndex width a < bound)
    (hkeyY : ∀ a ∈ ys, packedIndex width a < bound)
    (hx₁ : ∀ a ∈ xs, a.exponents.1 < width) (hx₂ : ∀ a ∈ xs, a.exponents.2.1 < width)
    (hy₁ : ∀ a ∈ ys, a.exponents.1 < width) (hy₂ : ∀ a ∈ ys, a.exponents.2.1 < width)
    (hmass : ((termMass xs + termMass ys : ℕ) : ℤ) < base)
    (heval : evalTerms base (base ^ width) (base ^ (width ^ 2)) xs =
      evalTerms base (base ^ width) (base ^ (width ^ 2)) ys)
    (s t u : ℝ) : evalTerms s t u xs = evalTerms s t u ys := by
  have heq : packedPolynomial width xs = packedPolynomial width ys := by
    refine eq_of_eval_eq_of_coeff_sub_abs_lt hbase (degree_lt_of_packed_indices hbound hkeyX)
      (degree_lt_of_packed_indices hbound hkeyY) (fun i _ ↦ ?_) ?_
    · rw [Polynomial.coeff_sub]
      apply lt_of_le_of_lt (abs_sub _ _) _
      exact (add_le_add (coefficient_abs_le_mass _ _ _) (coefficient_abs_le_mass _ _ _)).trans_lt
        (by simpa only [Nat.cast_add] using hmass)
    · simpa only [packed_eval] using heval
  rw [← decoded_eval s t u hx₁ hx₂ hkeyX, ← decoded_eval s t u hy₁ hy₂ hkeyY, heq]

private def productTerms (xs ys : List Term) : List Term :=
  xs.flatMap fun a ↦ ys.map (Term.mul a)

private theorem eval_productTerms {R : Type*} [CommRing R] (s t u : R) (xs ys : List Term) :
    evalTerms s t u (productTerms xs ys) = evalTerms s t u xs * evalTerms s t u ys := by
  have hmap (a : Term) :
      evalTerms s t u (ys.map (Term.mul a)) = a.eval s t u * evalTerms s t u ys := by
    induction ys with
    | nil => simp [evalTerms]
    | cons b ys ih =>
      simp only [evalTerms, List.map_cons, List.sum_cons] at *
      rw [ih, mul_add]
      congr 1
      simp only [Term.eval, Term.mul, Int.cast_mul, pow_add]
      ring
  induction xs with
  | nil => simp [productTerms, evalTerms]
  | cons a xs ih =>
    change evalTerms s t u (ys.map (Term.mul a) ++ productTerms xs ys) =
      (a.eval s t u + evalTerms s t u xs) * evalTerms s t u ys
    rw [show ∀ xs ys : List Term, evalTerms s t u (xs ++ ys) =
      evalTerms s t u xs + evalTerms s t u ys by simp [evalTerms]]
    rw [hmap, ih, add_mul]

private theorem productTerms_mass (xs ys : List Term) :
    termMass (productTerms xs ys) = termMass xs * termMass ys := by
  have hmap (a : Term) :
      termMass (ys.map (Term.mul a)) = a.coefficient.natAbs * termMass ys := by
    induction ys with
    | nil => simp [termMass]
    | cons b ys ih =>
      simp only [termMass, List.map_cons, List.sum_cons] at *
      rw [ih, Nat.mul_add]
      simp [Term.mul, Int.natAbs_mul]
  induction xs with
  | nil => simp [productTerms, termMass]
  | cons a xs ih =>
    change termMass (ys.map (Term.mul a) ++ productTerms xs ys) =
      (a.coefficient.natAbs + termMass xs) * termMass ys
    rw [show ∀ xs ys : List Term, termMass (xs ++ ys) = termMass xs + termMass ys by
      simp [termMass]]
    rw [hmap, ih, Nat.add_mul]

/-- Bounds for each coordinate of a sparse polynomial's exponents. -/
def ExponentsLE (bounds : ℕ × ℕ × ℕ) (a : Term) : Prop :=
  a.exponents.1 ≤ bounds.1 ∧ a.exponents.2.1 ≤ bounds.2.1 ∧ a.exponents.2.2 ≤ bounds.2.2

instance (bounds : ℕ × ℕ × ℕ) (a : Term) : Decidable (ExponentsLE bounds a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Check an exact sparse product by comparing integer evaluations of its two factors and the
proposed result. The exponent and coefficient bounds use the factors directly. -/
theorem evalTerms_mul_eq_of_packed {width : ℕ} {base : ℤ} {xs ys zs : List Term}
    {l r z : ℕ × ℕ × ℕ} (hw : 0 < width) (hbase : 0 < base)
    (hx : ∀ a ∈ xs, ExponentsLE l a) (hy : ∀ a ∈ ys, ExponentsLE r a)
    (hz : ∀ a ∈ zs, ExponentsLE z a)
    (h₁ : l.1 + r.1 < width) (h₂ : l.2.1 + r.2.1 < width)
    (h₃ : l.2.2 + r.2.2 < width)
    (hz₁ : z.1 < width) (hz₂ : z.2.1 < width) (hz₃ : z.2.2 < width)
    (hmass : ((termMass xs * termMass ys + termMass zs : ℕ) : ℤ) < base)
    (heval : evalTerms base (base ^ width) (base ^ (width ^ 2)) xs *
      evalTerms base (base ^ width) (base ^ (width ^ 2)) ys =
        evalTerms base (base ^ width) (base ^ (width ^ 2)) zs)
    (s t u : ℝ) : evalTerms s t u xs * evalTerms s t u ys = evalTerms s t u zs := by
  have hp (a : Term) (ha : a ∈ productTerms xs ys) :
      ExponentsLE (l.1 + r.1, l.2.1 + r.2.1, l.2.2 + r.2.2) a := by
    obtain ⟨b, hb, h⟩ := List.mem_flatMap.mp ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    obtain ⟨hb₁, hb₂, hb₃⟩ := hx b hb
    obtain ⟨hc₁, hc₂, hc₃⟩ := hy c hc
    exact ⟨Nat.add_le_add hb₁ hc₁, Nat.add_le_add hb₂ hc₂, Nat.add_le_add hb₃ hc₃⟩
  have hkey (a : Term) (ha : a.exponents.1 < width) (hb : a.exponents.2.1 < width)
      (hc : a.exponents.2.2 < width) : packedIndex width a < width ^ 3 := by
    dsimp [packedIndex]
    have hb' : width * a.exponents.2.1 + width ≤ width ^ 2 := by
      rw [pow_two, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hb
    have hc' : width ^ 2 * a.exponents.2.2 + width ^ 2 ≤ width ^ 3 := by
      rw [show width ^ 3 = width ^ 2 * width by ring, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hc
    omega
  rw [← eval_productTerms]
  refine evalTerms_eq_of_packed hbase (pow_pos hw 3) ?_ ?_
    (fun a ha ↦ (hp a ha).1.trans_lt h₁) (fun a ha ↦ (hp a ha).2.1.trans_lt h₂)
    (fun a ha ↦ (hz a ha).1.trans_lt hz₁) (fun a ha ↦ (hz a ha).2.1.trans_lt hz₂) ?_ ?_ s t u
  · intro a ha
    exact hkey a ((hp a ha).1.trans_lt h₁) ((hp a ha).2.1.trans_lt h₂) ((hp a ha).2.2.trans_lt h₃)
  · intro a ha
    exact hkey a ((hz a ha).1.trans_lt hz₁) ((hz a ha).2.1.trans_lt hz₂) ((hz a ha).2.2.trans_lt hz₃)
  · simpa only [productTerms_mass] using hmass
  · simpa only [eval_productTerms] using heval

/-- Evaluate at a power-of-two base using integer shifts of individual coefficients. -/
def packTerms (width bits : ℕ) (xs : List Term) : ℤ :=
  xs.foldl (fun total a ↦ total + (a.coefficient <<< (bits * packedIndex width a))) 0

theorem packTerms_eq_eval (width bits : ℕ) (xs : List Term) :
    packTerms width bits xs = evalTerms ((2 : ℤ) ^ bits) ((2 ^ bits) ^ width)
      ((2 ^ bits) ^ (width ^ 2)) xs := by
  have h (a : Term) : (a.coefficient <<< (bits * packedIndex width a)) =
      a.eval ((2 : ℤ) ^ bits) ((2 ^ bits) ^ width) ((2 ^ bits) ^ (width ^ 2)) := by
    simp only [Int.shiftLeft_eq, Term.eval, Int.cast_id, packedIndex, ← pow_mul, Nat.mul_add,
      pow_add, mul_assoc]
  have hfold (ys : List Term) (initial : ℤ) :
      ys.foldl (fun total a ↦ total + (a.coefficient <<< (bits * packedIndex width a))) initial =
        initial + evalTerms ((2 : ℤ) ^ bits) ((2 ^ bits) ^ width) ((2 ^ bits) ^ (width ^ 2)) ys := by
    induction ys generalizing initial with
    | nil => simp [evalTerms]
    | cons a ys ih =>
      rw [List.foldl_cons, ih, h]
      simp only [evalTerms, List.map_cons, List.sum_cons, add_assoc]
  simpa only [packTerms, zero_add] using hfold xs 0

private def unpackProduct (width bits : ℕ) (packed : ℤ) : List Term := Id.run do
  let base : ℤ := 2 ^ bits
  let midpoint := base / 2
  -- Add a midpoint at every digit so coefficients of either sign can be read independently.
  let planeBits := bits * width ^ 2
  let offset := midpoint * (((1 : ℤ) <<< ((width - 1) * planeBits + bits)) - 1) / (base - 1)
  let biased := (packed + offset).toNat
  let digitMask := base.toNat - 1
  let planeMask := ((1 : ℕ) <<< planeBits) - 1
  -- Extract a plane once before reading its coefficients in the original term order.
  let planes := (List.range width).toArray.map fun z ↦ (biased >>> (z * planeBits)) &&& planeMask
  let mut terms := []
  for x in [:width] do
    for y in [:width - x] do
      for z in [:width - x - y] do
        let digit := (planes[z]! >>> (bits * (x + width * y))) &&& digitMask
        let coefficient := (digit : ℤ) - midpoint
        if coefficient != 0 then
          terms := ⟨(x, y, z), coefficient⟩ :: terms
  return terms.reverse

private def packedProductMatches (degree : ℕ) (xs ys zs : List Term) (mass bits : ℕ)
    (packed : ℤ) : Bool :=
  xs.all (fun a ↦ decide (ExponentsLE (degree, degree, degree) a)) &&
        ys.all (fun a ↦ decide (ExponentsLE (degree, degree, degree) a)) &&
        zs.all (fun a ↦ decide (ExponentsLE (2 * degree, 2 * degree, 2 * degree) a)) &&
        decide (((mass + termMass zs : ℕ) : ℤ) < (2 : ℤ) ^ bits) &&
        decide (packed = packTerms (2 * degree + 1) bits zs)

/-- Verify proposed exact coefficients without enumerating the product of two supports. -/
def checkPackedProduct (xs ys zs : List Term) : Bool :=
  let mass := termMass xs * termMass ys
  let bits := mass.log2 + 3
  packedProductMatches 12 xs ys zs mass bits (packTerms 25 bits xs * packTerms 25 bits ys)

private theorem eval_of_packedProductMatches (s t u : ℝ) {degree bits : ℕ}
    {xs ys zs : List Term}
    (hc : packedProductMatches degree xs ys zs (termMass xs * termMass ys) bits
      (packTerms (2 * degree + 1) bits xs * packTerms (2 * degree + 1) bits ys) = true) :
    evalTerms s t u zs = evalTerms s t u xs * evalTerms s t u ys := by
  unfold packedProductMatches at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hx, hy⟩, hz⟩, hmass⟩, hpacked⟩ := hc
  symm
  have hsum : degree + degree < 2 * degree + 1 := by omega
  have hdegree : 2 * degree < 2 * degree + 1 := Nat.lt_succ_self _
  refine evalTerms_mul_eq_of_packed (width := 2 * degree + 1) (base := (2 : ℤ) ^ bits)
    (l := (degree, degree, degree)) (r := (degree, degree, degree))
    (z := (2 * degree, 2 * degree, 2 * degree)) (by omega) (by positivity)
    (fun a ha ↦ of_decide_eq_true (List.all_eq_true.mp hx a ha))
    (fun a ha ↦ of_decide_eq_true (List.all_eq_true.mp hy a ha))
    (fun a ha ↦ of_decide_eq_true (List.all_eq_true.mp hz a ha))
    hsum hsum hsum hdegree hdegree hdegree hmass ?_ s t u
  simpa only [packTerms_eq_eval] using hpacked

theorem eval_of_checkPackedProduct (s t u : ℝ) {xs ys zs : List Term}
    (hc : checkPackedProduct xs ys zs = true) :
    evalTerms s t u zs = evalTerms s t u xs * evalTerms s t u ys :=
  eval_of_packedProductMatches s t u (degree := 12) hc

private def smallDegree (a : Term) : Bool :=
  decide (a.exponents.1 + a.exponents.2.1 + a.exponents.2.2 ≤ 6)

/-- Use packed multiplication for dense products when the exact comparison passes. -/
def checkedProduct (xs ys : List Term) : List Term :=
  if xs.length < 32 || ys.length < 32 then multiply xs ys
  else
    let degree := if xs.all smallDegree && ys.all smallDegree then 6 else 12
    let width := 2 * degree + 1
    let mass := termMass xs * termMass ys
    let bits := mass.log2 + 3
    let packed := packTerms width bits xs * packTerms width bits ys
    let zs := unpackProduct width bits packed
    if packedProductMatches degree xs ys zs mass bits packed then zs else multiply xs ys

theorem eval_checkedProduct (s t u : ℝ) (xs ys : List Term) :
    evalTerms s t u (checkedProduct xs ys) = evalTerms s t u xs * evalTerms s t u ys := by
  have hmul : evalTerms s t u (multiply xs ys) = evalTerms s t u xs * evalTerms s t u ys :=
    DimThree.eval_mul s t u ⟨xs⟩ ⟨ys⟩
  unfold checkedProduct
  split
  · exact hmul
  dsimp only
  split
  all_goals
    split
    · rename_i h
      exact eval_of_packedProductMatches s t u h
    · exact hmul

end RefinedBMV.DimThree.Certificate

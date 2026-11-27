/- GID: D5/S3/Quantum/Analysis/RefinedBMV/DimFourScalar
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/DimFourScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Each geometric-mean term in the refined BMV pairing is bounded by the mixed defect. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThree

/-! # Individual geometric means in the refined BMV pairing -/

namespace RefinedBMV.DimThree

open Certificate

variable {R : Type*} [CommRing R]

private def rawGap {R : Type*} [Add R] [Sub R] [Mul R] [Pow R Nat] [NatCast R]
    [Zero R] (p : ℕ) (f : Fin 3) (a b c : R) : R :=
  defect p a b c ^ 2 - (![defect p b b a * defect p c c a,
    defect p a a b * defect p c c b, defect p a a c * defect p b b c]) f

private def polynomial (p : ℕ) (f : Fin 3) : Sparse :=
  let s : Sparse := ⟨[⟨(1, 0, 0), 1⟩]⟩
  let t : Sparse := ⟨[⟨(0, 1, 0), 1⟩]⟩
  let u : Sparse := ⟨[⟨(0, 0, 1), 1⟩]⟩
  rawGap p f s (s + t) (s + t + u)

private theorem polynomial_control (p : ℕ) (f : Fin 3) :
    Controlled (polynomial p f).terms (3 * p + 3 * p) (2 * defectSize p ^ 2) := by
  let s : Sparse := ⟨[⟨(1, 0, 0), 1⟩]⟩
  let t : Sparse := ⟨[⟨(0, 1, 0), 1⟩]⟩
  let u : Sparse := ⟨[⟨(0, 0, 1), 1⟩]⟩
  let a := s
  let b := s + t
  let c := s + t + u
  have hs : Controlled s.terms 1 1 := by simp [Controlled, coefficientNorm, s, Term.degree]
  have ht : Controlled t.terms 1 1 := by simp [Controlled, coefficientNorm, t, Term.degree]
  have hu : Controlled u.terms 1 1 := by simp [Controlled, coefficientNorm, u, Term.degree]
  have ha : Controlled a.terms 1 3 := mono hs (by decide)
  have hb : Controlled b.terms 1 3 := mono (add_bound hs ht) (by decide)
  have hc : Controlled c.terms 1 3 := add_bound (add_bound hs ht) hu
  have hm : Controlled ((defect p a b c) ^ 2).terms (3 * p + 3 * p)
      (defectSize p * defectSize p) := by
    have hd : Controlled (defect p a b c).terms (3 * p) (defectSize p) :=
      defect_bound p ha hb hc
    simpa only [Nat.mul_succ, Nat.mul_zero, Nat.zero_add, Nat.pow_succ, Nat.pow_zero,
      Nat.one_mul] using pow_bound hd 2
  have hw : Controlled ((![defect p b b a * defect p c c a,
      defect p a a b * defect p c c b, defect p a a c * defect p b b c]) f).terms
      (3 * p + 3 * p) (defectSize p * defectSize p) := by
    fin_cases f
    · exact mul_bound (defect_bound p hb hb ha) (defect_bound p hc hc ha)
    · exact mul_bound (defect_bound p ha ha hb) (defect_bound p hc hc hb)
    · exact mul_bound (defect_bound p ha ha hc) (defect_bound p hb hb hc)
  have he : defectSize p * defectSize p + defectSize p * defectSize p =
      2 * defectSize p ^ 2 := by ring
  have hh := sub_bound hm hw
  change Controlled (polynomial p f).terms _ _ at hh
  exact he ▸ hh

private theorem eval_polynomial (p : ℕ) (f : Fin 3) (s t u : R) :
    (polynomial p f).eval s t u = rawGap p f s (s + t) (s + t + u) := by
  have hf (x y z : Sparse) :
      ((![x, y, z] : Fin 3 → Sparse) f).eval s t u =
        (![x.eval s t u, y.eval s t u, z.eval s t u] : Fin 3 → R) f := by
    fin_cases f <;> rfl
  simp only [polynomial, rawGap, eval_sub, eval_pow, hf, eval_mul, eval_defect, eval_add]
  simp [Sparse.eval, evalTerms, Term.eval]

private def checkMask (p : ℕ) (f : Fin 3) : Bool :=
  let d := 3 * p + 3 * p
  let base : ℕ := 2 ^ 81
  let mask := PackedCheck.centeredMask 80 d
  let value := rawGap p f (1 : ℤ) (1 + ↑base) (1 + ↑base + ↑(base ^ (d + 1)))
  ((value + ↑mask).toNat &&& mask) == mask

set_option maxHeartbeats 0 in
-- Kernel reduction checks nine packed integer evaluations.
private theorem check (p : ℕ) (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    ∀ f : Fin 3, checkMask p f = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

private theorem ordered_gap {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7) (f : Fin 3)
    (s t u : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 ≤ rawGap p f s (s + t) (s + t + u) := by
  let d := 3 * p + 3 * p
  let base : ℕ := 2 ^ (80 + 1)
  let xs := (polynomial p f).terms
  have hd : ∀ m ∈ xs, m.exponents.1 + m.exponents.2.1 + m.exponents.2.2 = d :=
    (polynomial_control p f).1
  have hnorm : coefficientNorm xs < 2 ^ 80 := by
    refine (polynomial_control p f).2.trans_lt ?_
    rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hpacked := encode_columns d (base : ℤ) xs hd
  change _ = (polynomial p f).eval (1 : ℤ) base ((base : ℤ) ^ (d + 1)) at hpacked
  rw [eval_polynomial] at hpacked
  have hn := column_digit_nonneg hnorm hpacked (by
    simpa only [checkMask, beq_iff_eq, Int.natCast_pow, base, d] using check p hp f)
  have h := real_eval_nonneg hs ht hu hd hn
  change 0 ≤ (polynomial p f).eval s t u at h
  rwa [eval_polynomial] at h

private theorem ordered_sq {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (s t u : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    let a := s
    let b := s + t
    let c := s + t + u
    defect p b b a * defect p c c a ≤ defect p a b c ^ 2 ∧
    defect p a a b * defect p c c b ≤ defect p a b c ^ 2 ∧
    defect p a a c * defect p b b c ≤ defect p a b c ^ 2 := by
  exact ⟨sub_nonneg.mp (ordered_gap hp 0 s t u hs ht hu),
    sub_nonneg.mp (ordered_gap hp 1 s t u hs ht hu),
    sub_nonneg.mp (ordered_gap hp 2 s t u hs ht hu)⟩

end RefinedBMV.DimThree

namespace RefinedBMV.DimFour

open DimThree

/-- The square of the geometric mean from any one center is bounded by the
square of the mixed defect. -/
theorem individual_sq {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    defect p a a c * defect p b b c ≤ defect p a b c ^ 2 := by
  have ordered (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :=
    ordered_sq hp x (y - x) (z - y) hx (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyz)
  have bounds (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
      defect p y y x * defect p z z x ≤ defect p x y z ^ 2 ∧
      defect p x x y * defect p z z y ≤ defect p x y z ^ 2 ∧
      defect p x x z * defect p y y z ≤ defect p x y z ^ 2 := by
    have hxy' : x + (y - x) = y := by ring
    have hyz' : y + (z - y) = z := by ring
    simpa only [hxy', hyz'] using ordered x y z hx hxy hyz
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact (bounds a b c ha hab hbc).2.2
    · rcases le_total a c with hac | hca
      · have h := (bounds a c b ha hac hcb).2.1
        rwa [defect_cycle hp b a c, defect_swap hp a b c] at h
      · simpa only [defect_cycle hp c a b] using (bounds c a b hc hca hab).1
  · rcases le_total a c with hac | hca
    · simpa only [mul_comm (defect p b b c), defect_swap hp a b c] using
        (bounds b a c hb hba hac).2.2
    · rcases le_total b c with hbc | hcb
      · simpa only [mul_comm (defect p b b c), defect_cycle hp a b c] using
          (bounds b c a hb hbc hca).2.1
      · have h := (bounds c b a hc hcb hba).1
        rwa [mul_comm, ← defect_cycle hp c b a, defect_swap hp a b c] at h

#print axioms individual_sq

end RefinedBMV.DimFour

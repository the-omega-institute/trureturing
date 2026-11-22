/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCover
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCover
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalChart]
   utility: none
   digest: The common zero set of the physical critical equations has a six-dimensional differentiable cover. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteCriticalChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRealPolynomialZeros

/-! The Cartesian change of variables transfers the relatively prime
complex equations to the real physical slice. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalCover

open MvPolynomial Set D5.S3.Quantum.Algebra
  PeriodicMPSSixSiteCriticalChart
  PeriodicMPSRealPolynomialZeros

noncomputable section

private abbrev finSum : Fin 4 ⊕ Fin 4 ≃ Fin 8 := finSumFinEquiv (m := 4) (n := 4)

private def sumOrder : Fin 8 ≃ Fin 4 ⊕ Fin 4 :=
  (((Equiv.swap (0 : Fin 8) 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)).trans
    finSum.symm

/-- The two conjugate weighted invariant tuples with their first traces fixed. -/
def lift (q : Fin 4 → ℂ) : Fin 10 → ℂ :=
  ![1, q 0, q 1, q 2, q 3, 1, star (q 0), star (q 1), star (q 2), star (q 3)]

/-- Ordinary trace coordinates in the chart where the first trace is nonzero. -/
def affineParameters (t s d e k : ℂ) : Fin 4 → ℂ :=
  ![s / t, d / t ^ 2, e / t ^ 2, k / t ^ 2]

private lemma eval_weighted_scale (w : Fin 10 → ℕ) {p : MvPolynomial (Fin 10) ℂ} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) (z : ℂ) (a : Fin 10 → ℂ) :
    eval (fun j => z ^ w j * a j) p = z ^ n * eval a p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hw : ∑ j ∈ m.support, w j * m j = n := by
    have h := hp (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    calc
      _ = ∑ j ∈ m.support, m j * w j :=
        Finset.sum_congr rfl fun j _ => Nat.mul_comm _ _
      _ = n := by simpa only [nsmul_eq_mul, Nat.cast_id] using h
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, hw]
  ac_rfl

/-- Normalizing both trace blocks extracts their respective nonzero scale
factors from each selected cofactor. -/
theorem eval_minorOver_affineParameters {t : ℂ} (ht : t ≠ 0) (s d e k : ℂ)
    (i : Fin 10) (hi : i = 0 ∨ i = 1) :
    eval ![t, s, d, e, k, star t, star s, star d, star e, star k] (minorOver i) =
      t ^ 47 * (star t) ^ 46 * eval (lift (affineParameters t s d e k)) (minorOver i) := by
  let a := lift (affineParameters t s d e k)
  have ht' : star t ≠ 0 := star_ne_zero.mpr ht
  have ht₂ : t ^ 2 ≠ 0 := pow_ne_zero _ ht
  have ht₂' : (star t) ^ 2 ≠ 0 := pow_ne_zero _ ht'
  have ha : (fun j => t ^ blockWeights true j * ((star t) ^ blockWeights false j * a j)) =
      ![t, s, d, e, k, star t, star s, star d, star e, star k] := by
    funext j
    fin_cases j
    · change t ^ 1 * ((star t) ^ 0 * 1) = t
      simp
    · change t ^ 1 * ((star t) ^ 0 * (s / t)) = s
      simp [mul_div_cancel₀, ht]
    · change t ^ 2 * ((star t) ^ 0 * (d / t ^ 2)) = d
      simp [mul_div_cancel₀, ht₂]
    · change t ^ 2 * ((star t) ^ 0 * (e / t ^ 2)) = e
      simp [mul_div_cancel₀, ht₂]
    · change t ^ 2 * ((star t) ^ 0 * (k / t ^ 2)) = k
      simp [mul_div_cancel₀, ht₂]
    · change t ^ 0 * ((star t) ^ 1 * 1) = star t
      simp
    · change t ^ 0 * ((star t) ^ 1 * star (s / t)) = star s
      rw [pow_zero, one_mul, pow_one, star_div₀, mul_div_cancel₀ _ ht']
    · change t ^ 0 * ((star t) ^ 2 * star (d / t ^ 2)) = star d
      rw [pow_zero, one_mul, star_div₀, star_pow, mul_div_cancel₀ _ ht₂']
    · change t ^ 0 * ((star t) ^ 2 * star (e / t ^ 2)) = star e
      rw [pow_zero, one_mul, star_div₀, star_pow, mul_div_cancel₀ _ ht₂']
    · change t ^ 0 * ((star t) ^ 2 * star (k / t ^ 2)) = star k
      rw [pow_zero, one_mul, star_div₀, star_pow, mul_div_cancel₀ _ ht₂']
  obtain ⟨hLeft, hRight⟩ := minorOver_bidegree (R := ℂ) i hi
  rw [← ha, eval_weighted_scale _ hLeft t (fun j => (star t) ^ blockWeights false j * a j),
    eval_weighted_scale _ hRight (star t) a, mul_assoc]

private def cartesianMinor (k : Fin 10) : MvPolynomial (Fin 8) ℂ :=
  renameEquiv ℂ finSum
    (PhasePolynomial.cartesianEquiv (renameEquiv ℂ sumOrder (chartMinor k)))

private theorem cartesian_relatively_prime : IsRelPrime (cartesianMinor 0) (cartesianMinor 1) := by
  let e : MvPolynomial (Fin 8) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 8) ℂ :=
    ((renameEquiv ℂ sumOrder).trans PhasePolynomial.cartesianEquiv).trans
      (renameEquiv ℂ finSum)
  change IsRelPrime (e (chartMinor 0)) (e (chartMinor 1))
  apply IsRelPrime.of_map e.symm
  simpa only [AlgEquiv.symm_apply_apply] using (relatively_prime_chartMinors (K := ℂ))

private theorem cartesian_nonzero : cartesianMinor 0 ≠ 0 := by
  intro h
  apply first_chartMinor_ne_zero (K := ℂ)
  apply (renameEquiv ℂ sumOrder).injective
  apply (PhasePolynomial.cartesianEquiv (ι := Fin 4)).injective
  apply (renameEquiv ℂ finSum).injective
  simpa only [cartesianMinor, map_zero] using h

/-- Real and imaginary parts are separated by the sum of the two index sets. -/
def cartesianInput (z : Fin 4 → ℂ) : Fin 8 → ℝ :=
  (Sum.elim (fun i => (z i).re) (fun i => (z i).im)) ∘ finSum.symm

private def fromCartesianInput (r : Fin 8 → ℝ) : Fin 4 → ℂ :=
  fun i => ⟨r (finSum (Sum.inl i)), r (finSum (Sum.inr i))⟩

private theorem fromCartesian_left (z : Fin 4 → ℂ) :
    fromCartesianInput (cartesianInput z) = z := by
  funext i
  apply Complex.ext <;> simp [fromCartesianInput, cartesianInput, Function.comp_def]

private theorem fromCartesian_differentiable : Differentiable ℝ fromCartesianInput := by
  apply differentiable_pi.mpr
  intro i
  change Differentiable ℝ (fun r : Fin 8 → ℝ =>
    (⟨r (finSum (Sum.inl i)), r (finSum (Sum.inr i))⟩ : ℂ))
  have he (r : Fin 8 → ℝ) :
      (⟨r (finSum (Sum.inl i)), r (finSum (Sum.inr i))⟩ : ℂ) =
        ((r (finSum (Sum.inl i)) : ℝ) : ℂ) +
          ((r (finSum (Sum.inr i)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp_rw [he]
  exact (Complex.ofRealCLM.differentiable.comp (differentiable_apply _)).add
    ((Complex.ofRealCLM.differentiable.comp (differentiable_apply _)).mul_const _)

private theorem eval_cartesianMinor (z : Fin 4 → ℂ) (k : Fin 10) :
    eval (fun j => (cartesianInput z j : ℂ)) (cartesianMinor k) = eval (lift z) (minorOver k) := by
  rw [cartesianMinor, renameEquiv_apply, eval_rename]
  have hcart : (fun j => (cartesianInput z j : ℂ)) ∘ finSum =
      PhasePolynomial.cartesian z := by
    funext j
    cases j <;> simp [cartesianInput, PhasePolynomial.cartesian, Function.comp_def]
  rw [hcart]
  change eval (PhasePolynomial.cartesian z)
    (PhasePolynomial.toCartesian (renameEquiv ℂ sumOrder (chartMinor k))) = _
  rw [PhasePolynomial.actual_cartesian, PhasePolynomial.actual, renameEquiv_apply, eval_rename,
    eval_chartMinor]
  apply congrArg (fun a : Fin 10 → ℂ => eval a (minorOver k))
  funext i
  fin_cases i <;> rfl

/-- The physical common zero set of the two affine minors is covered by
countably many differentiable maps from six real variables. -/
theorem cover_critical_equations :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin 6 → ℝ))
      (g : ι → (Fin 6 → ℝ) → (Fin 4 → ℂ)),
      (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {q | eval (lift q) (minorOver 0) = 0 ∧ eval (lift q) (minorOver 1) = 0} ⊆
        ⋃ i, g i '' D i := by
  obtain ⟨ι, hι, D, g, hd, hc⟩ := cover_real_common_zeros (n := 6)
    cartesian_nonzero cartesian_relatively_prime
  refine ⟨ι, hι, D, fun i => fromCartesianInput ∘ g i,
    fun i => fromCartesian_differentiable.differentiableOn.comp (hd i) (mapsTo_univ _ _), ?_⟩
  intro q hq
  have h : eval (fun j => (cartesianInput q j : ℂ)) (cartesianMinor 0) = 0 ∧
      eval (fun j => (cartesianInput q j : ℂ)) (cartesianMinor 1) = 0 := by
    rw [eval_cartesianMinor, eval_cartesianMinor]
    exact hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hc h)
  obtain ⟨u, hu, he⟩ := hi
  exact mem_iUnion.mpr ⟨i, u, hu, (congrArg fromCartesianInput he).trans (fromCartesian_left q)⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteCriticalCover

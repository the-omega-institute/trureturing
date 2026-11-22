/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalCover
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteCriticalCover
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalChart]
   utility: none
   digest: The common zero set of the physical critical equations has a six-dimensional differentiable cover. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteCriticalChart
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRealPolynomialZeros

/-! The Cartesian change of variables transfers the relatively prime
complex equations to the real physical slice. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCover

open MvPolynomial Set D5.S3.Quantum.Algebra
  PeriodicMPSFiveSiteCriticalChart PeriodicMPSFiveSiteCriticalDivisors
  PeriodicMPSRealPolynomialZeros

noncomputable section

private abbrev finSum : Fin 4 ⊕ Fin 4 ≃ Fin 8 := finSumFinEquiv (m := 4) (n := 4)

private def sumOrder : Fin 8 ≃ Fin 4 ⊕ Fin 4 :=
  (((Equiv.swap (0 : Fin 8) 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)).trans
    finSum.symm

/-- The two conjugate weighted invariant tuples with their first traces fixed. -/
def lift (q : Fin 4 → ℂ) : Fin 10 → ℂ :=
  ![1, q 0, q 1, q 2, q 3, 1, star (q 0), star (q 1), star (q 2), star (q 3)]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteCriticalCover

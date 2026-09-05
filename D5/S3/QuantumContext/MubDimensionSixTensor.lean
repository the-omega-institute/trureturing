/- GID: D5/S3/QuantumContext/MubDimensionSixTensor
   generality: I
   mirror-B: D5/B/S3/QuantumContext/MubDimensionSixTensor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify three mutually unbiased bases in complex dimension six by tensoring. -/

/- Library-search audit trail (2026-09-05):
   * Exact declaration and statement-shape searches of current `origin/dev` found no
     coordinate MUB tensor package, exact qutrit Gauss-sum table, or dimension-six
     three-basis certificate. The open fourth-basis compatibility lane is disjoint.
   * `HesseSicCertificate.omega` is the existing coordinate for `exp (2 pi i / 3)`;
     this module imports and reuses it instead of introducing a second definition.
   * Pinned Mathlib supplies `Matrix.kronecker`, `Matrix.kroneckerMap_apply`, finite
     product sums, complex conjugation/norm identities, and finite-index case analysis.
-/

import D5.S3.QuantumContext.HesseSicCertificate

open scoped BigOperators ComplexConjugate

namespace D5.S3.QuantumContext.MubDimensionSixTensor

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.QuantumContext.HesseSicCertificate

/-- The standard coordinate inner product, conjugate-linear in the first vector. -/
def coordinateInner {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) : ℂ :=
  ∑ k, star (x k) * y k

/-- A square coordinate family whose Gram matrix is the identity. -/
def CoordinateOrthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → ℂ) : Prop :=
  ∀ i j, coordinateInner (b i) (b j) = if i = j then 1 else 0

/-- Two coordinate families are mutually unbiased when every squared cross-overlap
is the reciprocal of the coordinate cardinality. -/
def MutuallyUnbiased {ι : Type*} [Fintype ι]
    (b c : ι → ι → ℂ) : Prop :=
  ∀ i j, ‖coordinateInner (b i) (c j)‖ ^ 2 =
    (Fintype.card ι : ℝ)⁻¹

/-- Coordinatewise tensor product of two vectors. -/
def tensorVector {α β : Type*}
    (x : α → ℂ) (y : β → ℂ) : α × β → ℂ :=
  fun k => x k.1 * y k.2

/-- Coordinatewise tensor product of two square basis families. -/
def tensorBasis {α β : Type*}
    (b : α → α → ℂ) (b' : β → β → ℂ) :
    (α × β) → (α × β) → ℂ :=
  Matrix.kronecker b b'

private theorem tensorBasis_row {α β : Type*}
    (b : α → α → ℂ) (b' : β → β → ℂ) (i : α × β) :
    tensorBasis b b' i = tensorVector (b i.1) (b' i.2) := by
  funext k
  change Matrix.kroneckerMap (fun x y : ℂ => x * y) b b' i k =
    b i.1 k.1 * b' i.2 k.2
  exact Matrix.kroneckerMap_apply (fun x y : ℂ => x * y) b b' i k

/-- A finite family of coordinate bases is pairwise mutually unbiased. -/
def PairwiseMUB {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (bs : κ → ι → ι → ℂ) : Prop :=
  (∀ r, CoordinateOrthonormalBasis (bs r)) ∧
    ∀ r s, r ≠ s → ∀ i j,
      ‖coordinateInner (bs r i) (bs s j)‖ ^ 2 =
        (Fintype.card ι : ℝ)⁻¹

private theorem coordinateInner_tensorVector_aux
    {α β : Type*} [Fintype α] [Fintype β]
    (x u : α → ℂ) (y v : β → ℂ) :
    coordinateInner (tensorVector x y) (tensorVector u v) =
      coordinateInner x u * coordinateInner y v := by
  classical
  simp only [coordinateInner, tensorVector, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [star_mul]
  ring

private theorem coordinateOrthonormalBasis_tensor_aux
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {b : α → α → ℂ} {b' : β → β → ℂ}
    (hb : CoordinateOrthonormalBasis b)
    (hb' : CoordinateOrthonormalBasis b') :
    CoordinateOrthonormalBasis (tensorBasis b b') := by
  intro i j
  rw [tensorBasis_row b b' i, tensorBasis_row b b' j,
    coordinateInner_tensorVector_aux]
  rw [hb i.1 j.1, hb' i.2 j.2]
  by_cases h₁ : i.1 = j.1
  · by_cases h₂ : i.2 = j.2
    · have hij : i = j := Prod.ext h₁ h₂
      subst j
      simp
    · have hij : i ≠ j := fun h => h₂ (congrArg Prod.snd h)
      simp [h₁, h₂, hij]
  · have hij : i ≠ j := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁, hij]

private theorem mutuallyUnbiased_tensor_aux
    {α β : Type*} [Fintype α] [Fintype β]
    {b c : α → α → ℂ} {b' c' : β → β → ℂ}
    (hbc : MutuallyUnbiased b c)
    (hbc' : MutuallyUnbiased b' c') :
    MutuallyUnbiased (tensorBasis b b') (tensorBasis c c') := by
  intro i j
  rw [tensorBasis_row b b' i, tensorBasis_row c c' j,
    coordinateInner_tensorVector_aux]
  rw [norm_mul, mul_pow, hbc i.1 j.1, hbc' i.2 j.2]
  simp [Fintype.card_prod, Nat.cast_mul, mul_comm]

/-- Coordinate inner products factor under tensor products, and tensor products preserve
coordinate orthonormality and the overlap-only mutually-unbiased condition. -/
theorem tensor_mub_package :
    (∀ {α β : Type*} [Fintype α] [Fintype β]
      (x u : α → ℂ) (y v : β → ℂ),
      coordinateInner (tensorVector x y) (tensorVector u v) =
        coordinateInner x u * coordinateInner y v) ∧
    (∀ {α β : Type*} [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β]
      {b : α → α → ℂ} {b' : β → β → ℂ},
      CoordinateOrthonormalBasis b →
      CoordinateOrthonormalBasis b' →
      CoordinateOrthonormalBasis (tensorBasis b b')) ∧
    (∀ {α β : Type*} [Fintype α] [Fintype β]
      {b c : α → α → ℂ} {b' c' : β → β → ℂ},
      MutuallyUnbiased b c → MutuallyUnbiased b' c' →
      MutuallyUnbiased (tensorBasis b b') (tensorBasis c c')) := by
  exact ⟨coordinateInner_tensorVector_aux,
    coordinateOrthonormalBasis_tensor_aux, mutuallyUnbiased_tensor_aux⟩

private theorem pairwiseMUB_tensor_aux
    {κ α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {bs : κ → α → α → ℂ} {cs : κ → β → β → ℂ}
    (hbs : PairwiseMUB bs) (hcs : PairwiseMUB cs) :
    PairwiseMUB (fun r => tensorBasis (bs r) (cs r)) := by
  constructor
  · intro r
    exact coordinateOrthonormalBasis_tensor_aux (hbs.1 r) (hcs.1 r)
  · intro r s hrs i j
    exact mutuallyUnbiased_tensor_aux (hbs.2 r s hrs) (hcs.2 r s hrs) i j

private lemma sq_norm_eq_iff_mul_star (z : ℂ) (x : ℝ) :
    ‖z‖ ^ 2 = x ↔ z * star z = (x : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq,
    show z * star z = (Complex.normSq z : ℂ) by
      simpa using Complex.mul_conj z]
  norm_cast

/-! ## The three qubit bases -/

private def invSqrtTwo : ℂ := (Real.sqrt 2 / 2 : ℝ)

private lemma invSqrtTwo_sq : invSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  apply Complex.ext
  · norm_num [invSqrtTwo, pow_two]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · norm_num [invSqrtTwo, pow_two]

@[simp] private lemma invSqrtTwo_mul_self :
    invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  simpa [pow_two] using invSqrtTwo_sq

@[simp] private lemma star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

@[simp] private lemma starRingEnd_invSqrtTwo :
    (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := by
  exact star_invSqrtTwo

private lemma invSqrtTwo_pow_four : invSqrtTwo ^ 4 = (1 / 4 : ℂ) := by
  calc
    invSqrtTwo ^ 4 = (invSqrtTwo ^ 2) ^ 2 := by ring
    _ = (1 / 4 : ℂ) := by rw [invSqrtTwo_sq]; norm_num

private def qubitZ : Fin 2 → Fin 2 → ℂ := ![
  ![1, 0],
  ![0, 1]
]

private def qubitX : Fin 2 → Fin 2 → ℂ := ![
  ![invSqrtTwo, invSqrtTwo],
  ![invSqrtTwo, -invSqrtTwo]
]

private def qubitY : Fin 2 → Fin 2 → ℂ := ![
  ![invSqrtTwo, invSqrtTwo * Complex.I],
  ![invSqrtTwo, -(invSqrtTwo * Complex.I)]
]

/-- The standard `Z`, `X`, and `Y` qubit eigenbases. -/
def qubitBases : Fin 3 → Fin 2 → Fin 2 → ℂ := ![
  qubitZ, qubitX, qubitY
]

private theorem qubitBases_orthonormal :
    ∀ r, CoordinateOrthonormalBasis (qubitBases r) := by
  intro r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [coordinateInner, qubitBases, qubitZ, qubitX, qubitY,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    simp [invSqrtTwo_sq, Complex.I_sq] <;>
    norm_num

private theorem qubit_three_mubs_aux : PairwiseMUB qubitBases := by
  refine ⟨qubitBases_orthonormal, ?_⟩
  intro r s hrs i j
  rw [sq_norm_eq_iff_mul_star]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp_all [coordinateInner, qubitBases, qubitZ, qubitX, qubitY,
      Fin.sum_univ_two] <;>
    ring_nf <;>
    simp [invSqrtTwo_sq, invSqrtTwo_pow_four] <;>
    ring

/-! ## Three Wootters--Fields qutrit bases -/

private lemma omega_cubed : omega ^ 3 = 1 := by
  rw [omega]
  calc
    Complex.exp (2 * Real.pi * Complex.I / 3) ^ 3 =
        Complex.exp ((3 : ℂ) * (2 * Real.pi * Complex.I / 3)) :=
      (Complex.exp_nat_mul _ 3).symm
    _ = Complex.exp (2 * Real.pi * Complex.I) := by
      congr 1
      ring
    _ = 1 := Complex.exp_two_pi_mul_I

private lemma omega_ne_one : omega ≠ 1 := by
  intro h
  have hdvd : (3 : ℕ) ∣ 1 :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
      (k := 1) (N := 3) (by norm_num)).mp (by
        simpa [omega] using h)
  norm_num at hdvd

private lemma omega_ne_zero : omega ≠ 0 := Complex.exp_ne_zero _

private lemma omega_sum : 1 + omega + omega ^ 2 = 0 := by
  have hfac : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    rw [show (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 by ring,
      omega_cubed]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · exact (omega_ne_one (sub_eq_zero.mp h)).elim
  · linear_combination h

private lemma omega_norm : ‖omega‖ = 1 := by
  rw [omega, show 2 * (Real.pi : ℂ) * Complex.I / 3 =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

@[simp] private lemma star_omega : star omega = omega ^ 2 := by
  apply mul_left_cancel₀ omega_ne_zero
  calc
    omega * star omega = (Complex.normSq omega : ℂ) := by
      simpa using Complex.mul_conj omega
    _ = 1 := by rw [omega_normSq]; norm_num
    _ = omega ^ 3 := omega_cubed.symm
    _ = omega * omega ^ 2 := by ring

@[simp] private lemma starRingEnd_omega :
    (starRingEnd ℂ) omega = omega ^ 2 := by
  exact star_omega

private lemma omega_sq_reduce : omega ^ 2 = -omega - 1 := by
  linear_combination omega_sum

private lemma omega_pow_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_five : omega ^ 5 = omega ^ 2 := by
  calc
    omega ^ 5 = omega ^ 3 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_six : omega ^ 6 = 1 := by
  calc
    omega ^ 6 = (omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_seven : omega ^ 7 = omega := by
  calc
    omega ^ 7 = (omega ^ 3) ^ 2 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_eight : omega ^ 8 = omega ^ 2 := by
  calc
    omega ^ 8 = (omega ^ 3) ^ 2 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_nine : omega ^ 9 = 1 := by
  calc
    omega ^ 9 = (omega ^ 3) ^ 3 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_ten : omega ^ 10 = omega := by
  calc
    omega ^ 10 = (omega ^ 3) ^ 3 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_eleven : omega ^ 11 = omega ^ 2 := by
  calc
    omega ^ 11 = (omega ^ 3) ^ 3 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_twelve : omega ^ 12 = 1 := by
  calc
    omega ^ 12 = (omega ^ 3) ^ 4 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_thirteen : omega ^ 13 = omega := by
  calc
    omega ^ 13 = (omega ^ 3) ^ 4 * omega := by ring
    _ = omega := by rw [omega_cubed]; ring

private lemma omega_pow_fourteen : omega ^ 14 = omega ^ 2 := by
  calc
    omega ^ 14 = (omega ^ 3) ^ 4 * omega ^ 2 := by ring
    _ = omega ^ 2 := by rw [omega_cubed]; ring

private lemma omega_pow_fifteen : omega ^ 15 = 1 := by
  calc
    omega ^ 15 = (omega ^ 3) ^ 5 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private lemma omega_pow_eighteen : omega ^ 18 = 1 := by
  calc
    omega ^ 18 = (omega ^ 3) ^ 6 := by ring
    _ = 1 := by rw [omega_cubed]; ring

private def invSqrtThree : ℂ := (Real.sqrt 3 / 3 : ℝ)

private lemma invSqrtThree_sq : invSqrtThree ^ 2 = (1 / 3 : ℂ) := by
  apply Complex.ext
  · norm_num [invSqrtThree, pow_two]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · norm_num [invSqrtThree, pow_two]

@[simp] private lemma invSqrtThree_mul_self :
    invSqrtThree * invSqrtThree = (1 / 3 : ℂ) := by
  simpa [pow_two] using invSqrtThree_sq

@[simp] private lemma star_invSqrtThree :
    star invSqrtThree = invSqrtThree := by
  simp [invSqrtThree]

@[simp] private lemma starRingEnd_invSqrtThree :
    (starRingEnd ℂ) invSqrtThree = invSqrtThree := by
  exact star_invSqrtThree

private lemma invSqrtThree_pow_four : invSqrtThree ^ 4 = (1 / 9 : ℂ) := by
  calc
    invSqrtThree ^ 4 = (invSqrtThree ^ 2) ^ 2 := by ring
    _ = (1 / 9 : ℂ) := by rw [invSqrtThree_sq]; norm_num

private def qutritZ : Fin 3 → Fin 3 → ℂ := ![
  ![1, 0, 0],
  ![0, 1, 0],
  ![0, 0, 1]
]

private def qutritFourier : Fin 3 → Fin 3 → ℂ := ![
  ![invSqrtThree, invSqrtThree, invSqrtThree],
  ![invSqrtThree, invSqrtThree * omega, invSqrtThree * omega ^ 2],
  ![invSqrtThree, invSqrtThree * omega ^ 2, invSqrtThree * omega]
]

private def qutritQuadratic : Fin 3 → Fin 3 → ℂ := ![
  ![invSqrtThree, invSqrtThree * omega, invSqrtThree * omega],
  ![invSqrtThree, invSqrtThree * omega ^ 2, invSqrtThree],
  ![invSqrtThree, invSqrtThree, invSqrtThree * omega ^ 2]
]

/-- The standard, Fourier, and one quadratic-phase qutrit basis. -/
def qutritBases : Fin 3 → Fin 3 → Fin 3 → ℂ := ![
  qutritZ, qutritFourier, qutritQuadratic
]

private theorem qutritBases_orthonormal :
    ∀ r, CoordinateOrthonormalBasis (qutritBases r) := by
  intro r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [coordinateInner, qutritBases, qutritZ, qutritFourier,
      qutritQuadratic, Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [invSqrtThree_sq, omega_cubed, omega_pow_four,
      omega_pow_five, omega_pow_six, omega_sq_reduce] <;>
    ring

/-- The standard, Fourier, and quadratic-phase qutrit bases are pairwise mutually
unbiased, as certified by the complete exact finite overlap table. -/
theorem qutrit_three_mubs : PairwiseMUB qutritBases := by
  refine ⟨qutritBases_orthonormal, ?_⟩
  intro r s hrs i j
  rw [sq_norm_eq_iff_mul_star]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp_all [coordinateInner, qutritBases, qutritZ, qutritFourier,
      qutritQuadratic, Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [invSqrtThree_sq, invSqrtThree_pow_four,
      omega_cubed, omega_pow_four,
      omega_pow_five, omega_pow_six, omega_pow_eight,
      omega_pow_nine, omega_pow_ten, omega_pow_eleven, omega_pow_twelve,
      omega_pow_thirteen, omega_pow_fourteen, omega_pow_fifteen,
      omega_pow_eighteen, omega_sq_reduce] <;>
    ring

/-! ## The dimension-six certificate -/

/-- Three product bases on the six-coordinate carrier `Fin 2 × Fin 3`. -/
def dimensionSixBases :
    Fin 3 → (Fin 2 × Fin 3) → (Fin 2 × Fin 3) → ℂ :=
  fun r => tensorBasis (qubitBases r) (qutritBases r)

private theorem dimension_six_three_mubs_aux : PairwiseMUB dimensionSixBases := by
  exact pairwiseMUB_tensor_aux qubit_three_mubs_aux qutrit_three_mubs

/-- Three explicit tensor-product bases give the exact `M(6) ≥ 3` certificate,
including orthonormality and every displayed cross-overlap value `1/6`. -/
theorem dimension_six_three_mubs_certificate :
    PairwiseMUB dimensionSixBases ∧
      ((∀ r, CoordinateOrthonormalBasis (dimensionSixBases r)) ∧
        ∀ r s, r ≠ s → ∀ i j,
          ‖coordinateInner (dimensionSixBases r i) (dimensionSixBases s j)‖ ^ 2 =
            (1 / 6 : ℝ)) := by
  refine ⟨dimension_six_three_mubs_aux,
    dimension_six_three_mubs_aux.1, ?_⟩
  intro r s hrs i j
  simpa using dimension_six_three_mubs_aux.2 r s hrs i j

example : Fin 3 := 0
example : Fin 2 × Fin 3 := (0, 0)
example : CoordinateOrthonormalBasis (qutritBases 0) := qutrit_three_mubs.1 0
example : MutuallyUnbiased (qutritBases 0) (qutritBases 1) :=
  qutrit_three_mubs.2 0 1 (by decide)
example : PairwiseMUB dimensionSixBases := dimension_six_three_mubs_certificate.1

#print axioms tensor_mub_package
#print axioms qutrit_three_mubs
#print axioms dimension_six_three_mubs_certificate

end

end D5.S3.QuantumContext.MubDimensionSixTensor

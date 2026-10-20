/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: Positive weighted power sums and the ordered Coulter-Do differential operator. -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
The positive power-sum algebra for the Coulter–Do operator. Variable `n` denotes
`p_(n+1)`; in particular there is no variable of weight zero. Coefficients of the
literal differential operator have input partition first and output partition
second. Identification with the native row coefficient belongs to its supplier.
-/

noncomputable section

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

open scoped BigOperators
open MvPolynomial

abbrev Exponent := ℕ →₀ ℕ
abbrev PowerSum (K : Type*) [CommSemiring K] := MvPolynomial ℕ K

def variableWeight (i : ℕ) : ℕ := i + 1

def exponentParts (d : Exponent) : Multiset ℕ := d.toMultiset.map Nat.succ

def partitionExponent {k : ℕ} (ρ : Nat.Partition k) : Exponent :=
  (ρ.parts.map Nat.pred).toFinsupp

private theorem sum_exponentParts (d : Exponent) :
    (exponentParts d).sum = Finsupp.weight variableWeight d := by
  refine d.induction ?_ ?_
  · simp [exponentParts]
  · intro i n d hi hn ih
    simpa [exponentParts, Finsupp.toMultiset_add, Multiset.map_nsmul,
      Multiset.sum_nsmul, map_add, Finsupp.weight_single, variableWeight] using
      congrArg (fun x => n * (i + 1) + x) ih

def exponentPartition (d : Exponent) : Nat.Partition (Finsupp.weight variableWeight d) where
  parts := exponentParts d
  parts_pos := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hi
    exact Nat.succ_pos _
  parts_sum := sum_exponentParts d

@[simp] theorem exponentParts_partitionExponent {k : ℕ} (ρ : Nat.Partition k) :
    exponentParts (partitionExponent ρ) = ρ.parts := by
  simp only [exponentParts, partitionExponent, Multiset.toFinsupp_toMultiset,
    Multiset.map_map]
  simpa [Function.comp_def] using
    Multiset.map_congr rfl (fun n hn => Nat.succ_pred_eq_of_pos (ρ.parts_pos hn))

@[simp] theorem partitionExponent_exponentPartition (d : Exponent) :
    partitionExponent (exponentPartition d) = d := by
  simp [partitionExponent, exponentPartition, exponentParts, Multiset.map_map,
    Function.comp_def]

theorem partitionExponent_injective (k : ℕ) :
    Function.Injective (@partitionExponent k) := by
  intro ρ σ h
  apply Nat.Partition.ext
  simpa using congrArg exponentParts h

@[simp] theorem partitionExponent_weight {k : ℕ} (ρ : Nat.Partition k) :
    Finsupp.weight variableWeight (partitionExponent ρ) = k := by
  rw [← sum_exponentParts, exponentParts_partitionExponent, ρ.parts_sum]

theorem exists_partitionExponent {d : Exponent} {k : ℕ}
    (h : Finsupp.weight variableWeight d = k) :
    ∃ ρ : Nat.Partition k, partitionExponent ρ = d := by
  subst k
  exact ⟨exponentPartition d, partitionExponent_exponentPartition d⟩

def powerSumMonomial {K : Type*} [CommSemiring K] {k : ℕ}
    (ρ : Nat.Partition k) : PowerSum K := monomial (partitionExponent ρ) 1

theorem powerSumMonomial_homogeneous {K : Type*} [CommSemiring K] {k : ℕ}
    (ρ : Nat.Partition k) :
    IsWeightedHomogeneous variableWeight (powerSumMonomial (K := K) ρ) k := by
  exact isWeightedHomogeneous_monomial _ _ _ (partitionExponent_weight ρ)

theorem homogeneous_expansion {K : Type*} [CommSemiring K] {k : ℕ}
    (f : PowerSum K) (hf : IsWeightedHomogeneous variableWeight f k) :
    f = ∑ ρ : Nat.Partition k, f.coeff (partitionExponent ρ) • powerSumMonomial ρ := by
  classical
  ext d
  simp only [coeff_sum, coeff_smul, powerSumMonomial, coeff_monomial, mul_ite,
    mul_one, mul_zero, smul_eq_mul]
  by_cases hd : f.coeff d = 0
  · rw [hd]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro ρ _
    split_ifs with h
    · simpa [h] using hd
    · rfl
  · obtain ⟨ρ, rfl⟩ := exists_partitionExponent (hf hd)
    rw [Finset.sum_eq_single ρ]
    · simp
    · intro σ _ hσ
      simp [(partitionExponent_injective k).ne hσ]
    · simp

section Differential

variable {K : Type*} [Field K] [CharZero K]

/-- The literal ordered derivative formula with a finite positive-index bound.
The two occurrences of `range N` are ordered, including the diagonal `i = j`.
-/
def boundedOperator (b : K) (N : ℕ) : PowerSum K →ₗ[K] PowerSum K :=
  (2 : K)⁻¹ •
    ((1 + b) • ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((i + 1 : ℕ) * (j + 1) : K) •
        ((LinearMap.mulLeft K (X (i + j + 1))).comp
          ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap)) +
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((i + j + 2 : ℕ) : K) •
        ((LinearMap.mulLeft K (X i * X j)).comp (pderiv (i + j + 1)).toLinearMap) +
    b • ∑ i ∈ Finset.range N,
      ((i + 1 : ℕ) * i : K) •
        ((LinearMap.mulLeft K (X i)).comp (pderiv i).toLinearMap))

/-- The operator on a monomial is defined by actual derivatives. -/
def monomialOperator (b : K) (d : Exponent) : K →ₗ[K] PowerSum K :=
  (boundedOperator b (Finsupp.weight variableWeight d)).comp (monomial d)

/-- Linear extension from all monomials in the genuine infinite polynomial ring. -/
def differentialOperator (b : K) : PowerSum K →ₗ[K] PowerSum K :=
  (Finsupp.lsum K (monomialOperator b)).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem differentialOperator_monomial (b : K) (d : Exponent) (a : K) :
    differentialOperator b (monomial d a) =
      boundedOperator b (Finsupp.weight variableWeight d) (monomial d a) := by
  simp [differentialOperator, monomial, AddMonoidAlgebra.lsingle,
    monomialOperator]


private theorem cut_homogeneous (d : Exponent) (a : K) (i j : ℕ) :
    IsWeightedHomogeneous variableWeight
      (X i * X j * pderiv (i + j + 1) (monomial d a))
      (Finsupp.weight variableWeight d) := by
  by_cases h : d (i + j + 1) = 0
  · simp [pderiv_monomial, h, isWeightedHomogeneous_zero]
  · rw [pderiv_monomial, X, X, monomial_mul_monomial, monomial_mul_monomial]
    apply isWeightedHomogeneous_monomial
    have hw := Finsupp.weight_sub_single_add (w := variableWeight) h
    simp only [map_add, Finsupp.weight_single, one_nsmul]
    dsimp [variableWeight] at *
    omega

private theorem join_homogeneous (d : Exponent) (a : K) (i j : ℕ) :
    IsWeightedHomogeneous variableWeight
      (X (i + j + 1) * pderiv i (pderiv j (monomial d a)))
      (Finsupp.weight variableWeight d) := by
  by_cases hj : d j = 0
  · simp [pderiv_monomial, hj, isWeightedHomogeneous_zero]
  by_cases hi : (d - Finsupp.single j 1 : Exponent) i = 0
  · simp [pderiv_monomial, hi, isWeightedHomogeneous_zero]
  rw [pderiv_monomial, pderiv_monomial, X, monomial_mul_monomial]
  apply isWeightedHomogeneous_monomial
  have hwj := Finsupp.weight_sub_single_add (w := variableWeight) hj
  have hwi := Finsupp.weight_sub_single_add (w := variableWeight) hi
  simp only [map_add, Finsupp.weight_single, one_nsmul]
  dsimp [variableWeight] at *
  omega


theorem boundedOperator_monomial_homogeneous (b : K) (N : ℕ)
    (d : Exponent) (a : K) :
    IsWeightedHomogeneous variableWeight (boundedOperator b N (monomial d a))
      (Finsupp.weight variableWeight d) := by
  let H := weightedHomogeneousSubmodule K variableWeight (Finsupp.weight variableWeight d)
  change boundedOperator b N (monomial d a) ∈ H
  simp only [boundedOperator, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ]
  apply H.smul_mem
  apply H.add_mem
  · apply H.add_mem
    · apply H.smul_mem
      apply H.sum_mem
      intro i _
      apply H.sum_mem
      intro j _
      apply H.smul_mem
      exact join_homogeneous d a i j
    · apply H.sum_mem
      intro i _
      apply H.sum_mem
      intro j _
      apply H.smul_mem
      exact cut_homogeneous d a i j
  · apply H.smul_mem
    apply H.sum_mem
    intro i _
    apply H.smul_mem
    change X i * pderiv i (monomial d a) ∈ H
    rw [X_mul_pderiv_monomial]
    apply H.nsmul_mem
    exact isWeightedHomogeneous_monomial _ _ _ rfl

theorem differentialOperator_homogeneous (b : K) {f : PowerSum K} {k : ℕ}
    (hf : IsWeightedHomogeneous variableWeight f k) :
    IsWeightedHomogeneous variableWeight (differentialOperator b f) k := by
  classical
  rw [homogeneous_expansion f hf, map_sum]
  apply (weightedHomogeneousSubmodule K variableWeight k).sum_mem
  intro ρ _
  rw [map_smul]
  apply (weightedHomogeneousSubmodule K variableWeight k).smul_mem
  unfold powerSumMonomial
  rw [differentialOperator_monomial]
  change IsWeightedHomogeneous variableWeight _ k
  simpa only [partitionExponent_weight] using
    boundedOperator_monomial_homogeneous b (Finsupp.weight variableWeight (partitionExponent ρ))
      (partitionExponent ρ) (1 : K)

/-- On the entire homogeneous component the operator is the literal ordered
formula with the uniform bound `k`. The monomial extension uses the positive weighted degree; higher
derivative indices vanish by the pinned monomial derivative and weight formulas. -/
theorem differentialOperator_on_homogeneous (b : K) {f : PowerSum K} {k : ℕ}
    (hf : IsWeightedHomogeneous variableWeight f k) :
    differentialOperator b f = boundedOperator b k f := by
  classical
  rw [homogeneous_expansion f hf]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro ρ _
  congr 1
  unfold powerSumMonomial
  rw [differentialOperator_monomial, partitionExponent_weight]

theorem boundedOperator_apply (b : K) (N : ℕ) (f : PowerSum K) :
    boundedOperator b N f = (2 : K)⁻¹ •
      ((1 + b) • (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (((i + 1 : ℕ) * (j + 1) : K) •
          (X (i + j + 1) * pderiv i (pderiv j f)))) +
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((i + j + 2 : ℕ) : K) • (X i * X j * pderiv (i + j + 1) f)) +
      b • (∑ i ∈ Finset.range N,
        (((i + 1 : ℕ) * i : K) • (X i * pderiv i f)))) := by
  simp only [boundedOperator, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ]
  rfl


/-- The coefficient matrix is extracted from the differential operator. It is
not a second declaration of the native occurrence formula. -/
def operatorCoefficient (b : K) {k : ℕ} (ρ σ : Nat.Partition k) : K :=
  (differentialOperator b (powerSumMonomial ρ)).coeff (partitionExponent σ)

theorem differentialOperator_partition_expansion (b : K) {k : ℕ}
    (ρ : Nat.Partition k) :
    differentialOperator b (powerSumMonomial ρ) =
      ∑ σ : Nat.Partition k, operatorCoefficient b ρ σ • powerSumMonomial σ := by
  exact homogeneous_expansion _
    (differentialOperator_homogeneous b (powerSumMonomial_homogeneous ρ))

end Differential

def zExponent (d : Exponent) : ℕ :=
  d.prod fun i m => (i + 1) ^ m * Nat.factorial m

theorem zExponent_pos (d : Exponent) : 0 < zExponent d := by
  apply Finset.prod_pos
  intro i _
  exact Nat.mul_pos (Nat.pow_pos (Nat.succ_pos i)) (Nat.factorial_pos _)

theorem zExponent_add_single (d : Exponent) (i : ℕ) :
    zExponent (d + Finsupp.single i 1) =
      (i + 1) * (d i + 1) * zExponent d := by
  let g : ℕ → ℕ → ℕ := fun j m => (j + 1) ^ m * Nat.factorial m
  have hg : ∀ j, g j 0 = 1 := by intro j; simp [g]
  have he : (d + Finsupp.single i 1).erase i = d.erase i := by
    ext j
    by_cases h : j = i <;> simp [h, Finsupp.erase_ne, Finsupp.single_apply]
  change (d + Finsupp.single i 1).prod g = (i + 1) * (d i + 1) * d.prod g
  rw [← Finsupp.mul_prod_erase' (d + Finsupp.single i 1) i g hg,
    ← Finsupp.mul_prod_erase' d i g hg, he]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  dsimp [g]
  rw [pow_succ, Nat.factorial_succ]
  ring


def zPartition {k : ℕ} (ρ : Nat.Partition k) : ℕ := zExponent (partitionExponent ρ)

def exponentNormalization {K : Type*} [CommSemiring K] (α : K) (d : Exponent) : K :=
  α ^ d.toMultiset.card * (zExponent d : K)

theorem exponentNormalization_add_single {K : Type*} [CommSemiring K]
    (α : K) (d : Exponent) (i : ℕ) :
    exponentNormalization α (d + Finsupp.single i 1) =
      α * (i + 1 : ℕ) * (d i + 1 : ℕ) * exponentNormalization α d := by
  simp only [exponentNormalization, Finsupp.toMultiset_add,
    Finsupp.toMultiset_single, Multiset.card_add, Multiset.card_nsmul,
    Multiset.card_singleton, mul_one, zExponent_add_single, Nat.cast_mul, pow_succ]
  ring


abbrev CoefficientField := RatFunc ℂ

section Pairing

variable {K : Type*} [Field K] [CharZero K]

/-- The diagonal bilinear pairing with squared monomial norm
`α^length * z`. No conjugation or finite-variable restriction is used. -/
def fockPairing (α : K) : PowerSum K →ₗ[K] PowerSum K →ₗ[K] K :=
  (Finsupp.lsum K (fun d : Exponent =>
    (LinearMap.id : K →ₗ[K] K).smulRight
      (exponentNormalization α d • lcoeff K d))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem fockPairing_monomial (α : K) (d : Exponent) (a : K)
    (g : PowerSum K) :
    fockPairing α (monomial d a) g = a * exponentNormalization α d * g.coeff d := by
  simp [fockPairing, monomial, AddMonoidAlgebra.lsingle, mul_assoc]

theorem fockPairing_symmetric (α : K) (f g : PowerSum K) :
    fockPairing α f g = fockPairing α g f := by
  have h : fockPairing α = (fockPairing α).flip := by
    apply MvPolynomial.linearMap_ext
    intro d
    apply LinearMap.ext
    intro a
    apply MvPolynomial.linearMap_ext
    intro e
    apply LinearMap.ext
    intro c
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, fockPairing_monomial,
      coeff_monomial]
    by_cases he : d = e
    · subst e
      simp only [ite_true]
      ring
    · simp [he, Ne.symm he]
  exact congrArg (fun q : PowerSum K →ₗ[K] PowerSum K →ₗ[K] K => q f g) h

@[simp] theorem fockPairing_monomial_right (α : K) (d : Exponent) (a : K)
    (f : PowerSum K) :
    fockPairing α f (monomial d a) = a * exponentNormalization α d * f.coeff d := by
  rw [fockPairing_symmetric, fockPairing_monomial]

theorem fockPairing_X_left (α : K) (i : ℕ) (f g : PowerSum K) :
    fockPairing α (X i * f) g =
      (α * (i + 1 : ℕ)) * fockPairing α f (pderiv i g) := by
  have h : (fockPairing α).flip g ∘ₗ LinearMap.mulLeft K (X i) =
      (α * (i + 1 : ℕ)) • (fockPairing α).flip (pderiv i g) := by
    apply MvPolynomial.linearMap_ext
    intro d
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.flip_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [X, monomial_mul_monomial, one_mul, fockPairing_monomial,
      fockPairing_monomial, coeff_pderiv]
    rw [add_comm (Finsupp.single i 1) d, exponentNormalization_add_single]
    push_cast
    ring
  exact congrArg (fun q : PowerSum K →ₗ[K] K => q f) h

theorem fockPairing_pderiv_left (α : K) (hα : α ≠ 0) (i : ℕ)
    (f g : PowerSum K) :
    fockPairing α (pderiv i f) g =
      (α * (i + 1 : ℕ))⁻¹ * fockPairing α f (X i * g) := by
  have hi : (i + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have h := fockPairing_X_left α i g f
  rw [fockPairing_symmetric α (X i * g) f,
    fockPairing_symmetric α g (pderiv i f)] at h
  rw [h]
  field_simp

/-- Each ordered join is adjoint to the corresponding ordered cut. -/
theorem fockPairing_join_cut (α : K) (hα : α ≠ 0) (i j : ℕ)
    (f g : PowerSum K) :
    (α * (i + 1 : ℕ) * (j + 1 : ℕ)) *
        fockPairing α (X (i + j + 1) * pderiv i (pderiv j f)) g =
      (i + j + 2 : ℕ) * fockPairing α f (X i * X j * pderiv (i + j + 1) g) := by
  have hi : (i + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  have hj : (j + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [fockPairing_X_left, fockPairing_pderiv_left α hα,
    fockPairing_pderiv_left α hα]
  have hm : X j * (X i * pderiv (i + j + 1) g) =
      X i * X j * pderiv (i + j + 1) g := by ring
  rw [hm]
  push_cast
  field_simp
  <;> ring

theorem fockPairing_cut_join (α : K) (hα : α ≠ 0) (i j : ℕ)
    (f g : PowerSum K) :
    (i + j + 2 : ℕ) * fockPairing α (X i * X j * pderiv (i + j + 1) f) g =
      (α * (i + 1 : ℕ) * (j + 1 : ℕ)) *
        fockPairing α f (X (i + j + 1) * pderiv i (pderiv j g)) := by
  rw [fockPairing_symmetric α (X i * X j * pderiv (i + j + 1) f) g,
    fockPairing_symmetric α f (X (i + j + 1) * pderiv i (pderiv j g))]
  exact (fockPairing_join_cut α hα i j g f).symm

theorem fockPairing_euler (α : K) (i : ℕ) (f g : PowerSum K) :
    fockPairing α (X i * pderiv i f) g =
      fockPairing α f (X i * pderiv i g) := by
  calc
    _ = (α * (i + 1 : ℕ)) * fockPairing α (pderiv i f) (pderiv i g) :=
      fockPairing_X_left α i _ _
    _ = (α * (i + 1 : ℕ)) * fockPairing α (pderiv i g) (pderiv i f) := by
      rw [fockPairing_symmetric α (pderiv i f) (pderiv i g)]
    _ = fockPairing α (X i * pderiv i g) f := (fockPairing_X_left α i _ _).symm
    _ = _ := fockPairing_symmetric α _ _

theorem boundedOperator_self_adjoint (b : K) (hα : 1 + b ≠ 0) (N : ℕ)
    (f g : PowerSum K) :
    fockPairing (1 + b) (boundedOperator b N f) g =
      fockPairing (1 + b) f (boundedOperator b N g) := by
  let P := fockPairing (1 + b)
  have hJ : (1 + b) * (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((i + 1 : ℕ) * (j + 1) : K) * P (X (i + j + 1) * pderiv i (pderiv j f)) g) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (i + j + 2 : ℕ) * P f (X i * X j * pderiv (i + j + 1) g) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc, P] using
      fockPairing_join_cut (1 + b) hα i j f g
  have hC : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (i + j + 2 : ℕ) * P (X i * X j * pderiv (i + j + 1) f) g) =
      (1 + b) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((i + 1 : ℕ) * (j + 1) : K) * P f (X (i + j + 1) * pderiv i (pderiv j g)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc, P] using
      fockPairing_cut_join (1 + b) hα i j f g
  rw [boundedOperator_apply, boundedOperator_apply]
  simp only [map_smul, map_nsmul, map_add, map_sum, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sum_apply, smul_eq_mul, nsmul_eq_mul]
  change (2 : K)⁻¹ * ((1 + b) * _ + _ + b * _) =
    (2 : K)⁻¹ * ((1 + b) * _ + _ + b * _)
  rw [hJ, hC]
  simp_rw [fockPairing_euler]
  ring

end Pairing

def normalization {k : ℕ} (ρ : Nat.Partition k) : CoefficientField :=
  (1 + RatFunc.X) ^ ρ.parts.card * (zPartition ρ : CoefficientField)

theorem alpha_ne_zero : (1 + (RatFunc.X : CoefficientField)) ≠ 0 := by
  have hp : (1 + Polynomial.X : Polynomial ℂ) ≠ 0 := by
    intro h
    have := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X] at this
  simpa only [map_add, map_one, RatFunc.algebraMap_X] using
    (RatFunc.algebraMap_ne_zero hp)

theorem normalization_ne_zero {k : ℕ} (ρ : Nat.Partition k) : normalization ρ ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ alpha_ne_zero)
  exact_mod_cast (Nat.ne_of_gt (zExponent_pos (partitionExponent ρ)))

theorem normalization_eq_exponent {k : ℕ} (ρ : Nat.Partition k) :
    normalization ρ = exponentNormalization (1 + RatFunc.X) (partitionExponent ρ) := by
  have hc : (partitionExponent ρ).toMultiset.card = ρ.parts.card := by
    simpa only [exponentParts, Multiset.card_map] using
      congrArg Multiset.card (exponentParts_partitionExponent ρ)
  simp only [normalization, exponentNormalization, zPartition, hc]

/-- Full algebraic detailed balance, for every partition pair, including the
diagonal and pairs with zero transition coefficients. -/
theorem operatorCoefficient_balance {k : ℕ} (μ lam : Nat.Partition k) :
    normalization lam * operatorCoefficient (RatFunc.X : CoefficientField) μ lam =
      normalization μ * operatorCoefficient (RatFunc.X : CoefficientField) lam μ := by
  unfold operatorCoefficient
  simp only [powerSumMonomial, differentialOperator_monomial, partitionExponent_weight]
  have h := boundedOperator_self_adjoint (RatFunc.X : CoefficientField) alpha_ne_zero k
    (monomial (partitionExponent μ) 1) (monomial (partitionExponent lam) 1)
  simpa only [fockPairing_monomial_right, fockPairing_monomial, one_mul,
    ← normalization_eq_exponent] using h

theorem operatorCoefficient_div_normalization {k : ℕ} (μ lam : Nat.Partition k) :
    operatorCoefficient (RatFunc.X : CoefficientField) μ lam / normalization μ =
      operatorCoefficient (RatFunc.X : CoefficientField) lam μ / normalization lam := by
  apply (div_eq_div_iff (normalization_ne_zero μ) (normalization_ne_zero lam)).2
  simpa only [mul_comm] using operatorCoefficient_balance μ lam

/-- The original orientation of C2 for the actual differential coefficient.
Identification with the one canonical native `rowCoefficient` remains the
separate supplier integration obligation. No native-row hypothesis occurs here. -/
theorem normalized_operatorCoefficient_C2 {k : ℕ} (lam : Nat.Partition k) :
    (∑ μ : Nat.Partition k,
      (operatorCoefficient (RatFunc.X : CoefficientField) μ lam / normalization μ) •
        powerSumMonomial μ) =
      differentialOperator (RatFunc.X : CoefficientField)
        ((normalization lam)⁻¹ • powerSumMonomial lam) := by
  rw [map_smul, differentialOperator_partition_expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [smul_smul]
  congr 1
  rw [operatorCoefficient_div_normalization μ lam]
  simp only [div_eq_mul_inv, mul_comm]

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2

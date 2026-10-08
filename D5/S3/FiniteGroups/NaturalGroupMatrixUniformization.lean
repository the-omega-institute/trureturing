/- GID: D5/S3/FiniteGroups/NaturalGroupMatrixUniformization
   generality: G
   utility: exact positive uniformization time and natural equal-power criteria
   digest: Constant group coefficients persist under multiplication, and equal augmentation determines every uniform natural group-matrix power at the exact least-positive threshold.
-/
import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Order.WithBot
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

namespace D5.S3.FiniteGroups.NaturalGroupMatrixUniformization

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}

/-- Actual augmentation of the natural group algebra. -/
def augmentation : MonoidAlgebra ℕ H →+* ℕ :=
  (MonoidAlgebra.lift ℕ ℕ H (1 : H →* ℕ)).toRingHom

def matrixAugmentation : GroupMat H n n →+* Matrix (Fin n) (Fin n) ℕ :=
  (augmentation (H := H)).mapMatrix

/-- Equality of all actual coefficients, including zero coefficients. -/
def Uniform (x : MonoidAlgebra ℕ H) : Prop :=
  ∀ g : H, x.coeff g = x.coeff 1

def UniformMatrix (A : GroupMat H n n) : Prop := ∀ i j, Uniform (A i j)

def Uniformizes (A : GroupMat H n n) : Prop :=
  ∃ k : ℕ, 0 < k ∧ UniformMatrix (A^k)

/-- Least positive uniformizing exponent, only when it exists. -/
def positiveTau (A : GroupMat H n n) (hA : Uniformizes A) : ℕ := by
  classical
  exact Nat.find hA

/-- Original positive-exponent convention, with infinity if no exponent exists. -/
def tau (A : GroupMat H n n) : WithTop ℕ := by
  classical
  exact if hA : Uniformizes A then (positiveTau A hA : WithTop ℕ) else ⊤

theorem augmentation_eq_sum (x : MonoidAlgebra ℕ H) :
    augmentation x = ∑ g : H, x.coeff g := by
  classical
  change MonoidAlgebra.lift ℕ ℕ H (1 : H →* ℕ) x = _
  rw [MonoidAlgebra.lift_apply']
  simp only [MonoidHom.one_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

private theorem augmentation_of_uniform (x : MonoidAlgebra ℕ H) (hx : Uniform x) :
    augmentation x = Fintype.card H * x.coeff 1 := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  rw [augmentation_eq_sum]
  simp_rw [hx]
  simp

/-- Uniform natural coefficients are determined by their actual augmentation. -/
private theorem uniform_eq_of_augmentation_eq (x y : MonoidAlgebra ℕ H)
    (hx : Uniform x) (hy : Uniform y) (h : augmentation x = augmentation y) : x = y := by
  have hs : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨1⟩
  have h1 : x.coeff 1 = y.coeff 1 := by
    apply Nat.eq_of_mul_eq_mul_left hs
    simpa only [augmentation_of_uniform x hx, augmentation_of_uniform y hy] using h
  ext g
  exact (hx g).trans (h1.trans (hy g).symm)

private theorem uniform_mul_right (x y : MonoidAlgebra ℕ H) (hx : Uniform x) :
    Uniform (x*y) := by
  change ∀ g, x.coeff g = x.coeff 1 at hx
  intro g
  rw [MonoidAlgebra.coeff_mul_apply_right, MonoidAlgebra.coeff_mul_apply_right]
  simp_rw [hx]

/-- Uniformity is preserved by right multiplication, without commutativity of H. -/
private theorem uniformMatrix_mul_right (A B : GroupMat H n n)
    (hA : UniformMatrix A) : UniformMatrix (A*B) := by
  classical
  intro i j g
  change (∑ t, A i t * B t j).coeff g = (∑ t, A i t * B t j).coeff 1
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro t _
  exact uniform_mul_right (A i t) (B t j) (hA i t) g

/-- One uniform power implies every later power is uniform. -/
theorem uniform_power_mono (A : GroupMat H n n) {a k : ℕ}
    (hak : a ≤ k) (ha : UniformMatrix (A^a)) : UniformMatrix (A^k) := by
  rw [← Nat.add_sub_of_le hak, pow_add]
  exact uniformMatrix_mul_right (A^a) (A^(k-a)) ha

private theorem positiveTau_spec (A : GroupMat H n n) (hA : Uniformizes A) :
    0 < positiveTau A hA ∧ UniformMatrix (A^(positiveTau A hA)) := by
  classical
  exact Nat.find_spec hA

private theorem positiveTau_le (A : GroupMat H n n) (hA : Uniformizes A)
    {k : ℕ} (hk : 0 < k) (hu : UniformMatrix (A^k)) : positiveTau A hA ≤ k := by
  classical
  exact Nat.find_min' hA ⟨hk, hu⟩

/-- The output is equality in the original natural group-matrix ring. -/
private theorem equal_power_of_uniform (A B : GroupMat H n n) {k : ℕ}
    (haug : matrixAugmentation A = matrixAugmentation B)
    (hA : UniformMatrix (A^k)) (hB : UniformMatrix (B^k)) : A^k = B^k := by
  have hpow : matrixAugmentation (A^k) = matrixAugmentation (B^k) := by
    simpa only [map_pow] using congrArg (fun M => M^k) haug
  ext i j g
  exact congrArg (fun x : MonoidAlgebra ℕ H => x.coeff g)
    (uniform_eq_of_augmentation_eq ((A^k) i j) ((B^k) i j) (hA i j) (hB i j)
      (congrFun (congrFun hpow i) j))

/-- The positive-exponent convention applies also to the zero matrix. -/
private theorem one_le_tau (A : GroupMat H n n) : (1 : WithTop ℕ) ≤ tau A := by
  classical
  by_cases hA : Uniformizes A
  · have hpos : 1 ≤ positiveTau A hA := (positiveTau_spec A hA).1
    simpa [tau, hA] using hpos
  · simp [tau, hA]

/-- A finite upper bound on tau is equivalent to uniformity at that exact
positive exponent. Infinity and exponent zero are handled by the same statement. -/
theorem tau_le_iff_uniform_power (A : GroupMat H n n) (k : ℕ) :
    tau A ≤ (k : WithTop ℕ) ↔ 0 < k ∧ UniformMatrix (A^k) := by
  classical
  constructor
  · intro hbound
    by_cases hA : Uniformizes A
    · have hmin : positiveTau A hA ≤ k := by
        simpa [tau, hA] using hbound
      exact ⟨lt_of_lt_of_le (positiveTau_spec A hA).1 hmin,
        uniform_power_mono A hmin (positiveTau_spec A hA).2⟩
    · simp [tau, hA] at hbound
  · rintro ⟨hk,huniform⟩
    have hA : Uniformizes A := ⟨k,hk,huniform⟩
    simpa [tau, hA] using positiveTau_le A hA hk huniform

/-- Uniform matrices have least positive exponent one. This includes zero
matrices and every matrix over a trivial group. -/
theorem tau_eq_one_iff_uniform (A : GroupMat H n n) :
    tau A = 1 ↔ UniformMatrix A := by
  constructor
  · intro h
    have hu := ((tau_le_iff_uniform_power A 1).mp h.le).2
    simpa only [pow_one] using hu
  · intro hu
    apply le_antisymm
    · exact (tau_le_iff_uniform_power A 1).mpr ⟨by decide, by simpa only [pow_one] using hu⟩
    · exact one_le_tau A

/-- Every original admissible k yields equality in the natural group-matrix
ring. Neither positivity nor equality of powers is an additional premise. -/
theorem equal_power_of_tau_le (A B : GroupMat H n n)
    (haug : matrixAugmentation A = matrixAugmentation B)
    {k : ℕ} (hk : max (tau A) (tau B) ≤ (k : WithTop ℕ)) :
    0 < k ∧ A^k = B^k := by
  have hA := (tau_le_iff_uniform_power A k).mp ((le_max_left _ _).trans hk)
  have hB := (tau_le_iff_uniform_power B k).mp ((le_max_right _ _).trans hk)
  exact ⟨hA.1,equal_power_of_uniform A B haug hA.2 hB.2⟩

end D5.S3.FiniteGroups.NaturalGroupMatrixUniformization

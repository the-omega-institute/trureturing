/- GID: D5/S3/Quantum/Entanglement/EJMInflationScore
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJMInflationScore
   mirror-E: none(waiver:exact-inflation-certificate-consumer)
   anchors: []
   utility: none
   digest: The exact 32 EJM inflation blocks cancel under every actual local model. -/

/-
Library search: TriangleInflationSoundness owns the actual continuous lift;
Mathlib owns finite-sum reindexing. No existing module combines the original
32 marginal maps, the asymmetric BAC export order and their exact contractions.
admission_basis: escape-witness
score_expectation_zero: proof_shape: content; escape_witness: every retained
head/tail source support is checked and the expectation of the full observed
law is derived before contraction, without a symmetry assumption on that law.
The block and positivity-consumer helpers are consumed on the exact coefficient
certificate path. The coefficient functions remain arbitrary here; positivity
of the pinned upstream data is a separate mathematical obligation.
Four-slot source registration remains unfinished under issue #16309.
-/

import D5.S3.Quantum.Entanglement.EJMWightedCancellation
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJMInflationScore
open D5.S3.Quantum.Entanglement.EJMWightedCancellation
open D5.S3.Quantum.Entanglement.ElegantJointMeasurementInflation
open D5.S3.Quantum.Entanglement.TriangleInflationSoundness
open scoped BigOperators

def lhsTriangle : Fin 16 → Fin 10 → Node :=
  ![![0,1,2,10,14,18,11,15,19,7],
    ![0,3,4,10,14,18,9,13,17,6],
    ![1,5,6,11,15,19,8,12,16,4],
    ![3,5,7,9,13,17,8,12,16,2],
    ![8,9,2,5,14,18,3,15,19,7],
    ![8,11,4,5,14,18,1,13,17,6],
    ![9,10,6,3,15,19,0,12,16,4],
    ![10,11,7,0,12,16,1,13,17,2],
    ![12,13,2,5,10,18,3,11,19,7],
    ![12,15,4,5,10,18,1,9,17,6],
    ![13,14,6,3,11,19,0,8,16,4],
    ![14,15,7,0,8,16,1,9,17,2],
    ![16,17,2,5,10,14,3,11,15,7],
    ![16,19,4,5,10,14,1,9,13,6],
    ![17,18,6,3,11,15,0,8,12,4],
    ![18,19,7,0,8,12,1,9,13,2]]

def lhsSingleton : Fin 16 → Fin 9 → Node :=
  ![![0,9,11,13,15,17,19,6,7],
    ![1,8,10,12,14,16,18,4,7],
    ![3,8,10,12,14,16,18,2,6],
    ![5,9,11,13,15,17,19,2,4],
    ![8,1,3,13,15,17,19,6,7],
    ![9,0,5,12,14,16,18,4,7],
    ![10,1,3,13,15,17,19,2,4],
    ![11,0,5,12,14,16,18,2,6],
    ![12,1,3,9,11,17,19,6,7],
    ![13,0,5,8,10,16,18,4,7],
    ![14,1,3,9,11,17,19,2,4],
    ![15,0,5,8,10,16,18,2,6],
    ![16,1,3,9,11,13,15,6,7],
    ![17,0,5,8,10,12,14,4,7],
    ![18,1,3,9,11,13,15,2,4],
    ![19,0,5,8,10,12,14,2,6]]

def ejmIntNumerator (a b c : Fin 4) : ℤ :=
  if a = b ∧ b = c then 25
  else if a ≠ b ∧ b ≠ c ∧ c ≠ a then 5
  else 1

noncomputable def ejmDistribution (a b c : Fin 4) : ℝ := ejmNumerator a b c / 256

def triangleTail (i : Fin 16) : Fin 7 → Node := fun j => lhsTriangle i (Fin.natAdd 3 j)
def singletonTail (i : Fin 16) : Fin 8 → Node := fun j => lhsSingleton i (Fin.natAdd 1 j)

def triangleBlock (F : (Fin 10 → Fin 4) → ℤ) (i : Fin 16) (o : Node → Fin 4) : ℤ :=
  256 * F (o ∘ lhsTriangle i) -
    ∑ h : Fin 3 → Fin 4, ejmIntNumerator (h 0) (h 1) (h 2) *
      F (Fin.append h (o ∘ triangleTail i))

def singletonBlock (F : (Fin 9 → Fin 4) → ℤ) (i : Fin 16) (o : Node → Fin 4) : ℤ :=
  256 * F (o ∘ lhsSingleton i) -
    64 * ∑ h : Fin 1 → Fin 4, F (Fin.append h (o ∘ singletonTail i))

def score (F1 : (Fin 10 → Fin 4) → ℤ) (F2 : (Fin 9 → Fin 4) → ℤ)
    (o : Node → Fin 4) : ℤ :=
  (∑ i : Fin 16, triangleBlock F1 i o) + (∑ i : Fin 16, singletonBlock F2 i o)

private theorem numerator_cast (a b c : Fin 4) :
    (ejmIntNumerator a b c : ℝ) = ejmNumerator a b c := by
  simp only [ejmIntNumerator, ejmNumerator]
  split_ifs <;> norm_num



def triangleHead (i : Fin 16) : Fin 3 → Node :=
  fun j => lhsTriangle i (Fin.castAdd 7 j)

def singletonHead (i : Fin 16) : Fin 1 → Node :=
  fun j => lhsSingleton i (Fin.castAdd 8 j)

def triangleA (i : Fin 16) : Node :=
  if spec.party (lhsTriangle i 0) = 0 then lhsTriangle i 0 else lhsTriangle i 1
def triangleB (i : Fin 16) : Node :=
  if spec.party (lhsTriangle i 0) = 0 then lhsTriangle i 1 else lhsTriangle i 0
def triangleC (i : Fin 16) : Node := lhsTriangle i 2

theorem triangle_injective (i : Fin 16) : Function.Injective (lhsTriangle i) := by
  have h : ∀ i : Fin 16, Function.Injective (lhsTriangle i) := by decide
  exact h i

theorem singleton_injective (i : Fin 16) : Function.Injective (lhsSingleton i) := by
  have h : ∀ i : Fin 16, Function.Injective (lhsSingleton i) := by decide
  exact h i

theorem triangle_support_disjoint (i : Fin 16) :
    Disjoint (sourceSupport spec (nodeRange (triangleHead i)))
      (sourceSupport spec (nodeRange (triangleTail i))) := by
  have h : ∀ i : Fin 16, Disjoint (sourceSupport spec (nodeRange (triangleHead i)))
      (sourceSupport spec (nodeRange (triangleTail i))) := by decide
  exact h i

theorem singleton_support_disjoint (i : Fin 16) :
    Disjoint (sourceSupport spec (nodeRange (singletonHead i)))
      (sourceSupport spec (nodeRange (singletonTail i))) := by
  have h : ∀ i : Fin 16, Disjoint (sourceSupport spec (nodeRange (singletonHead i)))
      (sourceSupport spec (nodeRange (singletonTail i))) := by decide
  exact h i

private theorem triangle_head_range (i : Fin 16) :
    nodeRange (triangleHead i) = {triangleA i, triangleB i, triangleC i} := by
  have h : ∀ i : Fin 16, nodeRange (triangleHead i) =
      {triangleA i, triangleB i, triangleC i} := by decide
  exact h i

private theorem singleton_head_range (i : Fin 16) :
    nodeRange (singletonHead i) = {lhsSingleton i 0} := by
  have h : ∀ i : Fin 16, nodeRange (singletonHead i) = {lhsSingleton i 0} := by decide
  exact h i

private theorem triangle_wiring (i : Fin 16) :
    spec.party (triangleA i) = 0 ∧ spec.party (triangleB i) = 1 ∧
    spec.party (triangleC i) = 2 ∧
    spec.firstCopy (triangleB i) = spec.secondCopy (triangleA i) ∧
    spec.firstCopy (triangleC i) = spec.secondCopy (triangleB i) ∧
    spec.secondCopy (triangleC i) = spec.firstCopy (triangleA i) := by
  have h : ∀ i : Fin 16,
      spec.party (triangleA i) = 0 ∧ spec.party (triangleB i) = 1 ∧
      spec.party (triangleC i) = 2 ∧
      spec.firstCopy (triangleB i) = spec.secondCopy (triangleA i) ∧
      spec.firstCopy (triangleC i) = spec.secondCopy (triangleB i) ∧
      spec.secondCopy (triangleC i) = spec.firstCopy (triangleA i) := by decide
  exact h i

private theorem triangle_numerator_order (i : Fin 16) (o : Node → Fin 4) :
    ejmNumerator (o (triangleA i)) (o (triangleB i)) (o (triangleC i)) =
      ejmNumerator (o (lhsTriangle i 0)) (o (lhsTriangle i 1)) (o (lhsTriangle i 2)) := by
  unfold triangleA triangleB triangleC
  split_ifs <;> simp only [ejmNumerator_swap_ab]

/-- The triangle head is read in actual A,B,C party order, even for BAC maps.
No symmetry of the represented probability is assumed. -/
theorem triangle_head_mass_of_represents (R : ResponseModel)
    (p : Fin 4 → Fin 4 → Fin 4 → ℝ) (hp : Represents R p)
    (i : Fin 16) (o : Node → Fin 4) :
    marginalMass spec R (nodeRange (triangleHead i)) o =
      p (o (triangleA i)) (o (triangleB i)) (o (triangleC i)) := by
  obtain ⟨hA, hB, hC, hB₁, hC₁, hC₂⟩ := triangle_wiring i
  rw [triangle_head_range]
  have h := triangle_mass_in_BAC_order spec R p hp
    (triangleA i) (triangleB i) (triangleC i)
    (spec.secondCopy (triangleB i)) (spec.firstCopy (triangleA i))
    (spec.secondCopy (triangleA i)) o hA hB hC rfl rfl hB₁ rfl hC₁ hC₂
  simpa only [Finset.insert_comm] using h

private theorem triangle_head_mass (R : ResponseModel) (hp : Represents R ejmDistribution)
    (i : Fin 16) (o : Node → Fin 4) :
    marginalMass spec R (nodeRange (triangleHead i)) o =
      ejmNumerator (o (lhsTriangle i 0)) (o (lhsTriangle i 1)) (o (lhsTriangle i 2)) / 256 := by
  simpa only [ejmDistribution, triangle_numerator_order] using
    triangle_head_mass_of_represents R ejmDistribution hp i o

private theorem ejmNumerator_sum_B (b : Fin 4) :
    (∑ a : Fin 4, ∑ c : Fin 4, ejmNumerator a b c) = 64 := by
  simp_rw [ejmNumerator_swap_ab]
  exact ejmNumerator_sum b

/-- Every singleton block uses an A or B node, so the corresponding two uniform
one-party marginals suffice. No permutation symmetry of p is assumed. -/
theorem singleton_head_mass_of_uniform (R : ResponseModel)
    (p : Fin 4 → Fin 4 → Fin 4 → ℝ) (hp : Represents R p)
    (hA : ∀ a, (∑ b : Fin 4, ∑ c : Fin 4, p a b c) = 1 / 4)
    (hB : ∀ b, (∑ a : Fin 4, ∑ c : Fin 4, p a b c) = 1 / 4)
    (i : Fin 16) (o : Node → Fin 4) :
    marginalMass spec R (nodeRange (singletonHead i)) o = 1 / 4 := by
  rw [singleton_head_range]
  fin_cases i
  · change marginalMass spec R {0} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 0 1 2
      0 0 0 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {1} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 0 1 2
      0 0 0 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {3} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 0 3 4
      1 0 0 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {5} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 5 1 6
      0 1 0 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {8} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 8 9 2
      0 0 1 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {9} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 8 9 2
      0 0 1 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {10} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 10 9 6
      0 1 1 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {11} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 8 11 4
      1 0 1 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {12} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 12 13 2
      0 0 2 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {13} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 12 13 2
      0 0 2 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {14} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 14 13 6
      0 1 2 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {15} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 12 15 4
      1 0 2 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {16} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 16 17 2
      0 0 3 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {17} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 16 17 2
      0 0 3 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h
  · change marginalMass spec R {18} o = 1 / 4
    have h := marginalMass_singleton_A spec R p hp 18 17 6
      0 1 3 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hA] using h
  · change marginalMass spec R {19} o = 1 / 4
    have h := singleton_mass_in_B_order spec R p hp 16 19 4
      1 0 3 o (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    simpa only [hB] using h


private theorem singleton_head_mass (R : ResponseModel) (hp : Represents R ejmDistribution)
    (i : Fin 16) (o : Node → Fin 4) :
    marginalMass spec R (nodeRange (singletonHead i)) o = 1 / 4 := by
  apply singleton_head_mass_of_uniform R ejmDistribution hp
  · intro a
    simp only [ejmDistribution, ← Finset.sum_div, ejmNumerator_sum]
    norm_num
  · intro b
    simp only [ejmDistribution, ← Finset.sum_div, ejmNumerator_sum_B]
    norm_num



/-- Each original three-node centered coefficient block has zero expected
score under the actual independent-source inflation lift. -/
theorem triangle_block_expectation_zero (F : (Fin 10 → Fin 4) → ℤ)
    (R : ResponseModel) (hp : Represents R ejmDistribution) (i : Fin 16) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (triangleBlock F i o : ℝ)) = 0 := by
  classical
  have h := inflation_centered_fin_expectation (m := 3) (n := 7) spec R
    (lhsTriangle i) (triangle_injective i)
    (fun h => ejmNumerator (h 0) (h 1) (h 2)) 256 256 (-1)
    (fun a => (F a : ℝ)) (by norm_num) (triangle_support_disjoint i)
    (fun o => triangle_head_mass R hp i o)
  simpa [triangleBlock, triangleTail, Function.comp_def, numerator_cast, sub_eq_add_neg] using h

/-- Each original one-node centered coefficient block has zero expected
score; its factor 64 is the exact 256 times the uniform singleton mass. -/
theorem singleton_block_expectation_zero (F : (Fin 9 → Fin 4) → ℤ)
    (R : ResponseModel) (hp : Represents R ejmDistribution) (i : Fin 16) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (singletonBlock F i o : ℝ)) = 0 := by
  classical
  have h := inflation_centered_fin_expectation (m := 1) (n := 8) spec R
    (lhsSingleton i) (singleton_injective i) (fun _ => (1 : ℝ)) 4 256 (-64)
    (fun a => (F a : ℝ)) (by norm_num) (singleton_support_disjoint i)
    (fun o => singleton_head_mass R hp i o)
  simpa [singletonBlock, singletonTail, Function.comp_def, sub_eq_add_neg] using h

/-- Uniform A and B marginals still cancel every original singleton block,
including when the represented triangle distribution differs from the EJM target. -/
theorem singleton_block_expectation_zero_of_uniform (F : (Fin 9 → Fin 4) → ℤ)
    (R : ResponseModel) (p : Fin 4 → Fin 4 → Fin 4 → ℝ) (hp : Represents R p)
    (hA : ∀ a, (∑ b : Fin 4, ∑ c : Fin 4, p a b c) = 1 / 4)
    (hB : ∀ b, (∑ a : Fin 4, ∑ c : Fin 4, p a b c) = 1 / 4) (i : Fin 16) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (singletonBlock F i o : ℝ)) = 0 := by
  classical
  have h := inflation_centered_fin_expectation (m := 1) (n := 8) spec R
    (lhsSingleton i) (singleton_injective i) (fun _ => (1 : ℝ)) 4 256 (-64)
    (fun a => (F a : ℝ)) (by norm_num) (singleton_support_disjoint i)
    (fun o => singleton_head_mass_of_uniform R p hp hA hB i o)
  simpa [singletonBlock, singletonTail, Function.comp_def, sub_eq_add_neg] using h

private theorem expectation_sum {E I : Type*} [Fintype E] [Fintype I]
    (mass : E → ℝ) (F : I → E → ℝ) :
    (∑ e, mass e * ∑ i, F i e) = ∑ i, ∑ e, mass e * F i e := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The exact 32-block centered score cancels for arbitrary integer coefficient
functions. Thus the finite positivity proof can use the original upstream
coefficients without assumptions of symmetry on the local model. -/
theorem score_expectation_zero (F1 : (Fin 10 → Fin 4) → ℤ)
    (F2 : (Fin 9 → Fin 4) → ℤ) (R : ResponseModel)
    (hp : Represents R ejmDistribution) :
    (∑ o : Node → Fin 4, inflationMass spec R o * (score F1 F2 o : ℝ)) = 0 := by
  classical
  calc
    _ = (∑ i : Fin 16, ∑ o : Node → Fin 4,
        inflationMass spec R o * (triangleBlock F1 i o : ℝ)) +
      (∑ i : Fin 16, ∑ o : Node → Fin 4,
        inflationMass spec R o * (singletonBlock F2 i o : ℝ)) := by
      simp only [score, Int.cast_add, Int.cast_sum, mul_add, Finset.sum_add_distrib]
      rw [expectation_sum, expectation_sum]
    _ = 0 := by
      simp only [triangle_block_expectation_zero F1 R hp, singleton_block_expectation_zero F2 R hp,
        Finset.sum_const_zero, add_zero]

/-- A checked strict global bound for these exact coefficients contradicts
normalization and zero expectation of every continuous triangle-local lift. -/
theorem positive_score_excludes_triangle_local (F1 : (Fin 10 → Fin 4) → ℤ)
    (F2 : (Fin 9 → Fin 4) → ℤ) (hpositive : ∀ o : Node → Fin 4, 1 ≤ score F1 F2 o) :
    ¬ D5.S3.Quantum.Entanglement.TriangleSymmetricLocalRefutation.IsTriangleLocal
      ejmDistribution := by
  intro hlocal
  obtain ⟨R, hp⟩ := isTriangleLocal_responseModel ejmDistribution hlocal
  have hzero := score_expectation_zero F1 F2 R hp
  have hbound : 1 ≤ ∑ o : Node → Fin 4, inflationMass spec R o * (score F1 F2 o : ℝ) := by
    calc
      1 = ∑ o : Node → Fin 4, inflationMass spec R o := (inflationMass_normalized spec R).symm
      _ ≤ _ := Finset.sum_le_sum (fun o _ => by
        have hpos : (1 : ℝ) ≤ (score F1 F2 o : ℝ) := by exact_mod_cast hpositive o
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpos
          (inflationMass_nonnegative spec R o))
  linarith

#print axioms triangle_head_mass_of_represents
#print axioms singleton_head_mass_of_uniform
#print axioms singleton_block_expectation_zero_of_uniform
#print axioms score_expectation_zero
#print axioms positive_score_excludes_triangle_local

end D5.S3.Quantum.Entanglement.EJMInflationScore

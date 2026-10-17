/- GID: D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/QuantumCrystalYangianRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.claim; result=D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.result; claim=D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation.claim
   digest: Three-box removable counts refute the bosonic Yangian linear-combination conjecture. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.QuantumCrystalYangianRefutation

/-- Plane partitions are finite lower sets in the product order on three coordinates. -/
abbrev PlanePartition : Type :=
  {s : Finset (ℕ × ℕ × ℕ) // IsLowerSet (s : Set (ℕ × ℕ × ℕ))}

def boxCount (Λ : PlanePartition) : ℕ := Λ.1.card

/-- A box is removable precisely when no different box lies above it. -/
def removableCount (Λ : PlanePartition) : ℕ :=
  (Λ.1.filter fun p => ∀ q ∈ Λ.1, p ≤ q → q = p).card

abbrev State : Type := PlanePartition →₀ ℂ

def IsGrade (n : ℕ) (u : State) : Prop :=
  ∀ Λ ∈ u.support, boxCount Λ = n

/-- The negative-flip potential of (2b) counts removable boxes on each basis state. -/
noncomputable def potentialMinus : State →ₗ[ℂ] State :=
  Finsupp.linearCombination ℂ (fun Λ => Finsupp.single Λ (removableCount Λ : ℂ))

private def row : PlanePartition :=
  ⟨{(0, 0, 0), (1, 0, 0), (2, 0, 0)}, by
    intro p q hqp hp
    have lower : ∀ p ∈ ({(0, 0, 0), (1, 0, 0), (2, 0, 0)} :
        Finset (ℕ × ℕ × ℕ)), Finset.Iic p ⊆
          {(0, 0, 0), (1, 0, 0), (2, 0, 0)} := by decide
    exact lower p hp (Finset.mem_Iic.mpr hqp)⟩

private def hook : PlanePartition :=
  ⟨{(0, 0, 0), (1, 0, 0), (0, 1, 0)}, by
    intro p q hqp hp
    have lower : ∀ p ∈ ({(0, 0, 0), (1, 0, 0), (0, 1, 0)} :
        Finset (ℕ × ℕ × ℕ)), Finset.Iic p ⊆
          {(0, 0, 0), (1, 0, 0), (0, 1, 0)} := by decide
    exact lower p hp (Finset.mem_Iic.mpr hqp)⟩

private def column : PlanePartition :=
  ⟨{(0, 0, 0), (0, 1, 0), (0, 2, 0)}, by
    intro p q hqp hp
    have lower : ∀ p ∈ ({(0, 0, 0), (0, 1, 0), (0, 2, 0)} :
        Finset (ℕ × ℕ × ℕ)), Finset.Iic p ⊆
          {(0, 0, 0), (0, 1, 0), (0, 2, 0)} := by decide
    exact lower p hp (Finset.mem_Iic.mpr hqp)⟩

/-- The single-layer identity-class state of S₃: the coefficients 1, 2, 1 are χ_λ
on the identity class in (A13), as in (46) and Appendix C of arXiv:2005.09103v2. -/
noncomputable def bosonicIdentityThree : State :=
  Finsupp.single row 1 + 2 • Finsupp.single hook 1 + Finsupp.single column 1

/-- The grade and eigenvector consequences of (49)--(50), and the conjectured finite
linear combination for the negative-flip potential, restricted to the identity-class state. -/
def claim : Prop :=
  ∃ (e f φ : ℕ → State →ₗ[ℂ] State) (a b c : ℕ →₀ ℂ),
    (∀ j, IsGrade 4 (e j bosonicIdentityThree)) ∧
    (∀ j, IsGrade 2 (f j bosonicIdentityThree)) ∧
    (∀ j, ∃ t : ℂ, φ j bosonicIdentityThree = t • bosonicIdentityThree) ∧
    potentialMinus bosonicIdentityThree =
      (a.sum fun j x => x • e j bosonicIdentityThree) +
      (b.sum fun j x => x • f j bosonicIdentityThree) +
      (c.sum fun j x => x • φ j bosonicIdentityThree)

private theorem shape_data :
    boxCount row = 3 ∧ boxCount hook = 3 ∧ boxCount column = 3 ∧
    row ≠ hook ∧ row ≠ column ∧ hook ≠ column := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem removable_data :
    removableCount row = 1 ∧ removableCount hook = 2 ∧ removableCount column = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

private theorem potential_state :
    potentialMinus bosonicIdentityThree =
      Finsupp.single row 1 + 4 • Finsupp.single hook 1 + Finsupp.single column 1 := by
  rw [bosonicIdentityThree.eq_1, map_add, map_add, map_nsmul, potentialMinus.eq_1]
  simp only [Finsupp.linearCombination_single, one_smul,
    removable_data.1, removable_data.2.1, removable_data.2.2, Nat.cast_one]
  norm_num [Finsupp.smul_single]

private theorem state_coefficients :
    bosonicIdentityThree row = 1 ∧ bosonicIdentityThree hook = 2 := by
  obtain ⟨_, _, _, hrh, hrc, hhc⟩ := shape_data
  simp [bosonicIdentityThree.eq_1, Finsupp.single_apply, hrh, hrc, hhc,
    Ne.symm hrh, Ne.symm hrc, Ne.symm hhc]

private theorem grade_vanish {n : ℕ} {u : State} (h : IsGrade n u)
    (Λ : PlanePartition) (hn : boxCount Λ ≠ n) : u Λ = 0 := by
  by_contra hne
  exact hn (h Λ (Finsupp.mem_support_iff.mpr hne))

private theorem sum_relation (c : ℕ →₀ ℂ) (u : ℕ → State)
    (h : ∀ j, u j hook = 2 * u j row) :
    (c.sum fun j x => x • u j) hook = 2 * (c.sum fun j x => x • u j) row := by
  simp only [Finsupp.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h j]
  ring

/-- The three-box identity-class state obstructs the conjectured Yangian generators. -/
theorem result : ¬ claim := by
  rintro ⟨e, f, φ, a, b, c, he, hf, hφ, hid⟩
  obtain ⟨hrow, hhook, _, hrh, hrc, hhc⟩ := shape_data
  have raising (j : ℕ) : (e j bosonicIdentityThree) hook =
      2 * (e j bosonicIdentityThree) row := by
    rw [grade_vanish (he j) hook (by rw [hhook]; decide),
      grade_vanish (he j) row (by rw [hrow]; decide), mul_zero]
  have lowering (j : ℕ) : (f j bosonicIdentityThree) hook =
      2 * (f j bosonicIdentityThree) row := by
    rw [grade_vanish (hf j) hook (by rw [hhook]; decide),
      grade_vanish (hf j) row (by rw [hrow]; decide), mul_zero]
  have diagonal (j : ℕ) : (φ j bosonicIdentityThree) hook =
      2 * (φ j bosonicIdentityThree) row := by
    obtain ⟨t, ht⟩ := hφ j
    rw [ht]
    simp only [Finsupp.smul_apply, smul_eq_mul, state_coefficients.1,
      state_coefficients.2, mul_one, mul_comm]
  have relation := congrArg (fun u : State => u hook - 2 * u row) hid
  rw [potential_state] at relation
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply, if_pos rfl, if_neg hrh, if_neg hrc, if_neg hhc,
    if_neg (Ne.symm hrh), if_neg (Ne.symm hrc), if_neg (Ne.symm hhc)] at relation
  rw [sum_relation a _ raising, sum_relation b _ lowering,
    sum_relation c _ diagonal] at relation
  ring_nf at relation
  norm_num at relation

end D5.S3.StatisticalMechanics.QuantumCrystalYangianRefutation

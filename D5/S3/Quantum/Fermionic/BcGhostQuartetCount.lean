/- GID: D5/S3/Quantum/Fermionic/BcGhostQuartetCount
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostQuartetCount
   mirror-E: none(waiver:algebraic-ghost-quartet-count)
   anchors: []
   utility: none
   digest: The actual locally finite bc mode count, its spectrum and its inverse. -/

import D5.S3.Quantum.Fermionic.BcGhostFock
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Span.Defs

/-!
The carrier and the modes below are the original
CountableOccupationFock.Fock and BcGhostFock.b/c. No tensor decomposition,
spectral hypothesis, dimension bound, or positivity hypothesis is used.
The uncounted site 3 is retained throughout the full-Fock statements.
-/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostQuartetCount

/-- Positive paired mode; the artificial natural-index zero summand is zero. -/
def U (k : ℕ) : Module.End ℂ Fock :=
  if k = 0 then 0 else c (-(k : ℤ)) * b (k : ℤ) + b (-(k : ℤ)) * c (k : ℤ)

@[simp] theorem U_zero : U 0 = 0 := by simp [U]

theorem U_pos (k : ℕ) (hk : 0 < k) :
    U k = c (-(k : ℤ)) * b (k : ℤ) + b (-(k : ℤ)) * c (k : ℤ) := by
  simp [U, Nat.ne_of_gt hk]

@[simp] theorem phase_insert_self (j : ℕ) (S : Finset ℕ) :
    phase j (insert j S) = phase j S := by
  simp [phase, lowerCount, Finset.filter_insert]

@[simp] theorem phase_erase_self (j : ℕ) (S : Finset ℕ) :
    phase j (S.erase j) = phase j S := by
  have h : (S.erase j).filter (· < j) = S.filter (· < j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨ne_of_lt h.2, h.1⟩, h.2⟩⟩
  simp only [phase, lowerCount, h]

@[simp] theorem phase_square (j : ℕ) (S : Finset ℕ) :
    phase j S * phase j S = 1 := by
  unfold phase
  rw [← mul_pow]
  norm_num

/-- The signs cancel by the two actual ket actions at the same site. -/
theorem create_annihilate_ket (j : ℕ) (S : Finset ℕ) :
    (create j * annihilate j) (ket S) = if j ∈ S then ket S else 0 := by
  classical
  by_cases hj : j ∈ S
  · simp [Module.End.mul_apply, hj, map_smul, smul_smul, Finset.insert_erase hj]
  · simp [Module.End.mul_apply, hj]

/-- Reversing the two actual ket actions detects a hole, with the same sign cancellation. -/
theorem annihilate_create_ket (j : ℕ) (S : Finset ℕ) :
    (annihilate j * create j) (ket S) = if j ∈ S then 0 else ket S := by
  classical
  by_cases hj : j ∈ S
  · simp [Module.End.mul_apply, hj]
  · simp [Module.End.mul_apply, hj, map_smul, smul_smul, Finset.erase_insert hj]

theorem b_positive (k : ℕ) : b (k : ℤ) = annihilate (2 * k + 3) := by
  calc
    b (k : ℤ) = b (((k + 1 : ℕ) : ℤ) - 1) := congrArg b (by omega)
    _ = annihilate (2 * (k + 1) + 1) := (mode_correspondence (k + 1)).2.2.2
    _ = annihilate (2 * k + 3) := by congr 1

theorem c_negative (k : ℕ) : c (-(k : ℤ)) = create (2 * k + 3) := by
  calc
    c (-(k : ℤ)) = c (1 - ((k + 1 : ℕ) : ℤ)) := congrArg c (by omega)
    _ = create (2 * (k + 1) + 1) := (mode_correspondence (k + 1)).2.2.1
    _ = create (2 * k + 3) := by congr 1

@[simp] theorem b_negative_one : b (-1) = annihilate 1 := by norm_num [b]
@[simp] theorem c_positive_one : c 1 = create 1 := by norm_num [c]
@[simp] theorem b_zero : b 0 = annihilate 3 := by norm_num [b]

theorem b_negative_ge_two (k : ℕ) (hk : 2 ≤ k) :
    b (-(k : ℤ)) = create (2 * (k - 2)) := by
  calc
    b (-(k : ℤ)) = b (-((k - 2 : ℕ) : ℤ) - 2) := congrArg b (by omega)
    _ = create (2 * (k - 2)) := (mode_correspondence (k - 2)).1

theorem c_positive_ge_two (k : ℕ) (hk : 2 ≤ k) :
    c (k : ℤ) = annihilate (2 * (k - 2)) := by
  calc
    c (k : ℤ) = c (((k - 2 : ℕ) : ℤ) + 2) := congrArg c (by omega)
    _ = annihilate (2 * (k - 2)) := (mode_correspondence (k - 2)).2.1

theorem c_negative_b_positive_ket (k : ℕ) (S : Finset ℕ) :
    (c (-(k : ℤ)) * b (k : ℤ)) (ket S) =
      if 2 * k + 3 ∈ S then ket S else 0 := by
  rw [c_negative, b_positive, create_annihilate_ket]

theorem b_negative_c_positive_ket (k : ℕ) (hk : 0 < k) (S : Finset ℕ) :
    (b (-(k : ℤ)) * c (k : ℤ)) (ket S) =
      if k = 1 then (if 1 ∈ S then 0 else ket S)
      else (if 2 * (k - 2) ∈ S then ket S else 0) := by
  by_cases hk1 : k = 1
  · subst k
    simpa using annihilate_create_ket 1 S
  · have hk2 : 2 ≤ k := by omega
    rw [b_negative_ge_two k hk2, c_positive_ge_two k hk2,
      create_annihilate_ket, ite_eq_right hk1]

/-- Three elementary natural indicator counts, including the exceptional site-1 hole. -/
def localCount (k : ℕ) (S : Finset ℕ) : ℕ :=
  (if 0 < k ∧ 2 * k + 3 ∈ S then 1 else 0) +
  (if k = 1 ∧ 1 ∉ S then 1 else 0) +
  (if 2 ≤ k ∧ 2 * (k - 2) ∈ S then 1 else 0)

theorem U_ket (k : ℕ) (S : Finset ℕ) :
    U k (ket S) = (localCount k S : ℂ) • ket S := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp [localCount]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [U_pos k hk, LinearMap.add_apply, c_negative_b_positive_ket,
      b_negative_c_positive_ket k hk]
    by_cases hk1 : k = 1
    · subst k
      by_cases ho : 5 ∈ S <;> by_cases hh : 1 ∈ S <;>
        simp [localCount, ho, hh, two_smul]
    · have hk2 : 2 ≤ k := by omega
      by_cases ho : 2 * k + 3 ∈ S <;> by_cases he : 2 * (k - 2) ∈ S <;>
        simp [localCount, hk, hk1, hk2, ho, he, two_smul]

/-- All occupied sites other than 1 and 3, together with the hole at site 1. -/
def count (S : Finset ℕ) : ℕ :=
  ((S.erase 1).erase 3).card + if 1 ∈ S then 0 else 1

theorem count_insert_regular (j : ℕ) (S : Finset ℕ)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∉ S) :
    count (insert j S) = count S + 1 := by
  classical
  have he : ((insert j S).erase 1).erase 3 = insert j ((S.erase 1).erase 3) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_insert]
    aesop
  have hn : j ∉ (S.erase 1).erase 3 := by simp [hj]
  have h1 : (1 ∈ insert j S) ↔ 1 ∈ S := by simp [Ne.symm hj1]
  simp only [count, he, h1, Finset.card_insert_of_notMem hn]
  omega

theorem count_erase_regular (j : ℕ) (S : Finset ℕ)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∈ S) :
    count S = count (S.erase j) + 1 := by
  have h := count_insert_regular j (S.erase j) hj1 hj3 (Finset.notMem_erase j S)
  simpa only [Finset.insert_erase hj] using h

theorem count_insert_one (S : Finset ℕ) (h1 : 1 ∉ S) :
    count (insert 1 S) + 1 = count S := by
  simp [count, h1, Finset.erase_insert h1, Finset.erase_eq_of_notMem h1]

theorem count_erase_one (S : Finset ℕ) (h1 : 1 ∈ S) :
    count (S.erase 1) = count S + 1 := by
  have h := count_insert_one (S.erase 1) (Finset.notMem_erase 1 S)
  simpa only [Finset.insert_erase h1] using h.symm

theorem count_nonnegative (S : Finset ℕ) : 0 ≤ count S := Nat.zero_le _

/-- Exact enumeration of the two occupied-site branches; no spectral premise is used. -/
theorem sum_localCount (S : Finset ℕ) (N : ℕ) (hN : 3 ≤ N)
    (hS : ∀ j ∈ S, j + 3 ≤ N) :
    (∑ k ∈ Finset.range N, localCount k S) = count S := by
  classical
  let T := (S.erase 1).erase 3
  have ho : ((Finset.range N).filter
      (fun k => 0 < k ∧ 2 * k + 3 ∈ S)).card =
      (T.filter (fun j => j % 2 ≠ 0)).card := by
    apply Finset.card_bij (fun k _ => 2 * k + 3)
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨_, hk, hmem⟩
      simp only [T, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨by omega, by omega, hmem⟩, by omega⟩
    · intro k hk l hl he
      omega
    · intro j hj
      simp only [T, Finset.mem_filter, Finset.mem_erase] at hj
      have he : 2 * ((j - 3) / 2) + 3 = j := by omega
      have hp : 0 < (j - 3) / 2 := by omega
      refine ⟨(j - 3) / 2, Finset.mem_filter.mpr ⟨?_, hp, ?_⟩, he⟩
      · apply Finset.mem_range.mpr
        have := hS j hj.1.2.2
        omega
      · simpa only [he] using hj.1.2.2
  have he : ((Finset.range N).filter
      (fun k => 2 ≤ k ∧ 2 * (k - 2) ∈ S)).card =
      (T.filter (fun j => j % 2 = 0)).card := by
    apply Finset.card_bij (fun k _ => 2 * (k - 2))
    · intro k hk
      rcases Finset.mem_filter.mp hk with ⟨_, hk, hmem⟩
      simp only [T, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨by omega, by omega, hmem⟩, by omega⟩
    · intro k hk l hl heq
      have hk2 := (Finset.mem_filter.mp hk).2.1
      have hl2 := (Finset.mem_filter.mp hl).2.1
      omega
    · intro j hj
      simp only [T, Finset.mem_filter, Finset.mem_erase] at hj
      have heq : 2 * (j / 2 + 2 - 2) = j := by omega
      refine ⟨j / 2 + 2, Finset.mem_filter.mpr ⟨?_, by omega, ?_⟩, heq⟩
      · apply Finset.mem_range.mpr
        have := hS j hj.1.2.2
        omega
      · simpa only [heq] using hj.1.2.2
  have hos : (∑ k ∈ Finset.range N,
      if 0 < k ∧ 2 * k + 3 ∈ S then 1 else 0) =
      (T.filter (fun j => j % 2 ≠ 0)).card :=
    (Finset.card_filter _ _).symm.trans ho
  have hes : (∑ k ∈ Finset.range N,
      if 2 ≤ k ∧ 2 * (k - 2) ∈ S then 1 else 0) =
      (T.filter (fun j => j % 2 = 0)).card :=
    (Finset.card_filter _ _).symm.trans he
  have hh : (∑ k ∈ Finset.range N,
      if k = 1 ∧ 1 ∉ S then 1 else 0) = (if 1 ∈ S then 0 else 1 : ℕ) := by
    by_cases h1 : 1 ∈ S
    · simp [h1]
    · simp [h1, Finset.sum_ite_eq', Finset.mem_range, show 1 < N by omega]
  have hp := Finset.card_filter_add_card_filter_not (s := T) (fun j => j % 2 = 0)
  simp only [localCount, Finset.sum_add_distrib]
  rw [hos, hh, hes]
  change _ = T.card + _
  simpa only [ne_eq, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun n : ℕ => n + if 1 ∈ S then 0 else 1) hp

theorem localCount_zero_of_capture (S : Finset ℕ) (k : ℕ) (hk : 3 ≤ k)
    (hS : ∀ j ∈ S, j + 3 ≤ k) : localCount k S = 0 := by
  have ho : 2 * k + 3 ∉ S := by
    intro h
    have := hS _ h
    omega
  have he : 2 * (k - 2) ∉ S := by
    intro h
    have := hS _ h
    omega
  simp [localCount, ho, he, show k ≠ 1 by omega]

/-- The explicit finite union of all occupied sites of an actual state. -/
def occupied (v : Fock) : Finset ℕ := v.support.biUnion id

/-- Every potentially nonzero positive summand is strictly below this bound. -/
def capture (v : Fock) : ℕ := (occupied v).sup id + 3

theorem site_capture (v : Fock) (S : Finset ℕ) (hS : S ∈ v.support)
    (j : ℕ) (hj : j ∈ S) : j + 3 ≤ capture v := by
  have hm : j ∈ occupied v := Finset.mem_biUnion.mpr ⟨S, hS, hj⟩
  have hs : j ≤ (occupied v).sup id := Finset.le_sup (f := id) hm
  change j + 3 ≤ (occupied v).sup id + 3
  omega

theorem ket_expansion (v : Fock) :
    (∑ S ∈ v.support, v S • ket S) = v := by
  simpa [Finsupp.sum, ket] using (Finsupp.sum_single v)

theorem U_zero_above_capture (v : Fock) (k : ℕ) (hk : capture v ≤ k) :
    U k v = 0 := by
  classical
  have hk3 : 3 ≤ k := by unfold capture at hk; omega
  calc
    U k v = U k (∑ S ∈ v.support, v S • ket S) :=
      congrArg (U k) (ket_expansion v).symm
    _ = ∑ S ∈ v.support, v S • U k (ket S) := by simp only [map_sum, map_smul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [U_ket, localCount_zero_of_capture S k hk3
        (fun j hj => (site_capture v S hS j hj).trans hk)]
      simp

theorem mode_support_subset (v : Fock) :
    Function.support (fun k => U k v) ⊆ (Finset.range (capture v) : Set ℕ) := by
  intro k hk
  change U k v ≠ 0 at hk
  exact Finset.mem_range.mpr (lt_of_not_ge (fun h => hk (U_zero_above_capture v k h)))

/-- Genuine local finiteness, proved for every finite-support original Fock state. -/
theorem mode_support_finite (v : Fock) :
    (Function.support (fun k => U k v)).Finite :=
  (Finset.range (capture v)).finite_toSet.subset (mode_support_subset v)

/-- The actual locally finite mode sum, before packaging its proved linearity. -/
def modeSum (v : Fock) : Fock := ∑ᶠ k : ℕ, U k v

theorem modeSum_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) :
    modeSum v = ∑ k ∈ Finset.range N, U k v := by
  apply finsum_eq_finsetSum_of_support_subset
  intro k hk
  have hklt := Finset.mem_range.mp (mode_support_subset v hk)
  exact Finset.mem_range.mpr (hklt.trans_le hN)

/-- Additivity is justified on a common finite capture of all three actual states. -/
theorem modeSum_add (v w : Fock) : modeSum (v + w) = modeSum v + modeSum w := by
  let N := max (capture (v + w)) (max (capture v) (capture w))
  rw [modeSum_eq_sum (v + w) N (le_max_left _ _),
    modeSum_eq_sum v N ((le_max_left _ _).trans (le_max_right _ _)),
    modeSum_eq_sum w N ((le_max_right _ _).trans (le_max_right _ _))]
  simp only [map_add, Finset.sum_add_distrib]

/-- Scalar compatibility is likewise a statement about two common finite captures. -/
theorem modeSum_smul (a : ℂ) (v : Fock) : modeSum (a • v) = a • modeSum v := by
  let N := max (capture (a • v)) (capture v)
  rw [modeSum_eq_sum (a • v) N (le_max_left _ _),
    modeSum_eq_sum v N (le_max_right _ _)]
  simp only [map_smul, Finset.smul_sum]

/-- The unweighted quartet count, defined from the original modes, not from its spectrum. -/
def M : Module.End ℂ Fock where
  toFun := modeSum
  map_add' := modeSum_add
  map_smul' := modeSum_smul

theorem M_eq_modeSum (v : Fock) : M v = ∑ᶠ k : ℕ, U k v := rfl

theorem M_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) :
    M v = ∑ k ∈ Finset.range N, U k v := modeSum_eq_sum v N hN

theorem M_ket (S : Finset ℕ) : M (ket S) = (count S : ℂ) • ket S := by
  classical
  let N := max (capture (ket S)) (S.sup id + 3)
  have hN : 3 ≤ N := by dsimp [N]; omega
  have hS : ∀ j ∈ S, j + 3 ≤ N := by
    intro j hj
    have hs : j ≤ S.sup id := Finset.le_sup (f := id) hj
    dsimp [N]
    omega
  rw [M_eq_sum (ket S) N (le_max_left _ _)]
  simp only [U_ket, ← Finset.sum_smul]
  rw [← Nat.cast_sum, sum_localCount S N hN hS]

/-- A coefficient multiplier on the same original carrier; used only after deriving M. -/
def diagonal (f : Finset ℕ → ℂ) : Module.End ℂ Fock :=
  Finsupp.lsum ℂ fun S => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (f S • ket S)

@[simp] theorem diagonal_ket (f : Finset ℕ → ℂ) (S : Finset ℕ) :
    diagonal f (ket S) = f S • ket S := by
  simp only [diagonal, ket, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul]

theorem diagonal_coefficient (f : Finset ℕ → ℂ) (v : Fock) (S : Finset ℕ) :
    diagonal f v S = f S * v S := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, Finsupp.add_apply, hv, hw, mul_add]
  | single T a =>
    have hs : Finsupp.single T a = a • ket T := by simp [ket]
    rw [hs, map_smul, diagonal_ket]
    by_cases h : S = T
    · subst S
      simp [ket, smul_smul, mul_comm]
    · simp [ket, h, Ne.symm h]

theorem M_eq_diagonal : M = diagonal (fun S => (count S : ℂ)) := by
  apply end_ext
  intro S
  rw [M_ket, diagonal_ket]

/-- Exact all-state coefficient formula, including non-basis states. -/
theorem M_coefficient (v : Fock) (S : Finset ℕ) :
    M v S = (count S : ℂ) * v S := by
  rw [M_eq_diagonal, diagonal_coefficient]

theorem M_support_subset (v : Fock) : (M v).support ⊆ v.support := by
  intro S hS
  apply Finsupp.mem_support_iff.mpr
  intro hz
  exact (Finsupp.mem_support_iff.mp hS) (by rw [M_coefficient, hz, mul_zero])

/-- Every nonzero coefficient of an eigenvector has exactly its stated natural count. -/
theorem eigenvector_iff (v : Fock) (z : ℂ) :
    M v = z • v ↔ ∀ S ∈ v.support, (count S : ℂ) = z := by
  constructor
  · intro h S hS
    have he := congrArg (fun w : Fock => w S) h
    change M v S = z * v S at he
    rw [M_coefficient] at he
    have hz : ((count S : ℂ) - z) * v S = 0 := by rw [sub_mul, he, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (Finsupp.mem_support_iff.mp hS))
  · intro h
    ext S
    change M v S = z * v S
    rw [M_coefficient]
    by_cases hS : S ∈ v.support
    · rw [h S hS]
    · have hz : v S = 0 := Finsupp.notMem_support_iff.mp hS
      rw [hz, mul_zero, mul_zero]

theorem nonzero_eigenvalue_is_natural (v : Fock) (z : ℂ)
    (hv : v ≠ 0) (he : M v = z • v) : ∃ q : ℕ, z = (q : ℂ) := by
  classical
  have hs : ∃ S : Finset ℕ, v S ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext S
    exact h S
  obtain ⟨S, hS⟩ := hs
  exact ⟨count S, ((eigenvector_iff v z).mp he S (Finsupp.mem_support_iff.mpr hS)).symm⟩

/-- Every natural count is attained even with the literal relative condition. -/
theorem count_surjective_relative (q : ℕ) :
    ∃ S : Finset ℕ, 3 ∉ S ∧ count S = q := by
  classical
  induction q with
  | zero => exact ⟨{1}, by simp, by simp [count]⟩
  | succ q ih =>
    obtain ⟨S, h3, hq⟩ := ih
    let j := S.sup id + 4
    have hj1 : j ≠ 1 := by dsimp [j]; omega
    have hj3 : j ≠ 3 := by dsimp [j]; omega
    have hj : j ∉ S := by
      intro hm
      have hs : j ≤ (occupied v).sup id := Finset.le_sup (f := id) hm
      dsimp [j] at hs
      omega
    refine ⟨insert j S, by simp [Ne.symm hj3, h3], ?_⟩
    rw [count_insert_regular j S hj1 hj3 hj, hq]

/-- Projection onto both zero-count basis states of the full Fock space. -/
def P : Module.End ℂ Fock := diagonal (fun S => if count S = 0 then 1 else 0)

/-- Actual spectral inverse: inverse natural count away from zero, zero at zero. -/
def invM : Module.End ℂ Fock :=
  diagonal (fun S => if count S = 0 then 0 else (count S : ℂ)⁻¹)

@[simp] theorem P_ket (S : Finset ℕ) :
    P (ket S) = (if count S = 0 then (1 : ℂ) else 0) • ket S := diagonal_ket _ _

@[simp] theorem invM_ket (S : Finset ℕ) :
    invM (ket S) = (if count S = 0 then (0 : ℂ) else (count S : ℂ)⁻¹) • ket S :=
  diagonal_ket _ _

theorem P_coefficient (v : Fock) (S : Finset ℕ) :
    P v S = if count S = 0 then v S else 0 := by
  rw [P, diagonal_coefficient]
  split_ifs <;> simp

theorem invM_coefficient (v : Fock) (S : Finset ℕ) :
    invM v S = if count S = 0 then 0 else (count S : ℂ)⁻¹ * v S := by
  rw [invM, diagonal_coefficient]
  split_ifs <;> simp

theorem M_mul_invM : M * invM = 1 - P := by
  apply end_ext
  intro S
  by_cases h : count S = 0
  · simp [Module.End.mul_apply, M_ket, h]
  · have hc : (count S : ℂ) ≠ 0 := by exact_mod_cast h
    simp [Module.End.mul_apply, M_ket, h, hc, smul_smul]

theorem invM_mul_M : invM * M = 1 - P := by
  apply end_ext
  intro S
  by_cases h : count S = 0
  · simp [Module.End.mul_apply, M_ket, h]
  · have hc : (count S : ℂ) ≠ 0 := by exact_mod_cast h
    simp [Module.End.mul_apply, M_ket, h, hc, smul_smul]

theorem P_idempotent : P * P = P := by
  apply end_ext
  intro S
  by_cases h : count S = 0 <;> simp [Module.End.mul_apply, h]

theorem P_sq : P ^ 2 = P := by simpa only [pow_two] using P_idempotent

theorem M_mul_P : M * P = 0 := by
  apply end_ext
  intro S
  by_cases h : count S = 0 <;> simp [Module.End.mul_apply, M_ket, h]

theorem P_mul_M : P * M = 0 := by
  apply end_ext
  intro S
  by_cases h : count S = 0 <;> simp [Module.End.mul_apply, M_ket, h]

theorem invM_mul_P : invM * P = 0 := by
  apply end_ext
  intro S
  by_cases h : count S = 0 <;> simp [Module.End.mul_apply, h]

theorem P_mul_invM : P * invM = 0 := by
  apply end_ext
  intro S
  by_cases h : count S = 0 <;> simp [Module.End.mul_apply, h]

/-- Site 3 is uncounted: the full zero eigenspace has two, not one, basis states. -/
theorem count_zero_iff (S : Finset ℕ) :
    count S = 0 ↔ S = {1} ∨ S = {1, 3} := by
  classical
  have hb : count S = 0 ↔ 1 ∈ S ∧ (S.erase 1).erase 3 = ∅ := by
    by_cases h1 : 1 ∈ S <;> simp [count, h1]
  constructor
  · intro hz
    rcases hb.mp hz with ⟨h1, he⟩
    have hsites : ∀ j ∈ S, j = 1 ∨ j = 3 := by
      intro j hj
      by_contra h
      have hne1 : j ≠ 1 := fun hh => h (Or.inl hh)
      have hne3 : j ≠ 3 := fun hh => h (Or.inr hh)
      have hm : j ∈ (S.erase 1).erase 3 := by simp [hj, hne1, hne3]
      rw [he] at hm
      exact Finset.notMem_empty j hm
    by_cases h3 : 3 ∈ S
    · right
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact hsites j
      · rintro (rfl | rfl)
        · exact h1
        · exact h3
    · left
      ext j
      simp only [Finset.mem_singleton]
      constructor
      · intro hj
        exact (hsites j hj).resolve_right (fun h => h3 (h ▸ hj))
      · rintro rfl
        exact h1
  · rintro (rfl | rfl) <;> norm_num [count]

theorem P_apply (v : Fock) :
    P v = v {1} • ket {1} + v {1, 3} • ket {1, 3} := by
  classical
  ext S
  rw [P_coefficient]
  by_cases h1 : S = {1}
  · subst S
    simp [count, ket, show ({1} : Finset ℕ) ≠ {1, 3} by decide]
  · by_cases h13 : S = {1, 3}
    · subst S
      simp [count, ket, show ({1, 3} : Finset ℕ) ≠ {1} by decide]
    · have hc : count S ≠ 0 := by
        intro hz
        rcases (count_zero_iff S).mp hz with he | he
        · exact h1 he
        · exact h13 he
      simp [hc, ket, h1, h13, Ne.symm h1, Ne.symm h13]

theorem M_eq_zero_iff_P_eq_self (v : Fock) : M v = 0 ↔ P v = v := by
  constructor
  · intro hv
    have h := LinearMap.congr_fun invM_mul_M v
    change invM (M v) = v - P v at h
    rw [hv, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  · intro hv
    calc
      M v = M (P v) := congrArg M hv.symm
      _ = 0 := LinearMap.congr_fun M_mul_P v

theorem full_kernel_iff (v : Fock) :
    M v = 0 ↔ ∃ a d : ℂ, v = a • ket {1} + d • ket {1, 3} := by
  constructor
  · intro hv
    refine ⟨v {1}, v {1, 3}, ?_⟩
    exact ((M_eq_zero_iff_P_eq_self v).mp hv).symm.trans (P_apply v)
  · rintro ⟨a, d, rfl⟩
    simp [map_add, map_smul, M_ket, count]

theorem full_kernel : LinearMap.ker M =
    Submodule.span ℂ ({ket {1}, ket {1, 3}} : Set Fock) := by
  ext v
  rw [LinearMap.mem_ker, full_kernel_iff, Submodule.mem_span_pair]
  exact ⟨fun ⟨a, d, h⟩ => ⟨a, d, h.symm⟩, fun ⟨a, d, h⟩ => ⟨a, d, h.symm⟩⟩

@[simp] theorem b0_down : b 0 (ket {1}) = 0 := by
  simp [annihilate_ket]

@[simp] theorem b0_other_ground : b 0 (ket {1, 3}) = -ket {1} := by
  have hf : ({1, 3} : Finset ℕ).filter (· < 3) = {1} := by decide
  have he : ({1, 3} : Finset ℕ).erase 3 = {1} := by decide
  simp [annihilate_ket, phase, lowerCount, hf, he]

/-- Literal relative condition: every coefficient occupying site 3 vanishes. -/
theorem b0_eq_zero_iff_coefficients (v : Fock) :
    b 0 v = 0 ↔ ∀ S : Finset ℕ, 3 ∈ S → v S = 0 := by
  classical
  have hocc (w : Fock) (S : Finset ℕ) :
      (create 3 (annihilate 3 w)) S = if 3 ∈ S then w S else 0 := by
    have hd : create 3 * annihilate 3 =
        diagonal (fun T => if 3 ∈ T then 1 else 0) := by
      apply end_ext
      intro T
      rw [create_annihilate_ket, diagonal_ket]
      split_ifs <;> simp
    have hh := LinearMap.congr_fun hd w
    change create 3 (annihilate 3 w) = _ at hh
    rw [hh, diagonal_coefficient]
    split_ifs <;> simp
  constructor
  · intro hv S hS
    have he := hocc v S
    rw [← b_zero, hv, map_zero, ite_eq_left hS] at he
    exact he.symm
  · intro hv
    calc
      b 0 v = b 0 (∑ S ∈ v.support, v S • ket S) :=
        congrArg (b 0) (ket_expansion v).symm
      _ = ∑ S ∈ v.support, v S • b 0 (ket S) := by simp only [map_sum, map_smul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro S hS
        have h3 : 3 ∉ S := fun h => (Finsupp.mem_support_iff.mp hS) (hv S h)
        simp [annihilate_ket, h3]

theorem relative_kernel_iff (v : Fock) :
    (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • ket {1} := by
  constructor
  · rintro ⟨hm, hb⟩
    obtain ⟨a, d, hv⟩ := (full_kernel_iff v).mp hm
    have hd : d = 0 := by
      have hcoeff := (b0_eq_zero_iff_coefficients v).mp hb {1, 3} (by simp)
      rw [hv] at hcoeff
      simpa [ket, show ({1, 3} : Finset ℕ) ≠ {1} by decide] using hcoeff
    exact ⟨a, by simpa [hd] using hv⟩
  · rintro ⟨a, rfl⟩
    constructor
    · simp [map_smul, M_ket, count]
    · simp

theorem relative_kernel : LinearMap.ker M ⊓ LinearMap.ker (b 0) =
    Submodule.span ℂ ({ket {1}} : Set Fock) := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_ker, relative_kernel_iff,
    Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

/-- The named original relative ground, not the original empty vacuum. -/
def c1vac : Fock := c 1 vacuum

theorem c1vac_eq : c1vac = ket {1} := ghost_vacuum.2.2.1

theorem relative_kernel_c1vac (v : Fock) :
    (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • c1vac := by
  rw [c1vac_eq]
  exact relative_kernel_iff v

/-- Exact algebraic eigenvalue set; the witnessing eigenstate can be relative. -/
theorem relative_eigenvalue_iff (z : ℂ) :
    (∃ v : Fock, v ≠ 0 ∧ b 0 v = 0 ∧ M v = z • v) ↔
      ∃ q : ℕ, z = (q : ℂ) := by
  constructor
  · rintro ⟨v, hv, _, he⟩
    exact nonzero_eigenvalue_is_natural v z hv he
  · rintro ⟨q, rfl⟩
    obtain ⟨S, h3, hq⟩ := count_surjective_relative q
    refine ⟨ket S, ?_, ?_, ?_⟩
    · simp [ket]
    · simp [annihilate_ket, h3]
    · rw [M_ket, hq]

theorem eigenvalue_iff (z : ℂ) :
    (∃ v : Fock, v ≠ 0 ∧ M v = z • v) ↔ ∃ q : ℕ, z = (q : ℂ) := by
  constructor
  · rintro ⟨v, hv, he⟩
    exact nonzero_eigenvalue_is_natural v z hv he
  · intro h
    obtain ⟨v, hv, _, he⟩ := (relative_eigenvalue_iff z).mpr h
    exact ⟨v, hv, he⟩

theorem M_create_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) :
    M * create j - create j * M = create j := by
  apply end_ext
  intro S
  by_cases hj : j ∈ S
  · simp [Module.End.mul_apply, M_ket, hj]
  · have hq := count_insert_regular j S hj1 hj3 hj
    simp only [LinearMap.sub_apply, Module.End.mul_apply, create_ket, ite_eq_right hj,
      map_smul, M_ket, smul_smul]
    rw [hq, Nat.cast_add, Nat.cast_one]
    module

theorem M_annihilate_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) :
    M * annihilate j - annihilate j * M = -annihilate j := by
  apply end_ext
  intro S
  by_cases hj : j ∈ S
  · have hq : (count S : ℂ) = (count (S.erase j) : ℂ) + 1 := by
      exact_mod_cast count_erase_regular j S hj1 hj3 hj
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply,
      annihilate_ket, ite_eq_left hj, map_smul, M_ket, smul_smul]
    rw [hq]
    module
  · simp [Module.End.mul_apply, M_ket, hj]

/-- Deleting occupied site 1 creates a hole and raises the count. -/
theorem M_annihilate_one : M * annihilate 1 - annihilate 1 * M = annihilate 1 := by
  apply end_ext
  intro S
  by_cases h1 : 1 ∈ S
  · have hq := count_erase_one S h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, annihilate_ket, ite_eq_left h1,
      map_smul, M_ket, smul_smul]
    rw [hq, Nat.cast_add, Nat.cast_one]
    module
  · simp [Module.End.mul_apply, M_ket, h1]

/-- Filling the site-1 hole lowers the count. -/
theorem M_create_one : M * create 1 - create 1 * M = -create 1 := by
  apply end_ext
  intro S
  by_cases h1 : 1 ∈ S
  · simp [Module.End.mul_apply, M_ket, h1]
  · have hq : (count S : ℂ) = (count (insert 1 S) : ℂ) + 1 := by
      exact_mod_cast (count_insert_one S h1).symm
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply,
      create_ket, ite_eq_right h1, map_smul, M_ket, smul_smul]
    rw [hq]
    module

theorem M_b_negative (k : ℕ) (hk : 0 < k) :
    M * b (-(k : ℤ)) - b (-(k : ℤ)) * M = b (-(k : ℤ)) := by
  by_cases h1 : k = 1
  · subst k
    simpa using M_annihilate_one
  · rw [b_negative_ge_two k (by omega)]
    exact M_create_regular _ (by omega) (by omega)

theorem M_c_negative (k : ℕ) (hk : 0 < k) :
    M * c (-(k : ℤ)) - c (-(k : ℤ)) * M = c (-(k : ℤ)) := by
  rw [c_negative]
  exact M_create_regular _ (by omega) (by omega)

theorem M_b_positive (k : ℕ) (hk : 0 < k) :
    M * b (k : ℤ) - b (k : ℤ) * M = -b (k : ℤ) := by
  rw [b_positive]
  exact M_annihilate_regular _ (by omega) (by omega)

theorem M_c_positive (k : ℕ) (hk : 0 < k) :
    M * c (k : ℤ) - c (k : ℤ) * M = -c (k : ℤ) := by
  by_cases h1 : k = 1
  · subst k
    simpa using M_create_one
  · rw [c_positive_ge_two k (by omega)]
    exact M_annihilate_regular _ (by omega) (by omega)

end D5.S3.Quantum.Fermionic.BcGhostQuartetCount

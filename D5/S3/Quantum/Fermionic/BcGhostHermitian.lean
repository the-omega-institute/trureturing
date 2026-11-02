/- GID: D5/S3/Quantum/Fermionic/BcGhostHermitian
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostHermitian
   mirror-E: none(waiver:algebraic-bc-hermitian)
   anchors: []
   utility: none
   digest: Native signed Hermitian and c₀-relative pairings on the original infinite finite-support bc occupation Fock space. -/

import D5.S3.Quantum.Fermionic.BcGhostCharge
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
The carrier, modes, phases and charge are the original algebraic ones. All
sums are Finsupp sums; there is no completion or cutoff parameter. The
functional rho is minus the coefficient of {1,3,5}. Dagger reverses the
operator word; it does not reverse the order in which successive toggles are
applied to a ket. This module is the kernel-checked implementation of the
terminal source proposal (sha256:
1158f8f0bc6f81dca58a4766f7170ee84503404413516a6878de33799262eec1).
-/

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open private charge_insert charge_erase number_ket from
  D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostHermitian

def E : Finset ℕ := {1, 3, 5}

def tau (j : ℕ) : ℕ :=
  if j ∈ E then 6 - j else if j % 2 = 0 then j + 7 else j - 7

@[simp] theorem mem_E (j : ℕ) : j ∈ E ↔ j = 1 ∨ j = 3 ∨ j = 5 := by
  simp [E]

@[simp] theorem tau_tau (j : ℕ) : tau (tau j) = j := by
  unfold tau
  simp only [mem_E]
  split_ifs <;> omega

theorem tau_injective : Function.Injective tau :=
  Function.LeftInverse.injective tau_tau

@[simp] theorem tau_mem_E (j : ℕ) : tau j ∈ E ↔ j ∈ E := by
  unfold tau
  simp only [mem_E]
  split_ifs <;> omega

private theorem tau_mem_E_explicit (j : ℕ) :
    tau j = 1 ∨ tau j = 3 ∨ tau j = 5 ↔ j ∈ E := by
  simpa only [mem_E] using tau_mem_E j

theorem tau_even (k : ℕ) : tau (2 * k) = 2 * k + 7 := by
  have he : 2 * k ∉ E := by simp only [mem_E]; omega
  simp [tau, he]

theorem tau_odd_bulk (k : ℕ) (hk : 3 ≤ k) :
    tau (2 * k + 1) = 2 * k + 1 - 7 := by
  have he : 2 * k + 1 ∉ E := by simp only [mem_E]; omega
  simp [tau, he]

/-- This is the literal exceptional-complement / bulk-image partner. -/
def partner (S : Finset ℕ) : Finset ℕ :=
  (S \ E).image tau ∪ (E \ (S ∩ E).image tau)

@[simp] theorem mem_partner (j : ℕ) (S : Finset ℕ) :
    j ∈ partner S ↔ if j ∈ E then tau j ∉ S else tau j ∈ S := by
  classical
  have himage (A : Finset ℕ) : j ∈ A.image tau ↔ tau j ∈ A := by
    constructor
    · rintro h
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp h
      simpa only [← hkj, tau_tau] using hk
    · intro h
      exact Finset.mem_image.mpr ⟨tau j, h, tau_tau j⟩
  simp only [partner, Finset.mem_union, Finset.mem_sdiff, himage,
    Finset.mem_inter, tau_mem_E]
  by_cases hj : j ∈ E <;> simp [hj]

@[simp] theorem tau_mem_partner (j : ℕ) (S : Finset ℕ) :
    tau j ∈ partner S ↔ if j ∈ E then j ∉ S else j ∈ S := by
  simpa only [tau_mem_E, tau_tau] using mem_partner (tau j) S

@[simp] theorem partner_partner (S : Finset ℕ) : partner (partner S) = S := by
  ext j
  rw [mem_partner j (partner S)]
  by_cases hj : j ∈ E
  · rw [if_pos hj, tau_mem_partner j S]
    simp [hj]
  · rw [if_neg hj, tau_mem_partner j S]
    simp [hj]

@[simp] theorem partner_empty : partner ∅ = E := by
  ext j
  simp [mem_partner]

theorem partner_insert (j : ℕ) (S : Finset ℕ) (hj : j ∉ S) :
    partner (insert j S) =
      if j ∈ E then (partner S).erase (tau j)
      else insert (tau j) (partner S) := by
  classical
  ext k
  have he : tau k = j ↔ k = tau j := by
    constructor
    · intro h; simpa only [← h, tau_tau]
    · intro h; simp [h]
  by_cases hE : j ∈ E <;> by_cases hkE : k ∈ E <;>
    simp only [Finset.mem_erase, Finset.mem_insert, mem_partner, he]
  all_goals simp [hE, hkE]
  all_goals
    have ht : k = tau j → (k ∈ E ↔ j ∈ E) := by
      intro h
      subst k
      exact tau_mem_E j
    tauto

theorem phase_real (j : ℕ) (S : Finset ℕ) : star (phase j S) = phase j S := by
  simp [phase]

theorem phase_sq (j : ℕ) (S : Finset ℕ) : phase j S * phase j S = 1 := by
  unfold phase
  rw [← pow_add, show lowerCount j S + lowerCount j S =
    2 * lowerCount j S by omega, pow_mul]
  norm_num

theorem phase_ne_zero (j : ℕ) (S : Finset ℕ) : phase j S ≠ 0 := by
  intro hz
  have h := phase_sq j S
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem phase_sign (j : ℕ) (S : Finset ℕ) :
    phase j S = 1 ∨ phase j S = -1 := by
  have hp : ∀ n : ℕ, (-1 : ℂ) ^ n = 1 ∨ (-1 : ℂ) ^ n = -1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      rcases ih with h | h <;> simp [h]
  exact hp _

theorem lowerCount_erase (j : ℕ) (S : Finset ℕ) :
    lowerCount j (S.erase j) = lowerCount j S := by
  unfold lowerCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hne, hi⟩, hlt⟩
    exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩
    exact ⟨⟨by omega, hi⟩, hlt⟩

theorem lowerCount_insert_self (j : ℕ) (S : Finset ℕ) :
    lowerCount j (insert j S) = lowerCount j S := by
  simp [lowerCount, Finset.filter_insert]

theorem phase_of_lower_bound (j : ℕ) (S : Finset ℕ)
    (h : ∀ i ∈ S, j ≤ i) : phase j S = 1 := by
  have he : S.filter (· < j) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hi
    exact not_lt_of_ge (h i hi)
  simp [phase, lowerCount, he]

theorem phase_insert_below (i j : ℕ) (S : Finset ℕ)
    (hi : i ∉ S) (hij : i < j) :
    phase j (insert i S) = -phase j S := by
  have hf : i ∉ S.filter (· < j) := by simp [hi]
  simp only [phase, lowerCount, Finset.filter_insert, if_pos hij,
    Finset.card_insert_of_notMem hf, pow_succ]
  ring

/-- Exact coefficient of the original creator, including the forbidden output. -/
theorem create_coefficient (j : ℕ) (v : Fock) (S : Finset ℕ) :
    create j v S = if j ∈ S then phase j S * v (S.erase j) else 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    split_ifs <;> ring
  | single T a =>
    have hs : Finsupp.single T a = a • ket T := by simp [ket]
    rw [hs, map_smul, create_ket]
    by_cases hT : j ∈ T
    · have he : S.erase j ≠ T := by
        intro he
        exact Finset.notMem_erase j S (he.symm ▸ hT)
      simp [hT, he, ket, eq_comm]
    · by_cases hS : j ∈ S
      · have he : insert j T = S ↔ T = S.erase j := by
          constructor
          · intro h
            simpa [Finset.erase_insert hT] using congrArg (fun U => U.erase j) h
          · intro h
            rw [h, Finset.insert_erase hS]
        by_cases heq : T = S.erase j
        · subst T
          simp [hS, hT, ket, lowerCount_erase, phase, mul_comm]
        · simp [hS, hT, he, heq, ket, eq_comm]
      · have he : insert j T ≠ S := by
          intro he; exact hS (he ▸ Finset.mem_insert_self j T)
        simp [hT, hS, he, ket, eq_comm]

/-- Exact coefficient of the original annihilator. -/
theorem annihilate_coefficient (j : ℕ) (v : Fock) (S : Finset ℕ) :
    annihilate j v S = if j ∈ S then 0 else phase j S * v (insert j S) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    split_ifs <;> ring
  | single T a =>
    have hs : Finsupp.single T a = a • ket T := by simp [ket]
    rw [hs, map_smul, annihilate_ket]
    by_cases hT : j ∈ T
    · by_cases hS : j ∈ S
      · have he : T.erase j ≠ S := by
          intro he; exact Finset.notMem_erase j T (he.symm ▸ hS)
        simp [hT, hS, he, ket, eq_comm]
      · have he : T.erase j = S ↔ T = insert j S := by
          constructor
          · intro h
            rw [← h, Finset.insert_erase hT]
          · intro h
            simp [h, hS]
        by_cases heq : T = insert j S
        · subst T
          simp [hS, ket, lowerCount_insert_self, phase, mul_comm]
        · simp [hS, hT, he, heq, ket, eq_comm]
    · have he : T ≠ insert j S := by
        intro he; exact hT (he.symm ▸ Finset.mem_insert_self j S)
      simp [hT, he, ket, eq_comm]

/-- The exceptional modes preserve creation/annihilation; bulk modes swap them. -/
def daggerMode (j : ℕ) (a : Bool) : Module.End ℂ Fock :=
  mode (tau j) (if j ∈ E then a else !a)

def dCreate (j : ℕ) : Module.End ℂ Fock := daggerMode j true
def dAnnihilate (j : ℕ) : Module.End ℂ Fock := daggerMode j false

/-- This CAR is derived from the original CAR and the explicit site involution. -/
theorem dagger_car (i j : ℕ) (a b : Bool) :
    daggerMode i a * daggerMode j b + daggerMode j b * daggerMode i a =
      if i = j ∧ a ≠ b then (1 : Module.End ℂ Fock) else 0 := by
  unfold daggerMode
  rw [car]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ E <;> cases a <;> cases b <;> simp [hi]
  · have ht : tau i ≠ tau j := fun h => hij (tau_injective h)
    simp [hij, ht]

theorem dCreate_anticommute (i j : ℕ) :
    dCreate i * dCreate j + dCreate j * dCreate i = 0 := by
  simpa [dCreate] using dagger_car i j true true

theorem dCreate_square (j : ℕ) : dCreate j * dCreate j = 0 := by
  have h : (2 : ℂ) • (dCreate j * dCreate j) = 0 := by
    simpa only [two_smul] using dCreate_anticommute j j
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

def rho : Fock →ₗ[ℂ] ℂ := -(Finsupp.lapply E)

/-- Head first on the ket means tail first in the functional composition. -/
def rowList : List ℕ → Fock →ₗ[ℂ] ℂ
  | [] => rho
  | j :: w => (rowList w).comp (dCreate j)

/-- A literal reverse-ordered dagger product. -/
def daggerWord : List ℕ → Module.End ℂ Fock
  | [] => 1
  | j :: w => daggerWord w * dCreate j

theorem rowList_daggerWord (w : List ℕ) (y : Fock) :
    rowList w y = rho (daggerWord w y) := by
  induction w generalizing y with
  | nil => rfl
  | cons j w ih => simpa only [rowList, LinearMap.comp_apply,
      daggerWord, Module.End.mul_apply] using ih (dCreate j y)

def row (S : Finset ℕ) : Fock →ₗ[ℂ] ℂ := rowList (S.sort (· ≤ ·))

/-- Epsilon is a finite literal CAR-toggle computation, with no compatibility axiom. -/
def epsList : List ℕ → ℂ
  | [] => -1
  | j :: w => epsList w * phase (tau j) (partner w.toFinset)

def eps (S : Finset ℕ) : ℂ := epsList (S.sort (· ≤ ·))

theorem rowList_coefficient (w : List ℕ) (hw : w.Nodup) (y : Fock) :
    rowList w y = epsList w * y (partner w.toFinset) := by
  revert hw y
  induction w with
  | nil => intro hw y; simp [rowList, rho, epsList]
  | cons j w ih =>
    intro hw y
    obtain ⟨hj, hw⟩ := List.nodup_cons.mp hw
    have hjF : j ∉ w.toFinset := by simpa using hj
    simp only [rowList, LinearMap.comp_apply, ih hw, epsList,
      List.toFinset_cons, partner_insert j w.toFinset hjF]
    by_cases he : j ∈ E
    · have ht : tau j ∈ partner w.toFinset := by
        simp [mem_partner, tau_mem_E_explicit, he, hjF]
      have hte : tau j ∈ E := (tau_mem_E j).mpr he
      simp [dCreate, daggerMode, mode, he, hte, create_coefficient, ht, mul_assoc]
    · have ht : tau j ∉ partner w.toFinset := by
        simp [mem_partner, tau_mem_E_explicit, he, hjF]
      have hte : tau j ∉ E := (tau_mem_E j).not.mpr he
      simp [dCreate, daggerMode, mode, he, hte, annihilate_coefficient, ht, mul_assoc]

theorem row_coefficient (S : Finset ℕ) (y : Fock) :
    row S y = eps S * y (partner S) := by
  simpa only [row, eps, Finset.sort_toFinset] using
    rowList_coefficient (S.sort (· ≤ ·)) (S.sort_nodup _) y

theorem epsList_sign (w : List ℕ) : epsList w = 1 ∨ epsList w = -1 := by
  induction w with
  | nil => simp [epsList]
  | cons j w ih =>
    rcases ih with h | h <;>
      rcases phase_sign (tau j) (partner w.toFinset) with hp | hp <;>
      simp [epsList, h, hp]

theorem eps_sign (S : Finset ℕ) : eps S = 1 ∨ eps S = -1 := epsList_sign _

theorem eps_ne_zero (S : Finset ℕ) : eps S ≠ 0 := by
  rcases eps_sign S with h | h <;> simp [h]

theorem eps_real (S : Finset ℕ) : star (eps S) = eps S := by
  rcases eps_sign S with h | h <;> simp [h]

def Hg (x y : Fock) : ℂ := x.sum fun S a => star a * row S y

theorem Hg_signed_coefficient (x y : Fock) :
    Hg x y = ∑ S ∈ x.support, star (x S) * eps S * y (partner S) := by
  simp only [Hg, Finsupp.sum, row_coefficient, mul_assoc]

@[simp] theorem Hg_zero_left (y : Fock) : Hg 0 y = 0 := by simp [Hg]
@[simp] theorem Hg_zero_right (x : Fock) : Hg x 0 = 0 := by simp [Hg]

theorem Hg_add_left (x z y : Fock) : Hg (x + z) y = Hg x y + Hg z y := by
  unfold Hg
  exact Finsupp.sum_add_index' (by intro S; simp)
    (by intro S a b; simp [add_mul])

theorem Hg_smul_left (a : ℂ) (x y : Fock) : Hg (a • x) y = star a * Hg x y := by
  unfold Hg
  rw [Finsupp.sum_smul_index' (by intro S; simp)]
  simp only [smul_eq_mul, star_mul]
  change (Finset.sum x.support (fun S => star (x S) * star a * row S y)) =
    star a * (Finset.sum x.support (fun S => star (x S) * row S y))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem Hg_add_right (x y z : Fock) : Hg x (y + z) = Hg x y + Hg x z := by
  simp [Hg, map_add, mul_add, Finsupp.sum_add]

theorem Hg_smul_right (a : ℂ) (x y : Fock) : Hg x (a • y) = a * Hg x y := by
  simp [Hg, map_smul, Finsupp.sum, Finset.mul_sum, mul_left_comm, mul_assoc]

theorem Hg_neg_left (x y : Fock) : Hg (-x) y = -Hg x y := by
  simpa using Hg_smul_left (-1) x y

theorem Hg_sub_left (x z y : Fock) : Hg (x - z) y = Hg x y - Hg z y := by
  simp [sub_eq_add_neg, Hg_add_left, Hg_neg_left]

@[simp] theorem Hg_ket_left (S : Finset ℕ) (y : Fock) : Hg (ket S) y = row S y := by
  simp [Hg, ket]

theorem Hg_ket_coefficient (S : Finset ℕ) (y : Fock) :
    Hg (ket S) y = eps S * y (partner S) := by
  rw [Hg_ket_left, row_coefficient]

theorem Hg_ket_ket (S T : Finset ℕ) :
    Hg (ket S) (ket T) = if T = partner S then eps S else 0 := by
  rw [Hg_ket_coefficient]
  by_cases h : T = partner S
  · simp [h, ket]
  · simp [h, ket]

theorem Hg_right_ket (x : Fock) (T : Finset ℕ) :
    Hg x (ket T) = star (x (partner T)) * eps (partner T) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [Hg_add_left, hf, hg, add_mul]
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    have he : T = partner S ↔ S = partner T := by
      constructor <;> intro h
      · simpa only [h, partner_partner]
      · simpa only [h, partner_partner]
    rw [hs, Hg_smul_left, Hg_ket_ket]
    by_cases h : S = partner T <;> simp [he, h, ket, eq_comm]

theorem Hg_left_radical (x : Fock) (hx : ∀ y, Hg x y = 0) : x = 0 := by
  ext S
  have h := hx (ket (partner S))
  rw [Hg_right_ket, partner_partner] at h
  have hz : star (x S) = 0 := (mul_eq_zero.mp h).resolve_right (eps_ne_zero S)
  simpa using congrArg star hz

theorem Hg_right_radical (y : Fock) (hy : ∀ x, Hg x y = 0) : y = 0 := by
  ext S
  have h := hy (ket (partner S))
  rw [Hg_ket_coefficient, partner_partner] at h
  exact (mul_eq_zero.mp h).resolve_left (eps_ne_zero _)

theorem rowList_sorted (w : List ℕ) (hw : w.Nodup)
    (hs : w.Pairwise (· ≤ ·)) : row w.toFinset = rowList w := by
  unfold row
  rw [(List.toFinset_sort (· ≤ ·) hw).mpr hs]

theorem row_insert_min (j : ℕ) (S : Finset ℕ) (hj : j ∉ S)
    (hs : ∀ i ∈ S, j ≤ i) (y : Fock) :
    row (insert j S) y = row S (dCreate j y) := by
  rw [row, Finset.sort_insert (· ≤ ·) hs hj]
  rfl

/-- Inserting an arbitrary creator retains exactly the source lowerCount sign.
The proof moves it through the sorted word one CAR transposition at a time. -/
theorem rowList_insert (w : List ℕ) (hw : w.Nodup)
    (hs : w.Pairwise (· ≤ ·)) (j : ℕ) (y : Fock) :
    rowList w (dCreate j y) =
      if j ∈ w.toFinset then 0
      else phase j w.toFinset * row (insert j w.toFinset) y := by
  revert hw hs j y
  induction w with
  | nil =>
    intro hw hs j y
    simp only [List.toFinset_nil, Finset.notMem_empty, if_false,
      phase, lowerCount, Finset.filter_empty, Finset.card_empty, pow_zero, one_mul]
    symm
    simpa [row] using row_insert_min j ∅ (by simp) (by simp) y
  | cons i w ih =>
    intro hw hs j y
    obtain ⟨hi, hw⟩ := List.nodup_cons.mp hw
    obtain ⟨hbound, hs⟩ := List.pairwise_cons.mp hs
    have hiF : i ∉ w.toFinset := by simpa using hi
    have hb : ∀ k ∈ w.toFinset, i ≤ k := by simpa using hbound
    by_cases hji : j = i
    · subst j
      have hz : dCreate i (dCreate i y) = 0 :=
        LinearMap.congr_fun (dCreate_square i) y
      simp [rowList, hz]
    · by_cases hlt : j < i
      · have hmin : ∀ k ∈ (i :: w).toFinset, j ≤ k := by
          intro k hk
          simp only [List.toFinset_cons, Finset.mem_insert] at hk
          rcases hk with rfl | hk
          · omega
          · exact le_trans (Nat.le_of_lt hlt) (hb k hk)
        have hjF : j ∉ (i :: w).toFinset := by
          intro h
          simp only [List.toFinset_cons, Finset.mem_insert] at h
          rcases h with h | h
          · exact hji h
          · have := hb j h; omega
        rw [if_neg hjF, phase_of_lower_bound j _ hmin, one_mul,
          row_insert_min j _ hjF hmin,
          rowList_sorted (i :: w) (List.nodup_cons.mpr ⟨hi, hw⟩)
            (List.pairwise_cons.mpr ⟨hbound, hs⟩)]
      · have hij : i < j := by omega
        have hswap : dCreate i (dCreate j y) = -dCreate j (dCreate i y) := by
          have h := LinearMap.congr_fun (dCreate_anticommute i j) y
          change dCreate i (dCreate j y) + dCreate j (dCreate i y) = 0 at h
          exact eq_neg_of_add_eq_zero_left h
        simp only [rowList, LinearMap.comp_apply, hswap, map_neg]
        rw [ih hw hs j (dCreate i y)]
        by_cases hj : j ∈ w.toFinset
        · simp [hj]
        · have hiI : i ∉ insert j w.toFinset := by simp [hiF, hji, Ne.symm hji]
          have hmin : ∀ k ∈ insert j w.toFinset, i ≤ k := by
            intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk
            · omega
            · exact hb k hk
          have hjcons : j ∉ (i :: w).toFinset := by simp [hji, hj]
          rw [if_neg hj, if_neg hjcons]
          simp only [List.toFinset_cons]
          change -(phase j w.toFinset * row (insert j w.toFinset) (dCreate i y)) =
            phase j (insert i w.toFinset) * row (insert j (insert i w.toFinset)) y
          rw [Finset.insert_comm j i,
            row_insert_min i (insert j w.toFinset) hiI hmin,
            phase_insert_below i j w.toFinset hiF hij]
          ring

theorem row_create (j : ℕ) (S : Finset ℕ) (y : Fock) :
    row S (dCreate j y) =
      if j ∈ S then 0 else phase j S * row (insert j S) y := by
  simpa only [row, Finset.sort_toFinset] using
    rowList_insert (S.sort (· ≤ ·)) (S.sort_nodup _) (S.pairwise_sort _) j y

/-- Genuine creator adjointness, with the original creation phase. -/
theorem Hg_create (j : ℕ) (x y : Fock) :
    Hg (create j x) y = Hg x (dCreate j y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Hg_add_left, hf, hg]
  | single S a =>
    have ha : Finsupp.single S a = a • ket S := by simp [ket]
    rw [ha, map_smul, Hg_smul_left, Hg_smul_left]
    congr 1
    by_cases hj : j ∈ S
    · simp [create_ket, hj, row_create]
    · simp [create_ket, hj, Hg_smul_left, phase_real, row_create]

theorem rho_dAnnihilate (j : ℕ) (y : Fock) : rho (dAnnihilate j y) = 0 := by
  by_cases hj : j ∈ E
  · have ht : tau j ∈ E := (tau_mem_E j).mpr hj
    simp [rho, dAnnihilate, daggerMode, mode, hj, annihilate_coefficient, ht]
  · have ht : tau j ∉ E := (tau_mem_E j).not.mpr hj
    simp [rho, dAnnihilate, daggerMode, mode, hj, ht, create_coefficient]

theorem annihilate_create (k j : ℕ) (x : Fock) :
    annihilate k (create j x) =
      (if k = j then x else 0) - create j (annihilate k x) := by
  have h := LinearMap.congr_fun (car k j false true) x
  have h' : annihilate k (create j x) + create j (annihilate k x) =
      if k = j then x else 0 := by
    by_cases he : k = j <;> simpa [mode, he, Module.End.mul_apply] using h
  exact eq_sub_of_add_eq h'

theorem dAnnihilate_dCreate (k j : ℕ) (y : Fock) :
    dAnnihilate k (dCreate j y) + dCreate j (dAnnihilate k y) =
      if k = j then y else 0 := by
  have h := LinearMap.congr_fun (dagger_car k j false true) y
  by_cases he : k = j <;>
    simpa [dAnnihilate, dCreate, he, Module.End.mul_apply] using h

/-- Genuine annihilator adjointness, derived by CAR induction on occupations. -/
theorem Hg_annihilate_ket (k : ℕ) (S : Finset ℕ) (y : Fock) :
    Hg (annihilate k (ket S)) y = Hg (ket S) (dAnnihilate k y) := by
  classical
  induction S using Finset.induction_on generalizing y with
  | empty =>
    change Hg (annihilate k vacuum) y = Hg vacuum (dAnnihilate k y)
    rw [annihilate_vacuum, Hg_zero_left, vacuum, Hg_ket_left]
    simpa [row, rowList] using (rho_dAnnihilate k y).symm
  | @insert j S hj ih =>
    have hstep : Hg (annihilate k (create j (ket S))) y =
        Hg (create j (ket S)) (dAnnihilate k y) := by
      rw [annihilate_create, Hg_sub_left, Hg_create, ih, Hg_create]
      have h := congrArg (fun z => Hg (ket S) z) (dAnnihilate_dCreate k j y)
      rw [Hg_add_right] at h
      by_cases he : k = j <;> simp only [he, if_true, if_false, Hg_zero_left,
        Hg_zero_right] at h ⊢ <;> linear_combination -h
    rw [create_ket, if_neg hj, map_smul, Hg_smul_left, Hg_smul_left] at hstep
    exact mul_left_cancel₀ (by simpa [phase_real] using phase_ne_zero j S) hstep

theorem Hg_annihilate (j : ℕ) (x y : Fock) :
    Hg (annihilate j x) y = Hg x (dAnnihilate j y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Hg_add_left, hf, hg]
  | single S a =>
    have ha : Finsupp.single S a = a • ket S := by simp [ket]
    simp only [ha, map_smul, Hg_smul_left, Hg_annihilate_ket]

theorem Hg_mode (j : ℕ) (a : Bool) (x y : Fock) :
    Hg (mode j a x) y = Hg x (daggerMode j a y) := by
  cases a
  · exact Hg_annihilate j x y
  · exact Hg_create j x y

theorem Hg_daggerMode (j : ℕ) (a : Bool) (x y : Fock) :
    Hg (daggerMode j a x) y = Hg x (mode j a y) := by
  unfold daggerMode
  rw [Hg_mode]
  simp only [daggerMode, tau_tau, tau_mem_E]
  by_cases hj : j ∈ E <;> cases a <;> simp [hj]

theorem Hg_dCreate (j : ℕ) (x y : Fock) :
    Hg (dCreate j x) y = Hg x (create j y) := Hg_daggerMode j true x y

theorem Hg_vacuum_left (y : Fock) : Hg vacuum y = -y E := by
  simp [vacuum, Hg_ket_left, row, rowList, rho]

theorem Hg_vacuum_symmetry (y : Fock) : Hg vacuum y = star (Hg y vacuum) := by
  rw [Hg_vacuum_left]
  have heps : eps E = -1 := by
    have hsort : E.sort (· ≤ ·) = [1, 3, 5] := by
      have hE : ([1, 3, 5] : List ℕ).toFinset = E := by
        ext i
        simp [E]
      rw [← hE]
      exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by simp)
    rw [eps, hsort]
    have h35 : partner ({3, 5} : Finset ℕ) = {5} := by decide
    have h5 : partner ({5} : Finset ℕ) = {3, 5} := by decide
    have h0 : partner (∅ : Finset ℕ) = E := partner_empty
    simp [epsList, h35, h5, h0]
    have hp1 : phase 1 E = 1 :=
      phase_of_lower_bound 1 E (by intro i hi; simp [E] at hi; omega)
    have hp3 : phase 3 ({3, 5} : Finset ℕ) = 1 :=
      phase_of_lower_bound 3 ({3, 5} : Finset ℕ)
        (by intro i hi; simp at hi; omega)
    have hp5 : phase 5 ({5} : Finset ℕ) = 1 :=
      phase_of_lower_bound 5 ({5} : Finset ℕ) (by
        intro i hi
        have hi' : i = 5 := by simpa using hi
        simpa [hi'])
    simp [tau, hp1, hp3, hp5]
  change -y E = star (Hg y (ket (∅ : Finset ℕ)))
  rw [Hg_right_ket, partner_empty, heps]
  simp

/-- Ordinary Hermitian symmetry; it is not supplied as a metric certificate. -/
theorem Hg_hermitian_ket (S : Finset ℕ) (y : Fock) :
    Hg (ket S) y = star (Hg y (ket S)) := by
  classical
  induction S using Finset.induction_on generalizing y with
  | empty => exact Hg_vacuum_symmetry y
  | @insert j S hj ih =>
    have hstep : Hg (create j (ket S)) y = star (Hg y (create j (ket S))) := by
      rw [Hg_create, ih, Hg_dCreate]
    simp only [create_ket, if_neg hj, Hg_smul_left, Hg_smul_right,
      star_mul, phase_real] at hstep
    apply mul_left_cancel₀ (phase_ne_zero j S)
    calc
      phase j S * Hg (ket (insert j S)) y =
          star (Hg y (ket (insert j S))) * phase j S := hstep
      _ = phase j S * star (Hg y (ket (insert j S))) := by ring

theorem Hg_hermitian (x y : Fock) : Hg x y = star (Hg y x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [Hg_add_left, Hg_add_right, hf, hg]
  | single S a =>
    have ha : Finsupp.single S a = a • ket S := by simp [ket]
    simp only [ha, Hg_smul_left, Hg_smul_right, star_mul, Hg_hermitian_ket]
    ring

theorem eps_partner (S : Finset ℕ) : eps (partner S) = eps S := by
  have h := Hg_hermitian (ket S) (ket (partner S))
  rw [Hg_ket_ket, Hg_ket_ket, partner_partner] at h
  simpa [eps_real] using h.symm

theorem Hg_literal_dagger (S : Finset ℕ) (y : Fock) :
    Hg (ket S) y = rho (daggerWord (S.sort (· ≤ ·)) y) := by
  rw [Hg_ket_left, row, rowList_daggerWord]

theorem dCreate_even (k : ℕ) : dCreate (2 * k) = annihilate (2 * k + 7) := by
  have he : 2 * k ∉ E := by simp only [mem_E]; omega
  simp [dCreate, daggerMode, mode, he, tau_even]

theorem dAnnihilate_even (k : ℕ) : dAnnihilate (2 * k) = create (2 * k + 7) := by
  have he : 2 * k ∉ E := by simp only [mem_E]; omega
  simp [dAnnihilate, daggerMode, mode, he, tau_even]

theorem dCreate_odd_bulk (k : ℕ) (hk : 3 ≤ k) :
    dCreate (2 * k + 1) = annihilate (2 * k + 1 - 7) := by
  have he : 2 * k + 1 ∉ E := by simp only [mem_E]; omega
  simp [dCreate, daggerMode, mode, he, tau_odd_bulk k hk]

theorem dAnnihilate_odd_bulk (k : ℕ) (hk : 3 ≤ k) :
    dAnnihilate (2 * k + 1) = create (2 * k + 1 - 7) := by
  have he : 2 * k + 1 ∉ E := by simp only [mem_E]; omega
  simp [dAnnihilate, daggerMode, mode, he, tau_odd_bulk k hk]

/-- Every integer b mode, including both cuts and all three exceptional sites. -/
theorem Hg_b (m : ℤ) (x y : Fock) : Hg (b m x) y = Hg x (b (-m) y) := by
  by_cases hm : m ≤ -2
  · have hn : ¬ -m ≤ -2 := by omega
    simp only [b, if_pos hm, if_neg hn]
    rw [Hg_create, dCreate_even]
    have he : 2 * (-m - 2).toNat + 7 = 2 * (-m + 1).toNat + 1 := by omega
    rw [he]
  · by_cases hp : 2 ≤ m
    · have hn : -m ≤ -2 := by omega
      have hk : 3 ≤ (m + 1).toNat := by omega
      simp only [b, if_neg hm, if_pos hn]
      rw [Hg_annihilate, dAnnihilate_odd_bulk _ hk]
      have he : 2 * (m + 1).toNat + 1 - 7 = 2 * (- -m - 2).toNat := by omega
      rw [he]
    · have hlo : -1 ≤ m := by omega
      have hhi : m ≤ 1 := by omega
      interval_cases m <;>
        simp [b, Hg_annihilate, dAnnihilate, daggerMode, mode, tau, E]

/-- Every integer c mode, with the original vacuum cut n ≤ 1. -/
theorem Hg_c (n : ℤ) (x y : Fock) : Hg (c n x) y = Hg x (c (-n) y) := by
  by_cases hp : 2 ≤ n
  · have hn : ¬ n ≤ 1 := by omega
    have hm : -n ≤ 1 := by omega
    simp only [c, if_neg hn, if_pos hm]
    rw [Hg_annihilate, dAnnihilate_even]
    have he : 2 * (n - 2).toNat + 7 = 2 * (1 - -n).toNat + 1 := by omega
    rw [he]
  · by_cases hn : n ≤ -2
    · have hcut : n ≤ 1 := by omega
      have hm : ¬ -n ≤ 1 := by omega
      have hk : 3 ≤ (1 - n).toNat := by omega
      simp only [c, if_pos hcut, if_neg hm]
      rw [Hg_create, dCreate_odd_bulk _ hk]
      have he : 2 * (1 - n).toNat + 1 - 7 = 2 * (-n - 2).toNat := by omega
      rw [he]
    · have hlo : -1 ≤ n := by omega
      have hhi : n ≤ 1 := by omega
      interval_cases n <;>
        simp [c, Hg_create, dCreate, daggerMode, mode, tau, E]

theorem siteSign_exceptional (j : ℕ) (hj : j ∈ E) : siteSign j = 1 := by
  simp only [mem_E] at hj
  rcases hj with rfl | rfl | rfl <;> norm_num [siteSign]

theorem siteSign_tau_bulk (j : ℕ) (hj : j ∉ E) :
    siteSign (tau j) = -siteSign j := by
  unfold tau siteSign
  simp only [if_neg hj]
  split_ifs <;> simp only [mem_E] at hj <;> omega

/-- The original signed ghost charge, with no shifted or replacement number. -/
theorem charge_partner (S : Finset ℕ) : charge S + charge (partner S) = 3 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hE : charge E = 3 := by
      decide
    rw [partner_empty, hE]
    simp [charge]
  | @insert j S hj ih =>
    rw [charge_insert j S hj, partner_insert j S hj]
    by_cases he : j ∈ E
    · have hte : tau j ∈ E := (tau_mem_E j).mpr he
      have ht : tau j ∈ partner S := by simp [mem_partner, hte, he, hj]
      rw [if_pos he, charge_erase _ _ ht,
        siteSign_exceptional j he,
        siteSign_exceptional (tau j) ((tau_mem_E j).mpr he)]
      omega
    · have hte : tau j ∉ E := (tau_mem_E j).not.mpr he
      have ht : tau j ∉ partner S := by simp [mem_partner, hte, he, hj]
      rw [if_neg he, charge_insert _ _ ht, siteSign_tau_bulk j he]
      omega

theorem ghostNumber_coefficient (x : Fock) (S : Finset ℕ) :
    ghostNumber x S = (charge S : ℂ) * x S := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg, mul_add]
  | single T a =>
    have ha : Finsupp.single T a = a • ket T := by simp [ket]
    by_cases he : T = S
    · subst T
      rw [ha, map_smul, number_ket]
      simp [ket, mul_comm]
    · rw [ha, map_smul, number_ket]
      simp [ket, he, Ne.symm he]

/-- Diagonal number is contragredient to 3 minus itself for this signed form. -/
theorem Hg_ghostNumber (x y : Fock) :
    Hg (ghostNumber x) y = Hg x ((3 : ℂ) • y - ghostNumber y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, Hg_add_left, hf, hg]
  | single S a =>
    have ha : Finsupp.single S a = a • ket S := by simp [ket]
    rw [ha, map_smul, Hg_smul_left, Hg_smul_left, number_ket,
      Hg_smul_left, Hg_ket_coefficient, Hg_ket_coefficient]
    simp only [star_intCast, Finsupp.sub_apply, Finsupp.smul_apply,
      smul_eq_mul, ghostNumber_coefficient]
    have hc : (charge S : ℂ) + (charge (partner S) : ℂ) = 3 := by
      exact_mod_cast charge_partner S
    linear_combination star a * eps S * y (partner S) * hc

/-- Homogeneity means actual coefficient support at the original charge. -/
def Homogeneous (g : ℤ) (x : Fock) : Prop :=
  ∀ S, x S ≠ 0 → charge S = g

theorem homogeneous_iff_number (g : ℤ) (x : Fock) :
    Homogeneous g x ↔ ghostNumber x = (g : ℂ) • x := by
  constructor
  · intro h
    ext S
    by_cases hx : x S = 0
    · simp [ghostNumber_coefficient, hx]
    · simp [ghostNumber_coefficient, h S hx]
  · intro h S hx
    have hs := congrArg (fun z : Fock => z S) h
    simp only [ghostNumber_coefficient, Finsupp.smul_apply, smul_eq_mul] at hs
    have hc : (charge S : ℂ) = (g : ℂ) := mul_right_cancel₀ hx hs
    exact_mod_cast hc

theorem Hg_charge_selection (g h : ℤ) (x y : Fock)
    (hx : Homogeneous g x) (hy : Homogeneous h y) (hgh : g + h ≠ 3) :
    Hg x y = 0 := by
  classical
  unfold Hg
  apply Finset.sum_eq_zero
  intro S hS
  change star (x S) * row S y = 0
  rw [row_coefficient]
  have hxs : x S ≠ 0 := Finsupp.mem_support_iff.mp hS
  have hys : y (partner S) = 0 := by
    by_contra hn
    have hc := charge_partner S
    rw [hx S hxs, hy (partner S) hn] at hc
    exact hgh hc
  simp [hys]

@[simp] theorem b_zero : b 0 = annihilate 3 := by norm_num [b]
@[simp] theorem c_zero : c 0 = create 3 := by norm_num [c]

/-- The relative carrier is the actual kernel of the original b_0. -/
def relativeSpace : Submodule ℂ Fock := LinearMap.ker (b 0)
abbrev Relative := ↥relativeSpace

theorem mem_relative_iff (x : Fock) :
    x ∈ relativeSpace ↔ ∀ S : Finset ℕ, 3 ∈ S → x S = 0 := by
  classical
  change b 0 x = 0 ↔ _
  rw [b_zero]
  constructor
  · intro hx S hS
    have h := congrArg (fun z : Fock => z (S.erase 3)) hx
    rw [annihilate_coefficient, if_neg (Finset.notMem_erase _ _),
      Finset.insert_erase hS] at h
    exact (mul_eq_zero.mp h).resolve_left (phase_ne_zero _ _)
  · intro hx
    ext S
    rw [annihilate_coefficient]
    by_cases hS : 3 ∈ S
    · simp [hS]
    · simp [hS, hx (insert 3 S) (Finset.mem_insert_self _ _)]

theorem ket_mem_relative (S : Finset ℕ) : ket S ∈ relativeSpace ↔ 3 ∉ S := by
  constructor
  · intro h hs
    have hz := (mem_relative_iff (ket S)).mp h S hs
    simpa [ket] using hz
  · intro h
    apply (mem_relative_iff _).mpr
    intro T hT
    have he : S ≠ T := by intro he; exact h (he.symm ▸ hT)
    simp [ket, he, Ne.symm he]

def relativeKet (S : Finset ℕ) (hS : 3 ∉ S) : Relative :=
  ⟨ket S, (ket_mem_relative S).mpr hS⟩

def relativePartner (S : Finset ℕ) : Finset ℕ := (partner S).erase 3

@[simp] theorem three_notMem_relativePartner (S : Finset ℕ) :
    3 ∉ relativePartner S := Finset.notMem_erase _ _

theorem three_mem_partner (S : Finset ℕ) (hS : 3 ∉ S) : 3 ∈ partner S := by
  rw [mem_partner]
  simp [E, tau, hS]

theorem partner_insert_three (S : Finset ℕ) (hS : 3 ∉ S) :
    partner (insert 3 S) = relativePartner S := by
  rw [partner_insert 3 S hS]
  simp [E, tau, relativePartner]

theorem relativePartner_involution (S : Finset ℕ) (hS : 3 ∉ S) :
    relativePartner (relativePartner S) = S := by
  calc
    relativePartner (relativePartner S) = partner (insert 3 (relativePartner S)) :=
      (partner_insert_three _ (three_notMem_relativePartner S)).symm
    _ = partner (partner S) := by
      rw [relativePartner, Finset.insert_erase (three_mem_partner S hS)]
    _ = S := partner_partner S

def relativeEps (S : Finset ℕ) : ℂ := eps S * phase 3 (partner S)

theorem relativeEps_sign (S : Finset ℕ) :
    relativeEps S = 1 ∨ relativeEps S = -1 := by
  rcases eps_sign S with h | h <;>
    rcases phase_sign 3 (partner S) with hp | hp <;>
    simp [relativeEps, h, hp]

theorem relativeEps_ne_zero (S : Finset ℕ) : relativeEps S ≠ 0 :=
  mul_ne_zero (eps_ne_zero S) (phase_ne_zero _ _)

/-- Actual c_0 insertion on actual ker(b_0), with no abstract carrier certificate. -/
def Hrel (x y : Relative) : ℂ := Hg (x : Fock) (c 0 (y : Fock))

theorem Hrel_hermitian (x y : Relative) : Hrel x y = star (Hrel y x) := by
  change Hg (x : Fock) (c 0 (y : Fock)) = star (Hg (y : Fock) (c 0 (x : Fock)))
  have hc : Hg (c 0 (x : Fock)) (y : Fock) = Hg (x : Fock) (c 0 (y : Fock)) := by
    simpa using Hg_c 0 (x : Fock) (y : Fock)
  rw [← hc]
  exact Hg_hermitian _ _

theorem Hrel_ket_coefficient (S : Finset ℕ) (hS : 3 ∉ S) (y : Relative) :
    Hrel (relativeKet S hS) y = relativeEps S * (y : Fock) (relativePartner S) := by
  change Hg (ket S) (c 0 (y : Fock)) = _
  rw [Hg_ket_coefficient, c_zero, create_coefficient,
    if_pos (three_mem_partner S hS)]
  simp only [relativeEps, relativePartner, mul_assoc]

/-- Every input still has a finite sum, now over its actual relative support. -/
theorem Hrel_signed_coefficient (x y : Relative) :
    Hrel x y = (x : Fock).sum (fun S a =>
      star a * relativeEps S * (y : Fock) (relativePartner S)) := by
  classical
  unfold Hrel Hg
  apply Finset.sum_congr rfl
  intro S hS
  have hxS : (x : Fock) S ≠ 0 := Finsupp.mem_support_iff.mp hS
  have hthree : 3 ∉ S := by
    intro h
    exact hxS ((mem_relative_iff _).mp x.property S h)
  change star ((x : Fock) S) * row S (c 0 (y : Fock)) = _
  rw [row_coefficient, c_zero, create_coefficient,
    if_pos (three_mem_partner S hthree)]
  simp only [relativeEps, relativePartner]
  ring

theorem Hrel_right_radical (y : Relative) (hy : ∀ x, Hrel x y = 0) : y = 0 := by
  apply Subtype.ext
  ext S
  by_cases hS : 3 ∈ S
  · exact (mem_relative_iff _).mp y.property S hS
  · have h := hy (relativeKet (relativePartner S) (three_notMem_relativePartner S))
    rw [Hrel_ket_coefficient, relativePartner_involution S hS] at h
    exact (mul_eq_zero.mp h).resolve_left (relativeEps_ne_zero _)

theorem Hrel_left_radical (x : Relative) (hx : ∀ y, Hrel x y = 0) : x = 0 := by
  apply Hrel_right_radical x
  intro y
  rw [Hrel_hermitian, hx y, star_zero]

theorem charge_relativePartner (S : Finset ℕ) (hS : 3 ∉ S) :
    charge S + charge (relativePartner S) = 2 := by
  rw [relativePartner, charge_erase 3 (partner S) (three_mem_partner S hS)]
  norm_num [siteSign]
  have h := charge_partner S
  omega

theorem homogeneous_c_zero (g : ℤ) (y : Fock) (hy : Homogeneous g y) :
    Homogeneous (g + 1) (c 0 y) := by
  intro S hS
  rw [c_zero, create_coefficient] at hS
  have hthree : 3 ∈ S := by
    by_contra h
    simp [h] at hS
  rw [if_pos hthree] at hS
  have hyS : y (S.erase 3) ≠ 0 := by
    intro hz; exact hS (by simp [hz])
  have hcharge := charge_insert 3 (S.erase 3) (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hthree, hy _ hyS] at hcharge
  norm_num [siteSign] at hcharge
  exact hcharge

theorem Hrel_charge_selection (g h : ℤ) (x y : Relative)
    (hx : Homogeneous g (x : Fock)) (hy : Homogeneous h (y : Fock))
    (hgh : g + h ≠ 2) : Hrel x y = 0 := by
  apply Hg_charge_selection g (h + 1) _ _ hx (homogeneous_c_zero h _ hy)
  omega

end D5.S3.Quantum.Fermionic.BcGhostHermitian

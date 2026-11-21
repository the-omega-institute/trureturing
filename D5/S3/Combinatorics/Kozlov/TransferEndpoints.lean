/- GID: D5/S3/Combinatorics/Kozlov/TransferEndpoints
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:literal-equal-shift-counting)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Mul]
   utility: none
   digest: Both equal-shift transfer laws are first-to-last entries of upper unitriangular powers. -/

import D5.S3.Combinatorics.Kozlov.LatticeCount
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

open Finset Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.Kozlov

variable {n : ℕ}

def firstState (hn : 1 ≤ n) : Fin n := ⟨0, by omega⟩

def lastState (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

private theorem state_skeleton (hn : 1 ≤ n) (i : Fin n) :
    topState hn (skeleton n (i.val + 1)) = i := by
  have ht := top_skeleton (n := n) (⟨i.val + 1, by omega⟩ : Fin (n + 1))
  apply Fin.ext
  change (top (skeleton n (i.val + 1))).toNat - 1 = i.val
  change top (skeleton n (i.val + 1)) = ((i.val + 1 : ℕ) : ℤ) at ht
  rw [ht, Int.toNat_natCast]
  omega

private theorem full_of_cond (hn : 1 ≤ n) {S : Finset (FVector n)}
    (hb : ∀ f ∈ S, Bounded f) {f : FVector n} (hf : f ∈ S) {i : Fin n}
    (hi : cond hn i f) {j : Fin (n + 1)} (hj : j.val ≤ i.val + 1) : f j = cap j :=
  full_below_indeg (hb _ hf) (lt_of_le_of_lt hj hi)

private theorem top_of_state (hn : 1 ≤ n) {f : FVector n} (hf : Fixed hn f)
    {i : Fin n} (h : topState hn f = i) : top f = (i.val : ℤ) + 1 := by
  rw [← topState_val hn hf, h]

private theorem state_is_last_iff (hn : 1 ≤ n) {f : FVector n} (hf : Fixed hn f) :
    topState hn f = lastState hn ↔ top f = (n : ℤ) := by
  have h := topState_val hn hf
  constructor
  · intro he
    rw [he] at h
    simp only [lastState] at h
    omega
  · intro he
    apply Fin.ext
    simp only [lastState]
    omega

section Endpoints

variable (hn : 1 ≤ n) (S : Finset (FVector n))
variable (hb : ∀ f ∈ S, Bounded f) (hf : ∀ f ∈ S, Fixed hn f)
variable (hs : ∀ k, 1 ≤ k → skeleton n k ∈ S)
variable (ht : ∀ f ∈ S, top f = (n : ℤ) → f = skeleton n n)

include hb hf in
theorem transfer_below {i j : Fin n} (hji : j < i) : transfer hn S i j = 0 := by
  change #((S.filter fun f => topState hn f = j ∧ cond hn i f)) = 0
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro f hf'
  obtain ⟨hmem, hstate, hcond⟩ := mem_filter.mp hf'
  let d : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  have hfull := full_of_cond hn hb hmem hcond (j := d) le_rfl
  have hp := le_top_of_pos (show 0 < f d by rw [hfull]; exact cap_pos d)
  have ht' := top_of_state hn (hf _ hmem) hstate
  have hlt : j.val < i.val := hji
  change ((i.val + 1 : ℕ) : ℤ) ≤ top f at hp
  omega

include hb hf hs in
theorem transfer_diag (i : Fin n) : transfer hn S i i = 1 := by
  change #((S.filter fun f => topState hn f = i ∧ cond hn i f)) = 1
  have he : (S.filter fun f => topState hn f = i ∧ cond hn i f) =
      {skeleton n (i.val + 1)} := by
    ext f
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hmem, hstate, hcond⟩
      funext d
      by_cases hd : d.val ≤ i.val + 1
      · simpa [skeleton, hd] using full_of_cond hn hb hmem hcond hd
      · have htop := top_of_state hn (hf _ hmem) hstate
        simpa [skeleton, hd] using
          (vanish_of_top_lt (f := f) (j := d) (by omega))
    · rintro rfl
      refine ⟨hs _ (by omega), state_skeleton hn i, ?_⟩
      apply (lt_indeg_iff (⟨i.val + 1, by omega⟩ : Fin (n + 1))
        (hb _ (hs _ (by omega)))).mpr
      intro d hd
      exact ite_eq_left hd
  rw [he, card_singleton]

include hb hf in
theorem transfer_first_row (j : Fin n) :
    transfer hn S (firstState hn) j = uG S (topState hn) j := by
  change #((S.filter fun f => topState hn f = j ∧ cond hn (firstState hn) f)) =
    #((S.filter fun f => topState hn f = j))
  congr 1
  ext f
  rw [mem_filter, mem_filter]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hmem, hstate⟩ => ⟨hmem, hstate, ?_⟩⟩
  apply (lt_indeg_iff (firstDegree hn) (hb _ hmem)).mpr
  intro d hd
  have he : d.val = 0 ∨ d.val = 1 := by
    change d.val ≤ 1 at hd
    omega
  rcases he with h0 | h1
  · rw [show d = 0 from Fin.ext h0, (hf _ hmem).1]
    simp [cap]
  · rw [show d = firstDegree hn from Fin.ext h1, (hf _ hmem).2]
    simp [cap, firstDegree]

include hb hf hs ht in
theorem transfer_last_column (i : Fin n) : transfer hn S i (lastState hn) = 1 := by
  change #((S.filter fun f => topState hn f = lastState hn ∧ cond hn i f)) = 1
  have he : (S.filter fun f => topState hn f = lastState hn ∧ cond hn i f) =
      {skeleton n n} := by
    ext f
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hmem, hstate, -⟩
      exact ht _ hmem ((state_is_last_iff hn (hf _ hmem)).mp hstate)
    · rintro rfl
      refine ⟨hs _ hn, ?_, ?_⟩
      · exact (state_is_last_iff hn (hf _ (hs _ hn))).mpr (top_skeleton (Fin.last n))
      · apply (lt_indeg_iff (⟨i.val + 1, by omega⟩ : Fin (n + 1)) (hb _ (hs _ hn))).mpr
        intro d _
        exact ite_eq_left (by omega)
  rw [he, card_singleton]

include hb hf in
theorem first_vecMul :
    (Pi.single (firstState hn) (1 : ℕ)) ᵥ* transfer hn S = uG S (topState hn) := by
  funext j
  change Pi.single (firstState hn) (1 : ℕ) ⬝ᵥ (fun i => transfer hn S i j) = _
  rw [single_dotProduct, one_mul, transfer_first_row hn S hb hf]

include hb hf hs ht in
theorem last_mulVec :
    transfer hn S *ᵥ Pi.single (lastState hn) (1 : ℕ) = fun _ => 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  exact transfer_last_column hn S hb hf hs ht i

include hb hf hs ht in
theorem transfer_sandwich (r : ℕ) :
    uG S (topState hn) ᵥ* transfer hn S ^ r ⬝ᵥ (fun _ => 1) =
      (transfer hn S ^ (r + 2)) (firstState hn) (lastState hn) := by
  let T := transfer hn S
  have hpow : T ^ (r + 2) = (T * T ^ r) * T := by
    rw [show r + 2 = (1 + r) + 1 by omega, pow_succ, pow_add, pow_one]
  calc
    _ = ((Pi.single (firstState hn) 1 : Fin n → ℕ) ᵥ* T ᵥ* T ^ r) ⬝ᵥ
        (T *ᵥ Pi.single (lastState hn) 1) := by
          rw [first_vecMul hn S hb hf, last_mulVec hn S hb hf hs ht]
    _ = _ := by
      rw [Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← hpow, Matrix.mulVec_single_one]
      change (Pi.single (firstState hn) (1 : ℕ) ⬝ᵥ
        (fun i => (T ^ (r + 2)) i (lastState hn))) = _
      rw [single_dotProduct, one_mul]

end Endpoints

noncomputable def properTransfer (hn : 1 ≤ n) : Matrix (Fin n) (Fin n) ℕ :=
  transfer hn (properVectors n)

noncomputable def latticeTransfer (hn : 1 ≤ n) : Matrix (Fin n) (Fin n) ℕ :=
  transfer hn (latticeVectors hn)

theorem proper_count_as_entry (hn : 1 ≤ n) (r : ℕ) :
    (properSumset n (r + 1)).ncard =
      (properTransfer hn ^ (r + 2)) (firstState hn) (lastState hn) := by
  rw [proper_count_transfer hn r, properTransfer]
  apply transfer_sandwich hn (properVectors n)
  · exact fun _ hf => SnF_bounded (mem_properVectors.mp hf)
  · exact fun _ hf => SnF_fixed hn (mem_properVectors.mp hf)
  · exact fun _ hk => mem_properVectors.mpr (skeleton_mem_SnF hk)
  · exact fun _ hf => SnF_terminal (mem_properVectors.mp hf)

theorem lattice_count_as_entry (hn : 1 ≤ n) (r : ℕ) :
    (dilateLattice n (r + 1)).ncard =
      (latticeTransfer hn ^ (r + 2)) (firstState hn) (lastState hn) := by
  rw [lattice_count_transfer hn r, latticeTransfer]
  apply transfer_sandwich hn (latticeVectors hn)
  · exact fun _ hf => normalized_one_bounded hn ((mem_latticeVectors hn).mp hf)
  · exact fun _ hf => normalized_one_fixed hn ((mem_latticeVectors hn).mp hf)
  · exact fun _ hk => skeleton_mem_latticeVectors hn hk
  · exact fun _ hf => lattice_terminal hn hf

theorem properTransfer_unitriangular (hn : 1 ≤ n) :
    (∀ i j, j < i → properTransfer hn i j = 0) ∧ (∀ i, properTransfer hn i i = 1) := by
  have hb : ∀ f ∈ properVectors n, Bounded f := fun _ hf => SnF_bounded (mem_properVectors.mp hf)
  have hf : ∀ f ∈ properVectors n, Fixed hn f := fun _ hf => SnF_fixed hn (mem_properVectors.mp hf)
  exact ⟨fun _ _ => transfer_below hn _ hb hf,
    transfer_diag hn _ hb hf (fun _ hk => mem_properVectors.mpr (skeleton_mem_SnF hk))⟩

theorem latticeTransfer_unitriangular (hn : 1 ≤ n) :
    (∀ i j, j < i → latticeTransfer hn i j = 0) ∧ (∀ i, latticeTransfer hn i i = 1) := by
  have hb : ∀ f ∈ latticeVectors hn, Bounded f := fun _ hf =>
    normalized_one_bounded hn ((mem_latticeVectors hn).mp hf)
  have hf : ∀ f ∈ latticeVectors hn, Fixed hn f := fun _ hf =>
    normalized_one_fixed hn ((mem_latticeVectors hn).mp hf)
  exact ⟨fun _ _ => transfer_below hn _ hb hf,
    transfer_diag hn _ hb hf (fun _ hk => skeleton_mem_latticeVectors hn hk)⟩

theorem firstState_eq_lastState_iff (hn : 1 ≤ n) :
    firstState hn = lastState hn ↔ n = 1 := by
  rw [Fin.ext_iff]
  simp only [firstState, lastState]
  omega

end D5.S3.Combinatorics.Kozlov

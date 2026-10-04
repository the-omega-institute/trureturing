/- GID: D5/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/HKNNBlockBlochLargestWeight/PairingCoefficients
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed pairing counts and cyclic translation control HKNN coefficients. -/

/-
proof_shape: pairing_data: content
escape_witness: Form (2): pairing_data is produced by the crossing-pairing equivalence,
  the prescribed interleaving sign swap and the unique cyclic-cut pair construction.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S1/Phase/SeatTowerCombinatorics.Stationing (Boolean configurations).
  statement_id: sha256:038fad99705f2c063108322eb2e26099ec5b7cc1bb5264176dc1480123d6b757
  D5/S3/Zeros/Convolution/PerfectMatchingCount.FixedPointFreeInvolution (carrier and instance).
  statement_id: sha256:6e0cb253a32bc30759501a78cf90a5ae8286a084748bf72325c36eb7f68f6b55
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S1.Phase.SeatTowerCombinatorics
import D5.S3.Zeros.Convolution.PerfectMatchingCount

noncomputable section
open scoped BigOperators
open Fin.NatCast
open D5.S1.Phase.SeatTowerCombinatorics (Stationing)
open D5.S3.Zeros.Convolution.PerfectMatchingCount

namespace D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight

def s : Bool → Bool → ℤ
  | false, true => 1
  | true, false => -1
  | _, _ => 0

def term (m : ℕ) (σ : Stationing (2 * m)) (f : FixedPointFreeInvolution (Fin (2 * m))) : ℤ :=
  ∏ i ∈ Finset.univ.filter (fun i => i < f.val i), s (σ i) (σ (f.val i))

def psi (m : ℕ) (σ : Stationing (2 * m)) : ℤ :=
  ∑ f : FixedPointFreeInvolution (Fin (2 * m)), term m σ f

def shift (m : ℕ) (σ : Stationing (2 * m)) : Stationing (2 * m) := fun i =>
  σ ⟨(i.val + (2 * m - 1)) % (2 * m),
    Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

def block (m : ℕ) : Stationing (2 * m) := fun i => decide (i.val < m)

def balanced (m : ℕ) (σ : Stationing (2 * m)) : Prop :=
  (Finset.univ.filter (fun i => σ i = true)).card = m

def isArc (m : ℕ) (σ : Stationing (2 * m)) : Prop :=
  ∃ j : ℕ, σ = ((shift m)^[j]) (block m)

def crossing {m : ℕ} (σ : Stationing (2 * m)) (f : FixedPointFreeInvolution (Fin (2 * m))) : Prop :=
  ∀ i, σ i ≠ σ (f.val i)

abbrev Down (m : ℕ) (σ : Stationing (2 * m)) := {i : Fin (2 * m) // σ i = true}

abbrev Up (m : ℕ) (σ : Stationing (2 * m)) := {i : Fin (2 * m) // σ i ≠ true}

abbrev CrossPairings (m : ℕ) (σ : Stationing (2 * m)) :=
  {f : FixedPointFreeInvolution (Fin (2 * m)) // crossing σ f}

private def crossingEquiv (m : ℕ) (σ : Stationing (2 * m)) (f : CrossPairings m σ) :
    Down m σ ≃ Up m σ where
  toFun i := ⟨f.val.val i.val, by
    intro he
    exact f.prop i.val (i.prop.trans he.symm)⟩
  invFun i := ⟨f.val.val i.val, by
    have h := f.prop i.val
    have hi := i.prop
    cases h₁ : σ i.val <;> cases h₂ : σ (f.val.val i.val) <;> simp_all⟩
  left_inv i := Subtype.ext ((f.val.prop.1 i.val))
  right_inv i := Subtype.ext ((f.val.prop.1 i.val))

private def pairingFromEquiv (m : ℕ) (σ : Stationing (2 * m)) (e : Down m σ ≃ Up m σ) :
    CrossPairings m σ := by
  let g : Fin (2 * m) → Fin (2 * m) := fun i =>
    if hi : σ i = true then (e ⟨i, hi⟩).val else (e.symm ⟨i, hi⟩).val
  have hg : Function.Involutive g := by
    intro i
    by_cases hi : σ i = true
    · have hu := (e ⟨i, hi⟩).prop
      simp [g, hi, hu]
    · have hd := (e.symm ⟨i, hi⟩).prop
      simp [g, hi, hd]
  have hn : ∀ i, g i ≠ i := by
    intro i he
    by_cases hi : σ i = true
    · have hu := (e ⟨i, hi⟩).prop
      have he' : (e ⟨i, hi⟩).val = i := by simpa [g, hi] using he
      rw [he'] at hu
      exact hu hi
    · have hd := (e.symm ⟨i, hi⟩).prop
      have he' : (e.symm ⟨i, hi⟩).val = i := by simpa [g, hi] using he
      rw [he'] at hd
      exact hi hd
  have hc : ∀ i, σ i ≠ σ (g i) := by
    intro i he
    by_cases hi : σ i = true
    · have hu := (e ⟨i, hi⟩).prop
      apply hu
      simpa [g, hi] using he.symm.trans hi
    · have hd := (e.symm ⟨i, hi⟩).prop
      apply hi
      simp [g, hi, hd] at he
  exact ⟨⟨hg.toPerm g, ⟨hg, hn⟩⟩, hc⟩

private def crossingPairingsEquiv (m : ℕ) (σ : Stationing (2 * m)) :
    CrossPairings m σ ≃ (Down m σ ≃ Up m σ) where
  toFun := crossingEquiv m σ
  invFun := pairingFromEquiv m σ
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : σ i = true
    · simp [pairingFromEquiv, crossingEquiv, Function.Involutive.toPerm]
    · simp [pairingFromEquiv, crossingEquiv, Function.Involutive.toPerm]
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    simp [crossingEquiv, pairingFromEquiv, i.prop, Function.Involutive.toPerm]

private def blockDownEquiv (m : ℕ) : Down m (block m) ≃ Fin m where
  toFun i := ⟨i.val.val, by simpa [block] using i.prop⟩
  invFun i := ⟨⟨i.val, by omega⟩, by simp [block, i.isLt]⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

open Classical in
def K (m : ℕ) : ℕ := Fintype.card (CrossPairings m (block m))

private def epsilon {n : ℕ} (d u : Fin n) : ℤ := if d < u then -1 else 1

private def rotatedDownEquiv (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
    Down m σ ≃ Down m (shift m σ) where
  toFun d := ⟨d.val + 1, by
    have shift_as_sub_one (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
        (σ : Stationing (2 * m)) (i : Fin (2 * m)) : shift m σ i = σ (i - 1) := by
      unfold shift
      congr 1
      apply Fin.ext
      simp only [Fin.sub_def, Fin.val_mk, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
      congr 1
      omega
    rw [shift_as_sub_one m hm]; simpa using d.prop⟩
  invFun d := ⟨d.val - 1, by
    have shift_as_sub_one (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
        (σ : Stationing (2 * m)) (i : Fin (2 * m)) : shift m σ i = σ (i - 1) := by
      unfold shift
      congr 1
      apply Fin.ext
      simp only [Fin.sub_def, Fin.val_mk, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
      congr 1
      omega
    simpa only [shift_as_sub_one m hm] using d.prop⟩
  left_inv d := by apply Subtype.ext; simp
  right_inv d := by apply Subtype.ext; simp

private def rotatedUpEquiv (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
    Up m σ ≃ Up m (shift m σ) where
  toFun d := ⟨d.val + 1, by
    have shift_as_sub_one (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
        (σ : Stationing (2 * m)) (i : Fin (2 * m)) : shift m σ i = σ (i - 1) := by
      unfold shift
      congr 1
      apply Fin.ext
      simp only [Fin.sub_def, Fin.val_mk, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
      congr 1
      omega
    rw [shift_as_sub_one m hm]; simpa using d.prop⟩
  invFun d := ⟨d.val - 1, by
    have shift_as_sub_one (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
        (σ : Stationing (2 * m)) (i : Fin (2 * m)) : shift m σ i = σ (i - 1) := by
      unfold shift
      congr 1
      apply Fin.ext
      simp only [Fin.sub_def, Fin.val_mk, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
      congr 1
      omega
    simpa only [shift_as_sub_one m hm] using d.prop⟩
  left_inv d := by apply Subtype.ext; simp
  right_inv d := by apply Subtype.ext; simp

theorem pairing_data (m : ℕ) :
    (∀ (σ : Stationing (2 * m)) (f : FixedPointFreeInvolution (Fin (2 * m))),
      crossing σ f → balanced m σ) ∧
    (0 < K m ∧ |psi m (block m)| = K m ∧
      (∀ σ : Stationing (2 * m), ¬ balanced m σ → psi m σ = 0) ∧
      (∀ σ : Stationing (2 * m), |psi m σ| ≤ K m)) ∧
    (∀ (σ : Stationing (2 * m)), balanced m σ →
      ∀ (d₁ d₂ : Down m σ) (u₁ u₂ : Up m σ),
      d₁.val < u₁.val → u₁.val < d₂.val → d₂.val < u₂.val → |psi m σ| < K m) ∧
    (∀ [NeZero (2 * m)], 1 ≤ m → ∀ σ : Stationing (2 * m), psi m (shift m σ) = -psi m σ) ∧
    (∀ (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)),
      ((shift m)^[j]) σ i = σ ⟨(i.val + (2 * m - 1) * j) % (2 * m),
        Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) ∧
    (∀ [NeZero (2 * m)], 1 ≤ m → ∀ (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)),
      ((shift m)^[j]) σ i = σ (i - (j : Fin (2 * m)))) := by
  classical
  have singlet_ne_zero_iff (a b : Bool) : s a b ≠ 0 ↔ a ≠ b := by
    cases a <;> cases b <;> decide
  have term_ne_zero_iff_crossing (m : ℕ) (σ : Stationing (2 * m))
      (f : FixedPointFreeInvolution (Fin (2 * m))) :
      term m σ f ≠ 0 ↔ crossing σ f := by
    unfold term crossing
    rw [Finset.prod_ne_zero_iff]
    constructor
    · intro h i
      by_cases hi : i < f.val i
      · exact (singlet_ne_zero_iff _ _).mp (h i (by simp [hi]))
      · have hlt : f.val i < i := lt_of_le_of_ne (le_of_not_gt hi) (f.prop.2 i)
        have hj : f.val i < f.val (f.val i) := by simpa [(f.prop.1 i)] using hlt
        have hs := (singlet_ne_zero_iff _ _).mp (h (f.val i) (by simp [hj]))
        simpa [(f.prop.1 i), ne_comm] using hs
    · intro h i hi
      exact (singlet_ne_zero_iff _ _).mpr (h i)
  have crossing_balanced (m : ℕ) (σ : Stationing (2 * m))
      (f : FixedPointFreeInvolution (Fin (2 * m)))
      (hf : crossing σ f) : balanced m σ := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing
    classical
    let D := Finset.univ.filter (fun i => σ i = true)
    have hc : D.card = Dᶜ.card := by
      apply Finset.card_bij (fun i _ => f.val i)
      · intro i hi
        have hd : σ i = true := (Finset.mem_filter.mp hi).2
        have hu : σ (f.val i) ≠ true := by
          intro he
          exact hf i (hd.trans he.symm)
        simp [D, hu]
      · intro i hi j hj he
        exact f.val.injective he
      · intro j hj
        have hu : σ j ≠ true := by simpa [D] using hj
        have hd : σ (f.val j) = true := by
          have h := hf j
          cases hsj : σ j <;> cases hsf : σ (f.val j) <;> simp_all
        refine ⟨f.val j, ?_, (f.prop.1 j)⟩
        simp [D, hd]
    have ht := Finset.card_compl D
    have hn : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
    unfold balanced
    change D.card = m
    rw [hn] at ht
    omega
  have psi_zero_of_unbalanced (m : ℕ) (σ : Stationing (2 * m))
      (hσ : ¬ balanced m σ) : psi m σ = 0 := by
    clear singlet_ne_zero_iff
    apply Finset.sum_eq_zero
    intro f hf
    by_contra ht
    exact hσ (crossing_balanced m σ f ((term_ne_zero_iff_crossing m σ f).mp ht))
  have card_down_eq (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      Fintype.card (Down m σ) = m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
    simpa [Down, Fintype.card_subtype, balanced] using hσ
  have balanced_block (m : ℕ) : balanced m (block m) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq
    have hc := Fintype.card_congr (blockDownEquiv m)
    simpa [Down, Fintype.card_subtype, balanced] using hc
  have card_up_eq (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      Fintype.card (Up m σ) = m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      balanced_block
    classical
    have he := Fintype.card_congr (Equiv.sumCompl (fun i : Fin (2 * m) => σ i = true))
    simp only [Fintype.card_sum, Fintype.card_fin] at he
    change Fintype.card (Down m σ) + Fintype.card (Up m σ) = 2 * m at he
    rw [card_down_eq m σ hσ] at he
    omega
  have crossing_count_constant (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      Fintype.card (CrossPairings m σ) = Fintype.card (CrossPairings m (block m)) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
    let eD : Down m σ ≃ Down m (block m) := Fintype.equivOfCardEq
      ((card_down_eq m σ hσ).trans (card_down_eq m (block m) (balanced_block m)).symm)
    let eU : Up m σ ≃ Up m (block m) := Fintype.equivOfCardEq
      ((card_up_eq m σ hσ).trans (card_up_eq m (block m) (balanced_block m)).symm)
    exact Fintype.card_congr ((crossingPairingsEquiv m σ).trans
      ((Equiv.equivCongr eD eU).trans (crossingPairingsEquiv m (block m)).symm))
  have term_abs_le_one (m : ℕ) (σ : Stationing (2 * m))
      (f : FixedPointFreeInvolution (Fin (2 * m))) :
      |term m σ f| ≤ 1 := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant
    rw [term, Finset.abs_prod]
    apply Finset.prod_le_one
    · intro i hi; exact abs_nonneg _
    · intro i hi
      cases h₁ : σ i <;> cases h₂ : σ (f.val i) <;> norm_num [s]
  have block_lower_iff (m : ℕ) (f : CrossPairings m (block m)) (i : Fin (2 * m)) :
      i < f.val.val i ↔ i.val < m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
    have hf := f.prop i
    by_cases hi : i.val < m
    · have hu : ¬(f.val.val i).val < m := by
        intro hfi
        apply hf
        simp [block, hi, hfi]
      constructor
      · intro h; exact hi
      · intro h
        change i.val < (f.val.val i).val
        omega
    · have hd : (f.val.val i).val < m := by
        by_contra hu
        apply hf
        simp [block, hi, hu]
      constructor
      · intro h
        change i.val < (f.val.val i).val at h
        omega
      · exact False.elim ∘ hi
  have block_term (m : ℕ) (f : CrossPairings m (block m)) :
      term m (block m) f.val = (-1 : ℤ) ^ m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq card_up_eq crossing_count_constant term_abs_le_one
    have he : Finset.univ.filter (fun i => i < f.val.val i) =
        Finset.univ.filter (fun i => (block m) i = true) := by
      ext i
      simp [block, block_lower_iff m f i]
    unfold term
    rw [he]
    have ht : ∀ i ∈ Finset.univ.filter (fun i => (block m) i = true),
        s ((block m) i) ((block m) (f.val.val i)) = -1 := by
      intro i hi
      have hd : (block m) i = true := (Finset.mem_filter.mp hi).2
      have hu : (block m) (f.val.val i) = false := by
        have hf := f.prop i
        cases h : (block m) (f.val.val i) <;> simp_all
      simp [hd, hu, s]
    rw [Finset.prod_congr rfl ht, Finset.prod_const]
    have hc := balanced_block m
    unfold balanced at hc
    rw [hc]
  have psi_crossing_sum (m : ℕ) (σ : Stationing (2 * m)) :
      psi m σ = ∑ f : CrossPairings m σ, term m σ f.val := by
    clear singlet_ne_zero_iff crossing_balanced psi_zero_of_unbalanced card_down_eq balanced_block
      card_up_eq crossing_count_constant term_abs_le_one block_lower_iff block_term
    classical
    unfold psi
    calc
      (∑ f : FixedPointFreeInvolution (Fin (2 * m)), term m σ f) =
          ∑ f ∈ Finset.univ.filter (crossing σ), term m σ f := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro f hf hn
        have hc : ¬ crossing σ f := by simpa using hn
        by_contra ht
        exact hc ((term_ne_zero_iff_crossing m σ f).mp ht)
      _ = ∑ f : CrossPairings m σ, term m σ f.val :=
        Finset.sum_subtype _ (by simp) _
  have K_positive (m : ℕ) : 0 < K m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      crossing_count_constant term_abs_le_one block_lower_iff block_term psi_crossing_sum
    classical
    let e : Down m (block m) ≃ Up m (block m) := Fintype.equivOfCardEq
      ((card_down_eq m (block m) (balanced_block m)).trans
        (card_up_eq m (block m) (balanced_block m)).symm)
    have hn : Nonempty (CrossPairings m (block m)) := ⟨pairingFromEquiv m (block m) e⟩
    exact Fintype.card_pos_iff.mpr hn
  have psi_block (m : ℕ) : psi m (block m) = (K m : ℤ) * (-1 : ℤ) ^ m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff K_positive
    rw [psi_crossing_sum]
    simp only [block_term, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K]
  have abs_psi_block (m : ℕ) : |psi m (block m)| = K m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive
    rw [psi_block, abs_mul]
    simp
  have abs_psi_bound_balanced (m : ℕ) (σ : Stationing (2 * m)) (hσ : balanced m σ) :
      |psi m σ| ≤ K m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq block_lower_iff block_term K_positive psi_block
      abs_psi_block
    rw [psi_crossing_sum]
    calc
      |∑ f : CrossPairings m σ, term m σ f.val| ≤
          ∑ f : CrossPairings m σ, |term m σ f.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _f : CrossPairings m σ, (1 : ℤ) :=
        Finset.sum_le_sum (fun f _ => term_abs_le_one m σ f.val)
      _ = K m := by simp [crossing_count_constant m σ hσ, K]
  have abs_psi_bound (m : ℕ) (σ : Stationing (2 * m)) : |psi m σ| ≤ K m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced card_down_eq
      balanced_block card_up_eq crossing_count_constant term_abs_le_one block_lower_iff block_term
      psi_crossing_sum K_positive psi_block abs_psi_block
    by_cases hs : balanced m σ
    · exact abs_psi_bound_balanced m σ hs
    · rw [psi_zero_of_unbalanced m σ hs]
      simp
  have term_down_product (m : ℕ) (σ : Stationing (2 * m)) (f : CrossPairings m σ) :
      term m σ f.val = ∏ d ∈ Finset.univ.filter (fun d => σ d = true),
        epsilon d (f.val.val d) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound
    let g := fun i : Fin (2 * m) => if σ i = true then i else f.val.val i
    unfold term
    apply Finset.prod_bij (fun i _ => g i)
    · intro i hi
      have hd : σ (g i) = true := by
        by_cases hs : σ i = true
        · simp [g, hs]
        · have hh := f.prop i
          cases h₁ : σ i <;> cases h₂ : σ (f.val.val i) <;> simp_all [g]
      simp [hd]
    · intro i hi j hj he
      have li : i < f.val.val i := (Finset.mem_filter.mp hi).2
      have lj : j < f.val.val j := (Finset.mem_filter.mp hj).2
      by_cases hsi : σ i = true <;> by_cases hsj : σ j = true
      · simpa [g, hsi, hsj] using he
      · have hei : i = f.val.val j := by simpa [g, hsi, hsj] using he
        rw [hei, (f.val.prop.1 j)] at li
        exact False.elim ((not_lt_of_gt lj) li)
      · have hej : f.val.val i = j := by simpa [g, hsi, hsj] using he
        rw [← hej, (f.val.prop.1 i)] at lj
        exact False.elim ((not_lt_of_gt li) lj)
      · apply f.val.val.injective
        simpa [g, hsi, hsj] using he
    · intro d hd
      have hs : σ d = true := (Finset.mem_filter.mp hd).2
      by_cases hl : d < f.val.val d
      · refine ⟨d, by simp [hl], ?_⟩
        simp [g, hs]
      · have hr : f.val.val d < d := lt_of_le_of_ne (le_of_not_gt hl) (f.val.prop.2 d)
        have hu : σ (f.val.val d) ≠ true := by
          intro he
          exact f.prop d (hs.trans he.symm)
        refine ⟨f.val.val d, ?_, ?_⟩
        · simp [(f.val.prop.1 d), hr]
        · simp [g, hu, (f.val.prop.1 d)]
    · intro i hi
      have hl : i < f.val.val i := (Finset.mem_filter.mp hi).2
      by_cases hs : σ i = true
      · have hu : σ (f.val.val i) = false := by
          have hf := f.prop i
          cases he : σ (f.val.val i) <;> simp_all
        simp [g, hs, hu, s, epsilon, hl]
      · have hd : σ (f.val.val i) = true := by
          have hf := f.prop i
          cases he : σ i <;> cases he' : σ (f.val.val i) <;> simp_all
        have hu : σ i = false := Bool.eq_false_of_not_eq_true hs
        simp [g, hs, hd, s, epsilon, (f.val.prop.1 i), not_lt_of_gt hl]
  have equiv_term_product (m : ℕ) (σ : Stationing (2 * m)) (e : Down m σ ≃ Up m σ) :
      term m σ (pairingFromEquiv m σ e).val =
        ∏ d : Down m σ, epsilon d.val (e d).val := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound
    rw [term_down_product]
    have he : (∏ d ∈ Finset.univ.filter (fun d => σ d = true),
        epsilon d ((pairingFromEquiv m σ e).val.val d)) =
        ∏ d : Down m σ, epsilon d.val ((pairingFromEquiv m σ e).val.val d.val) :=
      Finset.prod_subtype _ (by simp) _
    rw [he]
    apply Finset.prod_congr rfl
    intro d hd
    simp [pairingFromEquiv, Function.Involutive.toPerm, d.prop]
  have prescribed_sign_exchange (m : ℕ) (σ : Stationing (2 * m))
      (e : Down m σ ≃ Up m σ) (d₁ d₂ : Down m σ)
      (h₁ : d₁.val < (e d₁).val) (h₂ : (e d₁).val < d₂.val)
      (h₃ : d₂.val < (e d₂).val) :
      term m σ (pairingFromEquiv m σ ((Equiv.swap d₁ d₂).trans e)).val =
        -term m σ (pairingFromEquiv m σ e).val := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product
    classical
    rw [equiv_term_product, equiv_term_product]
    have hd : d₂ ≠ d₁ := by
      intro he
      have hh := lt_trans h₁ h₂
      rw [he] at hh
      exact lt_irrefl _ hh
    let a : Down m σ → ℤ := fun d => epsilon d.val (e d).val
    let b : Down m σ → ℤ := fun d => epsilon d.val (e (Equiv.swap d₁ d₂ d)).val
    change (∏ d, b d) = -(∏ d, a d)
    have split (f : Down m σ → ℤ) :
        (∏ d, f d) = f d₁ * f d₂ *
          ∏ d ∈ (Finset.univ.erase d₁).erase d₂, f d := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ d₁),
        ← Finset.mul_prod_erase (Finset.univ.erase d₁) f
          (Finset.mem_erase.mpr ⟨hd, Finset.mem_univ d₂⟩)]
      ring
    rw [split a, split b]
    have hp : (∏ d ∈ (Finset.univ.erase d₁).erase d₂, b d) =
        ∏ d ∈ (Finset.univ.erase d₁).erase d₂, a d := by
      apply Finset.prod_congr rfl
      intro d hh
      have hd₂ := (Finset.mem_erase.mp hh).1
      have hd₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hh).2).1
      simp [a, b, Equiv.swap_apply_of_ne_of_ne hd₁ hd₂]
    rw [hp]
    have h₄ := lt_trans h₁ (lt_trans h₂ h₃)
    have h₅ := not_lt_of_gt h₂
    simp [a, b, epsilon, h₁, h₃, h₄, h₅]
  have strict_coefficient_of_two_signs (m : ℕ) (σ : Stationing (2 * m))
      (hσ : balanced m σ) (f g : CrossPairings m σ)
      (hf : term m σ f.val = -1) (hg : term m σ g.val = 1) :
      |psi m σ| < K m := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq block_lower_iff block_term K_positive psi_block
      abs_psi_block abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange
    rw [abs_lt]
    constructor
    · have hs : (∑ h : CrossPairings m σ, -term m σ h.val) <
          ∑ _h : CrossPairings m σ, (1 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro h hh
          have ht := term_abs_le_one m σ h.val
          have hl := (abs_le.mp ht).1
          omega
        · exact ⟨g, Finset.mem_univ g, by rw [hg]; norm_num⟩
      rw [Finset.sum_neg_distrib, ← psi_crossing_sum] at hs
      have hk : (∑ _h : CrossPairings m σ, (1 : ℤ)) = (K m : ℤ) := by
        simp [crossing_count_constant m σ hσ, K]
      rw [hk] at hs
      omega
    · have hs : (∑ h : CrossPairings m σ, term m σ h.val) <
          ∑ _h : CrossPairings m σ, (1 : ℤ) := by
        apply Finset.sum_lt_sum
        · intro h hh
          exact (abs_le.mp (term_abs_le_one m σ h.val)).2
        · exact ⟨f, Finset.mem_univ f, by rw [hf]; norm_num⟩
      simpa [← psi_crossing_sum, crossing_count_constant m σ hσ, K] using hs
  have exists_equiv_prescribed (m : ℕ) (σ : Stationing (2 * m))
      (hσ : balanced m σ) (d₁ d₂ : Down m σ) (u₁ u₂ : Up m σ)
      (hd : d₁ ≠ d₂) (hu : u₁ ≠ u₂) :
      ∃ e : Down m σ ≃ Up m σ, e d₁ = u₁ ∧ e d₂ = u₂ := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      balanced_block crossing_count_constant term_abs_le_one block_lower_iff block_term
      psi_crossing_sum K_positive psi_block abs_psi_block abs_psi_bound_balanced abs_psi_bound
      term_down_product equiv_term_product prescribed_sign_exchange strict_coefficient_of_two_signs
    classical
    let f : Down m σ → Up m σ := fun d => if d = d₁ then u₁ else u₂
    have hc : Fintype.card (Down m σ) = (Finset.univ : Finset (Up m σ)).card := by
      simp [card_down_eq m σ hσ, card_up_eq m σ hσ]
    have hf : Set.InjOn f ({d₁, d₂} : Finset (Down m σ)) := by
      intro a ha b hb he
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · simp [f, Ne.symm hd] at he
        exact False.elim (hu he)
      · simp [f, Ne.symm hd] at he
        exact False.elim (hu he.symm)
      · rfl
    obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq hc
      (s := {d₁, d₂}) (f := f) (Finset.subset_univ _) hf
    refine ⟨e.trans (Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)), ?_, ?_⟩
    · simpa [f] using he d₁ (by simp)
    · simpa [f, Ne.symm hd] using he d₂ (by simp)
  have strict_coefficient_interleaving (m : ℕ) (σ : Stationing (2 * m))
      (hσ : balanced m σ) (d₁ d₂ : Down m σ) (u₁ u₂ : Up m σ)
      (h₁ : d₁.val < u₁.val) (h₂ : u₁.val < d₂.val) (h₃ : d₂.val < u₂.val) :
      |psi m σ| < K m := by
    clear singlet_ne_zero_iff crossing_balanced psi_zero_of_unbalanced card_down_eq balanced_block
      card_up_eq crossing_count_constant block_lower_iff block_term psi_crossing_sum K_positive
      psi_block abs_psi_block abs_psi_bound_balanced abs_psi_bound term_down_product
      equiv_term_product
    classical
    have hd : d₁ ≠ d₂ := fun he => by
      have hh := lt_trans h₁ h₂
      rw [he] at hh
      exact lt_irrefl _ hh
    have hu : u₁ ≠ u₂ := fun he => by
      have hh := lt_trans h₂ h₃
      rw [he] at hh
      exact lt_irrefl _ hh
    obtain ⟨e, he₁, he₂⟩ := exists_equiv_prescribed m σ hσ d₁ d₂ u₁ u₂ hd hu
    let f := pairingFromEquiv m σ e
    let g := pairingFromEquiv m σ ((Equiv.swap d₁ d₂).trans e)
    have hx : term m σ g.val = -term m σ f.val := by
      apply prescribed_sign_exchange m σ e d₁ d₂
      · simpa [he₁] using h₁
      · simpa [he₁] using h₂
      · simpa [he₂] using h₃
    have hb := abs_le.mp (term_abs_le_one m σ f.val)
    have hz := (term_ne_zero_iff_crossing m σ f.val).mpr f.prop
    have hs : term m σ f.val = -1 ∨ term m σ f.val = 1 := by omega
    rcases hs with hf | hf
    · have hg : term m σ g.val = 1 := by simpa [hf] using hx
      exact strict_coefficient_of_two_signs m σ hσ f g hf hg
    · have hg : term m σ g.val = -1 := by simpa [hf] using hx
      exact strict_coefficient_of_two_signs m σ hσ g f hg hf
  have shift_iterate_apply (m : ℕ) (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)) :
      ((shift m)^[j]) σ i =
        σ ⟨(i.val + (2 * m - 1) * j) % (2 * m),
          Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange strict_coefficient_of_two_signs exists_equiv_prescribed
      strict_coefficient_interleaving
    induction j generalizing i with
    | zero =>
      simp only [Function.iterate_zero_apply, mul_zero, add_zero]
      congr 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      change ((shift m)^[j]) σ
        ⟨(i.val + (2 * m - 1)) % (2 * m), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ = _
      rw [ih]
      congr 1
      apply Fin.ext
      change (((i.val + (2 * m - 1)) % (2 * m) + (2 * m - 1) * j) % (2 * m)) = _
      rw [Nat.mod_add_mod]
      congr 1
      ring
  have shift_as_sub_one (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (i : Fin (2 * m)) : shift m σ i = σ (i - 1) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange strict_coefficient_of_two_signs exists_equiv_prescribed
      strict_coefficient_interleaving shift_iterate_apply
    unfold shift
    congr 1
    apply Fin.ext
    simp only [Fin.sub_def, Fin.val_mk, Fin.val_one']
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * m)]
    congr 1
    omega
  have shift_iterate_sub (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (j : ℕ) (i : Fin (2 * m)) :
      ((shift m)^[j]) σ i = σ (i - (j : Fin (2 * m))) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange strict_coefficient_of_two_signs exists_equiv_prescribed
      strict_coefficient_interleaving shift_iterate_apply
    induction j generalizing i with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', shift_as_sub_one m hm, ih]
      simp [Nat.cast_add, Nat.cast_one, sub_sub, add_comm]
  have epsilon_rotate {n : ℕ} [NeZero n] (hn : 1 < n) (d u : Fin n) (hne : d ≠ u) :
      epsilon (d + 1) (u + 1) = epsilon d u *
        (if d.val = n - 1 ∨ u.val = n - 1 then -1 else 1) := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange strict_coefficient_of_two_signs exists_equiv_prescribed
      strict_coefficient_interleaving shift_iterate_apply shift_as_sub_one shift_iterate_sub
    have hd := d.isLt
    have hu := u.isLt
    have hdu : d.val ≠ u.val := fun h => hne (Fin.ext h)
    simp only [epsilon, Fin.lt_def, Fin.val_add_eq_ite, Fin.val_one']
    rw [Nat.mod_eq_of_lt hn]
    split_ifs <;> norm_num at * <;> omega
  have psi_equiv_sum (m : ℕ) (σ : Stationing (2 * m)) :
      psi m σ = ∑ e : Down m σ ≃ Up m σ, term m σ (pairingFromEquiv m σ e).val := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term K_positive psi_block abs_psi_block abs_psi_bound_balanced
      abs_psi_bound term_down_product equiv_term_product prescribed_sign_exchange
      strict_coefficient_of_two_signs exists_equiv_prescribed strict_coefficient_interleaving
      shift_iterate_apply shift_as_sub_one shift_iterate_sub epsilon_rotate
    rw [psi_crossing_sum]
    exact ((crossingPairingsEquiv m σ).symm.sum_comp
      (fun f : CrossPairings m σ => term m σ f.val)).symm
  have equiv_term_rotation (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
      (σ : Stationing (2 * m)) (e : Down m σ ≃ Up m σ) :
      let e' := (rotatedDownEquiv m hm σ).symm.trans (e.trans (rotatedUpEquiv m hm σ))
      term m (shift m σ) (pairingFromEquiv m (shift m σ) e').val =
        -term m σ (pairingFromEquiv m σ e).val := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product prescribed_sign_exchange
      strict_coefficient_of_two_signs exists_equiv_prescribed strict_coefficient_interleaving
      shift_iterate_apply shift_as_sub_one shift_iterate_sub psi_equiv_sum
    classical
    dsimp only
    rw [equiv_term_product, equiv_term_product]
    let ed := rotatedDownEquiv m hm σ
    let eu := rotatedUpEquiv m hm σ
    have hp := ed.prod_comp (fun d : Down m (shift m σ) =>
      epsilon d.val (((ed.symm.trans (e.trans eu)) d).val))
    rw [← hp]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    change (∏ d : Down m σ, epsilon (d.val + 1) ((e d).val + 1)) =
      -(∏ d : Down m σ, epsilon d.val (e d).val)
    have hne (d : Down m σ) : d.val ≠ (e d).val := by
      intro h
      exact (e d).prop (h ▸ d.prop)
    simp_rw [epsilon_rotate (by omega : 1 < 2 * m) _ _ (hne _)]
    rw [Finset.prod_mul_distrib]
    suffices hs : (∏ d : Down m σ,
        (if d.val.val = 2 * m - 1 ∨ (e d).val.val = 2 * m - 1 then (-1 : ℤ) else 1)) = -1 by
      rw [hs]
      ring
    let last : Fin (2 * m) := ⟨2 * m - 1, by omega⟩
    by_cases hl : σ last = true
    · let d₀ : Down m σ := ⟨last, hl⟩
      have he (d : Down m σ) :
          (d.val.val = 2 * m - 1 ∨ (e d).val.val = 2 * m - 1) ↔ d = d₀ := by
        constructor
        · rintro (hd | hu)
          · apply Subtype.ext; apply Fin.ext; exact hd
          · have hu' : (e d).val = last := Fin.ext hu
            exact False.elim ((e d).prop (hu' ▸ hl))
        · rintro rfl
          exact Or.inl rfl
      simp_rw [he]
      simp
    · let u₀ : Up m σ := ⟨last, hl⟩
      let d₀ : Down m σ := e.symm u₀
      have he (d : Down m σ) :
          (d.val.val = 2 * m - 1 ∨ (e d).val.val = 2 * m - 1) ↔ d = d₀ := by
        constructor
        · rintro (hd | hu)
          · have hd' : d.val = last := Fin.ext hd
            exact False.elim (hl (hd' ▸ d.prop))
          · apply e.injective
            apply Subtype.ext
            simpa [d₀, u₀, last] using Fin.ext hu
        · intro hd
          right
          subst d
          simp [d₀, u₀, last]
      simp_rw [he]
      simp
  have psi_shift (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m) (σ : Stationing (2 * m)) :
      psi m (shift m σ) = -psi m σ := by
    clear singlet_ne_zero_iff term_ne_zero_iff_crossing crossing_balanced psi_zero_of_unbalanced
      card_down_eq balanced_block card_up_eq crossing_count_constant term_abs_le_one
      block_lower_iff block_term psi_crossing_sum K_positive psi_block abs_psi_block
      abs_psi_bound_balanced abs_psi_bound term_down_product equiv_term_product
      prescribed_sign_exchange strict_coefficient_of_two_signs exists_equiv_prescribed
      strict_coefficient_interleaving shift_iterate_apply shift_as_sub_one shift_iterate_sub
      epsilon_rotate
    classical
    rw [psi_equiv_sum, psi_equiv_sum]
    let E := Equiv.equivCongr (rotatedDownEquiv m hm σ) (rotatedUpEquiv m hm σ)
    rw [← E.sum_comp]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    exact equiv_term_rotation m hm σ e
  exact ⟨crossing_balanced m, ⟨K_positive m, abs_psi_block m, psi_zero_of_unbalanced m,
    abs_psi_bound m⟩, strict_coefficient_interleaving m, psi_shift m,
    shift_iterate_apply m, shift_iterate_sub m⟩

#print axioms pairing_data

end D5.S3.Quantum.SpinChains.HKNNBlockBlochLargestWeight

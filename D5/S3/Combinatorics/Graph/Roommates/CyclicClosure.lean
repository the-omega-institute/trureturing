/- GID: D5/S3/Combinatorics/Graph/Roommates/CyclicClosure
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/CyclicClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Cyclic cutting, rank transport and six-site stable-profile closure. -/

import D5.S3.Combinatorics.Graph.Roommates.SourceModel
import D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
import D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
open OpenCertificates

/-- The supplier's four labels, in their original order. -/
def signed : Fin 4 → ℤ := ![1, 2, -1, -2]

/-- Reduction of an integer coordinate to the literal source cycle. -/
def wrap (n : ℕ) (z : ℤ) : Fin (n + 5) :=
  ⟨(z % (n + 5)).toNat, by
    have h := Int.emod_nonneg z (show (n : ℤ) + 5 ≠ 0 by omega)
    have h' := Int.emod_lt_of_pos z (show (0 : ℤ) < n + 5 by omega)
    omega⟩

theorem wrap_val (n : ℕ) (z : ℤ) :
    ((wrap n z).val : ℤ) = z % (n + 5) := by
  simp only [wrap]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem wrap_index {n : ℕ} (i : Fin (n + 5)) : wrap n i.val = i := by
  apply Fin.ext
  have h := wrap_val n i.val
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
  exact_mod_cast h

theorem wrap_add (n : ℕ) (a b : ℤ) :
    wrap n (a + b) = wrap n a + wrap n b := by
  apply Fin.ext
  have ha := wrap_val n a
  have hb := wrap_val n b
  have hab := wrap_val n (a + b)
  have hsum := wrap_val n ((wrap n a).val + (wrap n b).val)
  rw [Int.add_emod, ← ha, ← hb] at hab
  change (wrap n (a + b)).val = ((wrap n a).val + (wrap n b).val) % (n + 5)
  exact_mod_cast hab

theorem wrap_signed (n : ℕ) (s : Fin 4) : wrap n (signed s) = SourceModel.offset n s := by
  apply Fin.ext
  fin_cases s
  · change (wrap n 1).val = 1
    have h := wrap_val n 1
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
    omega
  · change (wrap n 2).val = 2
    have h := wrap_val n 2
    rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
    omega
  · change (wrap n (-1)).val = n + 4
    have h := wrap_val n (-1)
    have he : (-1 : ℤ) % (n + 5) = (n : ℤ) + 4 := by
      have hh : ((n : ℤ) + 4) % (n + 5) = (n : ℤ) + 4 :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have hmod : (-1 + ((n : ℤ) + 5)) % (n + 5) = (-1 : ℤ) % (n + 5) := by
        simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
      rw [show (-1 : ℤ) + (n + 5) = n + 4 by omega, hh] at hmod
      exact hmod.symm
    rw [he] at h
    omega
  · change (wrap n (-2)).val = n + 3
    have h := wrap_val n (-2)
    have he : (-2 : ℤ) % (n + 5) = (n : ℤ) + 3 := by
      have hh : ((n : ℤ) + 3) % (n + 5) = (n : ℤ) + 3 :=
        Int.emod_eq_of_lt (by omega) (by omega)
      have hmod : (-2 + ((n : ℤ) + 5)) % (n + 5) = (-2 : ℤ) % (n + 5) := by
        simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
      rw [show (-2 : ℤ) + (n + 5) = n + 3 by omega, hh] at hmod
      exact hmod.symm
    rw [he] at h
    omega

private theorem wrap_reverse {n : ℕ} (i j : Fin (n + 5)) (a b : ℤ)
    (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2)
    (hij : wrap n (i.val + a) = j) (hji : wrap n (j.val + b) = i) : b = -a := by
  have hi := congrArg (fun x : Fin (n + 5) => (x.val : ℤ)) hij
  have hj := congrArg (fun x : Fin (n + 5) => (x.val : ℤ)) hji
  rw [wrap_val] at hi hj
  have he : ((a + b) % (n + 5)) = 0 := by
    have h := congrArg (fun x : Fin (n + 5) => wrap n (x.val + b)) hij
    simp only [wrap_add, wrap_index] at h
    have hji' : j + wrap n b = i := by simpa only [wrap_add, wrap_index] using hji
    have ht : wrap n (i.val + (a + b)) = i := by
      simpa only [wrap_add, wrap_index, add_assoc] using h.trans hji'
    have hmod := congrArg (fun x : Fin (n + 5) => (x.val : ℤ)) ht
    rw [wrap_val] at hmod
    have heq : Int.ModEq (n + 5) (i.val + (a + b)) (i.val : ℤ) := by
      simpa only [Int.ModEq, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ i.val)
        (by omega : (i.val : ℤ) < n + 5)] using hmod
    have heq' : Int.ModEq (n + 5) (i.val + (a + b)) ((i.val : ℤ) + 0) := by simpa using heq
    have hh := Int.ModEq.add_left_cancel' (i.val : ℤ) heq'
    simpa only [Int.ModEq, Int.zero_emod] using hh
  have hdiv : (n + 5 : ℤ) ∣ a + b := Int.dvd_of_emod_eq_zero he
  have hz : a + b = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by omega)
  omega

theorem signed_bounds (s : Fin 4) : -2 ≤ signed s ∧ signed s ≤ 2 ∧ signed s ≠ 0 := by
  fin_cases s <;> norm_num [signed]

private theorem signed_rank (r : Ranking) (s : Fin 4) :
    offsetRank r (signed s) = (r s).val := by
  fin_cases s <;> simp [signed, offsetRank]

/-- Cut assignments retain signed offsets even when their integer target is exterior. -/
def displacement {n : ℕ} (μ : SourceModel.Matching (Fin (n + 5)))
    (ha : SourceModel.IsAcceptable (SourceModel.ring n) μ) (i : Fin (n + 5)) : ℤ :=
  if h : μ.val i = i then 0 else signed (Classical.choose ((ha i).resolve_left h))

private theorem displacement_spec {n : ℕ} (p : SourceModel.Profile n)
    (μ : SourceModel.Matching (Fin (n + 5)))
    (ha : SourceModel.IsAcceptable (SourceModel.ring n) μ) (i : Fin (n + 5)) :
    (-2 ≤ displacement μ ha i ∧ displacement μ ha i ≤ 2) ∧
    (displacement μ ha i = 0 ↔ μ.val i = i) ∧
    wrap n (i.val + displacement μ ha i) = μ.val i ∧
    offsetRank (p i) (displacement μ ha i) = SourceModel.rank p i (μ.val i) := by
  classical
  by_cases h : μ.val i = i
  · simp [displacement, h, offsetRank, wrap_index, SourceModel.rank_self]
  · let hex := (ha i).resolve_left h
    have hs : μ.val i = i + SourceModel.offset n (Classical.choose hex) :=
      Classical.choose_spec hex
    have hb := signed_bounds (Classical.choose hex)
    simp only [displacement, dif_neg h]
    refine ⟨⟨hb.1, hb.2.1⟩, ?_, ?_, ?_⟩
    · simp [hb.2.2, h]
    · calc
        wrap n (i.val + signed (Classical.choose hex)) =
            i + SourceModel.offset n (Classical.choose hex) := by
              rw [wrap_add, wrap_index, wrap_signed]
        _ = μ.val i := hs.symm
    · exact (signed_rank (p i) (Classical.choose hex)).trans
        ((SourceModel.rank_neighbor p i (Classical.choose hex)).symm.trans
          (congrArg (SourceModel.rank p i) hs.symm))

private theorem wrap_local {n : ℕ} (i j : Fin (n + 5)) :
    wrap n (i.val + ((j.val : ℤ) - i.val)) = j := by
  simpa only [add_sub_cancel] using wrap_index j

private theorem local_rank {n : ℕ} (p : SourceModel.Profile n)
    (i j : Fin (n + 5)) (hij : i.val < j.val) (hd : j.val ≤ i.val + 2) :
    SourceModel.rank p i j = offsetRank (p i) ((j.val : ℤ) - i.val) ∧
    SourceModel.rank p j i = offsetRank (p j) ((i.val : ℤ) - j.val) ∧
    (SourceModel.ring n).Adj i j := by
  have hdiff : (j.val : ℤ) - i.val = 1 ∨ (j.val : ℤ) - i.val = 2 := by omega
  rcases hdiff with h | h
  · have he : j = i + SourceModel.offset n 0 := by
      rw [← wrap_signed, ← wrap_index i, ← wrap_add]
      simpa [signed, h] using (wrap_local i j).symm
    have hr : i = j + SourceModel.offset n 2 := by
      rw [← wrap_signed, ← wrap_index j, ← wrap_add]
      have hh := wrap_local j i
      have : (i.val : ℤ) - j.val = -1 := by omega
      simpa [signed, this] using hh.symm
    refine ⟨?_, ?_, ⟨0, he⟩⟩
    · have hh := SourceModel.rank_neighbor p i 0
      rw [← he] at hh
      simpa [offsetRank, h] using hh
    · have hh := SourceModel.rank_neighbor p j 2
      rw [← hr] at hh
      simpa [offsetRank, show (i.val : ℤ) - j.val = -1 by omega] using hh
  · have he : j = i + SourceModel.offset n 1 := by
      rw [← wrap_signed, ← wrap_index i, ← wrap_add]
      simpa [signed, h] using (wrap_local i j).symm
    have hr : i = j + SourceModel.offset n 3 := by
      rw [← wrap_signed, ← wrap_index j, ← wrap_add]
      have hh := wrap_local j i
      have : (i.val : ℤ) - j.val = -2 := by omega
      simpa [signed, this] using hh.symm
    refine ⟨?_, ?_, ⟨1, he⟩⟩
    · have hh := SourceModel.rank_neighbor p i 1
      rw [← he] at hh
      simpa [offsetRank, h] using hh
    · have hh := SourceModel.rank_neighbor p j 3
      rw [← hr] at hh
      simpa [offsetRank, show (i.val : ℤ) - j.val = -2 by omega] using hh

/-- Cutting a stable source matching keeps its genuine ranks and all integer requests.
No pairing witness is counted by this theorem. -/
theorem cut_certificate {n : ℕ} (p : SourceModel.Profile n)
    (μ : SourceModel.Matching (Fin (n + 5)))
    (hs : SourceModel.IsStable (SourceModel.ring n) (SourceModel.rank p) μ) :
    Certificate p (displacement μ hs.1) := by
  let d := displacement μ hs.1
  have hd := displacement_spec p μ hs.1
  constructor
  · intro i
    exact (hd i).1
  · intro i j hdi he
    have hm : μ.val i = j := by
      rw [← (hd i).2.2.1, he, wrap_index]
    have hr : μ.val j = i := by rw [← hm]; exact μ.property i
    exact wrap_reverse i j (d i) (d j) (hd i).1 (hd j).1
      (by simpa [d, hm] using (hd i).2.2.1)
      (by simpa [d, hr] using (hd j).2.2.1)
  · intro i j _ _ he
    apply μ.val.injective
    rw [← (hd i).2.2.1, ← (hd j).2.2.1, he]
  · intro i j hij hdist
    have hl := local_rank p i j hij hdist
    by_cases hmatch : μ.val i = j
    · left
      have hji : μ.val j = i := by rw [← hmatch]; exact μ.property i
      have hr := wrap_reverse i j (d i) ((i.val : ℤ) - j.val) (hd i).1
        (by omega) (by simpa [d, hmatch] using (hd i).2.2.1) (wrap_local j i)
      dsimp [d] at hr ⊢
      omega
    · have hn := hs.2 i j
      have hless : offsetRank (p i) (d i) < offsetRank (p i) ((j.val : ℤ) - i.val) ∨
          offsetRank (p j) (d j) < offsetRank (p j) ((i.val : ℤ) - j.val) := by
        have hne₁ : offsetRank (p i) (d i) ≠ offsetRank (p i) ((j.val : ℤ) - i.val) := by
          intro heq
          by_cases hz : d i = 0
          · obtain ⟨s, hs⟩ := hl.2.2
            have hlt := SourceModel.rank_neighbor_lt_self p i s
            rw [← hs, hl.1, SourceModel.rank_self] at hlt
            rw [hz] at heq
            change 4 = offsetRank (p i) ((j.val : ℤ) - i.val) at heq
            omega
          · have he := rank_injective (p i) (hd i).1 (by omega) hz (by omega) heq
            apply hmatch
            rw [← (hd i).2.2.1, he, wrap_local]
        have hne₂ : offsetRank (p j) (d j) ≠ offsetRank (p j) ((i.val : ℤ) - j.val) := by
          intro heq
          by_cases hz : d j = 0
          · obtain ⟨s, hs⟩ := hl.2.2.symm
            have hlt := SourceModel.rank_neighbor_lt_self p j s
            rw [← hs, hl.2.1, SourceModel.rank_self] at hlt
            rw [hz] at heq
            change 4 = offsetRank (p j) ((i.val : ℤ) - j.val) at heq
            omega
          · have he := rank_injective (p j) (hd j).1 (by omega) hz (by omega) heq
            have hm : μ.val j = i := by rw [← (hd j).2.2.1, he, wrap_local]
            apply hmatch
            rw [← hm]
            exact μ.property j
        have hno : ¬ (offsetRank (p i) ((j.val : ℤ) - i.val) < offsetRank (p i) (d i) ∧
            offsetRank (p j) ((i.val : ℤ) - j.val) < offsetRank (p j) (d j)) := by
          rintro ⟨hi, hj⟩
          apply hn
          refine ⟨hl.2.2, hmatch, ?_, ?_⟩
          · have hri : offsetRank (p i) (d i) = SourceModel.rank p i (μ.val i) := (hd i).2.2.2
            simpa only [← hl.1, hri] using hi
          · have hrj : offsetRank (p j) (d j) = SourceModel.rank p j (μ.val j) := (hd j).2.2.2
            simpa only [← hl.2.1, hrj] using hj
        omega
      exact Or.inr hless

/-- The cut map is the identity on ranking words, so it is injective on profiles. -/
def cut {n : ℕ} (p : {p : SourceModel.Profile n // SourceModel.HasStableMatching p}) :
    CertifiedWord (n + 5) := by
  refine ⟨p.val, ?_⟩
  obtain ⟨μ, hs⟩ := p.property
  exact ⟨displacement μ hs.1, cut_certificate p.val μ hs⟩

/-- Every successful labelled cyclic profile is a certified open word, including N=5. -/
theorem source_count_le_open_count (n : ℕ) :
    Fintype.card {p : SourceModel.Profile n // SourceModel.HasStableMatching p} ≤ count (n + 5) := by
  apply Fintype.card_le_of_injective (@cut n)
  intro p q h
  apply Subtype.ext
  exact congrArg (fun r : CertifiedWord (n + 5) => r.val) h

/-- Exact independent-uniform normalization, with profiles counted once. -/
theorem source_probability_eq (n : ℕ) :
    SourceModel.solutionProbability n =
      (Fintype.card {p : SourceModel.Profile n // SourceModel.HasStableMatching p} : ℝ) /
        (24 : ℝ) ^ (n + 5) := by
  unfold SourceModel.solutionProbability
  rw [SourceModel.card_profile]
  norm_cast

/-- The literal source probability is bounded by the certified-word proportion.
This is only the cut side of the required cyclic sandwich. -/
theorem source_probability_le_open_proportion (n : ℕ) :
    SourceModel.solutionProbability n ≤ (count (n + 5) : ℝ) / (24 : ℝ) ^ (n + 5) := by
  rw [source_probability_eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast source_count_le_open_count n)
    (by positivity)

/-- A closing request reaches exactly its original signed-offset source neighbor.
The six-site insertion changes neither the old request nor its cyclic destination. -/
theorem closing_request_source_target {m : ℕ} {w : Word m} {d : Fin m → ℤ}
    (hw : Certificate w d) (i : PaddedCompletion.ClosingRequester d) :
    wrap (m + 1) (i.val.val + d i.val) =
      wrap (m + 1) ((m : ℤ) + (PaddedCompletion.closingRequest d hw.bounded i).val) := by
  have hc := PaddedCompletion.closing_coordinate hw.bounded i
  by_cases hn : (i.val.val : ℤ) + d i.val < 0
  · simp only [hn, ite_true] at hc
    apply Fin.ext
    have hl := wrap_val (m + 1) (i.val.val + d i.val)
    have hr := wrap_val (m + 1)
      ((m : ℤ) + (PaddedCompletion.closingRequest d hw.bounded i).val)
    have he : (m : ℤ) + (PaddedCompletion.closingRequest d hw.bounded i).val =
        i.val.val + d i.val + ((m : ℤ) + 1 + 5) := by omega
    have hmod : ((m : ℤ) + (PaddedCompletion.closingRequest d hw.bounded i).val) %
        ((m : ℤ) + 1 + 5) = (i.val.val + d i.val) % ((m : ℤ) + 1 + 5) := by
      rw [he]
      simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
    simp only [Nat.cast_add, Nat.cast_one] at hl hr
    rw [hmod] at hr
    omega
  · simp only [hn, ite_false] at hc
    congr 1
    omega

/-- No new edge between old vertices appears across the closing buffer.
This covers all positive old lengths, including one and two. -/
theorem closing_old_edge_local {m : ℕ} (i j : Fin m)
    (h : (SourceModel.ring (m + 1)).Adj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :
    (i.val : ℤ) < j.val + 3 ∧ (j.val : ℤ) < i.val + 3 := by
  obtain ⟨s, hs⟩ := h
  have he : wrap (m + 1) (i.val + signed s) = (⟨j.val, by omega⟩ : Fin (m + 1 + 5)) := by
    rw [wrap_add, wrap_signed]
    have hi : wrap (m + 1) i.val = (⟨i.val, by omega⟩ : Fin (m + 1 + 5)) :=
      wrap_index (⟨i.val, by omega⟩ : Fin (m + 1 + 5))
    rw [hi]
    exact hs.symm
  have heval := congrArg (fun x : Fin (m + 1 + 5) => (x.val : ℤ)) he
  rw [wrap_val] at heval
  simp only [Nat.cast_add, Nat.cast_one] at heval
  have hmod : Int.ModEq (m + 1 + 5 : ℤ) (i.val + signed s) (j.val : ℤ) := by
    simpa only [Int.ModEq, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ j.val)
      (by omega : (j.val : ℤ) < m + 1 + 5)] using heval
  have hdvd := hmod.dvd
  have hb := signed_bounds s
  have hz : (j.val : ℤ) - (i.val + signed s) = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
  omega

theorem rank_wrap {n : ℕ} (p : SourceModel.Profile n) (i : Fin (n + 5))
    (a : ℤ) (ha : -2 ≤ a ∧ a ≤ 2) :
    SourceModel.rank p i (wrap n (i.val + a)) = offsetRank (p i) a := by
  have hcases : a = 0 ∨ ∃ s, signed s = a := by
    rcases ha with ⟨hl, hu⟩
    interval_cases a
    · exact Or.inr ⟨3, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  rcases hcases with h | ⟨s, rfl⟩
  · simp [h, wrap_index, SourceModel.rank_self, offsetRank]
  · rw [wrap_add, wrap_index, wrap_signed, SourceModel.rank_neighbor, signed_rank]

/-- Appending six buffer sites preserves every old--old nonblocking test in the
literal source cycle, with actual ranks of exterior partners and of singles. -/
theorem closing_old_nonblocking {m : ℕ} {w : Word m} {d : Fin m → ℤ}
    (hw : Certificate w d) (p : SourceModel.Profile (m + 1))
    (hp : ∀ i : Fin m, p ⟨i.val, by omega⟩ = w i) (i j : Fin m)
    (hij : i.val < j.val)
    (hadj : (SourceModel.ring (m + 1)).Adj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :
    d i = (j.val : ℤ) - i.val ∨
      SourceModel.rank p ⟨i.val, by omega⟩ (wrap (m + 1) (i.val + d i)) <
        SourceModel.rank p ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ ∨
      SourceModel.rank p ⟨j.val, by omega⟩ (wrap (m + 1) (j.val + d j)) <
        SourceModel.rank p ⟨j.val, by omega⟩ ⟨i.val, by omega⟩ := by
  have hdist := closing_old_edge_local i j hadj
  have hh := hw.nonblocking i j hij (by omega)
  have hr := local_rank p (⟨i.val, by omega⟩ : Fin (m + 1 + 5)) ⟨j.val, by omega⟩
    hij (by change j.val ≤ i.val + 2; omega)
  have hri := rank_wrap p (⟨i.val, by omega⟩ : Fin (m + 1 + 5)) (d i) (hw.bounded i)
  have hrj := rank_wrap p (⟨j.val, by omega⟩ : Fin (m + 1 + 5)) (d j) (hw.bounded j)
  simpa only [hri, hrj, hr.1, hr.2.1, hp] using hh

#print axioms cut_certificate
#print axioms source_count_le_open_count
#print axioms source_probability_eq
#print axioms source_probability_le_open_proportion
#print axioms closing_request_source_target
#print axioms closing_old_edge_local
#print axioms closing_old_nonblocking

open OpenCertificates PaddedCompletion

variable {m : ℕ} {w : Word m} {d : Fin m → ℤ}

private def exterior (d : Fin m → ℤ) (i : Fin m) : Prop :=
  d i ≠ 0 ∧ ((i.val : ℤ) + d i < 0 ∨ (m : ℤ) ≤ i.val + d i)

private def inside (d : Fin m → ℤ) (i : Fin m) (h : ¬exterior d i) : Fin m :=
  ⟨((i.val : ℤ) + d i).toNat, by
    have hi := i.isLt
    simp only [exterior, not_and_or, not_or] at h
    rcases h with h | ⟨h,h'⟩ <;> omega⟩

private theorem inside_coord (i : Fin m) (h : ¬exterior d i) :
    ((inside d i h).val : ℤ) = i.val + d i := by
  have hi := i.isLt
  simp only [exterior, not_and_or, not_or] at h
  rcases h with h | ⟨h,h'⟩ <;> simp only [inside] <;> omega

private def joinPartner (hw : Certificate w d) : Fin m ⊕ Fin 6 → Fin m ⊕ Fin 6
  | .inl i => if h : exterior d i then .inr (closingRequest d hw.bounded ⟨i,h⟩)
      else .inl (inside d i h)
  | .inr b => match BufferLayout.partner (closingRequest d hw.bounded) (.inr b) with
      | .inl a => .inl a.val
      | .inr c => .inr c

private theorem joinPartner_involutive (hw : Certificate w d) :
    Function.Involutive (joinPartner hw) := by
  have hc := closing_request_completion hw
  intro x
  cases x with
  | inl i =>
    by_cases h : exterior d i
    · have he : ∃ a : ClosingRequester d, (closingRequest d hw.bounded) a = (closingRequest d hw.bounded) ⟨i,h⟩ := ⟨⟨i,h⟩,rfl⟩
      have hh : Classical.choose he = (⟨i,h⟩ : ClosingRequester d) := hc.1 (Classical.choose_spec he)
      simp only [joinPartner, dite_eq_left h, BufferLayout.partner, dite_eq_left he, hh]
    · let j := inside d i h
      have hj := inside_coord i h
      have hdj : d j = -d i := by
        by_cases hz : d i = 0
        · have he : j = i := Fin.ext (by change (j.val : ℤ) = i.val + d i at hj; omega)
          simp [he, hz]
        · exact hw.reciprocal i j hz hj.symm
      have hn : ¬exterior d j := by
        have hi := i.isLt
        dsimp [exterior]
        omega
      have he : inside d j hn = i := by
        apply Fin.ext
        have ht := inside_coord j hn
        omega
      simp only [joinPartner, dite_eq_right h]
      change joinPartner hw (.inl j) = .inl i
      simp only [joinPartner, dite_eq_right hn, he]
  | inr b =>
    by_cases h : ∃ a : ClosingRequester d, (closingRequest d hw.bounded) a = b
    · have ha : (closingRequest d hw.bounded) (Classical.choose h) = b := Classical.choose_spec h
      have he : exterior d (Classical.choose h).val := (Classical.choose h).property
      simp only [joinPartner, BufferLayout.partner, dite_eq_left h, dite_eq_left he]
      exact congrArg Sum.inr ha
    · have hfree : ¬∃ a : ClosingRequester d,
          (closingRequest d hw.bounded) a = BufferLayout.mate (BufferLayout.flags (closingRequest d hw.bounded)) b := by
        intro ⟨a,ha⟩
        have he := hc.2.1 (.inr b)
        simp only [BufferLayout.partner, dite_eq_right h, dite_eq_left (show ∃ a', (closingRequest d hw.bounded) a' =
          BufferLayout.mate (BufferLayout.flags (closingRequest d hw.bounded)) b from ⟨a,ha⟩)] at he
        cases he
      have he := hc.2.1 (.inr b)
      simp only [BufferLayout.partner, dite_eq_right h, dite_eq_right hfree, Sum.inr.injEq] at he
      simpa only [joinPartner, BufferLayout.partner, dite_eq_right h, dite_eq_right hfree] using congrArg Sum.inr he

/-- The full cycle partner map, retaining old interior pairs and fulfilling all requests. -/
def matching (hw : Certificate w d) : SourceModel.Matching (Fin (m + 1 + 5)) := by
  let e : (Fin m ⊕ Fin 6) ≃ Fin (m + 1 + 5) := finSumFinEquiv
  let f := joinPartner hw
  have hf := joinPartner_involutive hw
  let g := fun i => e (f (e.symm i))
  have hg : Function.Involutive g := by
    intro i
    dsimp [g]
    rw [e.symm_apply_apply]
    change e (joinPartner hw (joinPartner hw (e.symm i))) = i
    rw [hf, e.apply_symm_apply]
  exact ⟨hg.toPerm g, hg⟩

private theorem matching_apply_sum (hw : Certificate w d) (x : Fin m ⊕ Fin 6) :
    (matching hw).val ((@finSumFinEquiv m 6) x) = (@finSumFinEquiv m 6) (joinPartner hw x) := by
  simp [matching, Function.Involutive.toPerm]

private theorem matching_old (hw : Certificate w d) (i : Fin m) :
    (matching hw).val (Fin.castAdd 6 i) = wrap (m + 1) (i.val + d i) := by
  have he := matching_apply_sum hw (.inl i)
  simp only [finSumFinEquiv_apply_left] at he
  rw [he]
  by_cases h : exterior d i
  · simp only [joinPartner, dite_eq_left h, finSumFinEquiv_apply_right]
    have ht := closing_request_source_target hw ⟨i,h⟩
    have hh := @wrap_index (m+1) ((@Fin.natAdd 6 m) (closingRequest d hw.bounded ⟨i,h⟩))
    exact (ht.trans hh).symm
  · simp only [joinPartner, dite_eq_right h, finSumFinEquiv_apply_left]
    have hc := inside_coord i h
    have hh := wrap_index (Fin.castAdd 6 (inside d i h))
    rw [show ((Fin.castAdd 6 (inside d i h)).val : ℤ) = i.val + d i from hc] at hh
    exact hh.symm

private theorem wrap_return {n : ℕ} (i j : Fin (n+5)) (a : ℤ)
    (h : wrap n (i.val + a) = j) : wrap n (j.val - a) = i := by
  calc
    wrap n (j.val - a) = j + wrap n (-a) := by rw [sub_eq_add_neg, wrap_add, wrap_index]
    _ = wrap n (i.val + a) + wrap n (-a) := by rw [h]
    _ = wrap n (i.val + a + -a) := (wrap_add _ _ _).symm
    _ = i := by simp [wrap_index]

private def bufferD (hw : Certificate w d) : Fin 6 → ℤ :=
  bufferOffset (closingRequest d hw.bounded) (fun a => d a.val)

private theorem request_boundary (hw : Certificate w d) (a : ClosingRequester d) :
    closingRequest d hw.bounded a ≠ 2 ∧ closingRequest d hw.bounded a ≠ 3 := by
  have hc := closing_coordinate hw.bounded a
  have hb := hw.bounded a.val
  have hi := a.val.isLt
  split_ifs at hc <;> constructor <;> intro he <;>
    have hv := congrArg (fun b : Fin 6 => (b.val : ℤ)) he <;> norm_num at hv <;> omega

private theorem buffer_facts (hw : Certificate w d) :
    (∀ a : ClosingRequester d, bufferD hw (closingRequest d hw.bounded a) = -d a.val) ∧
    (∀ b, -2 ≤ bufferD hw b ∧ bufferD hw b ≤ 2) ∧
    (∀ b, bufferD hw b = 0 → b = 2 ∨ b = 3) ∧
    (∀ b c, bufferD hw b = 0 → b ≠ c → b.val ≤ c.val+2 → c.val ≤ b.val+2 →
      bufferD hw c ≠ 0) :=
  buffer_offset_completion _ _ (closing_request_completion hw).1 (request_boundary hw)
    (fun a => ⟨(hw.bounded a.val).1, (hw.bounded a.val).2, a.property.1⟩)

private theorem matching_buffer (hw : Certificate w d) (b : Fin 6) :
    (matching hw).val ((@Fin.natAdd 6 m) b) = wrap (m+1) ((m : ℤ)+b.val+bufferD hw b) := by
  let r := closingRequest d hw.bounded
  have he := matching_apply_sum hw (.inr b)
  simp only [finSumFinEquiv_apply_right] at he
  rw [he]
  by_cases h : ∃ a : ClosingRequester d, r a = b
  · let a := Classical.choose h
    have ha : r a = b := Classical.choose_spec h
    have hd : bufferD hw b = -d a.val := by rw [←ha]; exact (buffer_facts hw).1 a
    simp only [r] at h ha
    simp only [joinPartner, BufferLayout.partner, dite_eq_left h, finSumFinEquiv_apply_left]
    have ht : wrap (m+1) (a.val.val + d a.val) = (@Fin.natAdd 6 m) b := by
      rw [closing_request_source_target hw a]
      simpa [r, ha] using (@wrap_index (m+1) ((@Fin.natAdd 6 m) b))
    have hr := wrap_return (Fin.castAdd 6 a.val) ((@Fin.natAdd 6 m) b) (d a.val) ht
    simpa only [Fin.val_natAdd, Nat.cast_add, hd, sub_eq_add_neg] using hr.symm
  · simp only [r] at h
    simp only [joinPartner, BufferLayout.partner, dite_eq_right h, finSumFinEquiv_apply_right]
    have hd : bufferD hw b = (BufferLayout.mate (BufferLayout.flags r) b).val - (b.val : ℤ) := by
      simp only [bufferD, bufferOffset, dite_eq_right h, r]
    rw [hd, show (m : ℤ)+b.val+((BufferLayout.mate (BufferLayout.flags r) b).val-b.val) =
      (m : ℤ)+(BufferLayout.mate (BufferLayout.flags r) b).val by omega]
    exact (@wrap_index (m+1) ((@Fin.natAdd 6 m) (BufferLayout.mate (BufferLayout.flags r) b))).symm

/-- Six added rankings preserve every old ranking literally. -/
def profile (hw : Certificate w d) : SourceModel.Profile (m+1) :=
  fun i => if h : i.val < m then w ⟨i.val,h⟩
    else partnerFirst (bufferD hw ⟨i.val-m,by omega⟩)

private theorem profile_old (hw : Certificate w d) (i : Fin m) :
    profile hw (Fin.castAdd 6 i) = w i := by simp [profile, i.isLt]

private theorem profile_buffer (hw : Certificate w d) (b : Fin 6) :
    profile hw ((@Fin.natAdd 6 m) b) = partnerFirst (bufferD hw b) := by
  simp [profile, show ¬m+b.val<m by omega]

private theorem matching_buffer_rank (hw : Certificate w d) (b : Fin 6) :
    SourceModel.rank (profile hw) ((@Fin.natAdd 6 m) b) ((matching hw).val ((@Fin.natAdd 6 m) b)) =
      offsetRank (partnerFirst (bufferD hw b)) (bufferD hw b) := by
  rw [matching_buffer]
  have hr := rank_wrap (profile hw) ((@Fin.natAdd 6 m) b) (bufferD hw b) ((buffer_facts hw).2.1 b)
  simpa [profile_buffer, Fin.val_natAdd, Nat.cast_add] using hr

private theorem buffer_top (hw : Certificate w d) (b : Fin 6) (hz : bufferD hw b ≠ 0) :
    SourceModel.rank (profile hw) ((@Fin.natAdd 6 m) b) ((matching hw).val ((@Fin.natAdd 6 m) b)) = 0 := by
  rw [matching_buffer_rank]
  have hb := (buffer_facts hw).2.1 b
  generalize bufferD hw b = a at *
  rcases hb with ⟨hl,hu⟩
  interval_cases a <;> norm_num [partnerFirst, offsetRank] at *

private theorem acceptable_offset {n : ℕ} (i : Fin (n+5)) (a : ℤ)
    (ha : -2 ≤ a ∧ a ≤ 2) :
    wrap n (i.val+a) = i ∨ (SourceModel.ring n).Adj i (wrap n (i.val+a)) := by
  by_cases hz : a = 0
  · left; simp [hz, wrap_index]
  · right
    have hs : ∃ s : Fin 4, signed s = a := by
      rcases ha with ⟨hl,hu⟩
      interval_cases a
      · exact ⟨3,rfl⟩
      · exact ⟨2,rfl⟩
      · contradiction
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
    obtain ⟨s,rfl⟩ := hs
    exact ⟨s,by rw [wrap_add, wrap_index, wrap_signed]⟩

/-- All old and new partners are acceptable source neighbors or singles. -/
theorem acceptable (hw : Certificate w d) :
    SourceModel.IsAcceptable (SourceModel.ring (m+1)) (matching hw) := by
  intro i
  obtain ⟨x,rfl⟩ := (@finSumFinEquiv m 6).surjective i
  cases x with
  | inl j =>
    simp only [finSumFinEquiv_apply_left]
    rw [matching_old]
    exact acceptable_offset (Fin.castAdd 6 j) (d j) (hw.bounded j)
  | inr b =>
    simp only [finSumFinEquiv_apply_right]
    rw [matching_buffer]
    exact acceptable_offset ((@Fin.natAdd 6 m) b) (bufferD hw b) ((buffer_facts hw).2.1 b)

private theorem central_neighbor (hw : Certificate w d) (b : Fin 6)
    (hz : bufferD hw b = 0) (j : Fin (m+1+5))
    (hadj : (SourceModel.ring (m+1)).Adj ((@Fin.natAdd 6 m) b) j) :
    ∃ c : Fin 6, j = (@Fin.natAdd 6 m) c ∧ b ≠ c ∧
      b.val ≤ c.val+2 ∧ c.val ≤ b.val+2 := by
  obtain ⟨s,hs⟩ := hadj
  have hc := (buffer_facts hw).2.2.1 b hz
  have hb : b.val = 2 ∨ b.val = 3 := by rcases hc with rfl | rfl <;> simp
  have hsb := signed_bounds s
  have he : wrap (m+1) ((m : ℤ)+b.val+signed s) = j := by
    rw [wrap_add, wrap_signed]
    have hx := @wrap_index (m+1) ((@Fin.natAdd 6 m) b)
    change wrap (m+1) ((m : ℤ)+b.val) = (@Fin.natAdd 6 m) b at hx
    rw [hx]
    exact hs.symm
  have hv := congrArg (fun x : Fin (m+1+5) => (x.val : ℤ)) he
  rw [wrap_val, Int.emod_eq_of_lt (by omega) (by omega)] at hv
  let c : Fin 6 := ⟨j.val-m,by omega⟩
  refine ⟨c, Fin.ext (by dsimp [c]; omega), ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun x : Fin 6 => (x.val : ℤ)) h
    dsimp [c] at hh
    omega
  · dsimp [c]; omega
  · dsimp [c]; omega

private theorem no_buffer_blocker (hw : Certificate w d) (b : Fin 6) (j : Fin (m+1+5)) :
    ¬SourceModel.IsBlockingPair (SourceModel.ring (m+1)) (SourceModel.rank (profile hw))
      (matching hw) ((@Fin.natAdd 6 m) b) j := by
  rintro ⟨hadj,_,hb,hj⟩
  by_cases hz : bufferD hw b = 0
  · obtain ⟨c,rfl,hbc,h₁,h₂⟩ := central_neighbor hw b hz j hadj
    have hc := (buffer_facts hw).2.2.2 b c hz hbc h₁ h₂
    rw [buffer_top hw c hc] at hj
    omega
  · rw [buffer_top hw b hz] at hb
    omega

private theorem no_old_blocker (hw : Certificate w d) (i j : Fin m) :
    ¬SourceModel.IsBlockingPair (SourceModel.ring (m+1)) (SourceModel.rank (profile hw))
      (matching hw) (Fin.castAdd 6 i) (Fin.castAdd 6 j) := by
  rintro ⟨hadj,hn,hi,hj⟩
  have hne : i ≠ j := by intro h; subst j; exact (SourceModel.ring (m+1)).irrefl hadj
  have hcase (i j : Fin m) (hlt : i.val<j.val)
      (hadj : (SourceModel.ring (m+1)).Adj (Fin.castAdd 6 i) (Fin.castAdd 6 j)) :
      (matching hw).val (Fin.castAdd 6 i) = Fin.castAdd 6 j ∨
      SourceModel.rank (profile hw) (Fin.castAdd 6 i) ((matching hw).val (Fin.castAdd 6 i)) <
        SourceModel.rank (profile hw) (Fin.castAdd 6 i) (Fin.castAdd 6 j) ∨
      SourceModel.rank (profile hw) (Fin.castAdd 6 j) ((matching hw).val (Fin.castAdd 6 j)) <
        SourceModel.rank (profile hw) (Fin.castAdd 6 j) (Fin.castAdd 6 i) := by
    have hh := closing_old_nonblocking hw (profile hw) (profile_old hw) i j hlt hadj
    rcases hh with he | he | he
    · left
      rw [matching_old, he]
      simpa only [add_sub_cancel, Fin.val_castAdd] using (wrap_index (Fin.castAdd 6 j))
    · right;left; rw [matching_old]
      simpa only [Fin.castAdd, Fin.castLE] using he
    · right;right; rw [matching_old]
      simpa only [Fin.castAdd, Fin.castLE] using he
  rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun h => hne (Fin.ext h)) with hlt | hlt
  · rcases hcase i j hlt hadj with he | he | he <;> omega
  · have hn' : (matching hw).val (Fin.castAdd 6 j) ≠ Fin.castAdd 6 i := by
      intro he
      apply hn
      have hh := (matching hw).property (Fin.castAdd 6 j)
      rw [he] at hh
      exact hh
    rcases hcase j i hlt hadj.symm with he | he | he <;> omega

/-- Every certified word, of either parity and including lengths one and two,
closes to an actual acceptable stable partial matching on the cycle m+6. -/
theorem stable (hw : Certificate w d) :
    SourceModel.IsStable (SourceModel.ring (m+1)) (SourceModel.rank (profile hw)) (matching hw) := by
  refine ⟨acceptable hw, ?_⟩
  intro i j
  obtain ⟨x,rfl⟩ := (@finSumFinEquiv m 6).surjective i
  obtain ⟨y,rfl⟩ := (@finSumFinEquiv m 6).surjective j
  cases x with
  | inl i =>
    cases y with
    | inl j => exact no_old_blocker hw i j
    | inr b =>
      rintro ⟨ha,hn,hi,hj⟩
      apply no_buffer_blocker hw b (Fin.castAdd 6 i)
      refine ⟨ha.symm, ?_, hj, hi⟩
      intro he
      apply hn
      have hh := (matching hw).property ((@Fin.natAdd 6 m) b)
      rw [he] at hh
      exact hh
  | inr b => exact no_buffer_blocker hw b _

/-- Choose one certificate per word and retain the word in the first m positions. -/
def close (w : CertifiedWord m) :
    {p : SourceModel.Profile (m+1) // SourceModel.HasStableMatching p} := by
  let d := Classical.choose w.property
  have hw := Classical.choose_spec w.property
  exact ⟨profile hw, matching hw, stable hw⟩

/-- Recovery depends only on the source profile, never on a certificate witness. -/
theorem close_injective (m : ℕ) : Function.Injective (@close m) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrArg (fun p : {p : SourceModel.Profile (m+1) // SourceModel.HasStableMatching p} =>
    p.val (Fin.castAdd 6 i)) h
  simpa only [close, profile_old] using he

/-- Certified words inject into successful labelled profiles on m+6 sites.
This holds at every length, in particular every m≥1, and counts profiles once. -/
theorem count_le_successful_profile_count (m : ℕ) :
    count m ≤ Fintype.card {p : SourceModel.Profile (m+1) // SourceModel.HasStableMatching p} :=
  Fintype.card_le_of_injective close (close_injective m)

#print axioms matching
#print axioms acceptable
#print axioms stable
#print axioms close_injective
#print axioms count_le_successful_profile_count

end D5.S3.Combinatorics.Graph.Roommates.CyclicClosure

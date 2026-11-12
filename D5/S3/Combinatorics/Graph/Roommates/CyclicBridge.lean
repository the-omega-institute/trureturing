/- GID: D5/S3/Combinatorics/Graph/Roommates/CyclicBridge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/CyclicBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Literal cyclic ranks and stable partial matchings give integer-target open certificates. -/

import D5.S3.Combinatorics.Graph.Roommates.SourceModel
import D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
import D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Roommates.CyclicBridge
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

end D5.S3.Combinatorics.Graph.Roommates.CyclicBridge

import D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

/-! Finite-support deterministic adaptive two-readout collisions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.AdaptiveTwoReadout

open D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
open D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
open D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction

universe u
variable {α : Type u} [DecidableEq α]

abbrev SupportedCircle (A : Finset α) :=
  D5.S3.Combinatorics.CircularWords.DeletionReadoutReconstruction.SupportedCircle A

/-- The first label, first labelled residual, deterministic second label, and
    second labelled residual, all from the same original supported circle. -/
def adaptiveTrace (A : Finset α) (x : A) (σ : Cycle α → A)
    (C : SupportedCircle A) : A × Cycle α × A × Cycle α :=
  (x, delete x.1 C.1, σ (delete x.1 C.1),
    delete (σ (delete x.1 C.1)).1 C.1)

private theorem mem_support (C : Cycle α) (x : α) :
    x ∈ C.toFinset ↔ x ∈ C := by
  induction C using Quotient.inductionOn with
  | _ l => exact List.mem_toFinset

private theorem cycle_support_insert (r : α) (P Q : List α) (u z : α) :
    (r :: P ++ [u, z] ++ Q : List α).toFinset =
      insert u (r :: P ++ [z] ++ Q : List α).toFinset := by
  ext y
  simp [List.mem_append, or_assoc, or_left_comm, or_comm]

private theorem filter_absent {L : List α} {x : α} (hx : x ∉ L) :
    L.filter (fun y => decide (y ≠ x)) = L := by
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  exact fun e => hx (e ▸ hy)

/-- A supported residual always exists once the support has at least three labels. -/
theorem exists_supported_residual
    {A : Finset α} {x : α} (hx : x ∈ A) (hA : 3 ≤ A.card) :
    ∃ B : Cycle α, B.Nodup ∧ B.toFinset = A.erase x := by
  let L : List α := (A.erase x).toList
  refine ⟨(L : Cycle α), ?_, ?_⟩
  · exact Cycle.nodup_coe_iff.mpr (by simp [L, Finset.nodup_toList])
  · simp [L]

/-- Swapping x across the policy's distinct second label preserves both
    labelled deletions. -/
theorem adjacent_pair_collision
    {A : Finset α} (hA : 3 ≤ A.card) {x z : α} (hx : x ∈ A) (hz : z ∈ A) (hxz : x ≠ z)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B ∧
      delete z C = delete z D := by
  obtain ⟨r, hrA, hr⟩ : ∃ r ∈ A, r ∉ ({x, z} : Finset α) := by
    by_contra hn
    have hs : A ⊆ ({x, z} : Finset α) := by
      intro y hy
      by_contra hy'
      exact hn ⟨y, hy, hy'⟩
    have hc := Finset.card_le_card hs
    have ht : ({x, z} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have hrx : r ≠ x := by
    intro e
    exact hr (by simp [e])
  have hrz : r ≠ z := by
    intro e
    exact hr (by simp [e])
  have hrBfin : r ∈ B.toFinset := by
    rw [sB]
    exact Finset.mem_erase.mpr ⟨hrx, hrA⟩
  have hrB : r ∈ B := (mem_support B r).mp hrBfin
  have hzBfin : z ∈ B.toFinset := by
    rw [sB]
    exact Finset.mem_erase.mpr ⟨Ne.symm hxz, hz⟩
  have hzB : z ∈ B := (mem_support B z).mp hzBfin
  obtain ⟨L, hroot⟩ := rooted hrB
  have hnroot : (r :: L).Nodup := by simpa [hroot] using hB
  have hzroot : z ∈ (r :: L : List α) := by
    have : z ∈ (r :: L : Cycle α) := by simpa [hroot] using hzB
    exact Cycle.mem_coe_iff.mp this
  have hzL : z ∈ L := (List.mem_cons.mp hzroot).resolve_left (Ne.symm hrz)
  obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hzL
  have hbaseN : (r :: P ++ [z] ++ Q).Nodup := by
    simpa [hPQ, List.cons_append] using hnroot
  have hBform : B = (r :: P ++ [z] ++ Q : List α) := by
    simpa [hPQ, List.cons_append] using hroot
  have hbaseSup : (r :: P ++ [z] ++ Q : List α).toFinset = A.erase x := by
    simpa only [hBform, Cycle.coe_toFinset] using sB
  have hxbase : x ∉ r :: P ++ [z] ++ Q := by
    intro hm
    have hm' : x ∈ (r :: P ++ [z] ++ Q : List α).toFinset :=
      List.mem_toFinset.mpr hm
    rw [hbaseSup] at hm'
    simpa [hx] using hm'
  have hrtail : r ∉ P ++ [z] ++ Q := (List.nodup_cons.mp hbaseN).1
  have htailN : (P ++ [z] ++ Q).Nodup := (List.nodup_cons.mp hbaseN).2
  have hzfrontN : (z :: (P ++ Q)).Nodup := by
    apply (List.nodup_middle (l₁ := P) (a := z) (l₂ := Q)).mp
    simpa [List.append_assoc] using htailN
  have hzPQ : z ∉ P ++ Q := (List.nodup_cons.mp hzfrontN).1
  have hzP : z ∉ P := by
    intro hp
    exact hzPQ (by simp [hp])
  have hzQ : z ∉ Q := by
    intro hq
    exact hzPQ (by simp [hq])
  have hxTail : x ∉ P ++ [z] ++ Q := by
    intro hm
    exact hxbase (by simp [hm])
  have hxP : x ∉ P := by
    intro hp
    exact hxTail (by simp [hp])
  have hxQ : x ∉ Q := by
    intro hq
    exact hxTail (by simp [hq])
  have hrtailC : r ∉ P ++ [x, z] ++ Q := by
    simpa [List.mem_append, hrx, or_assoc, or_left_comm, or_comm] using hrtail
  have hrtailD : r ∉ P ++ [z, x] ++ Q := by
    simpa [List.mem_append, hrx, or_assoc, or_left_comm, or_comm] using hrtail
  have hxfrontN : (x :: (P ++ z :: Q)).Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simpa [List.append_assoc] using hxTail,
      by simpa [List.append_assoc] using htailN⟩
  have hCtail : (P ++ x :: z :: Q).Nodup := by
    have h := (List.nodup_middle (l₁ := P) (a := x) (l₂ := z :: Q)).mpr hxfrontN
    simpa [List.append_assoc] using h
  have hDtail : (P ++ z :: x :: Q).Nodup := by
    have h := (List.nodup_middle (l₁ := P ++ [z]) (a := x) (l₂ := Q)).mpr
      (by simpa [List.append_assoc] using hxfrontN)
    simpa [List.append_assoc] using h
  let C : Cycle α := (r :: P ++ [x, z] ++ Q : List α)
  let D : Cycle α := (r :: P ++ [z, x] ++ Q : List α)
  have hCnodup : C.Nodup := by
    apply Cycle.nodup_coe_iff.mpr
    exact List.nodup_cons.mpr ⟨hrtailC, by simpa [List.append_assoc] using hCtail⟩
  have hDnodup : D.Nodup := by
    apply Cycle.nodup_coe_iff.mpr
    exact List.nodup_cons.mpr ⟨hrtailD, by simpa [List.append_assoc] using hDtail⟩
  have hCsup : C.toFinset = A := by
    change (r :: P ++ [x, z] ++ Q : List α).toFinset = A
    rw [cycle_support_insert, hbaseSup, Finset.insert_erase hx]
  have hDsup : D.toFinset = A := by
    change (r :: P ++ [z, x] ++ Q : List α).toFinset = A
    have he : (r :: P ++ [z, x] ++ Q : List α).toFinset =
        (r :: P ++ [x, z] ++ Q : List α).toFinset := by
      ext y
      simp [or_assoc, or_left_comm, or_comm]
    rw [he, cycle_support_insert, hbaseSup, Finset.insert_erase hx]
  have hxfilterC :
      (r :: P ++ [x, z] ++ Q).filter (fun y => decide (y ≠ x)) =
        r :: P ++ [z] ++ Q := by
    simp [hrx, hxz, Ne.symm hxz, filter_absent hxP, filter_absent hxQ]
  have hxfilterD :
      (r :: P ++ [z, x] ++ Q).filter (fun y => decide (y ≠ x)) =
        r :: P ++ [z] ++ Q := by
    simp [hrx, hxz, Ne.symm hxz, filter_absent hxP, filter_absent hxQ]
  have hzfilterC :
      (r :: P ++ [x, z] ++ Q).filter (fun y => decide (y ≠ z)) =
        r :: P ++ [x] ++ Q := by
    simp [hrz, hxz, Ne.symm hxz, filter_absent hzP, filter_absent hzQ]
  have hzfilterD :
      (r :: P ++ [z, x] ++ Q).filter (fun y => decide (y ≠ z)) =
        r :: P ++ [x] ++ Q := by
    simp [hrz, hxz, Ne.symm hxz, filter_absent hzP, filter_absent hzQ]
  have hCdelx : delete x C = B := by
    dsimp [C]
    change (((r :: P ++ [x, z] ++ Q).filter (fun y => decide (y ≠ x))) : Cycle α) = B
    rw [hxfilterC, hBform]
  have hDdelx : delete x D = B := by
    dsimp [D]
    change (((r :: P ++ [z, x] ++ Q).filter (fun y => decide (y ≠ x))) : Cycle α) = B
    rw [hxfilterD, hBform]
  have hdelz : delete z C = delete z D := by
    dsimp [C, D]
    change (((r :: P ++ [x, z] ++ Q).filter (fun y => decide (y ≠ z))) : Cycle α) =
      (((r :: P ++ [z, x] ++ Q).filter (fun y => decide (y ≠ z))) : Cycle α)
    rw [hzfilterC, hzfilterD]
  have hneq : C ≠ D := by
    intro heq
    have hlist₀ := anchored_coe_injective (Cycle.nodup_coe_iff.mp hCnodup) heq
    have hlist : P ++ ([x, z] ++ Q) = P ++ ([z, x] ++ Q) := by
      simpa [List.append_assoc] using hlist₀
    have hmid := List.append_cancel_left hlist
    have hxy := List.append_cancel_right hmid
    exact hxz (List.cons.inj hxy).1
  exact ⟨C, D, hCnodup, hDnodup, hCsup, hDsup, hneq, hCdelx, hDdelx, hdelz⟩

/-- The two gaps immediately before and after a residual label are distinct
    when the residual has at least two labels. Both lifts delete back to B. -/
theorem two_gap_collision
    {A : Finset α} {x : α} (hx : x ∈ A) (hA : 3 ≤ A.card)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B := by
  have hpos : 0 < (A.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  have hz' := Finset.mem_erase.mp hz
  obtain ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx, _⟩ :=
    adjacent_pair_collision hA hx hz'.2 (Ne.symm hz'.1) hB sB
  exact ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx⟩

/-- For every residual branch, the policy's returned label has a collision. -/
theorem adaptive_branch_collision
    {A : Finset α} (hA : 3 ≤ A.card) {x : α} (hx : x ∈ A)
    {B : Cycle α} (hB : B.Nodup) (sB : B.toFinset = A.erase x)
    (σ : Cycle α → A) :
    ∃ C D : Cycle α,
      C.Nodup ∧ D.Nodup ∧ C.toFinset = A ∧ D.toFinset = A ∧
      C ≠ D ∧ delete x C = B ∧ delete x D = B ∧
      delete (σ B).1 C = delete (σ B).1 D := by
  by_cases h : (σ B).1 = x
  · obtain ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx⟩ :=
      two_gap_collision hx hA hB sB
    exact ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx, by simpa [h] using hCx.trans hDx.symm⟩
  · obtain ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx, hDz⟩ :=
      adjacent_pair_collision hA hx (σ B).property (Ne.symm h) hB sB
    exact ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx, hDz⟩

/-- No deterministic second-label policy can make the retained two-readout
    trace injective on any fixed support of size at least three. -/
theorem no_adaptive_two_reconstruction
    {A : Finset α} (hA : 3 ≤ A.card) :
    ∀ (x : A) (σ : Cycle α → A),
      ¬ Function.Injective (adaptiveTrace A x σ) := by
  intro x σ hinj
  obtain ⟨B, hB, sB⟩ := exists_supported_residual x.property hA
  obtain ⟨C, D, hC, hD, sC, sD, hneq, hCx, hDx, hDz⟩ :=
    adaptive_branch_collision hA x.property hB sB σ
  let C' : SupportedCircle A := ⟨C, hC, sC⟩
  let D' : SupportedCircle A := ⟨D, hD, sD⟩
  have htrace : adaptiveTrace A x σ C' = adaptiveTrace A x σ D' := by
    simp [adaptiveTrace, C', D', hCx, hDx, hDz]
  have hCD : C' = D' := hinj htrace
  exact hneq (congrArg Subtype.val hCD)

#check @adaptiveTrace
#check @exists_supported_residual
#check @adjacent_pair_collision
#check @two_gap_collision
#check @adaptive_branch_collision
#check @no_adaptive_two_reconstruction

#print axioms exists_supported_residual
#print axioms two_gap_collision
#print axioms adjacent_pair_collision
#print axioms adaptive_branch_collision
#print axioms no_adaptive_two_reconstruction

end D5.S3.Combinatorics.CircularWords.AdaptiveTwoReadout

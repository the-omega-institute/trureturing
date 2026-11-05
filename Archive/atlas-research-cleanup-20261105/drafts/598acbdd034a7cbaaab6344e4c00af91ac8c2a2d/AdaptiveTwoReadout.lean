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

/-- The first label, first labelled residual, deterministic second label, and
    second labelled residual, all from the same original supported circle. -/
def adaptiveTrace (A : Finset α) (x : A) (σ : Cycle α → A)
    (C : SupportedCircle A) : A × Cycle α × A × Cycle α :=
  (x, delete x.1 C.1, σ (delete x.1 C.1),
    delete (σ (delete x.1 C.1)).1 C.1)

private theorem filter_absent {L : List α} {x : α} (hx : x ∉ L) :
    L.filter (fun y => decide (y ≠ x)) = L := by
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  exact fun e => hx (e ▸ hy)

/-- A supported residual always exists once the support has at least three labels. -/
theorem exists_supported_residual
    {A : Finset α} {x : α} (_hx : x ∈ A) (_hA : 3 ≤ A.card) :
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
  induction B using Quotient.inductionOn with
  | _ W =>
    have hW : W.Nodup := Cycle.nodup_coe_iff.mp hB
    change W.toFinset = A.erase x at sB
    have hzW : z ∈ W := List.mem_toFinset.mp (by
      rw [sB]
      exact Finset.mem_erase.mpr ⟨Ne.symm hxz, hz⟩)
    obtain ⟨P, Q, rfl⟩ := List.mem_iff_append.mp hzW
    let R := Q ++ P
    have hfront : (z :: (P ++ Q)).Nodup := List.nodup_middle.mp hW
    have hzR : z ∉ R := by
      simpa [R, List.mem_append, or_comm] using (List.nodup_cons.mp hfront).1
    have hR : R.Nodup := List.nodup_append_comm.mp (List.nodup_cons.mp hfront).2
    have hZR : (z :: R).Nodup := List.nodup_cons.mpr ⟨hzR, hR⟩
    have hres : (P ++ z :: Q : List α) = (z :: R : Cycle α) := by
      apply Cycle.coe_eq_coe.mpr
      refine ⟨P.length, ?_⟩
      simpa only [List.cons_append, R] using List.rotate_append_length_eq P (z :: Q)
    have hsup : (z :: R : List α).toFinset = A.erase x :=
      (congrArg Cycle.toFinset hres).symm.trans sB
    have hxR : x ∉ R := by
      intro hm
      have hm' : x ∈ (z :: R : List α).toFinset := by simp [hm]
      rw [hsup] at hm'
      exact Finset.notMem_erase x A hm'
    have hsize : (A.erase x).card = (z :: R).length := by
      rw [← hsup, List.toFinset_card_of_nodup hZR]
    have hR0 : R ≠ [] := by
      intro he
      rw [he, Finset.card_erase_of_mem hx] at hsize
      simp only [List.length_cons, List.length_nil] at hsize
      omega
    let C : Cycle α := (x :: z :: R : List α)
    let D : Cycle α := (x :: (R ++ [z]) : List α)
    have hCnodup : C.Nodup := Cycle.nodup_coe_iff.mpr
      (List.nodup_cons.mpr ⟨by simp [hxz, hxR], hZR⟩)
    have hDnodup : D.Nodup := by
      apply Cycle.nodup_coe_iff.mpr
      apply List.nodup_cons.mpr
      refine ⟨by simp [hxR, hxz], ?_⟩
      exact (List.nodup_middle (l₁ := R) (a := z) (l₂ := [])).mpr (by simpa using hZR)
    have hCsup : C.toFinset = A := by
      change (x :: z :: R : List α).toFinset = A
      rw [List.toFinset_cons, hsup, Finset.insert_erase hx]
    have hDsup : D.toFinset = A := by
      change (x :: (R ++ [z]) : List α).toFinset = A
      have hs : (R ++ [z] : List α).toFinset = (z :: R : List α).toFinset := by
        ext y
        simp
      rw [List.toFinset_cons, hs, hsup, Finset.insert_erase hx]
    have hCx : delete x C = (z :: R : Cycle α) := by
      change (((x :: z :: R).filter (fun y => decide (y ≠ x))) : Cycle α) = _
      simp only [List.filter_cons, List.filter_append, List.filter_nil, filter_absent hxR]
      simp [Ne.symm hxz]
    have hDx : delete x D = (R ++ [z] : Cycle α) := by
      change (((x :: (R ++ [z])).filter (fun y => decide (y ≠ x))) : Cycle α) = _
      simp only [List.filter_cons, List.filter_append, List.filter_nil, filter_absent hxR]
      simp [Ne.symm hxz]
    have hCz : delete z C = (x :: R : Cycle α) := by
      change (((x :: z :: R).filter (fun y => decide (y ≠ z))) : Cycle α) = _
      simp only [List.filter_cons, List.filter_append, List.filter_nil, filter_absent hzR]
      simp [hxz]
    have hDz : delete z D = (x :: R : Cycle α) := by
      change (((x :: (R ++ [z])).filter (fun y => decide (y ≠ z))) : Cycle α) = _
      simp only [List.filter_cons, List.filter_append, List.filter_nil, filter_absent hzR]
      simp [hxz]
    have hneq : C ≠ D := by
      intro heq
      have ht : z :: R = R ++ [z] :=
        anchored_coe_injective (Cycle.nodup_coe_iff.mp hCnodup) heq
      cases hRT : R with
      | nil => exact hR0 hRT
      | cons t T =>
        have hzt : z = t := by
          rw [hRT] at ht
          exact (List.cons.inj ht).1
        apply hzR
        rw [hRT, hzt]
        exact List.mem_cons_self
    exact ⟨C, D, hCnodup, hDnodup, hCsup, hDsup, hneq,
      hCx.trans hres.symm,
      hDx.trans ((Cycle.coe_cons_eq_coe_append R z).symm.trans hres.symm),
      hCz.trans hDz.symm⟩

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

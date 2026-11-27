/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinTransferCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinLargeTransferCertificates.rowSeven; instance=D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinLargeTransferCertificates.rowSeven
   digest: Exact sparse successor actions for the column and proper-word transfers. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

/-! The sparse successor sets and their action on arbitrary integer vectors
supply the checked height-seven and width-seven quotient rows. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinTransferCertificates

open HardinActualTransfers
open HardinColumnContinuations (Column cross)
open HardinThinGraphTransport (Row proper compatible)

private def columnBond {n : ℕ} (i j : Fin n) : Prop :=
  i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1

private def wordBond {n : ℕ} (d : Bool) (i j : Fin n) : Prop :=
  if d then i.val + 1 = j.val ∨ j.val + 1 = i.val else i = j

private instance {n : ℕ} : DecidableRel (@columnBond n) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private instance {n : ℕ} (d : Bool) : DecidableRel (@wordBond n d) :=
  fun i j => by unfold wordBond; infer_instance

private theorem columnBond_spec {h : ℕ} (p q : Column h) :
    (∀ i j, columnBond i j → p i ≠ q j) ↔ cross p q := (cross_iff p q).symm

private theorem wordBond_spec {k : ℕ} (d : Bool) (p q : Row k) :
    (∀ i j, wordBond d i j → p i ≠ q j) ↔ compatible d p q := by
  cases d
  · simp only [wordBond, compatible, Bool.false_eq_true, ite_false]
    exact ⟨fun h i => h i i rfl, fun h i j hij => hij ▸ h i⟩
  · simp only [wordBond, compatible, ite_true]
    constructor
    · intro h a
      exact ⟨h a.castSucc a.succ (Or.inl rfl), h a.succ a.castSucc (Or.inr rfl)⟩
    · intro h i j hij
      rcases hij with hij | hij
      · let a : Fin k := ⟨i.val, by omega⟩
        have hi : i = a.castSucc := Fin.ext rfl
        have hj : j = a.succ := Fin.ext hij.symm
        rw [hi, hj]
        exact (h a).1
      · let a : Fin k := ⟨j.val, by omega⟩
        have hi : i = a.succ := Fin.ext hij.symm
        have hj : j = a.castSucc := Fin.ext rfl
        rw [hi, hj]
        exact (h a).2

private def candidates {n : ℕ} (bond : Fin n → Fin n → Prop) [DecidableRel bond]
    (p : Fin n → Fin 3) : Finset (Fin n → Fin 3) :=
  Fintype.piFinset fun j => Finset.univ.filter fun c => ∀ i, bond i j → p i ≠ c

private theorem mem_candidates {n : ℕ} (bond : Fin n → Fin n → Prop) [DecidableRel bond]
    (p q : Fin n → Fin 3) : q ∈ candidates bond p ↔ ∀ i j, bond i j → p i ≠ q j := by
  simp only [candidates, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h i j => h j i, fun h j i => h i j⟩

def code (n : ℕ) : (Fin n → Fin 3) ≃ Fin (3 ^ n) := finFunctionFinEquiv

def columnSuccessors (h : ℕ) (a : Fin (3 ^ (h + 1))) : Finset (Fin (3 ^ (h + 1))) :=
  (candidates columnBond ((code (h + 1)).symm a)).map (code (h + 1)).toEmbedding

def wordSuccessors (d : Bool) (k : ℕ) (a : Fin (3 ^ (k + 1))) :
    Finset (Fin (3 ^ (k + 1))) :=
  let p := (code (k + 1)).symm a
  if proper p then
    ((candidates (wordBond d) p).filter proper).map (code (k + 1)).toEmbedding
  else ∅

theorem column_action (h : ℕ) (p : Column h) (v : Fin (3 ^ (h + 1)) → ℤ) :
    (∑ j ∈ columnSuccessors h (code (h + 1) p), v j) =
      (C h).mulVec (fun q => v (code (h + 1) q)) p := by
  simp only [columnSuccessors, Equiv.symm_apply_apply, Finset.sum_map, Equiv.toEmbedding_apply]
  have hc : candidates columnBond p = Finset.univ.filter (cross p) := by
    ext x
    simp [mem_candidates, columnBond_spec]
  rw [hc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  change (if cross p q then v (code (h + 1) q) else 0) =
    (if cross p q then 1 else 0) * v (code (h + 1) q)
  split_ifs <;> simp

theorem word_action (d : Bool) (k : ℕ) (p : Word k) (v : Fin (3 ^ (k + 1)) → ℤ) :
    (∑ j ∈ wordSuccessors d k (code (k + 1) p.val), v j) =
      (wordTransfer d k).mulVec (fun q => v (code (k + 1) q.val)) p := by
  simp only [wordSuccessors, Equiv.symm_apply_apply, p.property, ite_true,
    Finset.sum_map, Equiv.toEmbedding_apply]
  have hc : (candidates (wordBond d) p.val).filter proper =
      Finset.univ.filter (fun q => proper q ∧ compatible d p.val q) := by
    ext x
    simp [mem_candidates, wordBond_spec, and_comm]
  rw [hc, Finset.sum_filter]
  change _ = ∑ q : Word k, (if compatible d p.val q.val then 1 else 0) * v (code (k + 1) q.val)
  rw [sum_words (fun q => (if compatible d p.val q then 1 else 0) * v (code (k + 1) q))]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hp : proper q <;> by_cases hb : compatible d p.val q <;> simp [hp, hb]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinTransferCertificates

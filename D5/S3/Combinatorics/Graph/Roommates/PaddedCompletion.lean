/- GID: D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/PaddedCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Separated certified pieces have globally injective requests into the six-site buffer. -/

import D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
import D5.S3.Combinatorics.Graph.Roommates.BufferLayout

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion
open OpenCertificates

/-- Integer coordinates retain every exterior target, rather than reducing it modulo a length. -/
def oldPosition {m k : ℕ} : Fin m ⊕ Fin k → ℤ
  | .inl i => i.val
  | .inr j => (m : ℤ) + 6 + j.val

def oldOffset {m k : ℕ} (d : Fin m → ℤ) (e : Fin k → ℤ) : Fin m ⊕ Fin k → ℤ
  | .inl i => d i
  | .inr j => e j

def oldTarget {m k : ℕ} (d : Fin m → ℤ) (e : Fin k → ℤ) (i : Fin m ⊕ Fin k) : ℤ :=
  oldPosition i + oldOffset d e i

/-- Two separated certified pieces cannot collide, even at exterior integer targets. -/
theorem old_target_injective {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e)
    (i j : Fin m ⊕ Fin k) (hi : oldOffset d e i ≠ 0) (hj : oldOffset d e j ≠ 0)
    (heq : oldTarget d e i = oldTarget d e j) : i = j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (hw.target_injective i j hi hj heq)
    | inr j =>
      have hb := hw.bounded i
      have hc := hv.bounded j
      simp only [oldTarget, oldPosition, oldOffset] at heq
      have := i.isLt
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hb := hv.bounded i
      have hc := hw.bounded j
      simp only [oldTarget, oldPosition, oldOffset] at heq
      have := j.isLt
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply hv.target_injective i j hi hj
      simp only [oldTarget, oldPosition, oldOffset] at heq
      omega

/-- Actual old vertices whose requests land inside the inserted buffer. -/
def Requester {m k : ℕ} (d : Fin m → ℤ) (e : Fin k → ℤ) :=
  {i : Fin m ⊕ Fin k // oldOffset d e i ≠ 0 ∧
    (m : ℤ) ≤ oldTarget d e i ∧ oldTarget d e i < (m : ℤ) + 6}

def request {m k : ℕ} (d : Fin m → ℤ) (e : Fin k → ℤ) (i : Requester d e) : Fin 6 :=
  ⟨(oldTarget d e i.val - m).toNat, by have := i.property; omega⟩

private theorem request_coordinate {m k : ℕ} {d : Fin m → ℤ} {e : Fin k → ℤ}
    (i : Requester d e) : (m : ℤ) + (request d e i).val = oldTarget d e i.val := by
  have := i.property
  simp only [request]
  omega

private theorem request_injective {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e) :
    Function.Injective (request d e) := by
  intro i j h
  apply Subtype.ext
  apply old_target_injective hw hv i.val j.val i.property.1 j.property.1
  have hi := request_coordinate i
  have hj := request_coordinate j
  rw [h] at hi
  omega

/-- Left requests land only at sites 0,1 and right requests only at sites 4,5. -/
private theorem request_boundary {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e)
    (i : Requester d e) : request d e i ≠ 2 ∧ request d e i ≠ 3 := by
  rcases i with ⟨i | i, hp⟩
  · have hr := request_coordinate (⟨.inl i, hp⟩ : Requester d e)
    have hb := hw.bounded i
    have hlt := i.isLt
    change (m : ℤ) + (request d e ⟨.inl i, hp⟩).val = (i.val : ℤ) + d i at hr
    constructor <;> intro h <;> have hh := congrArg Fin.val h <;> norm_num at hh <;> omega
  · have hr := request_coordinate (⟨.inr i, hp⟩ : Requester d e)
    have hb := hv.bounded i
    change (m : ℤ) + (request d e ⟨.inr i, hp⟩).val = (m : ℤ) + 6 + i.val + e i at hr
    constructor <;> intro h <;> have hh := congrArg Fin.val h <;> norm_num at hh <;> omega

/-- The completion for the actual requests of two certified pieces is an involution.
All integer target collisions have already been excluded, not assumed. This statement
does not yet assert nonblocking of the complete concatenated preference word. -/
theorem padded_request_completion {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e) :
    (∀ i j, oldOffset d e i ≠ 0 → oldOffset d e j ≠ 0 →
      oldTarget d e i = oldTarget d e j → i = j) ∧
    Function.Involutive (BufferLayout.partner (request d e)) ∧
    (∀ i, BufferLayout.partner (request d e) (.inl i) = .inr (request d e i)) ∧
    (∀ i, BufferLayout.partner (request d e) (.inr i) = .inr i → i = 2 ∨ i = 3) := by
  exact ⟨old_target_injective hw hv,
    BufferLayout.complete_requests (request d e) (request_injective hw hv) (request_boundary hw hv)⟩

#print axioms old_target_injective
#print axioms padded_request_completion
end D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

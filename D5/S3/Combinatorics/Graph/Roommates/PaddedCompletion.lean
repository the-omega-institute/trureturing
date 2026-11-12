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

def oldRanking {m k : ℕ} (w : Word m) (v : Word k) : Fin m ⊕ Fin k → Ranking
  | .inl i => w i
  | .inr j => v j

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

/-- All old--old nonblocking tests survive the actual six-gap placement.
The separation itself rules out an edge between different old pieces. -/
theorem old_nonblocking {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e)
    (i j : Fin m ⊕ Fin k) (hij : oldPosition i < oldPosition j)
    (hdist : oldPosition j ≤ oldPosition i + 2) :
    oldOffset d e i = oldPosition j - oldPosition i ∨
      offsetRank (oldRanking w v i) (oldOffset d e i) <
        offsetRank (oldRanking w v i) (oldPosition j - oldPosition i) ∨
      offsetRank (oldRanking w v j) (oldOffset d e j) <
        offsetRank (oldRanking w v j) (oldPosition i - oldPosition j) := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact hw.nonblocking i j (by simpa [oldPosition] using hij)
        (by simp only [oldPosition] at hdist; omega)
    | inr j =>
      simp only [oldPosition] at hdist
      have := i.isLt
      omega
  | inr i =>
    cases j with
    | inl j =>
      simp only [oldPosition] at hij
      have := j.isLt
      omega
    | inr j =>
      have hh := hv.nonblocking i j (by simp only [oldPosition] at hij; omega)
        (by simp only [oldPosition] at hdist; omega)
      simpa only [oldPosition, oldOffset, oldRanking, add_sub_add_left_eq_sub] using hh

/-- Exterior requests of one certified word when a six-site buffer closes its cycle. -/
def ClosingRequester {m : ℕ} (d : Fin m → ℤ) :=
  {i : Fin m // d i ≠ 0 ∧ ((i.val : ℤ) + d i < 0 ∨ (m : ℤ) ≤ i.val + d i)}

def closingRequest {m : ℕ} (d : Fin m → ℤ) (hd : ∀ i, -2 ≤ d i ∧ d i ≤ 2)
    (i : ClosingRequester d) : Fin 6 :=
  if h : (i.val.val : ℤ) + d i.val < 0 then
    ⟨((i.val.val : ℤ) + d i.val + 6).toNat, by have := hd i.val; omega⟩
  else ⟨((i.val.val : ℤ) + d i.val - m).toNat, by
    have := hd i.val; have := i.property; have := i.val.isLt; omega⟩

theorem closing_coordinate {m : ℕ} {d : Fin m → ℤ}
    (hd : ∀ i, -2 ≤ d i ∧ d i ≤ 2) (i : ClosingRequester d) :
    if (i.val.val : ℤ) + d i.val < 0 then
      (closingRequest d hd i).val = (i.val.val : ℤ) + d i.val + 6
    else (closingRequest d hd i).val = (i.val.val : ℤ) + d i.val - m := by
  have hb := hd i.val
  have hp := i.property
  have hi := i.val.isLt
  by_cases h : (i.val.val : ℤ) + d i.val < 0 <;>
    simp only [closingRequest, h, dite_true, dite_false, ite_true, ite_false] <;> omega

private theorem closing_injective {m : ℕ} {w : Word m} {d : Fin m → ℤ}
    (hw : Certificate w d) : Function.Injective (closingRequest d hw.bounded) := by
  intro i j he
  have hi := closing_coordinate hw.bounded i
  have hj := closing_coordinate hw.bounded j
  have hib := hw.bounded i.val
  have hjb := hw.bounded j.val
  have hip := i.property
  have hjp := j.property
  have hil := i.val.isLt
  have hjl := j.val.isLt
  have hev := congrArg (fun x : Fin 6 => (x.val : ℤ)) he
  apply Subtype.ext
  apply hw.target_injective i.val j.val hip.1 hjp.1
  split_ifs at hi hj <;> omega

private theorem closing_boundary {m : ℕ} {w : Word m} {d : Fin m → ℤ}
    (hw : Certificate w d) (i : ClosingRequester d) :
    closingRequest d hw.bounded i ≠ 2 ∧ closingRequest d hw.bounded i ≠ 3 := by
  have hi := closing_coordinate hw.bounded i
  have hb := hw.bounded i.val
  have hp := i.property
  have hil := i.val.isLt
  split_ifs at hi <;>
    constructor <;> intro h <;> have he := congrArg (fun x : Fin 6 => (x.val : ℤ)) h <;>
    norm_num at he <;> omega

/-- Closing requests are realized for every word length, without a parity condition.
In particular the four distinct exterior targets at m=1 remain distinct in the buffer.
The statement supplies the requester/buffer involution, not yet cyclic stability. -/
theorem closing_request_completion {m : ℕ} {w : Word m} {d : Fin m → ℤ}
    (hw : Certificate w d) :
    Function.Injective (closingRequest d hw.bounded) ∧
    Function.Involutive (BufferLayout.partner (closingRequest d hw.bounded)) ∧
    (∀ i, BufferLayout.partner (closingRequest d hw.bounded) (.inl i) =
      .inr (closingRequest d hw.bounded i)) ∧
    (∀ i, BufferLayout.partner (closingRequest d hw.bounded) (.inr i) = .inr i →
      i = 2 ∨ i = 3) := by
  exact ⟨closing_injective hw,
    BufferLayout.complete_requests _ (closing_injective hw) (closing_boundary hw)⟩

#print axioms old_target_injective
#print axioms padded_request_completion
#print axioms old_nonblocking
#print axioms closing_request_completion
end D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

/- GID: D5/S3/Combinatorics/Graph/Roommates/PaddedCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/PaddedCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Concrete six-buffer completion certifies padded profiles and proves the padded count inequality. -/

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

/-- Signed buffer assignments reverse actual old requests; free sites use the layout. -/
def bufferOffset {α : Type} (r : α → Fin 6) (d : α → ℤ) (i : Fin 6) : ℤ :=
  if h : ∃ a, r a = i then -d (Classical.choose h)
  else (BufferLayout.mate (BufferLayout.flags r) i).val - (i.val : ℤ)

/-- This assignment simultaneously fulfills all incoming requests, stays in range,
and isolates every buffer single from any other buffer single. -/
theorem buffer_offset_completion {α : Type} (r : α → Fin 6) (d : α → ℤ)
    (hr : Function.Injective r) (hc : ∀ a, r a ≠ 2 ∧ r a ≠ 3)
    (hd : ∀ a, -2 ≤ d a ∧ d a ≤ 2 ∧ d a ≠ 0) :
    (∀ a, bufferOffset r d (r a) = -d a) ∧
    (∀ i, -2 ≤ bufferOffset r d i ∧ bufferOffset r d i ≤ 2) ∧
    (∀ i, bufferOffset r d i = 0 → i = 2 ∨ i = 3) ∧
    (∀ i j, bufferOffset r d i = 0 → i ≠ j →
      i.val ≤ j.val + 2 → j.val ≤ i.val + 2 → bufferOffset r d j ≠ 0) := by
  have hl := BufferLayout.buffer_completion (BufferLayout.flags r)
  have ho := BufferLayout.occupied_iff r hc
  have hreq (i : Fin 6) (h : ∃ a, r a = i) :
      bufferOffset r d i = -d (Classical.choose h) := by
    simp only [bufferOffset, dif_pos h]
  have hfree (i : Fin 6) (h : ¬∃ a, r a = i) :
      bufferOffset r d i = (BufferLayout.mate (BufferLayout.flags r) i).val - (i.val : ℤ) := by
    simp only [bufferOffset, dif_neg h]
  have hzero (i : Fin 6) (hi : bufferOffset r d i = 0) :
      BufferLayout.occupied (BufferLayout.flags r) i = false ∧
        BufferLayout.mate (BufferLayout.flags r) i = i := by
    by_cases he : ∃ a, r a = i
    · rw [hreq i he] at hi
      have hb := hd (Classical.choose he)
      omega
    · constructor
      · cases hh : BufferLayout.occupied (BufferLayout.flags r) i
        · rfl
        · exact (he ((ho i).mp hh)).elim
      · apply Fin.ext
        rw [hfree i he] at hi
        omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    have he : ∃ b, r b = r a := ⟨a, rfl⟩
    rw [hreq (r a) he, hr (Classical.choose_spec he)]
  · intro i
    by_cases he : ∃ a, r a = i
    · rw [hreq i he]
      have hb := hd (Classical.choose he)
      omega
    · rw [hfree i he]
      have hb := hl.2.2.2.1 i
      omega
  · intro i hi
    exact hl.2.2.2.2.1 i (hzero i hi).1 (hzero i hi).2
  · intro i j hi hij h₁ h₂ hj
    have hzi := hzero i hi
    have hzj := hzero j hj
    rcases hl.2.2.2.2.2 i j hzi.1 hzi.2 hij h₁ h₂ with he | he
    · rw [hzj.1] at he
      cases he
    · exact he hzj.2

/-- Deterministic strict ranking with the prescribed nonzero partner first. -/
def partnerFirst (a : ℤ) : Ranking :=
  Equiv.swap 0 (if a = 1 then 0 else if a = 2 then 1 else if a = -1 then 2 else 3)

private theorem partnerFirst_top (a : ℤ) (ha : -2 ≤ a ∧ a ≤ 2) (hz : a ≠ 0) :
    offsetRank (partnerFirst a) a = 0 := by
  rcases ha with ⟨hl, hu⟩
  interval_cases a <;> norm_num [partnerFirst, offsetRank] at *

/-- Choose a certificate once per input word, rather than counting its witnesses. -/
def chosenOffset {m : ℕ} (w : CertifiedWord m) : Fin m → ℤ := Classical.choose w.property

private theorem chosen_certificate {m : ℕ} (w : CertifiedWord m) :
    Certificate w.val (chosenOffset w) := Classical.choose_spec w.property

/-- The actual buffer rankings determined by the two input words and their chosen certificates. -/
def paddedBuffer {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) : Word 6 :=
  fun i => partnerFirst (bufferOffset (request (chosenOffset w) (chosenOffset v))
    (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val) i)

/-- The ranking word retains both input words literally, with exactly six new sites. -/
def paddedWord {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) : Word (m + k + 6) :=
  fun i => if h : i.val < m then w.val ⟨i.val, h⟩
    else if h' : i.val < m + 6 then paddedBuffer w v ⟨i.val - m, by omega⟩
    else v.val ⟨i.val - (m + 6), by omega⟩

/-- Recovery is on preference words, independently of which certificate was chosen. -/
theorem padded_word_injective (m k : ℕ) :
    Function.Injective (fun p : CertifiedWord m × CertifiedWord k => paddedWord p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have he := congrFun h (⟨i.val, by omega⟩ : Fin (m + k + 6))
    simpa only [paddedWord, dif_pos i.isLt] using he
  · apply Subtype.ext
    funext i
    have he := congrFun h (⟨m + 6 + i.val, by omega⟩ : Fin (m + k + 6))
    simpa only [paddedWord, dif_neg (by omega : ¬m + 6 + i.val < m),
      dif_neg (by omega : ¬m + 6 + i.val < m + 6), Nat.add_sub_cancel_left] using he

/-- Every assigned buffer partner is first-ranked in the concrete padded word. -/
theorem padded_buffer_top {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) (i : Fin 6)
    (hn : bufferOffset (request (chosenOffset w) (chosenOffset v))
      (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val) i ≠ 0) :
    offsetRank (paddedBuffer w v i)
      (bufferOffset (request (chosenOffset w) (chosenOffset v))
        (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val) i) = 0 := by
  have hw := chosen_certificate w
  have hv := chosen_certificate v
  have hc := buffer_offset_completion (request (chosenOffset w) (chosenOffset v))
    (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val)
    (request_injective hw hv) (request_boundary hw hv) (by
      intro a
      refine ⟨?_, ?_, a.property.1⟩
      rcases a.val with a | a
      · exact (hw.bounded a).1
      · exact (hv.bounded a).1
      rcases a.val with a | a
      · exact (hw.bounded a).2
      · exact (hv.bounded a).2)
  exact partnerFirst_top _ (hc.2.1 i) hn


/-- The old vertices embedded in the actual padded interval. -/
def oldIndex {m k : ℕ} : Fin m ⊕ Fin k → Fin (m + k + 6)
  | .inl i => ⟨i.val, by omega⟩
  | .inr i => ⟨m + 6 + i.val, by omega⟩

def bufferIndex {m k : ℕ} (i : Fin 6) : Fin (m + k + 6) :=
  ⟨m + i.val, by omega⟩

/-- Preserve all old offsets, and use the concrete completion on the buffer. -/
def paddedOffset {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i : Fin (m + k + 6)) : ℤ :=
  if h : i.val < m then chosenOffset w ⟨i.val, h⟩
  else if h' : i.val < m + 6 then
    bufferOffset (request (chosenOffset w) (chosenOffset v))
      (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val) ⟨i.val - m, by omega⟩
  else chosenOffset v ⟨i.val - (m + 6), by omega⟩

private theorem index_cases {m k : ℕ} (i : Fin (m + k + 6)) :
    (∃ a : Fin m ⊕ Fin k, i = oldIndex a) ∨ ∃ b : Fin 6, i = bufferIndex b := by
  by_cases h : i.val < m
  · exact Or.inl ⟨.inl ⟨i.val, h⟩, rfl⟩
  · by_cases h' : i.val < m + 6
    · exact Or.inr ⟨⟨i.val - m, by omega⟩, Fin.ext (by simp [bufferIndex]; omega)⟩
    · exact Or.inl ⟨.inr ⟨i.val - (m + 6), by omega⟩,
        Fin.ext (by simp [oldIndex]; omega)⟩

private theorem old_index_position {m k : ℕ} (a : Fin m ⊕ Fin k) :
    ((oldIndex a).val : ℤ) = oldPosition a := by
  cases a <;> simp [oldIndex, oldPosition, Nat.cast_add]

private theorem old_index_offset {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (a : Fin m ⊕ Fin k) :
    paddedOffset w v (oldIndex a) = oldOffset (chosenOffset w) (chosenOffset v) a := by
  cases a with
  | inl a => simp [paddedOffset, oldIndex, oldOffset, a.isLt]
  | inr a => simp [paddedOffset, oldIndex, oldOffset, show ¬m + 6 + a.val < m by omega,
      show ¬m + 6 + a.val < m + 6 by omega]

private theorem buffer_index_offset {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i : Fin 6) : paddedOffset w v (bufferIndex i) =
    bufferOffset (request (chosenOffset w) (chosenOffset v))
      (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val) i := by
  simp [paddedOffset, bufferIndex, show ¬m + i.val < m by omega,
    show m + i.val < m + 6 by omega]

private theorem old_index_word {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (a : Fin m ⊕ Fin k) : paddedWord w v (oldIndex a) = oldRanking w.val v.val a := by
  cases a with
  | inl a => simp [paddedWord, oldIndex, oldRanking, a.isLt]
  | inr a => simp [paddedWord, oldIndex, oldRanking, show ¬m + 6 + a.val < m by omega,
      show ¬m + 6 + a.val < m + 6 by omega]

private theorem buffer_index_word {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i : Fin 6) : paddedWord w v (bufferIndex i) = paddedBuffer w v i := by
  simp [paddedWord, bufferIndex, show ¬m + i.val < m by omega,
    show m + i.val < m + 6 by omega]

private theorem request_bounds {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (a : Requester (chosenOffset w) (chosenOffset v)) :
    -2 ≤ oldOffset (chosenOffset w) (chosenOffset v) a.val ∧
      oldOffset (chosenOffset w) (chosenOffset v) a.val ≤ 2 ∧
      oldOffset (chosenOffset w) (chosenOffset v) a.val ≠ 0 := by
  refine ⟨?_, ?_, a.property.1⟩
  · cases a.val with
    | inl a => exact ((chosen_certificate w).bounded a).1
    | inr a => exact ((chosen_certificate v).bounded a).1
  · cases a.val with
    | inl a => exact ((chosen_certificate w).bounded a).2
    | inr a => exact ((chosen_certificate v).bounded a).2

private theorem padded_buffer_facts {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) :
    let r := request (chosenOffset w) (chosenOffset v)
    let d := fun a : Requester (chosenOffset w) (chosenOffset v) =>
      oldOffset (chosenOffset w) (chosenOffset v) a.val
    (∀ a, bufferOffset r d (r a) = -d a) ∧
    (∀ i, -2 ≤ bufferOffset r d i ∧ bufferOffset r d i ≤ 2) ∧
    (∀ i, bufferOffset r d i = 0 → i = 2 ∨ i = 3) ∧
    (∀ i j, bufferOffset r d i = 0 → i ≠ j →
      i.val ≤ j.val + 2 → j.val ≤ i.val + 2 → bufferOffset r d j ≠ 0) :=
  buffer_offset_completion (request (chosenOffset w) (chosenOffset v))
    (fun a => oldOffset (chosenOffset w) (chosenOffset v) a.val)
    (request_injective (chosen_certificate w) (chosen_certificate v))
    (request_boundary (chosen_certificate w) (chosen_certificate v)) (request_bounds w v)

private theorem old_reciprocal {m k : ℕ} {w : Word m} {v : Word k}
    {d : Fin m → ℤ} {e : Fin k → ℤ} (hw : Certificate w d) (hv : Certificate v e)
    (a b : Fin m ⊕ Fin k) (ha : oldOffset d e a ≠ 0)
    (he : oldTarget d e a = oldPosition b) : oldOffset d e b = -oldOffset d e a := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hw.reciprocal a b ha he
    | inr b =>
      have := hw.bounded a
      have := a.isLt
      simp only [oldTarget, oldPosition, oldOffset] at he
      omega
  | inr a =>
    cases b with
    | inl b =>
      have := hv.bounded a
      have := b.isLt
      simp only [oldTarget, oldPosition, oldOffset] at he
      omega
    | inr b =>
      apply hv.reciprocal a b ha
      simp only [oldTarget, oldPosition, oldOffset] at he
      omega

private theorem padded_bounded {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i : Fin (m + k + 6)) : -2 ≤ paddedOffset w v i ∧ paddedOffset w v i ≤ 2 := by
  rcases index_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [old_index_offset]
    cases a with
    | inl a => exact (chosen_certificate w).bounded a
    | inr a => exact (chosen_certificate v).bounded a
  · rw [buffer_index_offset]
    exact (padded_buffer_facts w v).2.1 b

private theorem old_to_buffer {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (a : Fin m ⊕ Fin k) (b : Fin 6)
    (ha : oldOffset (chosenOffset w) (chosenOffset v) a ≠ 0)
    (he : oldTarget (chosenOffset w) (chosenOffset v) a = (m : ℤ) + b.val) :
    paddedOffset w v (bufferIndex b) = -oldOffset (chosenOffset w) (chosenOffset v) a := by
  let ar : Requester (chosenOffset w) (chosenOffset v) := ⟨a, ha, by omega, by omega⟩
  have hr : request (chosenOffset w) (chosenOffset v) ar = b := by
    apply Fin.ext
    have hc := request_coordinate ar
    change (m : ℤ) + (request (chosenOffset w) (chosenOffset v) ar).val =
      oldTarget (chosenOffset w) (chosenOffset v) a at hc
    omega
  rw [buffer_index_offset, ← hr]
  exact (padded_buffer_facts w v).1 ar

private theorem buffer_offset_requested {α : Type} (r : α → Fin 6) (d : α → ℤ)
    (b : Fin 6) (h : ∃ a, r a = b) : bufferOffset r d b = -d (Classical.choose h) := by
  simp only [bufferOffset, dif_pos h]

private theorem buffer_offset_free {α : Type} (r : α → Fin 6) (d : α → ℤ)
    (b : Fin 6) (h : ¬∃ a, r a = b) :
    bufferOffset r d b = (BufferLayout.mate (BufferLayout.flags r) b).val - (b.val : ℤ) := by
  simp only [bufferOffset, dif_neg h]

/-- A new assignment always targets an actual vertex of the padded interval. -/
private theorem buffer_target_internal {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (b : Fin 6) : ∃ j : Fin (m + k + 6),
      ((bufferIndex (m := m) (k := k) b).val : ℤ) + paddedOffset w v (bufferIndex b) = j.val := by
  let r := request (chosenOffset w) (chosenOffset v)
  let d := fun a : Requester (chosenOffset w) (chosenOffset v) =>
    oldOffset (chosenOffset w) (chosenOffset v) a.val
  rw [buffer_index_offset]
  change ∃ j : Fin (m + k + 6), (↑(bufferIndex b).val : ℤ) + bufferOffset r d b = j.val
  by_cases h : ∃ a, r a = b
  · refine ⟨oldIndex (Classical.choose h).val, ?_⟩
    rw [buffer_offset_requested r d b h, old_index_position]
    have hc := request_coordinate (Classical.choose h)
    have hr := Classical.choose_spec h
    change r (Classical.choose h) = b at hr
    change (m : ℤ) + (r (Classical.choose h)).val = _ at hc
    rw [hr] at hc
    simp only [bufferIndex, Fin.val_mk, Nat.cast_add, oldTarget] at *
    dsimp [d]
    omega
  · refine ⟨bufferIndex (BufferLayout.mate (BufferLayout.flags r) b), ?_⟩
    rw [buffer_offset_free r d b h]
    simp only [bufferIndex, Fin.val_mk, Nat.cast_add]
    omega

private theorem padded_reciprocal {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i j : Fin (m + k + 6)) (hi : paddedOffset w v i ≠ 0)
    (he : (i.val : ℤ) + paddedOffset w v i = j.val) :
    paddedOffset w v j = -paddedOffset w v i := by
  let r := request (chosenOffset w) (chosenOffset v)
  let d := fun a : Requester (chosenOffset w) (chosenOffset v) =>
    oldOffset (chosenOffset w) (chosenOffset v) a.val
  rcases index_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [old_index_offset] at hi he ⊢
    rw [old_index_position] at he
    rcases index_cases j with ⟨a', rfl⟩ | ⟨b, rfl⟩
    · rw [old_index_offset, old_index_position] at *
      exact old_reciprocal (chosen_certificate w) (chosen_certificate v) a a' hi he
    · exact old_to_buffer w v a b hi (by simpa [oldTarget, bufferIndex] using he)
  · rw [buffer_index_offset] at hi he ⊢
    change bufferOffset r d b ≠ 0 at hi
    change (↑(bufferIndex b).val : ℤ) + bufferOffset r d b = j.val at he
    change paddedOffset w v j = -bufferOffset r d b
    by_cases h : ∃ a, r a = b
    · have ht := request_coordinate (Classical.choose h)
      have hr := Classical.choose_spec h
      change r (Classical.choose h) = b at hr
      change (m : ℤ) + (r (Classical.choose h)).val = _ at ht
      rw [hr] at ht
      rw [buffer_offset_requested r d b h] at he ⊢
      have hp := old_index_position (Classical.choose h).val
      have ho : j = oldIndex (Classical.choose h).val := by
        apply Fin.ext
        simp only [bufferIndex, Fin.val_mk, Nat.cast_add] at he
        simp only [oldTarget] at ht
        dsimp [d] at he
        omega
      rw [ho, old_index_offset]
      dsimp [d]
      omega
    · let c := BufferLayout.mate (BufferLayout.flags r) b
      have hl := BufferLayout.buffer_completion (BufferLayout.flags r)
      have hfree : ¬∃ a, r a = c := by
        intro ⟨a, ha⟩
        have hx := hl.2.1 c ((BufferLayout.occupied_iff r
          (request_boundary (chosen_certificate w) (chosen_certificate v)) c).mpr ⟨a, ha⟩)
        have hy := hl.1 b
        change BufferLayout.mate (BufferLayout.flags r) c = b at hy
        rw [hx] at hy
        exact h ⟨a, ha.trans hy⟩
      rw [buffer_offset_free r d b h] at he ⊢
      have hj : j = bufferIndex c := by
        apply Fin.ext
        simp only [bufferIndex, Fin.val_mk, Nat.cast_add] at he ⊢
        dsimp [c]
        omega
      rw [hj, buffer_index_offset]
      change bufferOffset r d c = -((BufferLayout.mate (BufferLayout.flags r) b).val - (b.val : ℤ))
      rw [buffer_offset_free r d c hfree]
      have hh := hl.1 b
      change BufferLayout.mate (BufferLayout.flags r) c = b at hh
      rw [hh]
      dsimp [c]
      omega

private theorem padded_target_injective {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i j : Fin (m + k + 6)) (hi : paddedOffset w v i ≠ 0) (hj : paddedOffset w v j ≠ 0)
    (he : (i.val : ℤ) + paddedOffset w v i = (j.val : ℤ) + paddedOffset w v j) : i = j := by
  by_cases ht : ∃ t : Fin (m + k + 6), (i.val : ℤ) + paddedOffset w v i = t.val
  · obtain ⟨t, ht⟩ := ht
    have hri := padded_reciprocal w v i t hi ht
    have hrj := padded_reciprocal w v j t hj (he.symm.trans ht)
    apply Fin.ext
    omega
  · rcases index_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rcases index_cases j with ⟨a', rfl⟩ | ⟨b, rfl⟩
      · have hh := old_target_injective (chosen_certificate w) (chosen_certificate v) a a'
          (by simpa only [old_index_offset] using hi)
          (by simpa only [old_index_offset] using hj)
          (by simpa only [oldTarget, old_index_offset, old_index_position] using he)
        exact congrArg oldIndex hh
      · obtain ⟨t, ht'⟩ := buffer_target_internal w v b
        exact (ht ⟨t, he.trans ht'⟩).elim
    · exact (ht (buffer_target_internal w v b)).elim

private theorem top_rejects (r : Ranking) (a b : ℤ)
    (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (htop : offsetRank r a = 0) (hne : a ≠ b) :
    offsetRank r a < offsetRank r b := by
  rw [htop]
  apply Nat.pos_of_ne_zero
  intro hz
  exact hne (rank_injective r ha hb ha0 hb0 (htop.trans hz.symm))

private theorem buffer_single_far_old {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (b : Fin 6) (a : Fin m ⊕ Fin k) (hz : paddedOffset w v (bufferIndex b) = 0) :
    ¬ (((bufferIndex (m := m) (k := k) b).val : ℤ) ≤ oldPosition a + 2 ∧
       oldPosition a ≤ (bufferIndex (m := m) (k := k) b).val + 2) := by
  rw [buffer_index_offset] at hz
  have hc := (padded_buffer_facts w v).2.2.1 b hz
  intro hd
  rcases hc with rfl | rfl <;> cases a with
  | inl a => have := a.isLt; simp only [oldPosition, bufferIndex, Fin.val_mk] at hd; norm_num at hd; omega
  | inr a => simp only [oldPosition, bufferIndex, Fin.val_mk] at hd; norm_num at hd; omega

private theorem padded_nonblocking {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k)
    (i j : Fin (m + k + 6)) (hij : i.val < j.val) (hdist : j.val ≤ i.val + 2) :
    paddedOffset w v i = (j.val : ℤ) - i.val ∨
      offsetRank (paddedWord w v i) (paddedOffset w v i) <
        offsetRank (paddedWord w v i) ((j.val : ℤ) - i.val) ∨
      offsetRank (paddedWord w v j) (paddedOffset w v j) <
        offsetRank (paddedWord w v j) ((i.val : ℤ) - j.val) := by
  by_cases he : paddedOffset w v i = (j.val : ℤ) - i.val
  · exact Or.inl he
  have left_reject (hn : paddedOffset w v i ≠ 0)
      (ht : offsetRank (paddedWord w v i) (paddedOffset w v i) = 0) :
      offsetRank (paddedWord w v i) (paddedOffset w v i) <
        offsetRank (paddedWord w v i) ((j.val : ℤ) - i.val) :=
    top_rejects _ _ _ (padded_bounded w v i) (by omega) hn (by omega) ht he
  have right_reject (hn : paddedOffset w v j ≠ 0)
      (ht : offsetRank (paddedWord w v j) (paddedOffset w v j) = 0) :
      offsetRank (paddedWord w v j) (paddedOffset w v j) <
        offsetRank (paddedWord w v j) ((i.val : ℤ) - j.val) := by
    apply top_rejects _ _ _ (padded_bounded w v j) (by omega) hn (by omega) ht
    intro hh
    have hr := padded_reciprocal w v j i hn (by omega)
    exact he (by omega)
  rcases index_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rcases index_cases j with ⟨a', rfl⟩ | ⟨c, rfl⟩
    · simpa only [old_index_offset, old_index_word, old_index_position] using
        old_nonblocking (chosen_certificate w) (chosen_certificate v) a a'
          (by rw [← old_index_position a, ← old_index_position a']; omega)
          (by rw [← old_index_position a, ← old_index_position a']; omega)
    · have hn : paddedOffset w v (bufferIndex c) ≠ 0 := by
        intro hz
        apply buffer_single_far_old w v c a hz
        rw [← old_index_position a]
        constructor <;> omega
      exact Or.inr (Or.inr (right_reject hn (by
        rw [buffer_index_word, buffer_index_offset]
        exact padded_buffer_top w v c (by simpa only [buffer_index_offset] using hn))))
  · by_cases hn : paddedOffset w v (bufferIndex b) ≠ 0
    · exact Or.inr (Or.inl (left_reject hn (by
        rw [buffer_index_word, buffer_index_offset]
        exact padded_buffer_top w v b (by simpa only [buffer_index_offset] using hn))))
    · have hz : paddedOffset w v (bufferIndex b) = 0 := not_ne_iff.mp hn
      rcases index_cases j with ⟨a, rfl⟩ | ⟨c, rfl⟩
      · exfalso
        apply buffer_single_far_old w v b a hz
        rw [← old_index_position a]
        constructor <;> omega
      · have hc : paddedOffset w v (bufferIndex c) ≠ 0 := by
          rw [buffer_index_offset]
          apply (padded_buffer_facts w v).2.2.2 b c
            (by simpa only [buffer_index_offset] using hz)
          · intro hh; subst c; omega
          · simp only [bufferIndex, Fin.val_mk] at hij hdist; omega
          · simp only [bufferIndex, Fin.val_mk] at hij hdist; omega
        exact Or.inr (Or.inr (right_reject hc (by
          rw [buffer_index_word, buffer_index_offset]
          exact padded_buffer_top w v c (by simpa only [buffer_index_offset] using hc))))

/-- The concrete six-buffer word has a full certificate, including exterior targets
and every old/new nonblocking test. No completion hypothesis is assumed. -/
theorem padded_certificate {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) :
    Certificate (paddedWord w v) (paddedOffset w v) :=
  ⟨padded_bounded w v, padded_reciprocal w v, padded_target_injective w v,
    padded_nonblocking w v⟩

/-- The completion is a map of certified preference profiles. -/
def paddedCertified {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k) :
    CertifiedWord (m + k + 6) :=
  ⟨paddedWord w v, paddedOffset w v, padded_certificate w v⟩

/-- Count input profiles once, regardless of how many certificates they admit.
The construction also covers empty input words, so positivity is unnecessary here. -/
theorem count_padded_supermultiplicative (m k : ℕ) :
    count m * count k ≤ count (m + k + 6) := by
  have hi : Function.Injective (fun p : CertifiedWord m × CertifiedWord k =>
      paddedCertified p.1 p.2) := by
    intro p q h
    exact padded_word_injective m k (congrArg Subtype.val h)
  simpa only [count, Fintype.card_prod] using Fintype.card_le_of_injective _ hi

#print axioms padded_certificate
#print axioms count_padded_supermultiplicative

#print axioms old_target_injective
#print axioms padded_request_completion
#print axioms old_nonblocking
#print axioms closing_request_completion
#print axioms buffer_offset_completion
#print axioms padded_word_injective
#print axioms padded_buffer_top
end D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

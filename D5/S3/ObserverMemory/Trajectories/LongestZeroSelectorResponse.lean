/- GID: D5/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.MinMax]
   utility: none
   digest: Exact longest-run selection and zero-input direction response. -/

import D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse

open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry

set_option autoImplicit false

/-- The original selector enumerates complete intervals in the actual window.
The absolute current vertex is `e`; its strict past is `[e-R,e)`. -/
noncomputable def candidates (s : Finset ℕ) (R e : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range e).product (Finset.range e)).filter fun c =>
    e ≤ R + c.1 ∧ Complete s c.1 c.2

/-- Length is the primary score; the later closing endpoint breaks ties. -/
def score (e : ℕ) (c : ℕ × ℕ) : ℕ := (c.2 - c.1 - 1) * (e + 1) + c.2

noncomputable def selected (s : Finset ℕ) (R e : ℕ) : Option (ℕ × ℕ) :=
  ((candidates s R e).toList).argmax (score e)

noncomputable def direction (s : Finset ℕ) (R e : ℕ) : ℕ :=
  match selected s R e with
  | none => 0
  | some c => transport s c.2 e

/-- The first surviving long-run interval. -/
def longAnchor : ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, p, R, e => if e ≤ R + p then some (p, p + 4) else none
  | r + 1, h, p, R, e =>
      if e ≤ R + p then some (p, p + 2 * (r + 1) + 4)
      else longAnchor r (fun i => h (i + 1))
        (p + 2 * (r + 1) + 4 + 4 * h 0) R e

/-- Surviving fillers cannot win: the predicted anchor is the unique maximum
of the original length/latest score over all actual complete candidates. -/
theorem family_selection (r : ℕ) (h : ℕ → ℕ) (p R e : ℕ)
    (he : p + span (familyGaps r h) < e) :
    match longAnchor r h p R e with
    | none => candidates (ones (familyGaps r h) p) R e = ∅
    | some c => c ∈ candidates (ones (familyGaps r h) p) R e ∧
        3 ≤ c.2 - c.1 - 1 ∧
        ∀ d ∈ candidates (ones (familyGaps r h) p) R e,
          d ≠ c → score e d < score e c := by
  classical
  have hcrun : ∀ (xs : List ℕ) (p : ℕ), p + span xs < e → ∀ c,
      c ∈ candidates (ones xs p) R e ↔ c ∈ intervals xs p ∧ e ≤ R + c.1 := by
    intro xs p hend c
    rcases c with ⟨a, b⟩
    simp only [candidates, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨_, hl, hc⟩
      exact ⟨(complete_iff_interval xs p _ _).mp hc, hl⟩
    · rintro ⟨hc, hl⟩
      have hg := (interval_geometry xs p).1 (a, b) hc
      exact ⟨⟨by omega, by omega⟩, hl, (complete_iff_interval xs p _ _).mpr hc⟩
  have hscore : ∀ c d : ℕ × ℕ,
      d.2 - d.1 - 1 < c.2 - c.1 - 1 → d.2 < e → score e d < score e c := by
    intro c d hlen hd
    dsimp [score]
    nlinarith
  have headcase : ∀ r h p, p + span (familyGaps r h) < e → e ≤ R + p →
      (p, p + 2 * r + 4) ∈ candidates (ones (familyGaps r h) p) R e ∧
      3 ≤ (p + 2 * r + 4) - p - 1 ∧
      ∀ d ∈ candidates (ones (familyGaps r h) p) R e,
        d ≠ (p, p + 2 * r + 4) → score e d < score e (p, p + 2 * r + 4) := by
    intro r h p hend hlive
    obtain ⟨hm, hmax⟩ := family_head_dominates r h p
    refine ⟨(hcrun _ _ hend _).mpr ⟨hm, hlive⟩, by omega, ?_⟩
    intro d hd hne
    have hd' := (hcrun _ _ hend _).mp hd
    have hlen := (hmax d hd'.1).resolve_left hne
    have hb := ((interval_geometry _ p).1 d hd'.1).2.2.1
    apply hscore
    · dsimp; omega
    · omega
  induction r generalizing h p with
  | zero =>
    simp only [longAnchor]
    split_ifs with hlive
    · exact headcase 0 h p he hlive
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      obtain ⟨hc, hl⟩ := (hcrun _ _ he c).mp hc
      simp [familyGaps, intervals] at hc
      subst c
      exact hlive hl
  | succ r ih =>
    simp only [longAnchor]
    split_ifs with hlive
    · exact headcase (r + 1) h p he hlive
    · let b := p + 2 * (r + 1) + 4
      let p' := b + 4 * h 0
      let ht := fun i => h (i + 1)
      have hsp : span (familyGaps (r + 1) h) =
          2 * (r + 1) + 4 + 4 * h 0 + span (familyGaps r ht) := by
        simp [familyGaps, span, ht, List.sum_append, List.sum_replicate]
        omega
      have hfillspan : span (List.replicate (2 * h 0) 1) = 4 * h 0 := by
        simp [span, List.sum_replicate]; omega
      have het : p' + span (familyGaps r ht) < e := by
        dsimp [p', b]
        omega
      have hints : intervals (familyGaps (r + 1) h) p =
          insert (p, b) (intervals (List.replicate (2 * h 0) 1) b ∪
            intervals (familyGaps r ht) p') := by
        simp only [familyGaps, intervals]
        rw [(interval_geometry (List.replicate (2 * h 0) 1) _).2]
        simp [hfillspan, b, p', ht, Nat.add_assoc]
      have hcases : ∀ c ∈ candidates (ones (familyGaps (r + 1) h) p) R e,
          (c ∈ intervals (List.replicate (2 * h 0) 1) b ∧ e ≤ R + c.1) ∨
          c ∈ candidates (ones (familyGaps r ht) p') R e := by
        intro c hc
        obtain ⟨hc, hl⟩ := (hcrun _ _ he c).mp hc
        rw [hints] at hc
        simp only [Finset.mem_insert, Finset.mem_union] at hc
        rcases hc with hc | hc | hc
        · subst c; exact (hlive hl).elim
        · exact Or.inl ⟨hc, hl⟩
        · exact Or.inr ((hcrun _ _ het c).mpr ⟨hc, hl⟩)
      have hinto : ∀ c ∈ candidates (ones (familyGaps r ht) p') R e,
          c ∈ candidates (ones (familyGaps (r + 1) h) p) R e := by
        intro c hc
        obtain ⟨hc, hl⟩ := (hcrun _ _ het c).mp hc
        apply (hcrun _ _ he c).mpr
        rw [hints]
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ hc), hl⟩
      have hfill : ∀ c ∈ intervals (List.replicate (2 * h 0) 1) b,
          c.2 - c.1 - 1 = 1 ∧ c.1 < p' := by
        intro c hc
        obtain ⟨_, hab, hb, hm⟩ := (interval_geometry _ b).1 c hc
        have hm' := List.eq_of_mem_replicate hm
        rw [hfillspan] at hb
        exact ⟨hm', by dsimp [p']; omega⟩
      have hih := ih ht p' het
      change match longAnchor r ht p' R e with
        | none => _
        | some c => _
      cases ha : longAnchor r ht p' R e with
      | none =>
        rw [ha] at hih
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        rcases hcases c hc with ⟨hf, hl⟩ | htmem
        · have hp' := (hfill c hf).2
          have hm := (family_head_dominates r ht p').1
          have htm := (hcrun _ _ het _).mpr ⟨hm, by dsimp; omega⟩
          rw [hih] at htm
          exact Finset.notMem_empty _ htm
        · rw [hih] at htmem
          exact Finset.notMem_empty _ htmem
      | some c =>
        rw [ha] at hih
        obtain ⟨hc, hlen, hmax⟩ := hih
        refine ⟨hinto c hc, hlen, ?_⟩
        intro d hd hne
        rcases hcases d hd with ⟨hf, _⟩ | hdt
        · have hf' := (hfill d hf).1
          have hd' := (hcrun _ _ he d).mp hd
          have hb := ((interval_geometry _ p).1 d hd'.1).2.2.1
          exact hscore c d (by omega) (by omega)
        · exact hmax d hdt hne

/-- A recursive response formula, subsequently identified with the actual direction. -/
def responseModel : ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | 0, _, R, n => if 5 + n ≤ R then n % 2 else 0
  | r + 1, h, R, n =>
      if span (familyGaps (r + 1) h) + 1 + n ≤ R then (r + 1 + n) % 2
      else responseModel r (fun i => h (i + 1)) R n

/-- The exact response of the original selector, with phase from every consumed bit. -/
theorem direction_family (r : ℕ) (h : ℕ → ℕ) (p R n : ℕ) :
    direction (ones (familyGaps r h) p) R (p + span (familyGaps r h) + 1 + n) =
      responseModel r h R n := by
  classical
  have hselected : ∀ r h p e, p + span (familyGaps r h) < e →
      selected (ones (familyGaps r h) p) R e = longAnchor r h p R e := by
    intro r h p e he
    have hs := family_selection r h p R e he
    cases ha : longAnchor r h p R e with
    | none => simp only [ha] at hs; simp [selected, hs]
    | some c =>
      simp only [ha] at hs
      obtain ⟨hc, _, hmax⟩ := hs
      apply List.argmax_eq_some_iff.mpr
      refine ⟨Finset.mem_toList.mpr hc, ?_, ?_⟩
      · intro d hd
        by_cases hdc : d = c
        · subst d; exact le_rfl
        · exact (hmax d (Finset.mem_toList.mp hd) hdc).le
      · intro d hd hle
        have hdc : d = c := by
          by_contra hn
          exact (not_lt_of_ge hle) (hmax d (Finset.mem_toList.mp hd) hn)
        subst d
        exact le_rfl
  have hparity : ∀ r h, (familyGaps r h).sum % 2 = (r + 1) % 2 := by
    intro r
    induction r with
    | zero => intro h; simp [familyGaps]
    | succ r ih =>
      intro h
      have hp := ih (fun i => h (i + 1))
      simp only [familyGaps, List.sum_cons, List.sum_append, List.sum_replicate,
        nsmul_eq_mul, mul_one, Nat.cast_id]
      omega
  have hirrel : ∀ (pre post : List ℕ) (p b e : ℕ), p + span pre ≤ b →
      transport (ones (pre ++ post) p) b e = transport (ones post (p + span pre)) b e := by
    intro pre
    induction pre with
    | nil => intro post p b e hp; simp [span]
    | cons l ls ih =>
      intro post p b e hp
      have hp' : p + l + 1 + span ls ≤ b := by
        simp only [span, List.map_cons, List.sum_cons] at hp ⊢
        omega
      have hp0 : p ≤ b := by omega
      have heq : transport (ones ((l :: ls) ++ post) p) b e =
          transport (ones (ls ++ post) (p + l + 1)) b e := by
        unfold transport
        congr 2
        ext x
        simp only [List.cons_append, ones, Finset.mem_filter, Finset.mem_Ioo,
          Finset.mem_insert, not_or]
        constructor
        · rintro ⟨hi, _, hx⟩; exact ⟨hi, hx⟩
        · rintro ⟨hi, hx⟩; exact ⟨hi, by omega, hx⟩
      rw [heq, ih post (p + l + 1) b e hp']
      congr 2
      simp [span]; omega
  induction r generalizing h p with
  | zero =>
    rw [direction, hselected _ _ _ _ (by omega)]
    simp only [longAnchor, responseModel]
    have hs : span (familyGaps 0 h) = 4 := by simp [span, familyGaps]
    rw [hs]
    by_cases hl : 5 + n ≤ R
    · rw [if_pos (by omega), if_pos hl]
      have hp := transport_suffix [3] [] p n
      simpa [familyGaps, span, Nat.add_assoc] using hp
    · rw [if_neg (by omega), if_neg hl]
  | succ r ih =>
    let ht := fun i => h (i + 1)
    let pre := (2 * (r + 1) + 3) :: List.replicate (2 * h 0) 1
    let p' := p + 2 * (r + 1) + 4 + 4 * h 0
    have hsp : span (familyGaps (r + 1) h) =
        2 * (r + 1) + 4 + 4 * h 0 + span (familyGaps r ht) := by
      simp [familyGaps, span, ht, List.sum_replicate]; omega
    have hpre : p + span pre = p' := by
      simp [pre, span, p', List.sum_replicate]; omega
    have heq : p + span (familyGaps (r + 1) h) + 1 + n =
        p' + span (familyGaps r ht) + 1 + n := by
      dsimp [p']; omega
    rw [direction, hselected _ _ _ _ (by omega)]
    simp only [longAnchor, responseModel]
    by_cases hl : span (familyGaps (r + 1) h) + 1 + n ≤ R
    · rw [if_pos (by omega), if_pos hl]
      let post := List.replicate (2 * h 0) 1 ++ familyGaps r ht
      have hp := transport_suffix [2 * (r + 1) + 3] post p n
      have hpost : post.sum % 2 = (r + 1) % 2 := by
        have := hparity r ht
        simp only [post, List.sum_append, List.sum_replicate, nsmul_eq_mul, mul_one, Nat.cast_id]
        omega
      have he' : p + span [2 * (r + 1) + 3] + span post + 1 + n =
          p + span (familyGaps (r + 1) h) + 1 + n := by
        simp [span, familyGaps, post, ht]; omega
      rw [he'] at hp
      have hb : p + span [2 * (r + 1) + 3] = p + 2 * (r + 1) + 4 := by
        simp [span]; omega
      rw [hb] at hp
      change transport (ones (familyGaps (r + 1) h) p)
        (p + 2 * (r + 1) + 4) _ = _
      change transport (ones ([2 * (r + 1) + 3] ++ post) p)
        (p + 2 * (r + 1) + 4) _ = _
      rw [hp]
      omega
    · rw [if_neg (by omega), if_neg hl]
      rw [heq, ← ih ht p']
      rw [direction, hselected _ _ _ _ (by omega)]
      change (match longAnchor r ht p' R (p' + span (familyGaps r ht) + 1 + n) with
        | none => 0
        | some c => transport (ones (familyGaps (r + 1) h) p) c.2 _) = _
      cases ha : longAnchor r ht p' R (p' + span (familyGaps r ht) + 1 + n) with
      | none => rfl
      | some c =>
        have hs := family_selection r ht p' R (p' + span (familyGaps r ht) + 1 + n)
          (by omega)
        rw [ha] at hs
        have hc : Complete (ones (familyGaps r ht) p') c.1 c.2 :=
          (Finset.mem_filter.mp hs.1).2.2
        have hp'c := ((ones_geometry (familyGaps r ht) p').1 c.2 hc.2.2.1).1
        have he' := hirrel pre (familyGaps r ht) p c.2
          (p' + span (familyGaps r ht) + 1 + n) (by omega)
        rw [hpre] at he'
        exact he'

end D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse

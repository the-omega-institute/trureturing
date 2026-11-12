/- GID: D5/S3/Combinatorics/Graph/Roommates/CyclicClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/CyclicClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Every certified word closes into a stable labelled cyclic profile after six sites. -/

import D5.S3.Combinatorics.Graph.Roommates.CyclicBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
open OpenCertificates CyclicBridge PaddedCompletion

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
  let r := closingRequest d hw.bounded
  have hc := closing_request_completion hw
  intro x
  cases x with
  | inl i =>
    by_cases h : exterior d i
    · have he : ∃ a : ClosingRequester d, r a = r ⟨i,h⟩ := ⟨⟨i,h⟩,rfl⟩
      have hh : Classical.choose he = (⟨i,h⟩ : ClosingRequester d) := hc.1 (Classical.choose_spec he)
      simp only [joinPartner, dif_pos h, BufferLayout.partner, dif_pos he, hh]
    · let j := inside d i h
      have hj := inside_coord i h
      have hdj : d j = -d i := by
        by_cases hz : d i = 0
        · have he : j = i := Fin.ext (by dsimp [j] at hj; omega)
          simpa [he, hz]
        · exact hw.reciprocal i j hz hj.symm
      have hn : ¬exterior d j := by
        have hi := i.isLt
        dsimp [exterior]
        omega
      have he : inside d j hn = i := by
        apply Fin.ext
        have ht := inside_coord j hn
        omega
      simp only [joinPartner, dif_neg h, dif_neg hn, he]
  | inr b =>
    by_cases h : ∃ a : ClosingRequester d, r a = b
    · let a := Classical.choose h
      have ha : r a = b := Classical.choose_spec h
      have he := a.property
      simp only [joinPartner, BufferLayout.partner, dif_pos h, dif_pos he]
      exact congrArg Sum.inr ha
    · have hfree : ¬∃ a : ClosingRequester d,
          r a = BufferLayout.mate (BufferLayout.flags r) b := by
        intro ⟨a,ha⟩
        have he := hc.2.1 (.inr b)
        simp only [BufferLayout.partner, dif_neg h, dif_pos (show ∃ a', r a' =
          BufferLayout.mate (BufferLayout.flags r) b from ⟨a,ha⟩)] at he
        cases he
      have he := hc.2.1 (.inr b)
      simp only [BufferLayout.partner, dif_neg h, dif_neg hfree, Sum.inr.injEq] at he
      simpa only [joinPartner, BufferLayout.partner, dif_neg h, dif_neg hfree] using congrArg Sum.inr he

/-- The full cycle partner map, retaining old interior pairs and fulfilling all requests. -/
def matching (hw : Certificate w d) : SourceModel.Matching (Fin (m + 1 + 5)) := by
  let e : (Fin m ⊕ Fin 6) ≃ Fin (m + 1 + 5) := finSumFinEquiv
  let f := joinPartner hw
  have hf := joinPartner_involutive hw
  let g := fun i => e (f (e.symm i))
  have hg : Function.Involutive g := by
    intro i
    simp only [g, Equiv.symm_apply_apply, hf, Equiv.apply_symm_apply]
  exact ⟨Equiv.ofInvolutive g hg, hg⟩

private theorem matching_apply_sum (hw : Certificate w d) (x : Fin m ⊕ Fin 6) :
    (matching hw).val (finSumFinEquiv x) = finSumFinEquiv (joinPartner hw x) := by
  simp [matching, Equiv.ofInvolutive]

private theorem matching_old (hw : Certificate w d) (i : Fin m) :
    (matching hw).val (Fin.castAdd 6 i) = wrap (m + 1) (i.val + d i) := by
  have he := matching_apply_sum hw (.inl i)
  simp only [finSumFinEquiv_apply_left] at he
  rw [he]
  by_cases h : exterior d i
  · simp only [joinPartner, dif_pos h, finSumFinEquiv_apply_right]
    exact (closing_request_source_target hw ⟨i,h⟩).symm.trans
      (wrap_index (Fin.natAdd m (closingRequest d hw.bounded ⟨i,h⟩))) |>.symm
  · simp only [joinPartner, dif_neg h, finSumFinEquiv_apply_left]
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
    (matching hw).val (Fin.natAdd m b) = wrap (m+1) ((m : ℤ)+b.val+bufferD hw b) := by
  let r := closingRequest d hw.bounded
  have he := matching_apply_sum hw (.inr b)
  simp only [finSumFinEquiv_apply_right] at he
  rw [he]
  by_cases h : ∃ a : ClosingRequester d, r a = b
  · let a := Classical.choose h
    have ha : r a = b := Classical.choose_spec h
    have hd : bufferD hw b = -d a.val := by rw [←ha]; exact (buffer_facts hw).1 a
    simp only [joinPartner, BufferLayout.partner, dif_pos h, finSumFinEquiv_apply_left]
    have ht : wrap (m+1) (a.val.val + d a.val) = Fin.natAdd m b := by
      rw [closing_request_source_target hw a]
      simpa [r, ha] using (wrap_index (Fin.natAdd m b))
    have hr := wrap_return (Fin.castAdd 6 a.val) (Fin.natAdd m b) (d a.val) ht
    simpa only [Fin.val_natAdd, Nat.cast_add, hd, sub_eq_add_neg] using hr.symm
  · simp only [joinPartner, BufferLayout.partner, dif_neg h, finSumFinEquiv_apply_right]
    have hd : bufferD hw b = (BufferLayout.mate (BufferLayout.flags r) b).val - (b.val : ℤ) := by
      simp only [bufferD, bufferOffset, dif_neg h]
    rw [hd, show (m : ℤ)+b.val+((BufferLayout.mate (BufferLayout.flags r) b).val-b.val) =
      (m : ℤ)+(BufferLayout.mate (BufferLayout.flags r) b).val by omega]
    exact (wrap_index (Fin.natAdd m (BufferLayout.mate (BufferLayout.flags r) b))).symm

/-- Six added rankings preserve every old ranking literally. -/
def profile (hw : Certificate w d) : SourceModel.Profile (m+1) :=
  fun i => if h : i.val < m then w ⟨i.val,h⟩
    else partnerFirst (bufferD hw ⟨i.val-m,by omega⟩)

private theorem profile_old (hw : Certificate w d) (i : Fin m) :
    profile hw (Fin.castAdd 6 i) = w i := by simp [profile, i.isLt]

private theorem profile_buffer (hw : Certificate w d) (b : Fin 6) :
    profile hw (Fin.natAdd m b) = partnerFirst (bufferD hw b) := by
  simp [profile, show ¬m+b.val<m by omega]

private theorem matching_buffer_rank (hw : Certificate w d) (b : Fin 6) :
    SourceModel.rank (profile hw) (Fin.natAdd m b) ((matching hw).val (Fin.natAdd m b)) =
      offsetRank (partnerFirst (bufferD hw b)) (bufferD hw b) := by
  rw [matching_buffer]
  have hr := rank_wrap (profile hw) (Fin.natAdd m b) (bufferD hw b) ((buffer_facts hw).2.1 b)
  simpa [profile_buffer, Fin.val_natAdd, Nat.cast_add] using hr

private theorem buffer_top (hw : Certificate w d) (b : Fin 6) (hz : bufferD hw b ≠ 0) :
    SourceModel.rank (profile hw) (Fin.natAdd m b) ((matching hw).val (Fin.natAdd m b)) = 0 := by
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
  obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective i
  cases x with
  | inl j =>
    simp only [finSumFinEquiv_apply_left]
    rw [matching_old]
    exact acceptable_offset (Fin.castAdd 6 j) (d j) (hw.bounded j)
  | inr b =>
    simp only [finSumFinEquiv_apply_right]
    rw [matching_buffer]
    exact acceptable_offset (Fin.natAdd m b) (bufferD hw b) ((buffer_facts hw).2.1 b)

private theorem central_neighbor (hw : Certificate w d) (b : Fin 6)
    (hz : bufferD hw b = 0) (j : Fin (m+1+5))
    (hadj : (SourceModel.ring (m+1)).Adj (Fin.natAdd m b) j) :
    ∃ c : Fin 6, j = Fin.natAdd m c ∧ b ≠ c ∧
      b.val ≤ c.val+2 ∧ c.val ≤ b.val+2 := by
  obtain ⟨s,hs⟩ := hadj
  have hc := (buffer_facts hw).2.2.1 b hz
  have hb : b.val = 2 ∨ b.val = 3 := by rcases hc with rfl | rfl <;> simp
  have hsb := signed_bounds s
  have he : wrap (m+1) ((m : ℤ)+b.val+signed s) = j := by
    rw [wrap_add, wrap_signed]
    simpa only [Fin.val_natAdd, Nat.cast_add, wrap_index] using hs.symm
  have hv := congrArg (fun x : Fin (m+1+5) => (x.val : ℤ)) he
  rw [wrap_val, Int.emod_eq_of_lt (by omega) (by omega)] at hv
  let c : Fin 6 := ⟨j.val-m,by omega⟩
  refine ⟨c, Fin.ext (by dsimp [c]; simp only [Fin.val_natAdd]; omega), ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun x : Fin 6 => (x.val : ℤ)) h
    dsimp [c] at hh
    omega
  · dsimp [c]; omega
  · dsimp [c]; omega

private theorem no_buffer_blocker (hw : Certificate w d) (b : Fin 6) (j : Fin (m+1+5)) :
    ¬SourceModel.IsBlockingPair (SourceModel.ring (m+1)) (SourceModel.rank (profile hw))
      (matching hw) (Fin.natAdd m b) j := by
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
  have hne : i ≠ j := by intro h; subst j; exact (SourceModel.ring (m+1)).irrefl _ hadj
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
      simpa only [add_sub_cancel] using (wrap_index (Fin.castAdd 6 j))
    · right;left; simpa only [matching_old] using he
    · right;right; simpa only [matching_old] using he
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
  obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective j
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
      have hh := (matching hw).property (Fin.natAdd m b)
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

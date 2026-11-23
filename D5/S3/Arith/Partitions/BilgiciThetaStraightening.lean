/- GID: D5/S3/Arith/Partitions/BilgiciThetaStraightening
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaStraightening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every projected centered degree-seven word lies in a four-word span. -/

import D5.S3.Arith.Partitions.BilgiciThetaStraighteningRows

/-! Every projected centered degree-seven word lies in a four-word span. -/

open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

set_option maxRecDepth 100000
set_option maxHeartbeats 450000

private theorem centered_cons (i : Fin 9) (m : Word) :
    centered (i :: m) = digit i^2 + centered m := rfl

private theorem total_squares : (∑ i : Fin 9, digit i ^ 2) = (0 : K) := by decide

private theorem complement_squares (l : Word) (hd : l.Nodup) :
    (∑ i ∈ l.toFinsetᶜ, digit i ^ 2) = -centered l := by
  have h := Finset.sum_compl_add_sum l.toFinset (fun i => digit i ^ 2)
  rw [total_squares, List.sum_toFinset _ hd] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem two_squares_not_zero (a b : Fin 9) : digit a^2 + digit b^2 ≠ 0 := by
  decide +revert

private theorem squarefree_impossible (m : Word) (hl : m.length = 7)
    (hd : m.Nodup) (hz : centered m = 0) : False := by
  have hc : (m.toFinsetᶜ).card = 2 := by
    rw [Finset.card_compl, List.toFinset_card_of_nodup hd, hl]
    decide
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp hc
  have hx := complement_squares m hd
  rw [he, Finset.sum_pair hab, hz, neg_zero] at hx
  exact two_squares_not_zero a b hx

set_option maxHeartbeats 2500000 in
private theorem omitted_triple (a b c : Fin 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hz : digit a^2 + digit b^2 + digit c^2 = 1) :
    let s : Finset (Fin 9) := {a,b,c}
    s = (baseC.tail.toFinset)ᶜ ∨ s = (baseD.tail.toFinset)ᶜ ∨
    s = (wordE.tail.toFinset)ᶜ ∨ s = (wordF.tail.toFinset)ᶜ := by
  fin_cases a <;> decide +revert

private def twoDoubleRepresentative (m : Word) : Prop :=
  m.Perm baseB ∨ m.Perm wordI ∨ m.Perm rootR3 ∨
    m.Perm wordB7 ∨ m.Perm wordH ∨ m.Perm wordG

instance (m : Word) : Decidable (twoDoubleRepresentative m) := by
  unfold twoDoubleRepresentative
  infer_instance

set_option maxHeartbeats 2500000 in
macro "smaller_mem" h:ident w:ident : tactic =>
  `(tactic| exact $h $w (by decide) (by decide) (by decide))

private theorem stepE {M : Submodule K A} (hs : smaller M wordE) : evalWord wordE ∈ M := by
  rw [relE]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseC
  · smaller_mem hs baseD

private theorem stepF {M : Submodule K A} (hs : smaller M wordF) : evalWord wordF ∈ M := by
  rw [relF]
  apply M.smul_mem
  smaller_mem hs baseC

private theorem stepI {M : Submodule K A} (hs : smaller M wordI) : evalWord wordI ∈ M := by
  rw [relI]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs wordE
  · smaller_mem hs wordF

private theorem stepR3 {M : Submodule K A} (hs : smaller M rootR3) : evalWord rootR3 ∈ M := by
  rw [relR3]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs wordF
  · smaller_mem hs baseD

private theorem stepB7 {M : Submodule K A} (hs : smaller M wordB7) : evalWord wordB7 ∈ M := by
  rw [scaleB7, relK]
  apply M.smul_mem
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseD
  · smaller_mem hs wordE

private theorem stepH {M : Submodule K A} (hs : smaller M wordH) : evalWord wordH ∈ M := by
  rw [relH]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseB
  · smaller_mem hs wordF

private theorem stepG {M : Submodule K A} (hs : smaller M wordG) : evalWord wordG ∈ M := by
  rw [relG]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseC
  · smaller_mem hs baseD

private theorem stepL {M : Submodule K A} (hs : smaller M wordL) : evalWord wordL ∈ M := by
  rw [relL]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseD
  · smaller_mem hs wordE

private theorem stepM {M : Submodule K A} (hs : smaller M wordM) : evalWord wordM ∈ M := by
  rw [relM]
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs wordE
  · smaller_mem hs baseD

private theorem stepN {M : Submodule K A} (hs : smaller M wordN) : evalWord wordN ∈ M := by
  rw [scaleN, relJ]
  apply M.smul_mem
  apply M.add_mem <;> apply M.smul_mem
  · smaller_mem hs baseB
  · smaller_mem hs wordF

private theorem twoDoubleRepresentative_mem {M : Submodule K A} {m : Word}
    (hr : twoDoubleRepresentative m) (hs : smaller M m) (hb : evalWord baseB ∈ M) :
    evalWord m ∈ M := by
  rcases hr with h | h | h | h | h | h
  · rwa [evalWord_perm h]
  · rw [evalWord_perm h]; exact stepI (smaller_perm h hs)
  · rw [evalWord_perm h]; exact stepR3 (smaller_perm h hs)
  · rw [evalWord_perm h]; exact stepB7 (smaller_perm h hs)
  · rw [evalWord_perm h]; exact stepH (smaller_perm h hs)
  · rw [evalWord_perm h]; exact stepG (smaller_perm h hs)

private theorem reduce22111 {M : Submodule K A} (a b c d e : Fin 9) (hd : [a,b,c,d,e].Nodup)
    (hb : evalWord baseB ∈ M) (hs : smaller M [a,a,b,b,c,d,e])
    (hz : centered [a,a,b,b,c,d,e] = 0) : evalWord [a,a,b,b,c,d,e] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (b c d e : Fin 9) (hd : [0,b,c,d,e].Nodup)
    (hz : centered [0,0,b,b,c,d,e] = 0) :
    twoDoubleRepresentative [0,0,b,b,c,d,e] ∨
      twoDoubleRepresentative (scaleWord (digit b ^ 17) [0,0,b,b,c,d,e]) := by
    fin_cases b <;> decide +revert
  obtain h | h := step _ _ _ _ hd' hz'
  · exact twoDoubleRepresentative_mem h hs' hb
  · have hn : digit (scaleIndex k b) ^ 17 ≠ 0 := pow_ne_zero _ (digit_nonzero _)
    obtain ⟨r, hr⟩ := evalWord_scale _ hn
      [0,0,scaleIndex k b,scaleIndex k b,scaleIndex k c,scaleIndex k d,scaleIndex k e]
    rw [hr]
    exact M.smul_mem _ (twoDoubleRepresentative_mem h (smaller_scale _ hn hs') hb)

private theorem reduce2221 {M : Submodule K A} (a b c d : Fin 9) (hd : [a,b,c,d].Nodup)
    (hs : smaller M [a,a,b,b,c,c,d]) (hz : centered [a,a,b,b,c,c,d] = 0) :
    evalWord [a,a,b,b,c,c,d] ∈ M := by
  apply normalize_at _ d hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (a b c : Fin 9) (hd : [a,b,c,0].Nodup)
    (hz : centered [a,a,b,b,c,c,0] = 0) :
    [a,a,b,b,c,c,0].Perm wordM ∨ [a,a,b,b,c,c,0].Perm wordN ∨
      [a,a,b,b,c,c,0].Perm wordL := by
    fin_cases a <;> decide +revert
  obtain h | h | h := step _ _ _ hd' hz'
  · rw [evalWord_perm h]; exact stepM (smaller_perm h hs')
  · rw [evalWord_perm h]; exact stepN (smaller_perm h hs')
  · rw [evalWord_perm h]; exact stepL (smaller_perm h hs')

private theorem reduce211111 {M : Submodule K A} (a b c d e f : Fin 9) (hd : [a,b,c,d,e,f].Nodup)
    (hc : evalWord baseC ∈ M) (hd₀ : evalWord baseD ∈ M)
    (hs : smaller M [a,a,b,c,d,e,f]) (hz : centered [a,a,b,c,d,e,f] = 0) :
    evalWord [a,a,b,c,d,e,f] ∈ M := by
  apply normalize_at _ a hs hz
  intro k hk h0 hs' hz'
  have hd' := hd.map (scaleIndex_injective hk)
  simp only [scaleWord, List.map_cons, List.map_nil, h0] at hs' hz' ⊢
  simp only [List.map_cons, List.map_nil, h0] at hd'
  have step (l : Word) (hl : l.length = 6) (hd : l.Nodup)
    (h0 : (0 : Fin 9) ∈ l) (hz : centered (0 :: l) = 0) :
    (0 :: l).Perm baseC ∨ (0 :: l).Perm baseD ∨
    (0 :: l).Perm wordE ∨ (0 :: l).Perm wordF := by
    have hcard : (l.toFinsetᶜ).card = 3 := by
      rw [Finset.card_compl, List.toFinset_card_of_nodup hd, hl]
      decide
    obtain ⟨a,b,c,hab,hac,hbc,he⟩ := Finset.card_eq_three.mp hcard
    have ha : a ≠ 0 := by
      have ha' : a ∈ l.toFinsetᶜ := he.symm ▸ Finset.mem_insert_self _ _
      exact fun hn => (Finset.mem_compl.mp ha') (List.mem_toFinset.mpr (hn.symm ▸ h0))
    have hb : b ≠ 0 := by
      have hb' : b ∈ l.toFinsetᶜ := he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      exact fun hn => (Finset.mem_compl.mp hb') (List.mem_toFinset.mpr (hn.symm ▸ h0))
    have hc : c ≠ 0 := by
      have hc' : c ∈ l.toFinsetᶜ := he.symm ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      exact fun hn => (Finset.mem_compl.mp hc') (List.mem_toFinset.mpr (hn.symm ▸ h0))
    have hsum := complement_squares l hd
    have hz' : -centered l = 1 := by
      rw [centered_cons, show digit 0 ^ 2 = 1 by decide] at hz
      exact (eq_neg_of_add_eq_zero_left hz).symm
    rw [hz', he, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc] at hsum
    have h := omitted_triple a b c hab hac hbc ha hb hc hsum
    rw [← he] at h
    have hp (t : Word) (ht : t.tail.Nodup) (hc : l.toFinsetᶜ = t.tail.toFinsetᶜ) :
        (0 :: l).Perm (0 :: t.tail) :=
      (List.perm_of_nodup_nodup_toFinset_eq hd ht (compl_injective hc)).cons 0
    rcases h with h | h | h | h
    · exact Or.inl (hp baseC (by decide) h)
    · exact Or.inr (Or.inl (hp baseD (by decide) h))
    · exact Or.inr (Or.inr (Or.inl (hp wordE (by decide) h)))
    · exact Or.inr (Or.inr (Or.inr (hp wordF (by decide) h)))
  obtain h | h | h | h := step _ rfl hd' (by simp) hz'
  · rw [evalWord_perm h]; exact hc
  · rw [evalWord_perm h]; exact hd₀
  · rw [evalWord_perm h]; exact stepE (smaller_perm h hs')
  · rw [evalWord_perm h]; exact stepF (smaller_perm h hs')


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem rootCoords1 :
    evalWord rootR1 = evalWord baseA + (10 : K) • evalWord baseB +
      (15 : K) • evalWord baseC + (8 : K) • evalWord baseD := by
  simp only [relR1, relU, relI, relJ, relE, relF]
  match_scalars <;> decide

private theorem rootCoords2 :
    evalWord rootR2 = (4 : K) • evalWord baseB + (18 : K) • evalWord baseC +
      (7 : K) • evalWord baseD := by
  simp only [relR2, relV, relG, relE]
  match_scalars <;> decide

private theorem rootCoords3 :
    evalWord rootR3 = (16 : K) • evalWord baseC + (9 : K) • evalWord baseD := by
  simp only [relR3, relF]
  match_scalars <;> decide

private theorem cancel_smul_mem {M : Submodule K A} {c : K} {v : A}
    (hc : c ≠ 0) (hv : c • v ∈ M) : v ∈ M := by
  have h := M.smul_mem c⁻¹ hv
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

private theorem cancel_sum_mem {M : Submodule K A} {c : K} {r u v : A}
    (hc : c ≠ 0) (he : r = u + c • v) (hr : r ∈ M) (hu : u ∈ M) : v ∈ M := by
  have h := M.sub_mem hr hu
  rw [he, add_sub_cancel_left] at h
  exact cancel_smul_mem hc h

private theorem bases_of_requested {M : Submodule K A}
    (h1 : evalWord paper1 ∈ M) (h2 : evalWord paper2 ∈ M)
    (h3 : evalWord paper3 ∈ M) (h4 : evalWord paper4 ∈ M) :
    evalWord baseA ∈ M ∧ evalWord baseB ∈ M ∧ evalWord baseC ∈ M ∧ evalWord baseD ∈ M := by
  rw [scalePaper1] at h1
  rw [scalePaper2] at h2
  rw [scalePaper3] at h3
  rw [scalePaper4, relR4, smul_smul] at h4
  have hr1 := cancel_smul_mem (by decide) h1
  have hr2 := cancel_smul_mem (by decide) h2
  have hr3 := cancel_smul_mem (by decide) h3
  have hc := cancel_smul_mem (by decide) h4
  have hd := cancel_sum_mem (by decide) rootCoords3 hr3 (M.smul_mem _ hc)
  have eb : evalWord rootR2 =
      ((18 : K) • evalWord baseC + (7 : K) • evalWord baseD) + (4 : K) • evalWord baseB := by
    rw [rootCoords2]
    abel
  have hb := cancel_sum_mem (by decide) eb hr2 (M.add_mem (M.smul_mem _ hc) (M.smul_mem _ hd))
  have ea : evalWord rootR1 =
      ((10 : K) • evalWord baseB + (15 : K) • evalWord baseC + (8 : K) • evalWord baseD) +
      (1 : K) • evalWord baseA := by
    rw [rootCoords1, one_smul]
    abel
  have ha := cancel_sum_mem (by decide) ea hr1
    (M.add_mem (M.add_mem (M.smul_mem _ hb) (M.smul_mem _ hc)) (M.smul_mem _ hd))
  exact ⟨ha,hb,hc,hd⟩


end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening
open D5.S3.Arith.Partitions.BilgiciThetaStructural

private theorem centered_span_of_bases {M : Submodule K A}
    (ha : evalWord baseA ∈ M) (hb : evalWord baseB ∈ M)
    (hc : evalWord baseC ∈ M) (hd : evalWord baseD ∈ M)
    (m : Word) : m.length = 7 → centered m = 0 → evalWord m ∈ M := by
  induction m using precedes_wf.induction with
  | h m ih =>
    intro hl hz
    obtain ⟨n, hp, hn⟩ := classify_profile m hl
    apply mem_case_perm hp ih hz
    intro hs hz'
    cases hn with
    | p7 a h => exact reduce7 a h hs hz'
    | p61 a b h => exact reduce61 a b h hs hz'
    | p52 a b h => exact reduce52 a b h hs hz'
    | p511 a b c h => exact reduce511 a b c h hs hz'
    | p43 a b h => exact reduce43 a b h hs hz'
    | p421 a b c h => exact reduce421 a b c h hs hz'
    | p4111 a b c d h => exact reduce4111 a b c d h hs hz'
    | p331 a b c h => exact reduce331 a b c h hs hz'
    | p322 a b c h => exact reduce322 a b c h hs hz'
    | p3211 a b c d h => exact reduce3211 a b c d h ha hs hz'
    | p31111 a b c d e h => exact reduce31111 a b c d e h hs hz'
    | p2221 a b c d h => exact reduce2221 a b c d h hs hz'
    | p22111 a b c d e h => exact reduce22111 a b c d e h hb hs hz'
    | p211111 a b c d e f h => exact reduce211111 a b c d e f h hc hd hs hz'
    | p1111111 a b c d e f g h => exact (squarefree_impossible _ rfl h hz').elim

noncomputable def requestedSpan : Submodule K A :=
  Submodule.span K {q (P (word paper1)), q (P (word paper2)),
    q (P (word paper3)), q (P (word paper4))}

private theorem requested_signed_roots :
    evalWord paper1 ∈ requestedSpan ∧ evalWord paper2 ∈ requestedSpan ∧
      evalWord paper3 ∈ requestedSpan ∧ evalWord paper4 ∈ requestedSpan := by
  unfold requestedSpan
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [evalWord_source] <;> apply Submodule.smul_mem <;>
    apply Submodule.subset_span <;> simp

theorem centered_degree_seven_span (m : Word)
    (hl : m.length = 7) (hz : centered m = 0) :
    q (P (word m)) ∈ requestedSpan := by
  obtain ⟨h1,h2,h3,h4⟩ := requested_signed_roots
  obtain ⟨ha,hb,hc,hd⟩ := bases_of_requested h1 h2 h3 h4
  rw [source_evalWord]
  exact requestedSpan.smul_mem _ (centered_span_of_bases ha hb hc hd m hl hz)

end D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening

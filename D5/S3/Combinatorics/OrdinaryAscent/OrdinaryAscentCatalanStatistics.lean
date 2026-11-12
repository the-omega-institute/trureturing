/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics
   mirror-E: none(waiver:ordinary-ascents-to-actual-dyck-peaks)
   anchors: []
   utility: none
   digest: The actual ordinary-avoider bijection transports ascents to complementary Dyck peaks. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanRank
import D5.S3.Combinatorics.OrdinaryAscent.DyckNarayana

/-! Strict ordinary ascents are transported through the actual rank-complement
equivalence. Dyck peak cardinalities are reused from the licensed supplier. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanStatistics

open OrdinaryAscentSemantics OrdinaryAscentCatalanSites OrdinaryAscentCatalanRank
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)
open D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck (dyckSteps)
open DyckStep

theorem rank_fresh (w : List ℕ) (hw : IsAscent w) :
    rank w (asc w + 1) + 1 = (sites w).card := by
  classical
  have heq : insert (asc w + 1) ((sites w).filter (· < asc w + 1)) = sites w := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨hy, _⟩)
      · exact fresh_mem_sites w hw
      · exact hy
    · intro hy
      have hb := ((mem_sites w y).mp hy).1
      by_cases he : y = asc w + 1
      · exact Or.inl he
      · exact Or.inr ⟨hy, by omega⟩
  have hnot : asc w + 1 ∉ (sites w).filter (· < asc w + 1) := by simp
  have hc := congrArg Finset.card heq
  rwa [Finset.card_insert_of_notMem hnot] at hc

/-- Strict rises in the east-count code are exactly the nonascents of the word. -/
theorem asc_eastCode (w : List ℕ) (hw : CatalanWord w) :
    asc (eastCode w) + asc w = w.length - 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [eastCode, asc]
  | append_singleton w x ih =>
    by_cases he : w = []
    · subst w
      have hx : x = 0 := (singleton_word x).mp hw
      subst x
      have hc : eastCode ([] ++ [0]) = [0] := by rw [eastCode_append]; simp [eastCode]
      rw [hc]
      simp [asc]
    · obtain ⟨hp, hx⟩ := (catalan_append_iff w he x).mp hw
      have hcode : eastCode w ≠ [] := by
        intro hh
        have hl := eastCode_length w
        simp only [hh, List.length_nil] at hl
        exact he (List.length_eq_zero_iff.mp hl.symm)
      have hi := rank_lt_card w x hx
      have hc := card_sites_le w he
      have hf := rank_fresh w hp.1
      have hs := sites_shape w hp he x hx
      have hl := (eastCode_valid w hp).2.2 he
      have hp0 := List.length_pos_iff.mpr he
      have hold := ih hp
      have hget : (eastCode w).getD ((eastCode w).length - 1) 0 =
          (eastCode w).getLastD 0 := by
        simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        rfl
      have ha := asc_append w x
      have hb := asc_append (eastCode w) (w.length - rank w x)
      simp only [if_neg he] at ha
      simp only [if_neg hcode, hget] at hb
      rw [eastCode_append]
      by_cases hu : w.getD (w.length - 1) 0 < x
      · have heq : x = asc w + 1 := by omega
        rw [← heq] at hf
        have heast : w.length - rank w x = (eastCode w).getLastD 0 := by omega
        simp only [if_pos hu] at ha
        rw [if_neg (by omega : ¬ (eastCode w).getLastD 0 < w.length - rank w x),
          Nat.add_zero] at hb
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        omega
      · have hxlt : x < asc w + 1 := by
          have hh := entry_le_asc w hp.1 (w.length - 1) (by omega)
          omega
        have hr := rank_strictMono w hx hxlt
        have heast : (eastCode w).getLastD 0 < w.length - rank w x := by omega
        simp only [if_neg hu, Nat.add_zero] at ha
        simp only [if_pos heast] at hb
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
        omega

private theorem asc_cons_cons (a b : ℕ) (l : List ℕ) :
    asc (a :: b :: l) = asc (b :: l) + if a < b then 1 else 0 := by
  unfold asc
  simp only [List.length_cons, Nat.add_sub_cancel, Finset.card_filter]
  rw [Finset.sum_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add]

private theorem peaks_down (d : ℕ) (l : List DyckStep) :
    DyckWord.peakCountList (List.replicate d D ++ l) = DyckWord.peakCountList l := by
  induction d with
  | zero => simp
  | succ d ih => simpa only [List.replicate_succ, List.cons_append, DyckWord.pc_D] using ih

private theorem head_dyckSteps (n east v : ℕ) (e : List ℕ) :
    (dyckSteps n east (v :: e)).head? = if east < v then some D else some U := by
  by_cases h : east < v
  · have hp : 0 < v - east := by omega
    obtain ⟨d, hd⟩ : ∃ d, v - east = d + 1 := ⟨v - east - 1, by omega⟩
    simp [dyckSteps, hd, List.replicate_succ, h]
  · have hz : v - east = 0 := by omega
    simp [dyckSteps, hz, h]

/-- Peaks of the existing east-count Dyck encoding, with all endpoint bounds explicit. -/
theorem peaks_dyckSteps (n east : ℕ) (e : List ℕ)
    (hb : ∀ v ∈ e, v < n) :
    DyckWord.peakCountList (dyckSteps n east e) =
      if e = [] then 0 else 1 + asc e := by
  induction e generalizing east with
  | nil => simpa [dyckSteps, DyckWord.peakCountList] using peaks_down (n - east) []
  | cons v e ih =>
    rw [dyckSteps, peaks_down, DyckWord.pc_U]
    cases e with
    | nil =>
      have hv : v < n := hb v (by simp)
      have hp : 0 < n - v := by omega
      obtain ⟨d, hd⟩ : ∃ d, n - v = d + 1 := ⟨n - v - 1, by omega⟩
      have hz := peaks_down (n - v) []
      simp only [List.append_nil] at hz
      have hzd : DyckWord.peakCountList (List.replicate d D) = 0 := by
        simpa [DyckWord.peakCountList] using peaks_down d []
      simp [dyckSteps, hd, List.replicate_succ, asc, DyckWord.peakCountList, hzd]
    | cons u e =>
      have ht := ih v (by intro a ha; exact hb a (by simp [ha]))
      rw [head_dyckSteps]
      simp only [List.cons_ne_nil, if_false] at ht ⊢
      rw [ht, asc_cons_cons]
      split_ifs <;> simp_all <;> omega

/-- The actual Mathlib Dyck word has exactly length minus ascents many UD peaks. -/
theorem dyckEquiv_peaks (n : ℕ) (w : avoiders n {.p101, .p201}) :
    (dyckEquiv n w).val.peakCount = n - asc w.val := by
  have hw := (mem_catalan_avoiders n w.val).mp w.property
  have hv := eastCode_valid w.val hw.2
  have hbounds : ∀ v ∈ eastCode w.val, v < n := by
    intro v hm
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    have hi := hv.1 j hj
    rw [List.getD_eq_getElem _ _ hj] at hi
    have hn : (eastCode w.val).length = n := (eastCode_length w.val).trans hw.1
    omega
  rw [DyckWord.peakCount, dyckEquiv_forward, peaks_dyckSteps n 0 _ hbounds]
  have hc := asc_eastCode w.val hw.2
  have hl := eastCode_length w.val
  have ha := asc_le w.val
  split_ifs with he
  · have hn : n = 0 := by simp only [he, List.length_nil] at hl; omega
    subst n
    simp
  · have hp : 0 < n := by
      have := List.length_pos_iff.mpr he
      omega
    omega

/-- Restrict the proved ordinary-word equivalence to actual ascent/peak fibers. -/
def ascentPeakEquiv (n r : ℕ) (hr : r < n) :
    {w : List ℕ // w ∈ avoiders n {.p101, .p201} ∧ asc w = r} ≃
      {p : {p : DyckWord // p.semilength = n} // p.val.peakCount = n - r} where
  toFun w := ⟨dyckEquiv n ⟨w.val, w.property.1⟩, by
    rw [dyckEquiv_peaks, w.property.2]⟩
  invFun p := ⟨((dyckEquiv n).symm p.val).val, by
    refine ⟨((dyckEquiv n).symm p.val).property, ?_⟩
    have hh := dyckEquiv_peaks n ((dyckEquiv n).symm p.val)
    rw [(dyckEquiv n).apply_symm_apply, p.property] at hh
    have hl := ((mem_catalan_avoiders n _).mp ((dyckEquiv n).symm p.val).property).1
    have ha := asc_le ((dyckEquiv n).symm p.val).val
    omega⟩
  left_inv w := by
    apply Subtype.ext
    exact congrArg (fun z : avoiders n {.p101, .p201} => z.val)
      ((dyckEquiv n).symm_apply_apply ⟨w.val, w.property.1⟩)
  right_inv p := Subtype.ext ((dyckEquiv n).apply_symm_apply p.val)

/-- The ascent distribution is Narayana, with positive-peak boundary hypotheses
discharged before applying the licensed supplier. -/
theorem narayana_ascents (n r : ℕ) (hr : r < n) :
    n * {w : List ℕ | w ∈ avoiders n {.p101, .p201} ∧ asc w = r}.ncard =
      n.choose r * n.choose (r + 1) := by
  rw [← Nat.card_coe_set_eq]
  change n * Nat.card {w : List ℕ // w ∈ avoiders n {.p101, .p201} ∧ asc w = r} = _
  rw [Nat.card_congr (ascentPeakEquiv n r hr),
    Nat.card_eq_fintype_card, DyckWord.card_semilength_peakCount n (n - r) (by omega),
    Nat.narayana_mul n (n - r) (by omega) (by omega)]
  rw [Nat.choose_symm (Nat.le_of_lt hr)]
  have hsub : n - r - 1 = n - (r + 1) := by omega
  rw [hsub, Nat.choose_symm (by omega : r + 1 ≤ n)]

private theorem dyckSteps_append (n east : ℕ) (e : List ℕ) (v : ℕ) :
    dyckSteps n east (e ++ [v]) = dyckSteps v east e ++ U :: List.replicate (n - v) D := by
  induction e generalizing east with
  | nil => simp [dyckSteps]
  | cons a e ih => simp [dyckSteps, ih, List.append_assoc]

private theorem dyckSteps_split (n t east : ℕ) (e : List ℕ) (ht : t ≤ n)
    (he : east ≤ t) (hb : ∀ a ∈ e, a ≤ t) :
    dyckSteps n east e = dyckSteps t east e ++ List.replicate (n - t) D := by
  induction e generalizing east with
  | nil =>
    simp only [dyckSteps]
    rw [← List.replicate_add]
    congr 1
    omega
  | cons a e ih =>
    simp only [dyckSteps]
    rw [ih a (hb a (by simp)) (by intro b hm; exact hb b (by simp [hm]))]
    simp only [List.append_assoc, List.cons_append]

/-- The actual word equivalence inserts UD immediately before the last i downsteps,
where i is the appended letter's actual zero-based rank. The displayed formulas
also give the rightmost-U/following-D deletion inverse at every nonroot step. -/
theorem dyckEquiv_insert (n : ℕ) (w : avoiders n {.p101, .p201})
    (hne : w.val ≠ []) (x : ℕ) (v : avoiders (n + 1) {.p101, .p201})
    (hv : v.val = w.val ++ [x]) :
    ∃ Q : List DyckStep,
      (dyckEquiv n w).val.toList = Q ++ List.replicate (rank w.val x) D ∧
      (dyckEquiv (n + 1) v).val.toList = Q ++ U :: List.replicate (rank w.val x + 1) D := by
  have hw := (mem_catalan_avoiders n w.val).mp w.property
  have hchild := ((mem_catalan_avoiders (n + 1) v.val).mp v.property).2
  rw [hv] at hchild
  have hx := ((catalan_append_iff w.val hne x).mp hchild).2
  have hi := rank_lt_card w.val x hx
  have hc := card_sites_le w.val hne
  have hp := eastCode_valid w.val hw.2
  have hl := hp.2.2 hne
  have hir : rank w.val x ≤ n := by omega
  have ht : n - rank w.val x ≤ n := Nat.sub_le _ _
  have hbound : ∀ a ∈ eastCode w.val, a ≤ n - rank w.val x := by
    intro a ha
    have hn := List.ne_nil_of_mem ha
    have hm := hp.2.1.rel_getLast ha
    have heq : (eastCode w.val).getLastD 0 = (eastCode w.val).getLast hn := by
      simp [List.getLast?_eq_some_getLast hn]
    omega
  refine ⟨dyckSteps (n - rank w.val x) 0 (eastCode w.val), ?_, ?_⟩
  · rw [dyckEquiv_forward, dyckSteps_split n (n - rank w.val x) 0 _ ht (by omega) hbound,
      Nat.sub_sub_self hir]
  · rw [dyckEquiv_forward, hv, eastCode_append, hw.1, dyckSteps_append]
    have heq : n + 1 - (n - rank w.val x) = rank w.val x + 1 := by omega
    rw [heq]

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanStatistics

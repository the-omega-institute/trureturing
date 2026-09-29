/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps
   mirror-E: none(waiver:prefix-gap-normal-form-for-the-arrow-pattern-32-1-to-3)
   anchors: [D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection]
   utility: none
   digest: Increasing relabelling preserves Foata edges; ordered value cuts give the unique independent gap words of a last-cycle prefix. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijection

/-- The edge condition on a possibly incomplete value interval. Missing values
between the endpoints are forbidden as well. -/
def ClosedEdges (p : List ℕ) : Prop :=
  ∀ a c : ℕ, a ∈ p → a < c → c < hat p a → [c, hat p a].Sublist p

/-- An increasing change of labels conjugates the inverse Foata map on its support. -/
theorem hat_map_strictMono (p : List ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (a : ℕ) (ha : a ∈ p) : hat (p.map f) (f a) = f (hat p a) := by
  have hidx : (p.map f).idxOf (f a) = p.idxOf a := by
    induction p with
    | nil => simp
    | cons b p ih =>
        by_cases hab : a = b
        · subst a; simp
        · have hfab : f a ≠ f b := fun h => hab (hf.injective h)
          have ha' : a ∈ p := by simpa [hab] using ha
          simp [Ne.symm hab, hfab.symm, ih ha']
  have hget (i : ℕ) (hi : i < p.length) :
      (p.map f).getD i 0 = f (p.getD i 0) := by
    rw [List.getD_eq_getElem _ 0 (by simpa using hi),
      List.getD_eq_getElem _ 0 hi, List.getElem_map]
  have hltr (i : ℕ) (hi : i < p.length) :
      IsLtrMax (p.map f) i ↔ IsLtrMax p i := by
    constructor
    · intro h j hj
      have h' := h j hj
      rw [hget j (by omega), hget i hi] at h'
      exact hf.lt_iff_lt.mp h'
    · intro h j hj
      rw [hget j (by omega), hget i hi]
      exact hf (h j hj)
  have hg (i : ℕ) (hi : i < p.length) :
      Nat.findGreatest (IsLtrMax (p.map f)) i = Nat.findGreatest (IsLtrMax p) i := by
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [Nat.findGreatest_succ, Nat.findGreatest_succ]
        by_cases h : IsLtrMax p (i + 1)
        · simp [h, (hltr _ hi).mpr h]
        · simp [h, (hltr _ hi).not.mpr h, ih (by omega)]
  have hi : p.idxOf a < p.length := List.idxOf_lt_length_of_mem ha
  have hb :
      (p.idxOf a + 1 < (p.map f).length ∧ ¬ IsLtrMax (p.map f) (p.idxOf a + 1)) ↔
      (p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)) := by
    simp only [List.length_map]
    constructor <;> rintro ⟨h, hn⟩
    · exact ⟨h, (hltr _ h).mpr.mt hn⟩
    · exact ⟨h, (hltr _ h).mp.mt hn⟩
  unfold hat
  rw [hidx]
  dsimp only
  by_cases h : p.idxOf a + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf a + 1)
  · rw [if_pos h, if_pos (hb.mpr h)]
    exact hget _ h.1
  · rw [if_neg h, if_neg (hb.not.mpr h), hg _ hi,
      hget _ (lt_of_le_of_lt (Nat.findGreatest_le _) hi)]

/-- Translation between an interval and an initial interval preserves the full
edge condition, including the requirement that intermediate values exist. -/
theorem closedEdges_translate (p : List ℕ) (d : ℕ) :
    ClosedEdges (p.map (fun x => d + x)) ↔ ClosedEdges p := by
  have hf : StrictMono (fun x : ℕ => d + x) := by intro a b h; dsimp; omega
  have hh (a : ℕ) (ha : a ∈ p) := hat_map_strictMono p _ hf a ha
  constructor
  · intro h a c ha hac hcb
    have hs := h (d + a) (d + c) (List.mem_map.mpr ⟨a, ha, rfl⟩)
      (by omega) (by rw [hh a ha]; omega)
    rw [hh a ha] at hs
    have hs' : ([c, hat p a].map (fun x => d + x)).Sublist
        (p.map (fun x => d + x)) := by simpa using hs
    obtain ⟨v, hv, heq⟩ := List.sublist_map_iff.mp hs'
    have hvEq : [c, hat p a] = v := (List.map_injective_iff.mpr hf.injective) heq
    rwa [← hvEq] at hv
  · intro h a c ha hac hcb
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [hh b hb] at hcb ⊢
    have hdc : d ≤ c := by omega
    have hs := h b (c - d) hb (by omega) (by omega)
    have hs' := hs.map (fun x => d + x)
    simpa only [List.map_cons, List.map_nil, Nat.add_sub_of_le hdc] using hs'

/-- Every edge stays inside its value block when two ordered words are joined. -/
theorem hat_append_ordered (L R : List ℕ)
    (horder : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    (∀ a ∈ L, hat (L ++ R) a = hat L a) ∧
      (∀ a ∈ R, hat (L ++ R) a = hat R a) := by
  have hget (i : ℕ) (hi : i < R.length) :
      (L ++ R).getD (L.length + i) 0 = R.getD i 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hltr (i : ℕ) (hi : i < R.length) :
      IsLtrMax (L ++ R) (L.length + i) ↔ IsLtrMax R i := by
    constructor
    · intro h j hj
      have h' := h (L.length + j) (by omega)
      rwa [hget j (by omega), hget i hi] at h'
    · intro h j hj
      rw [hget i hi]
      by_cases hjL : j < L.length
      · rw [List.getD_append _ _ _ _ hjL]
        exact horder _ (by rw [List.getD_eq_getElem _ 0 hjL]; exact List.getElem_mem hjL)
          _ (by rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi)
      · have hjR : j - L.length < i := by omega
        have hjEq : L.length + (j - L.length) = j := by omega
        rw [← hjEq, hget _ (by omega)]
        exact h _ hjR
  have hg (i : ℕ) (hi : i < R.length) :
      Nat.findGreatest (IsLtrMax (L ++ R)) (L.length + i) =
        L.length + Nat.findGreatest (IsLtrMax R) i := by
    induction i with
    | zero =>
        have h : IsLtrMax R 0 := by intro j hj; omega
        simpa using Nat.findGreatest_eq ((hltr 0 hi).mpr h)
    | succ i ih =>
        have heq : L.length + (i + 1) = (L.length + i) + 1 := by omega
        rw [heq, Nat.findGreatest_succ, Nat.findGreatest_succ]
        by_cases h : IsLtrMax R (i + 1)
        · rw [if_pos h, if_pos (by simpa [heq] using (hltr _ hi).mpr h)]; omega
        · rw [if_neg h, if_neg (by simpa [heq] using (hltr _ hi).not.mpr h), ih (by omega)]
  constructor
  · intro a ha
    cases R with
    | nil => simp
    | cons b R =>
        exact hat_append_final_cycle L R b a
          (fun x hx => horder x hx b (by simp)) ha
  · intro a ha
    have haL : a ∉ L := by intro h; exact (Nat.lt_irrefl a) (horder a h a ha)
    have hi : R.idxOf a < R.length := List.idxOf_lt_length_of_mem ha
    have hb :
        (L.length + R.idxOf a + 1 < (L ++ R).length ∧
          ¬ IsLtrMax (L ++ R) (L.length + R.idxOf a + 1)) ↔
        (R.idxOf a + 1 < R.length ∧ ¬ IsLtrMax R (R.idxOf a + 1)) := by
      constructor <;> rintro ⟨h, hn⟩
      · have hi' : R.idxOf a + 1 < R.length := by simp at h; omega
        exact ⟨hi', (hltr _ hi').mpr.mt (by simpa [Nat.add_assoc] using hn)⟩
      · exact ⟨by simp; omega,
          by simpa [Nat.add_assoc] using (hltr _ h).mp.mt hn⟩
    unfold hat
    rw [List.idxOf_append_of_notMem haL]
    dsimp only
    by_cases h : R.idxOf a + 1 < R.length ∧ ¬ IsLtrMax R (R.idxOf a + 1)
    · rw [if_pos h, if_pos (hb.mpr h)]
      simpa [Nat.add_assoc] using hget (R.idxOf a + 1) h.1
    · rw [if_neg h, if_neg (hb.not.mpr h), hg _ hi,
        hget _ (lt_of_le_of_lt (Nat.findGreatest_le _) hi)]

/-- The complete edge condition is a product condition on ordered value blocks. -/
theorem closedEdges_append_ordered (L R : List ℕ)
    (horder : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    ClosedEdges (L ++ R) ↔ ClosedEdges L ∧ ClosedEdges R := by
  have hh := hat_append_ordered L R horder
  have hmem (p : List ℕ) (a : ℕ) (ha : a ∈ p) : hat p a ∈ p := by
    unfold hat
    dsimp only
    split_ifs with h
    · rw [List.getD_eq_getElem _ 0 h.1]; exact List.getElem_mem h.1
    · have hi := List.idxOf_lt_length_of_mem ha
      have hg := lt_of_le_of_lt (Nat.findGreatest_le (P := IsLtrMax p) (p.idxOf a)) hi
      rw [List.getD_eq_getElem _ 0 hg]; exact List.getElem_mem hg
  constructor
  · intro h
    constructor
    · intro a c ha hac hcb
      have hs := h a c (List.mem_append.mpr (Or.inl ha)) hac
        (by rw [hh.1 a ha]; exact hcb)
      rw [hh.1 a ha] at hs
      apply hs.of_sublist_append_left
      intro x hx hxR
      rcases (show x = c ∨ x = hat L a by simpa using hx) with he | he
      · subst x; have := horder (hat L a) (hmem L a ha) c hxR; omega
      · subst x; exact (Nat.lt_irrefl _) (horder _ (hmem L a ha) _ hxR)
    · intro a c ha hac hcb
      have hs := h a c (List.mem_append.mpr (Or.inr ha)) hac
        (by rw [hh.2 a ha]; exact hcb)
      rw [hh.2 a ha] at hs
      apply hs.of_sublist_append_right
      intro x hx hxL
      rcases (show x = c ∨ x = hat R a by simpa using hx) with he | he
      · subst x; have := horder c hxL a ha; omega
      · subst x; exact (Nat.lt_irrefl _) (horder _ hxL _ (hmem R a ha))
  · rintro ⟨hL, hR⟩ a c ha hac hcb
    rcases List.mem_append.mp ha with ha | ha
    · rw [hh.1 a ha] at hcb ⊢
      exact List.sublist_append_of_sublist_left (hL a c ha hac hcb)
    · rw [hh.2 a ha] at hcb ⊢
      exact List.sublist_append_of_sublist_right (hR a c ha hac hcb)

/-- Cutting at a missing value is canonical: every lower value precedes every
higher value. Thus a prefix cannot interleave two gaps of its selected set. -/
theorem closedEdges_value_cut (p : List ℕ) (c : ℕ) (hnd : p.Nodup)
    (hc : c ∉ p) (hp : ClosedEdges p) :
    p = p.filter (fun x => x < c) ++ p.filter (fun x => c < x) := by
  have hgetmem (i : ℕ) (hi : i < p.length) : p.getD i 0 ∈ p := by
    rw [List.getD_eq_getElem _ 0 hi]; exact List.getElem_mem hi
  have hmax : ∀ i, i < p.length → ∀ j, j ≤ i →
      p.getD j 0 ≤ p.getD (Nat.findGreatest (IsLtrMax p) i) 0 := by
    intro i
    induction i with
    | zero =>
        intro hi j hj
        have hj0 : j = 0 := by omega
        subst j
        simp
    | succ i ih =>
        intro hi j hj
        rw [Nat.findGreatest_succ]
        by_cases h : IsLtrMax p (i + 1)
        · rw [if_pos h]
          by_cases hj' : j = i + 1
          · simp [hj']
          · exact (h j (by omega)).le
        · rw [if_neg h]
          by_cases hj' : j ≤ i
          · exact ih (by omega) j hj'
          · have hjEq : j = i + 1 := by omega
            subst j
            have hn : ∃ t, t < i + 1 ∧ p.getD (i + 1) 0 ≤ p.getD t 0 := by
              simpa [IsLtrMax, not_forall, not_lt] using h
            obtain ⟨t, ht, hval⟩ := hn
            exact hval.trans (ih (by omega) t (by omega))
  have hlow : ∀ d i, p.length - i = d → i < p.length → p.getD i 0 < c →
      p.getD (Nat.findGreatest (IsLtrMax p) i) 0 < c := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hd hi hilow
        have hidx : p.idxOf (p.getD i 0) = i := by
          rw [List.getD_eq_getElem _ 0 hi]; exact hnd.idxOf_getElem i hi
        have hhatlow : hat p (p.getD i 0) < c := by
          by_contra hn
          have hhatmem : hat p (p.getD i 0) ∈ p := by
            unfold hat; rw [hidx]; dsimp only
            split_ifs with h
            · exact hgetmem _ h.1
            · exact hgetmem _ (lt_of_le_of_lt (Nat.findGreatest_le _) hi)
          have hne : hat p (p.getD i 0) ≠ c := fun h => hc (h ▸ hhatmem)
          have hsub := hp _ c (hgetmem i hi) hilow (by omega)
          exact hc (hsub.subset (by simp))
        have hhatlow' := hhatlow
        unfold hat at hhatlow'
        rw [hidx] at hhatlow'
        dsimp only at hhatlow'
        by_cases hb : i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)
        · have hnext : p.getD (i + 1) 0 < c := by
            rwa [if_pos hb] at hhatlow'
          have hg : Nat.findGreatest (IsLtrMax p) (i + 1) =
              Nat.findGreatest (IsLtrMax p) i := Nat.findGreatest_of_not hb.2
          rw [← hg]
          exact ih (p.length - (i + 1)) (by omega) (i + 1) rfl hb.1 hnext
        · rwa [if_neg hb] at hhatlow'
  have hbefore : ∀ i j, i < j → j < p.length → p.getD j 0 < c → p.getD i 0 < c := by
    intro i j hij hj hjlow
    exact lt_of_le_of_lt (hmax j hj i hij.le) (hlow _ j rfl hj hjlow)
  have split : ∀ (v : List ℕ), c ∉ v →
      (∀ i j, i < j → j < v.length → v.getD j 0 < c → v.getD i 0 < c) →
      v = v.filter (fun x => x < c) ++ v.filter (fun x => c < x) := by
    intro v
    induction v with
    | nil => simp
    | cons a v ih =>
        intro hc hb
        have hca : a ≠ c := by intro h; exact hc (by simp [h])
        have hcv : c ∉ v := fun h => hc (by simp [h])
        have hbv : ∀ i j, i < j → j < v.length → v.getD j 0 < c → v.getD i 0 < c := by
          intro i j hij hj hval
          simpa using hb (i + 1) (j + 1) (by omega) (by simp; omega) (by simpa using hval)
        by_cases halow : a < c
        · simpa [halow, show ¬ c < a by omega] using congrArg (List.cons a) (ih hcv hbv)
        · have hhigh : ∀ b ∈ v, c < b := by
            intro b hbm
            obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hbm
            have hbne : b ≠ c := fun h => hcv (h ▸ hbm)
            by_contra hn
            have hbval : v.getD j 0 < c := by rw [List.getD_eq_getElem _ 0 hj, hjb]; omega
            have ha' := hb 0 (j + 1) (by omega) (by simp; omega) (by simpa using hbval)
            have : a < c := by simpa using ha'
            exact halow this
          have hfilterlow : v.filter (fun x => x < c) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro b hb; have := hhigh b hb; simp; omega
          have hfilterhigh : v.filter (fun x => c < x) = v := by
            apply List.filter_eq_self.mpr
            intro b hb; simpa using hhigh b hb
          simp [halow, show c < a by omega, hfilterlow, hfilterhigh]
  exact split p hc hbefore

/-- Every cycle stays on the same side of each missing selected value. Applying
this to all selected letters confines every prefix cycle to a single gap. -/
theorem closedEdges_cycle_confinement (p : List ℕ) (c a : ℕ) (hnd : p.Nodup)
    (hc : c ∉ p) (hp : ClosedEdges p) (ha : a ∈ p) :
    ∀ t : ℕ, (hat p)^[t] a ∈ p ∧ ((hat p)^[t] a < c ↔ a < c) := by
  let L := p.filter (fun x => x < c)
  let R := p.filter (fun x => c < x)
  have hsplit : p = L ++ R := closedEdges_value_cut p c hnd hc hp
  have horder : ∀ x ∈ L, ∀ y ∈ R, x < y := by
    intro x hx y hy
    have hx' : x < c := by simpa using (List.mem_filter.mp hx).2
    have hy' : c < y := by simpa using (List.mem_filter.mp hy).2
    omega
  have hh := hat_append_ordered L R horder
  have hmem (v : List ℕ) (x : ℕ) (hx : x ∈ v) : hat v x ∈ v := by
    unfold hat
    dsimp only
    split_ifs with h
    · rw [List.getD_eq_getElem _ 0 h.1]; exact List.getElem_mem h.1
    · have hi := List.idxOf_lt_length_of_mem hx
      have hg := lt_of_le_of_lt (Nat.findGreatest_le (P := IsLtrMax v) (v.idxOf x)) hi
      rw [List.getD_eq_getElem _ 0 hg]; exact List.getElem_mem hg
  have hstep (x : ℕ) (hx : x ∈ p) : hat p x ∈ p ∧ (hat p x < c ↔ x < c) := by
    refine ⟨hmem p x hx, ?_⟩
    by_cases hxc : x < c
    · have hxL : x ∈ L := List.mem_filter.mpr ⟨hx, by simpa using hxc⟩
      have hhat : hat p x = hat L x := by rw [hsplit]; exact hh.1 x hxL
      have hlow : hat L x < c := by
        simpa using (List.mem_filter.mp (hmem L x hxL)).2
      simp [hhat, hlow, hxc]
    · have hne : x ≠ c := fun h => hc (h ▸ hx)
      have hcx : c < x := by omega
      have hxR : x ∈ R := List.mem_filter.mpr ⟨hx, by simpa using hcx⟩
      have hhat : hat p x = hat R x := by rw [hsplit]; exact hh.2 x hxR
      have hhigh : c < hat R x := by
        simpa using (List.mem_filter.mp (hmem R x hxR)).2
      simp [hhat, show ¬ hat R x < c by omega, hxc]
  intro t
  induction t with
  | zero => simpa using ha
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hs := hstep ((hat p)^[t] a) ih.1
      exact ⟨hs.1, hs.2.trans ih.2⟩

end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps

#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_translate
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_append_ordered
#print axioms D5.S3.Combinatorics.ArrowThirtyTwoOneThreeBijectionGaps.closedEdges_cycle_confinement

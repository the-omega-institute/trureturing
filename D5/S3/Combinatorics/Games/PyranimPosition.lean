/- GID: D5/S3/Combinatorics/Games/PyranimPosition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Games/PyranimPosition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable Pyranim positions, recursive legal options and their Dyck encoding. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/33619
-/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Mathlib.Data.List.GetD

/-! Stable Pyranim positions, recursive legal options and their Dyck encoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

namespace D5.S3.Combinatorics.Games.Pyranim

section

open D5.S3.Combinatorics.InversionSeq

@[ext]
structure Interval (n : ℕ) where
  left : ℕ
  right : ℕ
  left_pos : 0 < left
  left_le_right : left ≤ right
  right_le_width : right ≤ n

instance {n : ℕ} : PartialOrder (Interval n) where
  le a b := b.left ≤ a.left ∧ a.right ≤ b.right
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ hab hbc := ⟨hbc.1.trans hab.1, hab.2.trans hbc.2⟩
  le_antisymm _ _ hab hba := Interval.ext (Nat.le_antisymm hba.1 hab.1)
    (Nat.le_antisymm hab.2 hba.2)

abbrev Stable (n : ℕ) := {s : Set (Interval n) // IsLowerSet s}

def emptyStable (n : ℕ) : Stable n :=
  ⟨∅, by
    intro _ _ _ h
    exact h.elim⟩

private def column {n : ℕ} (c : Interval n) : Fin (n + 1) :=
  ⟨c.right, Nat.lt_succ_of_le c.right_le_width⟩

/-- Include zero as the default for a column with no omitted chips. -/
private noncomputable def omittedStarts {n : ℕ} (I : Stable n) (j : Fin (n + 1)) : Finset ℕ := by
  classical
  exact insert 0 ((Finset.range (j.val + 1)).filter
    (fun i => ∃ c : Interval n, c.left = i ∧ c.right = j.val ∧ c ∉ I.val))

private theorem mem_omittedStarts {n : ℕ} (I : Stable n) (j : Fin (n + 1)) (i : ℕ) :
    i ∈ omittedStarts I j ↔
      i = 0 ∨ ∃ c : Interval n, c.left = i ∧ c.right = j.val ∧ c ∉ I.val := by
  classical
  simp only [omittedStarts, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (hzero | ⟨_, hc⟩)
    · exact Or.inl hzero
    · exact Or.inr hc
  · rintro (hzero | ⟨c, hi, hj, hc⟩)
    · exact Or.inl hzero
    · exact Or.inr ⟨by simpa [← hi, ← hj] using Nat.lt_succ_of_le c.left_le_right,
        c, hi, hj, hc⟩

/-- The largest omitted starting index at the given right endpoint. -/
private noncomputable def edge {n : ℕ} (I : Stable n) (j : Fin (n + 1)) : ℕ :=
  (omittedStarts I j).max' ⟨0, (mem_omittedStarts I j 0).mpr (Or.inl rfl)⟩

private theorem edge_mem {n : ℕ} (I : Stable n) (j : Fin (n + 1)) :
    edge I j ∈ omittedStarts I j :=
  Finset.max'_mem _ _

private theorem le_edge {n : ℕ} {I : Stable n} {j : Fin (n + 1)} {i : ℕ}
    (h : i ∈ omittedStarts I j) : i ≤ edge I j :=
  Finset.le_max' _ _ h

private theorem edge_le {n : ℕ} (I : Stable n) (j : Fin (n + 1)) : edge I j ≤ j.val := by
  rcases (mem_omittedStarts I j _).mp (edge_mem I j) with hzero | ⟨c, hi, hj, _⟩
  · simp [hzero]
  · simpa [← hi, ← hj] using c.left_le_right

private theorem edge_mono {n : ℕ} (I : Stable n) : Monotone (edge I) := by
  intro j k hjk
  rcases (mem_omittedStarts I j _).mp (edge_mem I j) with hzero | ⟨c, hi, hj, hc⟩
  · simp [hzero]
  · have hright : c.right ≤ k.val := hj ▸ hjk
    let bigger : Interval n :=
      ⟨c.left, k.val, c.left_pos, c.left_le_right.trans hright, Nat.le_of_lt_succ k.isLt⟩
    have hcontains : c ≤ bigger := ⟨le_rfl, hright⟩
    have hbigger : bigger ∉ I.val := fun hb => hc (I.property hcontains hb)
    exact le_edge ((mem_omittedStarts I k _).mpr (Or.inr ⟨bigger, hi, rfl, hbigger⟩))

private theorem mem_iff_edge_lt {n : ℕ} (I : Stable n) (c : Interval n) :
    c ∈ I.val ↔ edge I (column c) < c.left := by
  constructor
  · intro hc
    rcases (mem_omittedStarts I (column c) _).mp (edge_mem I (column c)) with
      hzero | ⟨omitted, hi, hj, homitted⟩
    · simpa [hzero] using c.left_pos
    · apply lt_of_not_ge
      intro h
      exact homitted (I.property ⟨hi.symm ▸ h, hj.le⟩ hc)
  · intro h
    by_contra hc
    have hle := le_edge ((mem_omittedStarts I (column c) c.left).mpr
      (Or.inr ⟨c, rfl, rfl, hc⟩))
    exact (not_lt_of_ge hle) h

private abbrev MonoInversion (size : ℕ) :=
  {word : List ℕ // word.length = size ∧ InversionSeqDefs.IsInversionSeq word ∧
    word.Pairwise (· ≤ ·)}

private noncomputable def encode {n : ℕ} (I : Stable n) : MonoInversion (n + 1) := by
  refine ⟨List.ofFn (edge I), List.length_ofFn, ?_, ?_⟩
  · intro j hj
    rw [List.getD_eq_getElem _ _ hj, List.getElem_ofFn]
    exact edge_le I _
  · exact List.pairwise_ofFn.mpr (fun _ _ h => edge_mono I h.le)

private theorem encode_getD {n : ℕ} (I : Stable n) (j : Fin (n + 1)) :
    (encode I).val.getD j.val 0 = edge I j := by
  have hj : j.val < (encode I).val.length := (encode I).property.1.symm ▸ j.isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_ofFn _

private def entry {size : ℕ} (w : MonoInversion size) (j : Fin size) : ℕ :=
  w.val.getD j.val 0

private theorem entry_le {size : ℕ} (w : MonoInversion size) (j : Fin size) :
    entry w j ≤ j.val :=
  w.property.2.1 j.val (w.property.1.symm ▸ j.isLt)

private theorem entry_mono {size : ℕ} (w : MonoInversion size) : Monotone (entry w) := by
  intro j k h
  have hj : j.val < w.val.length := w.property.1.symm ▸ j.isLt
  have hk : k.val < w.val.length := w.property.1.symm ▸ k.isLt
  rcases lt_or_eq_of_le h with hlt | rfl
  · simpa only [entry, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] using
      (List.pairwise_iff_getElem.mp w.property.2.2 j.val k.val hj hk hlt)
  · exact le_rfl

private def decode {n : ℕ} (w : MonoInversion (n + 1)) : Stable n := by
  refine ⟨{c | entry w (column c) < c.left}, ?_⟩
  intro bigger smaller hcontains hmem
  change entry w (column smaller) < smaller.left
  exact (entry_mono w hcontains.2).trans_lt (hmem.trans_le hcontains.1)

private theorem decode_mem {n : ℕ} (w : MonoInversion (n + 1)) (c : Interval n) :
    c ∈ (decode w).val ↔ entry w (column c) < c.left :=
  Iff.rfl

private theorem decode_encode {n : ℕ} (I : Stable n) : decode (encode I) = I := by
  apply Subtype.ext
  ext c
  rw [decode_mem, entry, encode_getD, mem_iff_edge_lt]

private theorem edge_decode {n : ℕ} (w : MonoInversion (n + 1)) (j : Fin (n + 1)) :
    edge (decode w) j = entry w j := by
  apply Nat.le_antisymm
  · rcases (mem_omittedStarts (decode w) j _).mp (edge_mem (decode w) j) with
      hzero | ⟨c, hi, hj, hc⟩
    · simp [hzero]
    · have hcol : column c = j := Fin.ext hj
      rw [decode_mem, hcol] at hc
      exact hi ▸ Nat.le_of_not_gt hc
  · by_cases hz : entry w j = 0
    · simp [hz]
    · let c : Interval n :=
        ⟨entry w j, j.val, Nat.pos_of_ne_zero hz, entry_le w j,
          Nat.le_of_lt_succ j.isLt⟩
      have hcol : column c = j := Fin.ext rfl
      have hc : c ∉ (decode w).val := by
        rw [decode_mem, hcol]
        exact Nat.lt_irrefl _
      exact le_edge ((mem_omittedStarts (decode w) j _).mpr (Or.inr ⟨c, rfl, rfl, hc⟩))

private theorem encode_decode {n : ℕ} (w : MonoInversion (n + 1)) : encode (decode w) = w := by
  apply Subtype.ext
  apply List.ext_getElem ((encode (decode w)).property.1.trans w.property.1.symm)
  intro j hj hk
  let index : Fin (n + 1) := ⟨j, w.property.1 ▸ hk⟩
  have hget : (encode (decode w)).val.getD j 0 = w.val.getD j 0 :=
    (encode_getD (decode w) index).trans (edge_decode w index)
  simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] using hget

private noncomputable def stableEquivMono (n : ℕ) : Stable n ≃ MonoInversion (n + 1) where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

noncomputable def stableEquivDyck (n : ℕ) :
    Stable n ≃ {path : DyckWord // path.semilength = n + 1} :=
  (stableEquivMono n).trans (Classical.choose (InversionSeq152Dyck.monoDyckEquiv (n + 1)))

theorem stableCard (n : ℕ) : Nat.card (Stable n) = catalan (n + 1) := by
  rw [Nat.card_congr (stableEquivDyck n), Nat.card_eq_fintype_card]
  exact DyckWord.card_dyckWord_semilength_eq_catalan (n + 1)

abbrev FullBottom (n : ℕ) :=
  {I : Stable n // ∀ c : Interval n, c.left = c.right → c ∈ I.val}

/-- The width-`n` board identifies with the nonsingleton chips at width `n+1`. -/
def raiseRight {n : ℕ} (c : Interval n) : Interval (n + 1) :=
  ⟨c.left, c.right + 1, c.left_pos, c.left_le_right.trans (Nat.le_succ _),
    Nat.succ_le_succ c.right_le_width⟩

def lowerRight {n : ℕ} (c : Interval (n + 1)) (h : c.left < c.right) : Interval n :=
  ⟨c.left, c.right - 1, c.left_pos, by omega,
    by have := c.right_le_width; omega⟩

theorem raiseRight_lowerRight {n : ℕ} (c : Interval (n + 1)) (h : c.left < c.right) :
    raiseRight (lowerRight c h) = c :=
  Interval.ext rfl (by change c.right - 1 + 1 = c.right; omega)

def removeBottom {n : ℕ} (I : FullBottom (n + 1)) : Stable n := by
  refine ⟨{c | raiseRight c ∈ I.val.val}, ?_⟩
  intro bigger smaller hcontains hmem
  have hraised : raiseRight smaller ≤ raiseRight bigger :=
    ⟨hcontains.1, Nat.succ_le_succ hcontains.2⟩
  exact I.val.property hraised hmem

private def addBottom {n : ℕ} (I : Stable n) : FullBottom (n + 1) := by
  refine ⟨⟨{c | c.left = c.right ∨ ∃ h : c.left < c.right, lowerRight c h ∈ I.val},
    ?_⟩, ?_⟩
  · intro bigger smaller hcontains hmem
    by_cases hsingle : smaller.left = smaller.right
    · exact Or.inl hsingle
    · have hsmaller : smaller.left < smaller.right :=
        lt_of_le_of_ne smaller.left_le_right hsingle
      have hbigger : bigger.left < bigger.right :=
        hcontains.1.trans_lt (hsmaller.trans_le hcontains.2)
      rcases hmem with hsingleBigger | ⟨h, hBiggerMem⟩
      · exact (hbigger.ne hsingleBigger).elim
      · have hlowered : lowerRight smaller hsmaller ≤ lowerRight bigger h :=
          ⟨hcontains.1, Nat.sub_le_sub_right hcontains.2 1⟩
        exact Or.inr ⟨hsmaller, I.property hlowered hBiggerMem⟩
  · intro _ hsingle
    exact Or.inl hsingle

private theorem removeBottom_addBottom {n : ℕ} (I : Stable n) :
    removeBottom (addBottom I) = I := by
  apply Subtype.ext
  ext c
  have h : (raiseRight c).left < (raiseRight c).right :=
    Nat.lt_succ_of_le c.left_le_right
  have lowerRaised (h' : (raiseRight c).left < (raiseRight c).right) :
      lowerRight (raiseRight c) h' = c :=
    Interval.ext rfl (Nat.add_sub_cancel _ _)
  change ((raiseRight c).left = (raiseRight c).right ∨
    ∃ h', lowerRight (raiseRight c) h' ∈ I.val) ↔ c ∈ I.val
  constructor
  · rintro (hsingle | ⟨h', hmem⟩)
    · exact (h.ne hsingle).elim
    · rwa [lowerRaised h'] at hmem
  · intro hmem
    exact Or.inr ⟨h, (lowerRaised h).symm ▸ hmem⟩

private theorem addBottom_removeBottom {n : ℕ} (I : FullBottom (n + 1)) :
    addBottom (removeBottom I) = I := by
  apply Subtype.ext
  apply Subtype.ext
  ext c
  change (c.left = c.right ∨ ∃ h, raiseRight (lowerRight c h) ∈ I.val.val) ↔ c ∈ I.val.val
  constructor
  · rintro (hsingle | ⟨h, hmem⟩)
    · exact I.property c hsingle
    · rwa [raiseRight_lowerRight c h] at hmem
  · intro hmem
    rcases lt_or_eq_of_le c.left_le_right with h | h
    · exact Or.inr ⟨h, (raiseRight_lowerRight c h).symm ▸ hmem⟩
    · exact Or.inl h

def fullBottomSuccEquiv (n : ℕ) : FullBottom (n + 1) ≃ Stable n where
  toFun := removeBottom
  invFun := addBottom
  left_inv := addBottom_removeBottom
  right_inv := removeBottom_addBottom

end

section

variable {n m : ℕ}

/-- Lemma 3.1 computes the full cascade, including the selected chip. -/
def removeChip (I : Stable n) (c : Interval n) : Stable n :=
  ⟨{b | b ∈ I.val ∧ ¬ c ≤ b}, fun _ _ hab hb =>
    ⟨I.property hab hb.1, fun ha => hb.2 (ha.trans hab)⟩⟩

def LeftAbove (c u : Interval n) : Prop :=
  u.left + 1 = c.left ∧ u.right = c.right

def RightAbove (c u : Interval n) : Prop :=
  u.left = c.left ∧ c.right + 1 = u.right

def Visible (I : Stable n) (c : Interval n) : Prop :=
  c ∈ I.val ∧ ¬ ((∃ u ∈ I.val, LeftAbove c u) ∧ (∃ u ∈ I.val, RightAbove c u))

/-- Covers computed inside the surviving chips. -/
def UpperCover (I : Stable n) (c u : Interval n) : Prop :=
  u ∈ I.val ∧ c < u ∧ ∀ v ∈ I.val, c < v → v < u → False

private theorem interval_lt_iff (c u : Interval n) :
    c < u ↔ u.left ≤ c.left ∧ c.right ≤ u.right ∧
      (u.left < c.left ∨ c.right < u.right) := by
  rw [lt_iff_le_not_ge]
  change (u.left ≤ c.left ∧ c.right ≤ u.right) ∧
    ¬ (c.left ≤ u.left ∧ u.right ≤ c.right) ↔ _
  omega

private theorem upperCover_iff (I : Stable n) (c u : Interval n) :
    UpperCover I c u ↔ u ∈ I.val ∧ (LeftAbove c u ∨ RightAbove c u) := by
  constructor
  · rintro ⟨hu, hcu, hcover⟩
    obtain ⟨hl, hr, hlt⟩ := (interval_lt_iff c u).mp hcu
    refine ⟨hu, ?_⟩
    rcases hlt with hleft | hright
    · let v : Interval n := ⟨c.left - 1, c.right,
        by have := u.left_pos; omega,
        Nat.sub_le _ _ |>.trans c.left_le_right, c.right_le_width⟩
      have hvu : v ≤ u := ⟨by dsimp [v]; omega, hr⟩
      have hcv : c < v := (interval_lt_iff c v).mpr (by dsimp [v]; omega)
      have heq : v = u := by
        by_contra hn
        exact hcover v (I.property hvu hu) hcv (lt_of_le_of_ne hvu hn)
      exact Or.inl ⟨by have h := congrArg Interval.left heq; dsimp [v] at h; omega,
        (congrArg Interval.right heq).symm⟩
    · let v : Interval n := ⟨c.left, c.right + 1, c.left_pos,
        c.left_le_right.trans (Nat.le_succ _), (Nat.succ_le_of_lt hright).trans u.right_le_width⟩
      have hvu : v ≤ u := ⟨hl, Nat.succ_le_of_lt hright⟩
      have hcv : c < v := (interval_lt_iff c v).mpr (by dsimp [v]; omega)
      have heq : v = u := by
        by_contra hn
        exact hcover v (I.property hvu hu) hcv (lt_of_le_of_ne hvu hn)
      exact Or.inr ⟨(congrArg Interval.left heq).symm, congrArg Interval.right heq⟩
  · rintro ⟨hu, habove⟩
    refine ⟨hu, (interval_lt_iff c u).mpr ?_, ?_⟩
    · rcases habove with h | h <;> obtain ⟨h₁, h₂⟩ := h <;> omega
    · intro v _ hcv hvu
      have h₁ := (interval_lt_iff c v).mp hcv
      have h₂ := (interval_lt_iff v u).mp hvu
      rcases habove with h | h <;> obtain ⟨h₃, h₄⟩ := h <;> omega

theorem visible_iff_covers (I : Stable n) (c : Interval n) :
    Visible I c ↔ c ∈ I.val ∧
      ¬ ∃ u v, UpperCover I c u ∧ UpperCover I c v ∧ u ≠ v := by
  unfold Visible
  constructor
  · rintro ⟨hc, hvisible⟩
    refine ⟨hc, ?_⟩
    rintro ⟨u, v, hu, hv, hne⟩
    obtain ⟨hu, hlu | hru⟩ := (upperCover_iff I c u).mp hu
    · obtain ⟨hv, hlv | hrv⟩ := (upperCover_iff I c v).mp hv
      · obtain ⟨hu₁, hu₂⟩ := hlu
        obtain ⟨hv₁, hv₂⟩ := hlv
        exact hne (Interval.ext (by omega) (hu₂.trans hv₂.symm))
      · exact hvisible ⟨⟨u, hu, hlu⟩, ⟨v, hv, hrv⟩⟩
    · obtain ⟨hv, hlv | hrv⟩ := (upperCover_iff I c v).mp hv
      · exact hvisible ⟨⟨v, hv, hlv⟩, ⟨u, hu, hru⟩⟩
      · obtain ⟨hu₁, hu₂⟩ := hru
        obtain ⟨hv₁, hv₂⟩ := hrv
        exact hne (Interval.ext (hu₁.trans hv₁.symm) (hu₂.symm.trans hv₂))
  · rintro ⟨hc, hcover⟩
    refine ⟨hc, ?_⟩
    rintro ⟨⟨u, hu, hlu⟩, ⟨v, hv, hrv⟩⟩
    refine hcover ⟨u, v, (upperCover_iff I c u).mpr ⟨hu, Or.inl hlu⟩,
      (upperCover_iff I c v).mpr ⟨hv, Or.inr hrv⟩, ?_⟩
    intro heq
    subst v
    exact Nat.succ_ne_self u.left (hlu.1.trans hrv.1.symm)

def LegalOption (I J : Stable n) : Prop :=
  ∃ c, Visible I c ∧ J = removeChip I c

abbrev Options (I : Stable n) := {J : Stable n // LegalOption I J}

theorem legalOption_ssubset {I J : Stable n} (h : LegalOption I J) : J.val ⊂ I.val := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun _ hb => hb.1, fun h => (h hc.1).2 le_rfl⟩

instance : Finite (Interval n) :=
  Finite.of_injective
    (fun c => ((⟨c.left, Nat.lt_succ_of_le (c.left_le_right.trans c.right_le_width)⟩,
      ⟨c.right, Nat.lt_succ_of_le c.right_le_width⟩) : Fin (n + 1) × Fin (n + 1)))
    (fun _ _ h => Interval.ext (congrArg (fun p => p.1.val) h)
      (congrArg (fun p => p.2.val) h))

noncomputable def chipCount (I : Stable n) : ℕ := by
  classical
  letI := Fintype.ofFinite (Interval n)
  exact I.val.toFinset.card

theorem chipCount_lt_of_option {I J : Stable n} (h : LegalOption I J) :
    chipCount J < chipCount I := by
  classical
  apply Finset.card_lt_card
  simpa only [Set.toFinset_ssubset_toFinset] using legalOption_ssubset h

theorem legalOption_wellFounded (n : ℕ) : WellFounded (fun J I : Stable n => LegalOption I J) :=
  (measure chipCount).wf.mono (fun _ _ h => chipCount_lt_of_option h)

noncomputable def GameIso (I : Stable n) (J : Stable m) : Prop :=
  ∃ e : Options I ≃ Options J, ∀ a : Options I, GameIso a.val (e a).val
termination_by chipCount I
decreasing_by exact chipCount_lt_of_option a.property

theorem gameIso_iff (I : Stable n) (J : Stable m) :
    GameIso I J ↔ ∃ e : Options I ≃ Options J, ∀ a : Options I, GameIso a.val (e a).val := by
  rw [GameIso]

theorem gameIso_refl (I : Stable n) : GameIso I I := by
  induction I using (legalOption_wellFounded n).induction with
  | h I ih =>
    rw [gameIso_iff]
    exact ⟨Equiv.refl _, fun a => ih a.val a.property⟩

theorem gameIso_symm (I : Stable n) (J : Stable m) (h : GameIso I J) : GameIso J I := by
  induction I using (legalOption_wellFounded n).induction generalizing J with
  | h I ih =>
    obtain ⟨e, he⟩ := (gameIso_iff I J).mp h
    apply (gameIso_iff J I).mpr
    refine ⟨e.symm, fun a => ?_⟩
    have ha := he (e.symm a)
    rw [Equiv.apply_symm_apply] at ha
    exact ih _ (e.symm a).property _ ha

theorem gameIso_trans {l : ℕ} (I : Stable n) (J : Stable m) (K : Stable l)
    (hIJ : GameIso I J) (hJK : GameIso J K) : GameIso I K := by
  induction I using (legalOption_wellFounded n).induction generalizing J K with
  | h I ih =>
    obtain ⟨e, he⟩ := (gameIso_iff I J).mp hIJ
    obtain ⟨f, hf⟩ := (gameIso_iff J K).mp hJK
    exact (gameIso_iff I K).mpr
      ⟨e.trans f, fun a => ih a.val a.property _ _ (he a) (hf (e a))⟩

end

section

open DyckStep

open D5.S3.Combinatorics.InversionSeq.InversionSeq152Dyck

abbrev DyckAt (n : ℕ) := {w : DyckWord // w.semilength = n}

/-- A Dyck block with a single movable down-step. The index is the number of extra up-steps
before the movable step, beyond the required initial up-step. -/
def rankBlock (L : ℕ) (i : Fin (L + 1)) : DyckWord where
  toList := List.replicate (i.val + 1) U ++ [D] ++ List.replicate (L - i.val) U ++
    List.replicate L D
  count_U_eq_count_D := by
    have := i.isLt
    simp [List.count_append, List.count_replicate]
    omega
  count_D_le_count_U k := by
    have hi : i.val ≤ L := Nat.le_of_lt_succ i.isLt
    simp [List.take_append, List.take_replicate, List.count_replicate]
    by_cases hk : k ≤ i.val + 1
    · simp [Nat.sub_eq_zero_of_le hk]
    · rw [show k - (i.val + 1) = (k - (i.val + 1) - 1) + 1 by omega, List.take_succ_cons]
      simp [List.take_append, List.take_replicate, List.count_replicate]
      omega

theorem rankBlock_semilength (L : ℕ) (i : Fin (L + 1)) : (rankBlock L i).semilength = L + 1 := by
  have := i.isLt
  simp [rankBlock, DyckWord.semilength, List.count_replicate]
  omega

theorem rankBlock_length (L : ℕ) (i : Fin (L + 1)) :
    (rankBlock L i).toList.length = 2 * (L + 1) := by
  rw [← DyckWord.two_mul_semilength_eq_length, rankBlock_semilength]

private theorem eastCounts_append (e : ℕ) (x y : List DyckStep) :
    eastCounts e (x ++ y) = eastCounts e x ++ eastCounts (e + x.count D) y := by
  induction x generalizing e with
  | nil => simp [eastCounts]
  | cons s x ih =>
    cases s <;> simp [eastCounts, ih, Nat.add_comm, Nat.add_left_comm]

private theorem eastCounts_replicate_U (e k : ℕ) :
    eastCounts e (List.replicate k U) = List.replicate k e := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, eastCounts, ih]

private theorem eastCounts_replicate_D (e k : ℕ) :
    eastCounts e (List.replicate k D) = [] := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, eastCounts, ih]

private theorem eastCounts_rankBlock (e L : ℕ) (i : Fin (L + 1)) :
    eastCounts e (rankBlock L i).toList =
      List.replicate (i.val + 1) e ++ List.replicate (L - i.val) (e + 1) := by
  simp [rankBlock, eastCounts_append, eastCounts_replicate_U, eastCounts_replicate_D,
    eastCounts, List.count_replicate]

/-- Replacing a Dyck block by another of the same size preserves legality and semilength. -/
def exchangeDyck {n : ℕ} (w : DyckAt (n + 1)) (pre post : List DyckStep) (u v : DyckWord)
    (hw : w.val.toList = pre ++ u.toList ++ post) (h : u.semilength = v.semilength) :
    DyckAt (n + 1) := by
  have hu : u.toList.count U = v.toList.count U := h
  have hd : u.toList.count D = v.toList.count D := by
    rw [← u.count_U_eq_count_D, ← v.count_U_eq_count_D, hu]
  have hl : u.toList.length = v.toList.length := by
    rw [← u.two_mul_semilength_eq_length, ← v.two_mul_semilength_eq_length, h]
  refine ⟨⟨pre ++ v.toList ++ post, ?_, ?_⟩, ?_⟩
  · have hbal := w.val.count_U_eq_count_D
    rw [hw] at hbal
    simpa only [List.count_append, hu, hd] using hbal
  · intro k
    by_cases hk : k ≤ pre.length + v.toList.length
    · rw [List.take_append_of_le_length (by simpa using hk), List.take_append]
      simp only [List.count_append]
      have hpre := w.val.count_D_le_count_U (min k pre.length)
      rw [hw, List.take_append_of_le_length (by simp), List.take_append_of_le_length (by omega)] at hpre
      have he : pre.take (min k pre.length) = pre.take k := by
        rw [min_comm, ← List.take_take, List.take_of_length_le (by simp)]
      rw [he] at hpre
      exact add_le_add hpre (v.count_D_le_count_U _)
    · have hp' := w.val.count_D_le_count_U k
      rw [hw] at hp'
      have hp : pre.length ≤ k := by omega
      have hq : u.toList.length ≤ k - pre.length := by omega
      have hr : v.toList.length ≤ k - pre.length := by omega
      simp only [List.take_append, List.length_append, List.count_append,
        List.take_of_length_le hp, List.take_of_length_le hq, hu, hd, hl] at hp'
      simpa only [List.take_append, List.length_append, List.count_append,
        List.take_of_length_le hp, List.take_of_length_le hr] using hp'
  · have hs := w.property
    change w.val.toList.count U = _ at hs
    change (pre ++ v.toList ++ post).count U = _
    rw [hw] at hs
    simpa only [List.count_append, hu] using hs

private theorem eastCounts_stable (n : ℕ) (p : DyckAt (n + 1)) :
    ((stableEquivMono n) ((stableEquivDyck n).symm p)).val = eastCounts 0 p.val.toList := by
  unfold stableEquivDyck
  rw [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  exact (Classical.choose_spec (monoDyckEquiv (n + 1))).2.1 p

private theorem getD_twoRuns (lo hi : ℕ) (P S : List ℕ) (m t k : ℕ) (ht : t ≤ m) :
    (P ++ List.replicate t lo ++ List.replicate (m - t) hi ++ S).getD k 0 =
      if k < P.length then P.getD k 0 else
      if k - P.length < t then lo else
      if k - P.length < m then hi else S.getD (k - P.length - m) 0 := by
  rw [List.append_assoc, List.append_assoc]
  by_cases hp : k < P.length
  · simp only [hp, ite_true, List.getD_append _ _ _ _ hp]
  · have hp' : P.length ≤ k := by omega
    rw [ite_eq_right hp, List.getD_append_right _ _ _ _ hp']
    by_cases ht' : k - P.length < t
    · rw [ite_eq_left ht', List.getD_append _ _ _ _ (by simpa using ht'), List.getD_replicate lo ht']
    · rw [ite_eq_right ht', List.getD_append_right _ _ _ _ (by simpa using not_lt.mp ht')]
      simp only [List.length_replicate]
      by_cases hm : k - P.length < m
      · rw [ite_eq_left hm, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_replicate hi (by omega)]
      · rw [ite_eq_right hm, List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_replicate]
        congr 1
        omega

/-- The ranks of different choices of the movable down-step are strictly ordered. -/
theorem rankBlock_strict {n L : ℕ} {i j : Fin (L + 1)} (hij : i < j)
    (p q : DyckAt (n + 1)) (pre post : List DyckStep)
    (hp : p.val.toList = pre ++ (rankBlock L i).toList ++ post)
    (hq : q.val.toList = pre ++ (rankBlock L j).toList ++ post) :
    chipCount ((stableEquivDyck n).symm p) < chipCount ((stableEquivDyck n).symm q) := by
  classical
  let A := (stableEquivDyck n).symm p
  let B := (stableEquivDyck n).symm q
  let e := pre.count D
  let P := eastCounts 0 pre
  let S := eastCounts (e + (L + 1)) post
  have hlist (z : DyckAt (n + 1)) (x : Fin (L + 1))
      (hx : z.val.toList = pre ++ (rankBlock L x).toList ++ post) :
      ((stableEquivMono n) ((stableEquivDyck n).symm z)).val =
        P ++ List.replicate (x.val + 1) e ++ List.replicate ((L + 1) - (x.val + 1)) (e + 1) ++ S := by
    rw [eastCounts_stable, hx, eastCounts_append, eastCounts_append,
      eastCounts_rankBlock, List.count_append, ← (rankBlock L x).semilength_eq_count_D, rankBlock_semilength]
    simp [e, P, S, List.append_assoc]
  have hmon (k : Fin (n + 1)) : edge B k ≤ edge A k := by
    rw [← encode_getD B k, ← encode_getD A k]
    change (((stableEquivMono n) B).val.getD k.val 0) ≤ (((stableEquivMono n) A).val.getD k.val 0)
    rw [hlist q j hq, hlist p i hp, getD_twoRuns _ _ _ _ _ _ _ (by have := j.isLt; omega),
      getD_twoRuns _ _ _ _ _ _ _ (by have := i.isLt; omega)]
    have hij' : i.val < j.val := hij
    by_cases hp : k.val < P.length <;> by_cases hit : k.val - P.length < i.val + 1 <;>
      by_cases hjt : k.val - P.length < j.val + 1 <;>
      by_cases hm : k.val - P.length < L + 1 <;>
      simp only [hp, hit, hjt, hm, ite_true, ite_false] <;> omega
  have hs : A.val ⊆ B.val := fun c hc =>
    (mem_iff_edge_lt B c).mpr ((hmon (column c)).trans_lt ((mem_iff_edge_lt A c).mp hc))
  have hne : A ≠ B := by
    intro h
    have hs' := (stableEquivDyck n).symm.injective h
    have he := congrArg (fun z : DyckAt (n + 1) => z.val.toList) hs'
    rw [hp, hq] at he
    have hblock := List.append_cancel_left (List.append_cancel_right he)
    have htake := congrArg (fun l : List DyckStep => (l.takeWhile (· == U)).length) hblock
    have ht (x : Fin (L + 1)) :
        ((rankBlock L x).toList.takeWhile (· == U)).length = x.val + 1 := by
      simp [rankBlock, List.append_assoc]
    rw [ht i, ht j] at htake
    exact (Nat.ne_of_lt (show i.val < j.val from hij)) (Nat.add_right_cancel htake)
  letI : Fintype (Interval n) := Fintype.ofFinite _
  have hlt := Finset.card_lt_card ((Set.toFinset_ssubset_toFinset).2
    (ssubset_of_subset_of_ne hs (fun h => hne (Subtype.ext h))))
  exact hlt

end

end D5.S3.Combinatorics.Games.Pyranim

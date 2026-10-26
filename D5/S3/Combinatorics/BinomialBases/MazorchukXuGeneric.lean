/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuGeneric
   mirror-E: none(waiver:universal-generic-pattern-edge-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Finite source coordinates, labelled reconstruction and generic completions. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuOrder
import D5.S3.Combinatorics.BinomialBases.MazorchukXuFamilies
import Mathlib.Data.Finset.Sort

/-! Exceptional edges in a generic position/cutoff pattern are forced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

/-- Exactly p listed ordinary vertices precede s, and s is not a listed vertex. -/
def Position {M : ℕ} (g : Fin M → ℕ) (s p : ℕ) : Prop :=
  p ≤ M ∧ ∀ r : Fin M, (g r < s ↔ r.val < p) ∧ (s < g r ↔ p ≤ r.val)

/-- Incidence with a zero-indexed ordinary list starts exactly at c. -/
def Cutoff {M : ℕ} (E : ℕ → ℕ → Prop) (g : Fin M → ℕ) (s c : ℕ) : Prop :=
  c ≤ M ∧ ∀ r : Fin M, Incident E s (g r) ↔ c ≤ r.val

/-- Distinct generic positions and cutoff-position pairs determine each exceptional edge. -/
theorem generic_exceptional_edge {E : ℕ → ℕ → Prop} (h : Rules E)
    {M s t ps pt cs ct : ℕ} (g : Fin M → ℕ)
    (ho : ∀ r, E 0 (g r)) (hps : 0 < ps) (hpst : ps < pt)
    (hposs : Position g s ps) (hpost : Position g t pt)
    (hcuts : Cutoff E g s cs) (hcutt : Cutoff E g t ct)
    (hcspt : cs ≠ pt) (hctps : ct ≠ ps) :
    E s t ↔ cs < pt ∧ ct < ps := by
  have hpsM : ps < M := hpst.trans_le hpost.1
  have hptM : pt ≤ M := hpost.1
  have hst : s < t := by
    let r : Fin M := ⟨ps, hpsM⟩
    exact ((hposs.2 r).2.mpr le_rfl).trans ((hpost.2 r).1.mpr hpst)
  constructor
  · intro hstedge
    have hct : ct ≤ ps := by
      let r : Fin M := ⟨ps, hpsM⟩
      have hsr := (hposs.2 r).2.mpr le_rfl
      have hrt := (hpost.2 r).1.mpr hpst
      have hrtedge := h.propagate (ho r) hstedge (Nat.zero_le s) hsr hrt
      have := (hcutt.2 r).mp (Or.inr hrtedge)
      exact this
    have hcs : cs ≤ pt := by
      by_cases hptM : pt = M
      · simpa only [hptM] using hcuts.1
      · have hptM' : pt < M := lt_of_le_of_ne hpost.1 hptM
        let r : Fin M := ⟨pt - 1, by omega⟩
        let z : Fin M := ⟨pt, hptM'⟩
        have hsr := (hposs.2 r).2.mpr (by dsimp [r]; omega)
        have hrt := (hpost.2 r).1.mpr (by dsimp [r]; omega)
        have htz := (hpost.2 z).2.mpr le_rfl
        have hrpos := h.ordered (ho r)
        have hj := h.join (ho r) hstedge (ho z) (Nat.zero_le s) hsr le_rfl
          hrpos hrt.le (hrt.le.trans htz.le)
        have hsz : E s (g z) := by
          simpa only [max_eq_left (Nat.zero_le s), max_eq_right htz.le] using hj
        exact (hcuts.2 z).mp (Or.inl hsz)
    exact ⟨lt_of_le_of_ne hcs hcspt, lt_of_le_of_ne hct hctps⟩
  · rintro ⟨hcs, hct⟩
    let r : Fin M := ⟨ps - 1, by omega⟩
    let q : Fin M := ⟨pt - 1, by omega⟩
    have hrs : g r < s := (hposs.2 r).1.mpr (by dsimp [r]; omega)
    have hsq : s < g q := (hposs.2 q).2.mpr (by dsimp [q]; omega)
    have hqt : g q < t := (hpost.2 q).1.mpr (by dsimp [q]; omega)
    have hrq : g r < g q := hrs.trans hsq
    have hrt : g r < t := hrs.trans hst
    have hinc₁ := (hcutt.2 r).mpr (by dsimp [r]; omega)
    have hinc₂ := (hcuts.2 q).mpr (by dsimp [q]; omega)
    have hrtedge : E (g r) t := hinc₁.resolve_left (by
      intro he; exact (not_lt_of_ge hrt.le) (h.ordered he))
    have hsqedge : E s (g q) := hinc₂.resolve_right (by
      intro he; exact (not_lt_of_ge hsq.le) (h.ordered he))
    have hrqedge : E (g r) (g q) :=
      h.propagate (ho r) (ho q) le_rfl (h.ordered (ho r)) hrq
    have hj := h.join hrqedge hrtedge hsqedge le_rfl hrq hrs.le hsq
      hqt.le le_rfl
    simpa only [max_eq_right hrs.le, max_eq_left hqt.le] using hj

private def integerThreshold (N : ℕ) (h : ℕ → ℕ) (a b : ℕ) : Prop :=
  a < b ∧ b ≤ N ∧ h a ≤ b ∧ h b ≤ a

private theorem rules_integerThreshold (N : ℕ) (h : ℕ → ℕ) :
    Rules (integerThreshold N h) := by
  let T := thresholdEdges (fun a : ℕ => (a : ℚ)) (fun a => (h a : ℚ) - 1 / 2)
  have hT : Rules T := rules_thresholdEdges _ _ (fun a b hab => Nat.cast_le.mpr hab)
  have hhalf (a b : ℕ) : (h a : ℚ) - 1 / 2 < (b : ℚ) ↔ h a ≤ b := by
    constructor
    · intro he
      by_contra hb
      have hn : b + 1 ≤ h a := by omega
      have hr : (b : ℚ) + 1 ≤ (h a : ℚ) := by exact_mod_cast hn
      linarith
    · intro he
      have hr : (h a : ℚ) ≤ (b : ℚ) := by exact_mod_cast he
      linarith
  have hrel : integerThreshold N h = fun a b => T a b ∧ b ≤ N := by
    funext a b
    apply propext
    simp only [integerThreshold, T, thresholdEdges, hhalf]
    tauto
  rw [hrel]
  refine ⟨fun he => hT.ordered he.1, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact ⟨hT.propagate hab.1 hcd.1 hac hcb hbd, hcd.2⟩
  · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
    exact ⟨hT.join hab.1 hcd.1 hef.1 hac hcb hae heb hbd hbf,
      max_le hcd.2 hef.2⟩

/-- Arbitrary position/cutoff values admit a completion, with precisely the prescribed
anchor, ordinary incidences, and exceptional-edge criterion. -/
theorem exists_cutoff_completion {N M i : ℕ}
    (g : Fin M → ℕ) (s : Fin i → ℕ) (p c : Fin i → ℕ)
    (hg : StrictMono g) (hs : Function.Injective s)
    (hgp : ∀ r, 0 < g r) (hgb : ∀ r, g r ≤ N)
    (hsp : ∀ j, 0 < s j) (hsb : ∀ j, s j ≤ N)
    (hp : ∀ j, Position g (s j) (p j)) (hc : ∀ j, c j ≤ M) :
    ∃ E : ℕ → ℕ → Prop, Rules E ∧
      (∀ a b, E a b → b ≤ N) ∧
      (∀ a, E 0 a ↔ 0 < a ∧ a ≤ N ∧ ∀ j, s j ≠ a) ∧
      (∀ j, Cutoff E g (s j) (c j)) ∧
      (∀ j k, s j < s k → (E (s j) (s k) ↔ c j < p k ∧ c k < p j)) := by
  classical
  let q : Fin i → ℕ := fun j => if hj : c j < M then g ⟨c j, hj⟩ else N + 1
  have hqpos : ∀ j, 0 < q j := by
    intro j
    dsimp [q]
    split_ifs with hj
    · exact hgp _
    · omega
  have hgs : ∀ r j, g r ≠ s j := by
    intro r j heq
    have h := (hp j).2 r
    rcases lt_or_ge r.val (p j) with hr | hr
    · have := h.1.mpr hr; omega
    · have := h.2.mpr hr; omega
  let h : ℕ → ℕ := fun a => if ha : ∃ j, s j = a then q (Classical.choose ha) else 0
  have hh_s : ∀ j, h (s j) = q j := by
    intro j
    dsimp [h]
    rw [dite_eq_left ⟨j, rfl⟩]
    congr 1
    apply hs
    exact Classical.choose_spec (show ∃ k, s k = s j from ⟨j, rfl⟩)
  have hh_g : ∀ r, h (g r) = 0 := by
    intro r
    dsimp [h]
    apply dite_eq_right
    rintro ⟨j, hj⟩
    exact hgs r j hj.symm
  have hh_zero : h 0 = 0 := by
    dsimp [h]
    apply dite_eq_right
    rintro ⟨j, hj⟩
    have := hsp j
    omega
  have hqg : ∀ j r, q j ≤ g r ↔ c j ≤ r.val := by
    intro j r
    dsimp [q]
    split_ifs with hj
    · exact hg.le_iff_le
    · have := hgb r
      have := r.isLt
      omega
  have hqs : ∀ j k, q j ≤ s k ↔ c j < p k := by
    intro j k
    dsimp [q]
    split_ifs with hj
    · have hp' := (hp k).2 ⟨c j, hj⟩
      have hne := hgs ⟨c j, hj⟩ k
      change g ⟨c j, hj⟩ ≤ s k ↔ c j < p k
      exact ⟨fun he => hp'.1.mp (lt_of_le_of_ne he hne), fun he => (hp'.1.mpr he).le⟩
    · have := hsb k
      have := (hp k).1
      omega
  refine ⟨integerThreshold N h, rules_integerThreshold N h,
    fun a b he => he.2.1, ?_, ?_, ?_⟩
  · intro a
    simp only [integerThreshold, hh_zero, Nat.zero_le, true_and]
    constructor
    · rintro ⟨ha, hb, hh⟩
      refine ⟨ha, hb, ?_⟩
      intro j hj
      rw [← hj, hh_s] at hh
      have := hqpos j
      omega
    · rintro ⟨ha, hb, hex⟩
      have hh : h a = 0 := by
        dsimp [h]
        exact dite_eq_right (by rintro ⟨j, hj⟩; exact hex j hj)
      exact ⟨ha, hb, by omega⟩
  · intro j
    refine ⟨hc j, ?_⟩
    intro r
    have hneq := hgs r j
    have hboundg := hgb r
    have hbounds := hsb j
    simp only [Incident, integerThreshold, hh_s, hh_g, Nat.zero_le, and_true,
      true_and]
    rw [← hqg j r]
    omega
  · intro j k hjk
    simp only [integerThreshold, hh_s, hjk, hsb, true_and, hqs]

/-- The anchor edges, ordinary cutoffs and exceptional-edge bits determine every
bounded graph satisfying the rules. Empty ordinary and exceptional lists are permitted. -/
theorem edges_determined_by_data {N M i : ℕ} {E F : ℕ → ℕ → Prop}
    (hE : Rules E) (hF : Rules F)
    (hEb : ∀ {a b}, E a b → b ≤ N) (hFb : ∀ {a b}, F a b → b ≤ N)
    (g : Fin M → ℕ) (s : Fin i → ℕ) (c : Fin i → ℕ)
    (hcover : ∀ a, 0 < a → a ≤ N → (∃ r, g r = a) ∨ (∃ j, s j = a))
    (ho : ∀ r, E 0 (g r)) (ha : ∀ a, E 0 a ↔ F 0 a)
    (hEc : ∀ j, Cutoff E g (s j) (c j))
    (hFc : ∀ j, Cutoff F g (s j) (c j))
    (hbits : ∀ j k, E (s j) (s k) ↔ F (s j) (s k)) : E = F := by
  have step {A B : ℕ → ℕ → Prop} (hA : Rules A) (hB : Rules B)
      (hAb : ∀ {a b}, A a b → b ≤ N)
      (hoB : ∀ r, B 0 (g r)) (haAB : ∀ a, A 0 a → B 0 a)
      (hAc : ∀ j, Cutoff A g (s j) (c j))
      (hBc : ∀ j, Cutoff B g (s j) (c j))
      (hAB : ∀ j k, A (s j) (s k) → B (s j) (s k)) :
      ∀ a b, A a b → B a b := by
    intro a b hab
    have hab' := hA.ordered hab
    by_cases ha0 : a = 0
    · subst a; exact haAB b hab
    have hap : 0 < a := Nat.pos_of_ne_zero ha0
    have hbp : 0 < b := hap.trans hab'
    rcases hcover a hap (hab'.le.trans (hAb hab)) with ⟨r, rfl⟩ | ⟨j, rfl⟩
    · rcases hcover b hbp (hAb hab) with ⟨q, rfl⟩ | ⟨k, rfl⟩
      · exact hB.propagate (hoB r) (hoB q) le_rfl (hB.ordered (hoB r)) hab'
      · have hincA : Incident A (s k) (g r) := Or.inr hab
        have hincB := ((hBc k).2 r).mpr (((hAc k).2 r).mp hincA)
        exact hincB.resolve_left (fun hbad => (not_lt_of_ge hab'.le) (hB.ordered hbad))
    · rcases hcover b hbp (hAb hab) with ⟨q, rfl⟩ | ⟨k, rfl⟩
      · have hincA : Incident A (s j) (g q) := Or.inl hab
        have hincB := ((hBc j).2 q).mpr (((hAc j).2 q).mp hincA)
        exact hincB.resolve_right (fun hbad => (not_lt_of_ge hab'.le) (hB.ordered hbad))
      · exact hAB j k hab
  funext a b
  apply propext
  exact ⟨step hE hF hEb (fun r => (ha _).mp (ho r))
      (fun a => (ha a).mp) hEc hFc (fun j k => (hbits j k).mp) a b,
    step hF hE hFb ho (fun a => (ha a).mpr) hFc hEc
      (fun j k => (hbits j k).mpr) a b⟩

/-- Every fully generic coordinate datum has exactly one bounded admissible graph. -/
theorem exists_unique_generic_completion {N M i : ℕ}
    (g : Fin M → ℕ) (s : Fin i → ℕ) (p c : Fin i → ℕ)
    (hg : StrictMono g) (hs : StrictMono s) (hpm : StrictMono p)
    (hgp : ∀ r, 0 < g r) (hgb : ∀ r, g r ≤ N)
    (hsp : ∀ j, 0 < s j) (hsb : ∀ j, s j ≤ N)
    (hp : ∀ j, Position g (s j) (p j)) (hpp : ∀ j, 0 < p j)
    (hc : ∀ j, c j ≤ M) (hdisjoint : ∀ j k, c j ≠ p k)
    (hcover : ∀ a, 0 < a → a ≤ N → (∃ r, g r = a) ∨ (∃ j, s j = a)) :
    ∃! E : ℕ → ℕ → Prop, Rules E ∧
      (∀ a b, E a b → b ≤ N) ∧
      (∀ a, E 0 a ↔ ∃ r, g r = a) ∧
      (∀ j, Cutoff E g (s j) (c j)) := by
  classical
  obtain ⟨E, hE, hEb, hEa, hEc, _⟩ := exists_cutoff_completion g s p c
    hg hs.injective hgp hgb hsp hsb hp hc
  have hgs : ∀ r j, g r ≠ s j := by
    intro r j heq
    have h := (hp j).2 r
    rcases lt_or_ge r.val (p j) with hr | hr
    · have := h.1.mpr hr; omega
    · have := h.2.mpr hr; omega
  have hEa' : ∀ a, E 0 a ↔ ∃ r, g r = a := by
    intro a
    rw [hEa]
    constructor
    · rintro ⟨ha, hb, hnot⟩
      exact (hcover a ha hb).resolve_right (by rintro ⟨j, hj⟩; exact hnot j hj)
    · rintro ⟨r, rfl⟩
      exact ⟨hgp r, hgb r, fun j => (hgs r j).symm⟩
  refine ⟨E, ⟨hE, hEb, hEa', hEc⟩, ?_⟩
  intro F hFdata
  obtain ⟨hF, hFb, hFa, hFc⟩ := hFdata
  have hEo : ∀ r, E 0 (g r) := fun r => (hEa' _).mpr ⟨r, rfl⟩
  have hFo : ∀ r, F 0 (g r) := fun r => (hFa _).mpr ⟨r, rfl⟩
  have hbits : ∀ j k, E (s j) (s k) ↔ F (s j) (s k) := by
    intro j k
    by_cases hjk : j < k
    · exact (generic_exceptional_edge hE g hEo (hpp j) (hpm hjk)
        (hp j) (hp k) (hEc j) (hEc k) (hdisjoint j k) (hdisjoint k j)).trans
        (generic_exceptional_edge hF g hFo (hpp j) (hpm hjk)
          (hp j) (hp k) (hFc j) (hFc k) (hdisjoint j k) (hdisjoint k j)).symm
    · have hkj : s k ≤ s j := hs.monotone (le_of_not_gt hjk)
      exact iff_of_false (fun he => (not_lt_of_ge hkj) (hE.ordered he))
        (fun he => (not_lt_of_ge hkj) (hF.ordered he))
  exact (edges_determined_by_data hE hF (fun he => hEb _ _ he)
    (fun he => hFb _ _ he) g s c hcover hEo
    (fun a => (hEa' a).trans (hFa a).symm) hEc hFc hbits).symm

/-- The position and exceptional index reconstruct the original natural label.
This includes adjacent exceptional vertices and positions equal to zero. -/
theorem exceptional_label_eq_position_add_index {N M i : ℕ}
    (g : Fin M → ℕ) (s : Fin i → ℕ) (p : Fin i → ℕ)
    (hg : Function.Injective g) (hs : StrictMono s)
    (hgp : ∀ r, 0 < g r) (hsp : ∀ j, 0 < s j) (hsb : ∀ j, s j ≤ N)
    (hp : ∀ j, Position g (s j) (p j))
    (hcover : ∀ a, 0 < a → a ≤ N → (∃ r, g r = a) ∨ (∃ j, s j = a))
    (j : Fin i) : s j = p j + j.val + 1 := by
  classical
  let G := (Finset.univ.filter (fun r : Fin M => r.val < p j)).image g
  let S := (Finset.univ.filter (fun k : Fin i => k < j)).image s
  have hgs : ∀ r k, g r ≠ s k := by
    intro r k heq
    have h := (hp k).2 r
    rcases lt_or_ge r.val (p k) with hr | hr
    · have := h.1.mpr hr; omega
    · have := h.2.mpr hr; omega
  have hzero : 0 ∉ G ∪ S := by
    intro hz
    rcases Finset.mem_union.mp hz with hG | hS
    · obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hG
      have := hgp r; omega
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hS
      have := hsp k; omega
  have hdisj : Disjoint G S := by
    apply Finset.disjoint_left.mpr
    intro a hG hS
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hG
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hS
    exact hgs r k (hr.trans hk.symm)
  have hpartition : Finset.range (s j) = insert 0 (G ∪ S) := by
    ext a
    constructor
    · intro ha
      have haj : a < s j := Finset.mem_range.mp ha
      by_cases ha0 : a = 0
      · simp [ha0]
      apply Finset.mem_insert_of_mem
      have hap : 0 < a := Nat.pos_of_ne_zero ha0
      rcases hcover a hap (haj.le.trans (hsb j)) with ⟨r, rfl⟩ | ⟨k, rfl⟩
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨r,
          Finset.mem_filter.mpr ⟨Finset.mem_univ r, ((hp j).2 r).1.mp haj⟩, rfl⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨k,
          Finset.mem_filter.mpr ⟨Finset.mem_univ k, hs.lt_iff_lt.mp haj⟩, rfl⟩
    · intro ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Finset.mem_range.mpr (hsp j)
      · rcases Finset.mem_union.mp ha with hG | hS
        · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hG
          exact Finset.mem_range.mpr (((hp j).2 r).1.mpr (Finset.mem_filter.mp hr).2)
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hS
          exact Finset.mem_range.mpr (hs (Finset.mem_filter.mp hk).2)
  have hGcard : G.card = p j := by
    dsimp [G]
    rw [Finset.card_image_of_injective _ hg, Fin.card_filter_val_lt]
    exact min_eq_right (hp j).1
  have hScard : S.card = j.val := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hs.injective]
    change (Finset.univ.filter (fun k : Fin i => k.val < j.val)).card = j.val
    rw [Fin.card_filter_val_lt, min_eq_right j.isLt.le]
  have heq := congrArg Finset.card hpartition
  simpa only [Finset.card_range, Finset.card_insert_of_notMem hzero,
    Finset.card_union_of_disjoint hdisj, hGcard, hScard] using heq

private theorem exists_position {M : ℕ} (g : Fin M → ℕ) (hg : StrictMono g)
    (s : ℕ) (hnot : ∀ r, g r ≠ s) : ∃ p, Position g s p := by
  classical
  let p := (Finset.univ.filter (fun r : Fin M => g r < s)).card
  have hpM : p ≤ M := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun r => g r < s))
  have hdown : ∀ i j : Fin M, j ≤ i → g i < s → g j < s := by
    intro i j hji hi
    exact (hg.monotone hji).trans_lt hi
  refine ⟨p, hpM, ?_⟩
  intro r
  have hr : r.val < p ↔ g r < s :=
    Fin.lt_card_filter_univ_iff_apply_of_imp (fun r => g r < s) hdown
  refine ⟨hr.symm, ?_⟩
  have hne := hnot r
  omega

/-- Every ordered anchor/exception partition has a monotone position list, one cutoff
per exception, and exact reconstruction of each exceptional natural label. -/
theorem exists_coordinate_encoding {N M i : ℕ} {E : ℕ → ℕ → Prop}
    (hE : Rules E) (g : Fin M → ℕ) (s : Fin i → ℕ)
    (hg : StrictMono g) (hs : StrictMono s)
    (ho : ∀ r, E 0 (g r)) (hmissing : ∀ j, ¬ E 0 (s j))
    (hsp : ∀ j, 0 < s j) (hsb : ∀ j, s j ≤ N)
    (hcover : ∀ a, 0 < a → a ≤ N → (∃ r, g r = a) ∨ (∃ j, s j = a)) :
    ∃ p c : Fin i → ℕ, Monotone p ∧ (∀ j, Position g (s j) (p j)) ∧
      (∀ j, Cutoff E g (s j) (c j)) ∧ (∀ j, s j = p j + j.val + 1) := by
  classical
  have hgs : ∀ r j, g r ≠ s j := by
    intro r j heq
    exact hmissing j (heq ▸ ho r)
  have hp : ∀ j : Fin i, ∃ p, Position g (s j) p :=
    fun j => exists_position g hg (s j) (fun r => hgs r j)
  choose p hp using hp
  have hc : ∀ j : Fin i, ∃ c, Cutoff E g (s j) c := by
    intro j
    obtain ⟨c, hc, _⟩ := exists_unique_ordinary_cutoff hE (hmissing j) g hg ho
    exact ⟨c, hc⟩
  choose c hc using hc
  have hpm : Monotone p := by
    intro j k hjk
    by_cases heq : j = k
    · simp [heq]
    have hsjk : s j < s k := hs (lt_of_le_of_ne hjk heq)
    by_contra hpjk
    have hpk : p k < p j := lt_of_not_ge hpjk
    have hpkM : p k < M := hpk.trans_le (hp j).1
    let r : Fin M := ⟨p k, hpkM⟩
    have hgj := ((hp j).2 r).1.mpr hpk
    have hkg := ((hp k).2 r).2.mpr le_rfl
    omega
  exact ⟨p, c, hpm, hp, hc, exceptional_label_eq_position_add_index g s p
    hg.injective hs (fun r => hE.ordered (ho r)) hsp hsb hp hcover⟩

private def ordinaryVertices (A : Finset (ℕ × ℕ)) : Finset ℕ :=
  (A.filter (fun z => z.1 = 0)).image Prod.snd

private theorem mem_ordinaryVertices {A : Finset (ℕ × ℕ)} {a : ℕ} :
    a ∈ ordinaryVertices A ↔ (0, a) ∈ A := by
  simp only [ordinaryVertices, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨b, c⟩, ⟨hbc, hb⟩, hc⟩
    change b = 0 at hb
    change c = a at hc
    simpa only [hb, hc] using hbc
  · intro ha
    exact ⟨(0, a), ⟨ha, rfl⟩, rfl⟩

private theorem ordinaryVertices_card (A : Finset (ℕ × ℕ)) :
    (ordinaryVertices A).card = firstColumnCard A := by
  classical
  unfold ordinaryVertices firstColumnCard
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hx0 := (Finset.mem_filter.mp hx).2
  have hy0 := (Finset.mem_filter.mp hy).2
  exact Prod.ext (hx0.trans hy0.symm) hxy

/-- Every member of the literal bounded edge family admits finite position/cutoff
coordinates with exactly i exceptions, including the zero-ordinary case. -/
theorem edgeFamily_has_coordinates {n i : ℕ} (hi : i ≤ n + 1)
    {A : Finset (ℕ × ℕ)} (hA : A ∈ edgeFamily n (n + 1 - i)) :
    ∃ (g : Fin (n + 1 - i) → ℕ) (s : Fin i → ℕ) (p c : Fin i → ℕ),
      StrictMono g ∧ StrictMono s ∧ Monotone p ∧
      (∀ a, (0, a) ∈ A ↔ ∃ r, g r = a) ∧
      (∀ j, (0, s j) ∉ A ∧ 0 < s j ∧ s j ≤ n + 1) ∧
      (∀ a, 0 < a → a ≤ n + 1 → (∃ r, g r = a) ∨ (∃ j, s j = a)) ∧
      (∀ j, Position g (s j) (p j)) ∧
      (∀ j, Cutoff (fun a b => (a, b) ∈ A) g (s j) (c j)) ∧
      (∀ j, s j = p j + j.val + 1) := by
  classical
  obtain ⟨hsubset, hE, hk⟩ := Finset.mem_filter.mp hA
  have hsub := Finset.mem_powerset.mp hsubset
  have hbound {a b : ℕ} (hab : (a, b) ∈ A) : b ≤ n + 1 := by
    have hm := Finset.mem_filter.mp (hsub hab)
    have hb := Finset.mem_range.mp (Finset.mem_product.mp hm.1).2
    omega
  let O := ordinaryVertices A
  have hOcard : O.card = n + 1 - i := (ordinaryVertices_card A).trans hk
  have hOsub : O ⊆ Finset.Icc 1 (n + 1) := by
    intro a ha
    have he : (0, a) ∈ A := mem_ordinaryVertices.mp ha
    exact Finset.mem_Icc.mpr ⟨hE.ordered he, hbound he⟩
  let S := Finset.Icc 1 (n + 1) \ O
  have hScard : S.card = i := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset hOsub, Nat.card_Icc, hOcard]
    omega
  let g : Fin (n + 1 - i) → ℕ := O.orderEmbOfFin hOcard
  let s : Fin i → ℕ := S.orderEmbOfFin hScard
  have hg : StrictMono g := (O.orderEmbOfFin hOcard).strictMono
  have hs : StrictMono s := (S.orderEmbOfFin hScard).strictMono
  have hOmem : ∀ r, g r ∈ O := O.orderEmbOfFin_mem hOcard
  have hSmem : ∀ j, s j ∈ S := S.orderEmbOfFin_mem hScard
  have hanchor : ∀ a, (0, a) ∈ A ↔ ∃ r, g r = a := by
    intro a
    rw [← mem_ordinaryVertices]
    change a ∈ O ↔ ∃ r, g r = a
    constructor
    · intro ha
      obtain ⟨r, hr⟩ := (O.orderIsoOfFin hOcard).surjective ⟨a, ha⟩
      exact ⟨r, congrArg Subtype.val hr⟩
    · rintro ⟨r, rfl⟩
      exact hOmem r
  have ho : ∀ r, (0, g r) ∈ A := fun r => mem_ordinaryVertices.mp (hOmem r)
  have hmissing : ∀ j, (0, s j) ∉ A := by
    intro j he
    exact (Finset.mem_sdiff.mp (hSmem j)).2 (mem_ordinaryVertices.mpr he)
  have hsp : ∀ j, 0 < s j := fun j =>
    (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (hSmem j)).1).1
  have hsb : ∀ j, s j ≤ n + 1 := fun j =>
    (Finset.mem_Icc.mp (Finset.mem_sdiff.mp (hSmem j)).1).2
  have hcover : ∀ a, 0 < a → a ≤ n + 1 → (∃ r, g r = a) ∨ (∃ j, s j = a) := by
    intro a hap hab
    by_cases haO : a ∈ O
    · left
      exact (hanchor a).mp (mem_ordinaryVertices.mp haO)
    · right
      have haS : a ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨hap, hab⟩, haO⟩
      obtain ⟨j, hj⟩ := (S.orderIsoOfFin hScard).surjective ⟨a, haS⟩
      exact ⟨j, congrArg Subtype.val hj⟩
  obtain ⟨p, c, hpm, hp, hc, hlabels⟩ :=
    exists_coordinate_encoding hE g s hg hs ho hmissing hsp hsb hcover
  exact ⟨g, s, p, c, hg, hs, hpm, hanchor,
    fun j => ⟨hmissing j, hsp j, hsb j⟩, hcover, hp, hc, hlabels⟩

end D5.S3.Combinatorics.MazorchukXu

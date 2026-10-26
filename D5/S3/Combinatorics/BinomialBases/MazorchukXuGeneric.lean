/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuGeneric
   mirror-E: none(waiver:universal-generic-pattern-edge-proof)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic]
   utility: none
   digest: Generic positions and cutoffs uniquely force exceptional edges. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuOrder

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
  have hptpos : 0 < pt := hps.trans hpst
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
  refine ⟨fun he => he.1, ?_, ?_⟩
  · intro a b c d hab hcd hac hcb hbd
    exact ⟨hbd, hcd.2.1, hab.2.2.2.trans (hac.trans (hcb.le.trans hbd.le)),
      hcd.2.2.2.trans hcb.le⟩
  · intro a b c d e f hab hcd hef hac hcb hae heb hbd hbf
    refine ⟨lt_of_lt_of_le (max_lt hcb heb) (hbd.trans (le_max_left d f)),
      max_le hcd.2.1 hef.2.1, ?_, ?_⟩
    · rcases le_total c e with hce | hec
      · rw [max_eq_right hce]
        exact hef.2.2.1.trans (le_max_right d f)
      · rw [max_eq_left hec]
        exact hcd.2.2.1.trans (le_max_left d f)
    · rcases le_total d f with hdf | hfd
      · rw [max_eq_right hdf]
        exact hef.2.2.2.trans (le_max_right c e)
      · rw [max_eq_left hfd]
        exact hcd.2.2.2.trans (le_max_left c e)

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
  exact (edges_determined_by_data hE hF (fun he => hEb _ _ he) (fun he => hFb _ _ he) g s c hcover hEo
    (fun a => (hEa' a).trans (hFa a).symm) hEc hFc hbits).symm

end D5.S3.Combinatorics.MazorchukXu

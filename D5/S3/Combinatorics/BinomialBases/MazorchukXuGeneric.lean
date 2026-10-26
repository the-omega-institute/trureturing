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

end D5.S3.Combinatorics.MazorchukXu

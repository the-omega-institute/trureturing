/- GID: D5/S3/TotalVariation/FairBiasChainContraction
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasChainContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral chain cancellation on the augmented signed fair-bias faces. -/

import D5.S3.TotalVariation.FairBiasMatching
import D5.S3.HomologicalAlgebra.FiniteMorseCancellation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! Ordered deletion on the actual signed faces, including the empty face. -/

set_option autoImplicit false

open Finset
open D5.S3.TotalVariation.FairBiasMatching
open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasShelling
open D5.S3.HomologicalAlgebra.FiniteMorseCancellation

namespace D5.S3.TotalVariation.FairBiasChainContraction

universe u v
variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

noncomputable section

local instance (c : L → A) : Fintype (Face c) := by
  classical
  unfold Face
  infer_instance

local instance (c : L → A) : DecidableEq (Face c) := Classical.decEq _

private def deletionSign {V : Type*} [LinearOrder V] (s : Finset V) (x : V) : ℤ :=
  (-1) ^ (s.filter (· < x)).card

private def signedEntry {V : Type*} [LinearOrder V] (s t : Finset V) : ℤ :=
  ∑ x ∈ t, if s = t.erase x then deletionSign t x else 0

/-- The integral boundary in augmented signed-face coordinates, with column inputs. -/
def boundary (c : L → A) : Matrix (Face c) (Face c) ℤ :=
  fun s t => signedEntry s.val t.val

private theorem sign_erase {V : Type*} [LinearOrder V] (s : Finset V) {x y : V}
    (hx : x ∈ s) :
    deletionSign (s.erase x) y =
      if x < y then -deletionSign s y else deletionSign s y := by
  unfold deletionSign
  rw [Finset.filter_erase]
  by_cases hxy : x < y
  · rw [ite_eq_left hxy, ← card_erase_add_one (mem_filter.mpr ⟨hx, hxy⟩), pow_succ]
    ring
  · rw [ite_eq_right hxy, erase_eq_of_notMem]
    exact fun h => hxy (mem_filter.mp h).2

private theorem signedEntry_eq_zero_of_not_cover {c : L → A} {s t : Face c}
    (hn : ¬ Cover s t) : boundary c s t = 0 := by
  unfold boundary signedEntry
  apply sum_eq_zero
  intro x hx
  apply ite_eq_right
  intro he
  apply hn
  unfold Cover
  rw [he]
  exact ⟨erase_subset x t.val, (card_erase_add_one hx).symm⟩

private theorem cover_of_boundary_ne_zero {c : L → A} {s t : Face c}
    (hn : boundary c s t ≠ 0) : Cover s t := by
  by_contra hc
  exact hn (signedEntry_eq_zero_of_not_cover hc)

private theorem erase_eq_of_cover {c : L → A} {s t : Face c} (h : Cover s t)
    {x : L × Bool} (hxt : x ∈ t.val) (hxs : x ∉ s.val) : t.val.erase x = s.val := by
  have hle : s.val ⊆ t.val.erase x := by
    intro y hy
    exact mem_erase.mpr ⟨fun hyx => hxs (hyx ▸ hy), h.1 hy⟩
  exact (eq_of_subset_of_card_le hle (by
    have hc := card_erase_add_one hxt
    have hcard := h.2
    omega)).symm

private theorem boundary_unit_of_cover {c : L → A} {s t : Face c}
    (h : Cover s t) : boundary c s t * boundary c s t = 1 := by
  classical
  let : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  have hne : (t.val \ s.val).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hts
    have he : t.val = s.val := Subset.antisymm hts h.1
    have hc := h.2
    simp only [he] at hc
    omega
  obtain ⟨x, hx⟩ := hne
  have hx' := mem_sdiff.mp hx
  have he := erase_eq_of_cover h hx'.1 hx'.2
  have hv : boundary c s t = deletionSign t.val x := by
    unfold boundary signedEntry
    rw [sum_eq_single x]
    · rw [ite_eq_left he.symm]
    · intro y hy hyx
      apply ite_eq_right
      intro hye
      have hnot := hx'.2
      rw [hye] at hnot
      exact hnot (mem_erase.mpr ⟨Ne.symm hyx, hx'.1⟩)
    · exact fun hn => False.elim (hn hx'.1)
  rw [hv, deletionSign, ← mul_pow]
  norm_num

private theorem deletionPair_antisymm {V : Type*} [LinearOrder V] (s t : Finset V)
    {x y : V} (hx : x ∈ t) (hy : y ∈ t) :
    (if y ∈ t.erase x ∧ s = (t.erase x).erase y then
      deletionSign (t.erase x) y * deletionSign t x else 0) =
    -(if x ∈ t.erase y ∧ s = (t.erase y).erase x then
      deletionSign (t.erase y) x * deletionSign t y else 0) := by
  by_cases he : x = y
  · subst y
    simp
  have hxy : y ∈ t.erase x := mem_erase.mpr ⟨Ne.symm he, hy⟩
  have hyx : x ∈ t.erase y := mem_erase.mpr ⟨he, hx⟩
  simp only [hxy, hyx, true_and]
  have herase : (t.erase x).erase y = (t.erase y).erase x := by
    ext z
    simp only [mem_erase]
    tauto
  rw [herase]
  rw [sign_erase t hx, sign_erase t hy]
  by_cases hlt : x < y
  · rw [ite_eq_left hlt, ite_eq_right (not_lt_of_ge hlt.le)]
    split <;> ring
  · rw [ite_eq_right hlt, ite_eq_left (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he))]
    split <;> ring


private theorem boundary_squared (c : L → A) (h : (facets c).Nonempty) :
    boundary c * boundary c = 0 := by
  classical
  let : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  ext s t
  obtain ⟨B, hB, ht, _⟩ := exists_first_facet c h t.property
  let term (x y : L × Bool) : ℤ :=
    if y ∈ t.val.erase x ∧ s.val = (t.val.erase x).erase y then
      deletionSign (t.val.erase x) y * deletionSign t.val x else 0
  have expand :
      (boundary c * boundary c) s t =
        ∑ x ∈ t.val, ∑ y ∈ t.val, term x y := by
    rw [Matrix.mul_apply]
    change (∑ u : Face c, boundary c s u *
      (∑ x ∈ t.val, if u.val = t.val.erase x then deletionSign t.val x else 0)) = _
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro x hx
    let u : Face c := ⟨t.val.erase x, augmented_of_subset_facet c hB
      ((erase_subset x t.val).trans ht)⟩
    rw [sum_eq_single u]
    · change boundary c s u *
        (if u.val = t.val.erase x then deletionSign t.val x else 0) = _
      simp only [u, ite_true]
      unfold boundary signedEntry
      rw [sum_mul]
      calc
        _ = ∑ y ∈ t.val.erase x, term x y := by
          apply sum_congr rfl
          intro y hy
          simp only [term, hy, true_and]
          split <;> simp
        _ = _ := by
          apply sum_subset (erase_subset x t.val)
          intro y _ hy
          exact ite_eq_right (fun hy' => hy hy'.1)
    · intro v _ hvu
      have hne : v.val ≠ t.val.erase x := fun hv => hvu (Subtype.ext hv)
      rw [ite_eq_right hne, mul_zero]
    · simp
  rw [expand, Matrix.zero_apply]
  have cancel : (∑ x ∈ t.val, ∑ y ∈ t.val, term x y) =
      -(∑ x ∈ t.val, ∑ y ∈ t.val, term x y) := calc
    _ = ∑ x ∈ t.val, ∑ y ∈ t.val, -(term y x) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact deletionPair_antisymm s.val t.val hx hy
    _ = -(∑ x ∈ t.val, ∑ y ∈ t.val, term y x) := by
      simp only [sum_neg_distrib]
    _ = _ := congrArg (fun z : ℤ => -z) sum_comm
  omega


private theorem actual_morse_data (c : L → A) (h : (facets c).Nonempty) :
    ∃ (mate : Face c → Face c) (rank : Face c → ℕ),
      IsIntervalMatching c mate ∧ Function.Involutive mate ∧
      (∀ s, mate s = s ↔ s.val ∈ facets c ∧ restrictionFace c s.val = s.val) ∧
      (∀ s, (mate s).val.card = s.val.card + 1 ∨
        s.val.card = (mate s).val.card + 1 ∨ mate s = s) ∧
      (∀ s t, boundary c s t ≠ 0 → t.val.card = s.val.card + 1) ∧
      (∀ s, (mate s).val.card + 1 = s.val.card →
        boundary c (mate s) s * boundary c (mate s) s = 1) ∧
      (∀ s t, boundary c s t ≠ 0 → mate t ≠ s → rank s < rank t) ∧
      (∀ s, (mate s).val.card = s.val.card + 1 → rank (mate s) < rank s) ∧
      (∀ s, mate s = s →
        s.val.card = Fintype.card L -
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c))) := by
  obtain ⟨mate, rank, hinterval, hinv, hcover, hfixed, hrank⟩ := actualAugmentedMatching c h
  refine ⟨mate, rank, hinterval, hinv, hfixed, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rcases hcover s with hup | hdown | hfix
    · exact Or.inl hup.2
    · exact Or.inr (Or.inl hdown.2)
    · exact Or.inr (Or.inr hfix)
  · intro s t hst
    exact (cover_of_boundary_ne_zero hst).2
  · intro s hs
    apply boundary_unit_of_cover
    rcases hcover s with hup | hdown | hfix
    · have hcard := hup.2
      omega
    · exact hdown
    · rw [hfix] at hs
      omega
  · intro s t hst hmt
    exact hrank t s (Or.inl ⟨cover_of_boundary_ne_zero hst, hmt⟩)
  · intro s hs
    apply hrank s (mate s)
    refine Or.inr ⟨?_, rfl⟩
    rcases hcover s with hup | hdown | hfix
    · exact hup
    · have hcard := hdown.2
      omega
    · rw [hfix] at hs
      omega
  · intro s hs
    exact facet_card_eq_nullity c s.val (mem_facets.mp ((hfixed s).mp hs).1)


/-- The augmented signed chains contract onto the full-restriction facets with
explicit finite correction matrices and their degree laws. -/
theorem actualContraction (c : L → A) (h : (facets c).Nonempty) :
    ∃ (m : Matching (Face c)) (N : ℕ),
      1 ≤ N ∧ m.D = boundary c ∧ (∀ s, m.d s = s.val.card) ∧
      IsIntervalMatching c m.mate ∧
      (∀ s, m.mate s = s ↔ s.val ∈ facets c ∧ restrictionFace c s.val = s.val) ∧
      (∀ s : m.Critical, m.d s.val = Fintype.card L -
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c))) ∧
      m.Contraction N := by
  classical
  obtain ⟨mate, rank, hinterval, hinv, hfixed, hadj, hdown, hunit, hunmatched,
    hmatched, hsize⟩ := actual_morse_data c h
  let m : Matching (Face c) :=
    { d := fun s => s.val.card
      mate := mate
      D := boundary c
      involutive := hinv
      adjacent := by
        intro s hne
        rcases hadj s with hup | hdown | heq
        · exact Or.inr hup.symm
        · exact Or.inl hdown.symm
        · exact (hne heq).elim
      differential_sq := boundary_squared c h
      downward := fun s t hst => (hdown s t hst).symm
      unit_entry := fun s hs => by simpa only [pow_two] using hunit s hs }
  let N := Finset.univ.sup rank + 1
  have hpos : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le _)
  have hbound (s : Face c) : rank s < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := rank) (Finset.mem_univ s))
  refine ⟨m, N, hpos, rfl, fun _ => rfl, hinterval, hfixed, ?_, ?_⟩
  · intro s
    exact hsize s.val s.property
  · exact m.finite_morse_cancellation rank _ N hpos hbound
      (fun s t hne hst => hunmatched s t hst (Ne.symm hne))
      (fun s hs => hmatched s hs.symm) hsize

end

end D5.S3.TotalVariation.FairBiasChainContraction

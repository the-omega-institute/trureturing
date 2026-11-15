/- GID: D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionGlobalFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal finite-poset toggle sweep equals the ceiling and lower-boundary formula. -/

import D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Fintype.EquivFin

/-!
The set-side argument generalizes the grid argument in Columbus Labs,
interval-closed-rowmotion, commit 380b1662eebbddfd1e6c6f046dbf7dbb3fa874dd,
formal/companions/Rowmotion/GlobalImageProperties.lean. The local flip test also
adapts ToggleCriteria.lean and SweepLocality.lean at that revision.
The finite-minimum step uses Mathlib for arbitrary finite partial orders.
These adaptations are replaced by direct applications if the pinned Mathlib
provides equivalent statements for arbitrary finite partial orders.

MIT License

Copyright (c) 2026 Columbus Labs

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula

open D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open scoped symmDiff

universe u
variable {P : Type u} [PartialOrder P]

/-- The minimal points in the upper closure outside the initial set. -/
def ceiling (I : Set P) : Set P := {c | Minimal (· ∈ (upperClosure I : Set P) \ I) c}

/-- The initial minimal points that lie below a ceiling point. -/
def lowerBoundary (I : Set P) : Set P :=
  {m | Minimal (· ∈ I) m} ∩ (lowerClosure (ceiling I) : Set P)

/-- The points incomparable with every member of a given set. -/
def incomparable (C : Set P) : Set P := {x | ∀ c ∈ C, ¬ x ≤ c ∧ ¬ c ≤ x}

/-- The formula uses only the initial set and its two extremal boundaries. -/
def formula (I : Set P) : Set P :=
  (incomparable (ceiling I) \ I) ∪
    ((lowerClosure (ceiling I) : Set P) \ (lowerClosure (lowerBoundary I) : Set P))

private def lowerFilled (I : Set P) (x : P) : Prop :=
  ∀ y ∈ I, ∀ z, y ≤ z → z < x → z ∈ I

private def upperFilled (J : Set P) (x : P) : Prop :=
  ∀ y ∈ J, ∀ z, x < z → z ≤ y → z ∈ J

private theorem formula_local [Finite P] (I : Set P) (hI : I.OrdConnected) :
    (∀ x ∈ I, x ∈ formula I ↔ ∃ a ∈ I, ∃ b ∈ formula I, a < x ∧ x < b) ∧
    (∀ x ∉ I, x ∈ formula I ↔ lowerFilled I x ∧ upperFilled (formula I) x) := by
  classical
  let C := ceiling I
  let H := lowerBoundary I
  let J := formula I
  have anti {c d : P} (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≤ d) : c = d :=
    le_antisymm hcd (hd.2 hc.1 hcd)
  have inc {x : P} : x ∈ incomparable C ↔
      x ∉ (lowerClosure C : Set P) ∧ x ∉ (upperClosure C : Set P) := by
    simp only [incomparable, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨fun ⟨c, hc, hxc⟩ => (h c hc).1 hxc,
        fun ⟨c, hc, hcx⟩ => (h c hc).2 hcx⟩
    · rintro ⟨hd, hu⟩ c hc
      exact ⟨fun h => hd ⟨c, hc, h⟩, fun h => hu ⟨c, hc, h⟩⟩
  have up (x : P) : x ∈ (upperClosure C : Set P) ↔
      x ∈ (upperClosure I : Set P) ∧ x ∉ I := by
    constructor
    · rintro hx
      obtain ⟨c, hc, hcx⟩ := mem_upperClosure.mp hx
      obtain ⟨a, ha, hac⟩ := mem_upperClosure.mp hc.1.1
      exact ⟨mem_upperClosure.mpr ⟨a, ha, hac.trans hcx⟩,
        fun hx => hc.1.2 (hI.out ha hx ⟨hac, hcx⟩)⟩
    · intro hx
      obtain ⟨c, hcx, hc⟩ :=
        (Set.toFinite ((upperClosure I : Set P) \ I)).isPWO.exists_le_minimal hx
      exact mem_upperClosure.mpr ⟨c, hc, hcx⟩
  have downup {x : P} (hd : x ∈ (lowerClosure C : Set P))
      (hu : x ∈ (upperClosure C : Set P)) : x ∈ C := by
    obtain ⟨d, hd, hxd⟩ := mem_lowerClosure.mp hd
    obtain ⟨c, hc, hcx⟩ := mem_upperClosure.mp hu
    have he := anti hc hd (hcx.trans hxd)
    have hxc : x = c := le_antisymm (he.symm ▸ hxd) hcx
    exact hxc.symm ▸ hc
  have notH {x : P} (hx : x ∈ J) : x ∉ (lowerClosure H : Set P) := by
    intro hh
    obtain ⟨m, hm, hxm⟩ := mem_lowerClosure.mp hh
    rcases hx with hx | hx
    · exact (inc.mp hx.1).1 ((lowerClosure C).lower hxm hm.2)
    · exact hx.2 (mem_lowerClosure.mpr ⟨m, hm, hxm⟩)
  have convex : J.OrdConnected := by
    constructor
    intro a ha b hb x hx
    have hn : x ∉ (lowerClosure H : Set P) :=
      fun hh => notH ha ((lowerClosure H).lower hx.1 hh)
    by_cases hd : x ∈ (lowerClosure C : Set P)
    · exact Or.inr ⟨hd, hn⟩
    · have hb' : b ∈ incomparable C \ I := by
        rcases hb with hb | hb
        · exact hb
        · exact False.elim (hd ((lowerClosure C).lower hx.2 hb.1))
      have hu : x ∉ (upperClosure C : Set P) :=
        fun hh => (inc.mp hb'.1).2 ((upperClosure C).upper hx.2 hh)
      have hnI : x ∉ I := by
        intro hxi
        exact (inc.mp hb'.1).2 ((up b).mpr ⟨mem_upperClosure.mpr ⟨x, hxi, hx.2⟩, hb'.2⟩)
      exact Or.inl ⟨inc.mpr ⟨hd, hu⟩, hnI⟩
  have ceiling_in {c : P} (hc : c ∈ C) : c ∈ J := by
    refine Or.inr ⟨mem_lowerClosure.mpr ⟨c, hc, le_rfl⟩, ?_⟩
    rintro hh
    obtain ⟨m, hm, hcm⟩ := mem_lowerClosure.mp hh
    exact ((up m).mp (mem_upperClosure.mpr ⟨c, hc, hcm⟩)).2 hm.1.1
  have minimal_out {m : P} (hm : Minimal (· ∈ I) m) : m ∉ J := by
    rintro (hj | hj)
    · exact hj.2 hm.1
    · exact hj.2 (mem_lowerClosure.mpr ⟨m, ⟨hm, hj.1⟩, le_rfl⟩)
  have aboveI_down {x : P} (hx : x ∈ J) (hu : x ∈ (upperClosure I : Set P)) :
      x ∈ (lowerClosure C : Set P) := by
    rcases hx with hx | hx
    · exact False.elim ((inc.mp hx.1).2 ((up x).mpr ⟨hu, hx.2⟩))
    · exact hx.1
  constructor
  · intro x hx
    constructor
    · intro hj
      obtain ⟨c, hc, hxc⟩ :=
        mem_lowerClosure.mp (aboveI_down hj (mem_upperClosure.mpr ⟨x, hx, le_rfl⟩))
      have hxc' : x < c := lt_of_le_of_ne hxc (fun h => hc.1.2 (h ▸ hx))
      have hn : ¬ Minimal (· ∈ I) x := fun hm => minimal_out hm hj
      obtain ⟨a, hax, ha⟩ := (not_minimal_iff_exists_lt hx).mp hn
      exact ⟨a, ha, c, ceiling_in hc, hax, hxc'⟩
    · rintro ⟨a, ha, b, hb, hax, hxb⟩
      refine Or.inr ⟨(lowerClosure C).lower hxb.le
        (aboveI_down hb (mem_upperClosure.mpr ⟨x, hx, hxb.le⟩)), ?_⟩
      intro hh
      obtain ⟨m, hm, hxm⟩ := mem_lowerClosure.mp hh
      have hma : m ≤ a := hm.1.2 ha (hax.le.trans hxm)
      exact (not_le_of_gt hax) (hxm.trans hma)
  · intro x hx
    constructor
    · intro hj
      constructor
      · intro a ha z haz hzx
        by_contra hz
        have hzu := (up z).mpr ⟨mem_upperClosure.mpr ⟨a, ha, haz⟩, hz⟩
        have hxu := (upperClosure C).upper hzx.le hzu
        have hxd : x ∈ (lowerClosure C : Set P) := by
          rcases hj with hj | hj
          · exact False.elim ((inc.mp hj.1).2 hxu)
          · exact hj.1
        have hxc := downup hxd hxu
        exact (not_le_of_gt hzx) (hxc.2 ⟨mem_upperClosure.mpr ⟨a, ha, haz⟩, hz⟩ hzx.le)
      · intro b hb z hxz hzb
        exact convex.out hj hb ⟨hxz.le, hzb⟩
    · rintro ⟨hl, hu⟩
      by_contra hj
      have hnup : x ∉ (upperClosure C : Set P) := by
        intro hh
        obtain ⟨c, hc, hcx⟩ := mem_upperClosure.mp hh
        by_cases he : c = x
        · exact hj (he ▸ ceiling_in hc)
        · obtain ⟨a, ha, hac⟩ := mem_upperClosure.mp hc.1.1
          exact hc.1.2 (hl a ha c hac (lt_of_le_of_ne hcx he))
      have hdown : x ∈ (lowerClosure C : Set P) := by
        by_contra hd
        exact hj (Or.inl ⟨inc.mpr ⟨hd, hnup⟩, hx⟩)
      have hh : x ∈ (lowerClosure H : Set P) := by
        by_contra hn
        exact hj (Or.inr ⟨hdown, hn⟩)
      obtain ⟨m, hm, hxm⟩ := mem_lowerClosure.mp hh
      obtain ⟨c, hc, hmc⟩ := mem_lowerClosure.mp hm.2
      have hxm' : x < m := lt_of_le_of_ne hxm (fun he => hx (he ▸ hm.1.1))
      exact minimal_out hm.1 (hu c (ceiling_in hc) m hxm' hmc)

private theorem mixed_cut_flip [Finite P] (I : Set P) (hI : I.OrdConnected)
    (S : Set P) (hS : S.OrdConnected) (x : P)
    (hself : x ∈ S ↔ x ∈ I)
    (hlower : ∀ y, y < x → (y ∈ S ↔ y ∈ I))
    (hupper : ∀ y, x < y → (y ∈ S ↔ y ∈ formula I)) :
    x ∈ toggle x S ↔ x ∈ formula I := by
  classical
  have self_flip : x ∈ S ∆ {x} ↔ x ∉ S := by simp [Set.mem_symmDiff]
  have other (y : P) (hy : y ≠ x) : y ∈ S ∆ {x} ↔ y ∈ S := by
    simp [Set.mem_symmDiff, hy]
  obtain ⟨present, absent⟩ := formula_local I hI
  by_cases hx : x ∈ I
  · have hxs : x ∈ S := hself.mpr hx
    have criterion : (S ∆ {x}).OrdConnected ↔
        ¬ (∃ a ∈ I, ∃ b ∈ formula I, a < x ∧ x < b) := by
      constructor
      · intro hc
        rintro ⟨a, ha, b, hb, hax, hxb⟩
        have ha' := (other a (ne_of_lt hax)).mpr ((hlower a hax).mpr ha)
        have hb' := (other b (ne_of_gt hxb)).mpr ((hupper b hxb).mpr hb)
        exact (self_flip.mp (hc.out ha' hb' ⟨hax.le, hxb.le⟩)) hxs
      · intro hn
        constructor
        intro a ha b hb z hz
        have hax : a ≠ x := fun he => by
          subst a
          exact (self_flip.mp ha) hxs
        have hbx : b ≠ x := fun he => by
          subst b
          exact (self_flip.mp hb) hxs
        have haS := (other a hax).mp ha
        have hbS := (other b hbx).mp hb
        have hzx : z ≠ x := by
          intro he
          subst z
          have hax' : a < x := lt_of_le_of_ne hz.1 hax
          have hxb' : x < b := lt_of_le_of_ne hz.2 (Ne.symm hbx)
          exact hn ⟨a, (hlower a hax').mp haS, b, (hupper b hxb').mp hbS, hax', hxb'⟩
        exact (other z hzx).mpr (hS.out haS hbS hz)
    by_cases hc : (S ∆ {x}).OrdConnected
    · have hn := criterion.mp hc
      have hnj : x ∉ formula I := fun hj => hn ((present x hx).mp hj)
      simp [toggle, hc, self_flip, hxs, hnj]
    · have hj : x ∈ formula I := (present x hx).mpr (by
        by_contra hn
        exact hc (criterion.mpr hn))
      simp [toggle, hc, hxs, hj]
  · have hxs : x ∉ S := fun hs => hx (hself.mp hs)
    have criterion : (S ∆ {x}).OrdConnected ↔
        lowerFilled I x ∧ upperFilled (formula I) x := by
      constructor
      · intro hc
        constructor
        · intro a ha z haz hzx
          have hax := lt_of_le_of_lt haz hzx
          have ha' := (other a (ne_of_lt hax)).mpr ((hlower a hax).mpr ha)
          have hz' := hc.out ha' (self_flip.mpr hxs) ⟨haz, hzx.le⟩
          exact (hlower z hzx).mp ((other z (ne_of_lt hzx)).mp hz')
        · intro b hb z hxz hzb
          have hxb := lt_of_lt_of_le hxz hzb
          have hb' := (other b (ne_of_gt hxb)).mpr ((hupper b hxb).mpr hb)
          have hz' := hc.out (self_flip.mpr hxs) hb' ⟨hxz.le, hzb⟩
          exact (hupper z hxz).mp ((other z (ne_of_gt hxz)).mp hz')
      · rintro ⟨hl, hu⟩
        constructor
        intro a ha b hb z hz
        by_cases hzx : z = x
        · subst z
          exact self_flip.mpr hxs
        apply (other z hzx).mpr
        by_cases hax : a = x
        · subst a
          have hxz := lt_of_le_of_ne hz.1 (Ne.symm hzx)
          have hxb := lt_of_lt_of_le hxz hz.2
          have hbS := (other b (ne_of_gt hxb)).mp hb
          exact (hupper z hxz).mpr (hu b ((hupper b hxb).mp hbS) z hxz hz.2)
        · have haS := (other a hax).mp ha
          by_cases hbx : b = x
          · subst b
            have hzx' := lt_of_le_of_ne hz.2 hzx
            have hax' := lt_of_le_of_lt hz.1 hzx'
            exact (hlower z hzx').mpr (hl a ((hlower a hax').mp haS) z hz.1 hzx')
          · exact hS.out haS ((other b hbx).mp hb) hz
    by_cases hc : (S ∆ {x}).OrdConnected
    · have hj := (absent x hx).mpr (criterion.mp hc)
      simp [toggle, hc, self_flip, hxs, hj]
    · have hnj : x ∉ formula I := fun hj => hc (criterion.mpr ((absent x hx).mp hj))
      simp [toggle, hc, hxs, hnj]

/-- Every complete reverse extension gives the same explicit ceiling formula,
without excluding the empty enumeration or any empty boundary. -/
theorem trace_eq_formula {N : ℕ} (e : Fin N ≃ P) (he : ReverseExtension e)
    (I : Set P) (hI : I.OrdConnected) : trace e I N = formula I := by
  classical
  let _ : Fintype P := Fintype.ofEquiv (Fin N) e
  let idx : P → ℕ := fun x => (e.symm x).val
  have inv : ∀ k, (trace e I k).OrdConnected ∧
      ∀ x, x ∈ trace e I k ↔ if idx x < k then x ∈ formula I else x ∈ I := by
    intro k
    induction k with
    | zero => exact ⟨hI, by intro x; simp [trace]⟩
    | succ k ih =>
      by_cases hk : k < N
      · let x : P := e ⟨k, hk⟩
        have hidx : idx x = k := by simp [idx, x]
        have hs : x ∈ trace e I k ↔ x ∈ I := by simpa [hidx] using ih.2 x
        have hl : ∀ y, y < x → (y ∈ trace e I k ↔ y ∈ I) := by
          intro y hy
          have hh : k < idx y := by
            have horder : idx x < idx y := he y x hy
            rwa [hidx] at horder
          simpa [show ¬ idx y < k by omega] using ih.2 y
        have hu : ∀ y, x < y → (y ∈ trace e I k ↔ y ∈ formula I) := by
          intro y hy
          have hh : idx y < k := by
            have horder : idx y < idx x := he x y hy
            rwa [hidx] at horder
          simpa [hh] using ih.2 y
        have flip := mixed_cut_flip I hI (trace e I k) ih.1 x hs hl hu
        have hc : (toggle x (trace e I k)).OrdConnected := by
          unfold toggle
          split
          · assumption
          · exact ih.1
        refine ⟨by simpa only [trace, dite_eq_left hk] using hc, ?_⟩
        intro y
        by_cases hy : y = x
        · subst y
          simpa only [trace, dite_eq_left hk, hidx, Nat.lt_succ_self, ↓reduceIte] using flip
        · have hne : idx y ≠ k := by
            intro hh
            apply hy
            apply e.symm.injective
            apply Fin.ext
            exact hh.trans hidx.symm
          have other : y ∈ toggle x (trace e I k) ↔ y ∈ trace e I k := by
            unfold toggle
            split <;> simp [Set.mem_symmDiff, hy]
          have order : (idx y < k + 1) = (idx y < k) := propext (by omega)
          simpa only [trace, dite_eq_left hk, order] using other.trans (ih.2 y)
      · have stable : trace e I (k + 1) = trace e I k := by simp only [trace, dite_eq_right hk]
        refine ⟨stable ▸ ih.1, ?_⟩
        intro x
        have hi : idx x < N := (e.symm x).isLt
        have h0 : idx x < k := by omega
        have h1 : idx x < k + 1 := by omega
        simpa only [stable, ite_eq_left h0, ite_eq_left h1] using ih.2 x
  apply Set.ext
  intro x
  have hi : idx x < N := (e.symm x).isLt
  simpa only [ite_eq_left hi] using (inv N).2 x

#print axioms trace_eq_formula

end D5.S3.Combinatorics.Geometry.RowmotionGlobalFormula

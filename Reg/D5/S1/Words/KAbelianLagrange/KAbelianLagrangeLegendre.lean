/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeLegendre
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeLegendre
   mirror-E: none(waiver:asymptotic-legendre-supplier)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Source-bound scalar readouts register both approximation limsup comparisons. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeLegendre
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIrrational
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeBounded
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange Filter
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeLegendre
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev upperArena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, Irrational x →
    limsup (fun q : ℕ => R.readout () ()
      (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop ≤
      max 2 (limsup (fun n : ℕ => ENNReal.ofReal
        (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop)

abbrev lowerArena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, Irrational x →
    limsup (fun n : ℕ => R.readout () ()
      (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop ≤
      limsup (fun q : ℕ => ENNReal.ofReal
        (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop

def upperRegistration : Registration upperArena (upperArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ upperArena.Law bad := by
      let g : GenContFract ℝ := ⟨0, Stream'.Seq.ofStream (fun _ => ⟨1, ((1 : ℕ) : ℝ)⟩)⟩
      have hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, rfl⟩
      obtain ⟨x, hx, _hp, _hl, _ht, hxc⟩ := integer_stream_value g rfl hg
      have hA : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 1 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, le_rfl, rfl⟩
      have hsep := (bounded_stream_separation g rfl 1 hA x hxc).2
      have hbound : ∀ n : ℕ, ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|)) ≤ 12 := by
        intro n
        let r := x.convergent n
        have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
        have he : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
        apply (ENNReal.ofReal_le_ofNat).mpr
        apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) he)).mpr
        have hs : 1 / (12 * (r.den : ℝ) ^ 2) ≤ |x - (r : ℝ)| := by
          convert hsep r using 1; norm_num
        have h := (div_le_iff₀ (by positivity : 0 < 12 * (r.den : ℝ) ^ 2)).mp hs
        nlinarith
      have hb := limsup_le_of_le (f := atTop) (by isBoundedDefault)
        (Eventually.of_forall hbound)
      intro h
      have ht : (⊤ : ℝ≥0∞) ≤ max 2 (limsup (fun n : ℕ => ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop) := by
        simpa [bad, realize] using h x hx
      have : (⊤ : ℝ≥0∞) ≤ 12 := ht.trans (max_le (by norm_num) hb)
      norm_num at this
    exact ⟨lagrange_limsup_upper, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ upperArena.Law bad := by
      let g : GenContFract ℝ := ⟨0, Stream'.Seq.ofStream (fun _ => ⟨1, ((1 : ℕ) : ℝ)⟩)⟩
      have hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, rfl⟩
      obtain ⟨x, hx, _hp, _hl, _ht, hxc⟩ := integer_stream_value g rfl hg
      have hA : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 1 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, le_rfl, rfl⟩
      have hsep := (bounded_stream_separation g rfl 1 hA x hxc).2
      have hbound : ∀ n : ℕ, ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|)) ≤ 12 := by
        intro n
        let r := x.convergent n
        have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
        have he : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
        apply (ENNReal.ofReal_le_ofNat).mpr
        apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) he)).mpr
        have hs : 1 / (12 * (r.den : ℝ) ^ 2) ≤ |x - (r : ℝ)| := by
          convert hsep r using 1; norm_num
        have h := (div_le_iff₀ (by positivity : 0 < 12 * (r.den : ℝ) ^ 2)).mp hs
        nlinarith
      have hb := limsup_le_of_le (f := atTop) (by isBoundedDefault)
        (Eventually.of_forall hbound)
      intro h
      have ht : (⊤ : ℝ≥0∞) ≤ max 2 (limsup (fun n : ℕ => ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop) := by
        simpa [bad, realize] using h x hx
      have : (⊤ : ℝ≥0∞) ≤ 12 := ht.trans (max_le (by norm_num) hb)
      norm_num at this
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def lowerRegistration : Registration lowerArena (lowerArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ lowerArena.Law bad := by
      let g : GenContFract ℝ := ⟨0, Stream'.Seq.ofStream (fun _ => ⟨1, ((1 : ℕ) : ℝ)⟩)⟩
      have hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, rfl⟩
      obtain ⟨x, hx, _hp, _hl, _ht, hxc⟩ := integer_stream_value g rfl hg
      have hA : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 1 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, le_rfl, rfl⟩
      have hsep := (bounded_stream_separation g rfl 1 hA x hxc).2
      have hbound : ∀ n : ℕ, ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|)) ≤ 12 := by
        intro n
        let r := x.convergent n
        have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
        have he : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
        apply (ENNReal.ofReal_le_ofNat).mpr
        apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) he)).mpr
        have hs : 1 / (12 * (r.den : ℝ) ^ 2) ≤ |x - (r : ℝ)| := by
          convert hsep r using 1; norm_num
        have h := (div_le_iff₀ (by positivity : 0 < 12 * (r.den : ℝ) ^ 2)).mp hs
        nlinarith
      have hb := limsup_le_of_le (f := atTop) (by isBoundedDefault)
        (Eventually.of_forall hbound)
      intro h
      have ht : (⊤ : ℝ≥0∞) ≤ limsup (fun q : ℕ => ENNReal.ofReal
          (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop := by
        simpa [bad, realize] using h x hx
      have : (⊤ : ℝ≥0∞) ≤ 12 := ht.trans
        ((lagrange_limsup_upper x hx).trans (max_le (by norm_num) hb))
      norm_num at this
    exact ⟨lagrange_limsup_lower, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ lowerArena.Law bad := by
      let g : GenContFract ℝ := ⟨0, Stream'.Seq.ofStream (fun _ => ⟨1, ((1 : ℕ) : ℝ)⟩)⟩
      have hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, rfl⟩
      obtain ⟨x, hx, _hp, _hl, _ht, hxc⟩ := integer_stream_value g rfl hg
      have hA : ∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ 1 ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩ :=
        fun _ => ⟨1, by norm_num, le_rfl, rfl⟩
      have hsep := (bounded_stream_separation g rfl 1 hA x hxc).2
      have hbound : ∀ n : ℕ, ENNReal.ofReal
          (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|)) ≤ 12 := by
        intro n
        let r := x.convergent n
        have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
        have he : 0 < |x - (r : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r))
        apply (ENNReal.ofReal_le_ofNat).mpr
        apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) he)).mpr
        have hs : 1 / (12 * (r.den : ℝ) ^ 2) ≤ |x - (r : ℝ)| := by
          convert hsep r using 1; norm_num
        have h := (div_le_iff₀ (by positivity : 0 < 12 * (r.den : ℝ) ^ 2)).mp hs
        nlinarith
      have hb := limsup_le_of_le (f := atTop) (by isBoundedDefault)
        (Eventually.of_forall hbound)
      intro h
      have ht : (⊤ : ℝ≥0∞) ≤ limsup (fun q : ℕ => ENNReal.ofReal
          (1 / ((q : ℝ) * |(q : ℝ) * x - (round ((q : ℝ) * x) : ℝ)|))) atTop := by
        simpa [bad, realize] using h x hx
      have : (⊤ : ℝ≥0∞) ≤ 12 := ht.trans
        ((lagrange_limsup_upper x hx).trans (max_le (by norm_num) hb))
      norm_num at this
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeLegendre
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "fn", "arg",
    "fn", "arg", "body", "fn"], functionOperand := true }] }

register_information_theorem lagrange_limsup_upper in upperArena
  readout via (realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e))
  realizes upperRegistration
  escape from source (selection)
  escape continues (open)

register_information_theorem lagrange_limsup_lower in lowerArena
  readout via (realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e))
  realizes lowerRegistration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeLegendre

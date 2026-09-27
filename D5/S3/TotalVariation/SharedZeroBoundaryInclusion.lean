/- GID: D5/S3/TotalVariation/SharedZeroBoundaryInclusion
   generality: I
   mirror-B: D5/B/S3/TotalVariation/SharedZeroBoundaryInclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.MinMax]
   utility: none
   digest: Every shared longest-zero-run defect meets an actual window boundary event. -/

import D5.S3.TotalVariation.ParrySharedZeroRule

namespace D5.S3.TotalVariation.SharedZeroBoundaryInclusion

open D5.S3.TotalVariation.ParrySharedZeroRule
open D5.S3.ObserverMemory.Trajectories.LongestZeroSelectorResponse
open D5.S3.ObserverMemory.Trajectories.ZeroRunWordGeometry

set_option autoImplicit false

/-- For arbitrary binary windows, a defect of the original length/latest-endpoint
selector requires an exiting old winner, an entering new winner, or no new winner.
Transport starts strictly after the selected closing one. -/
theorem shared_rule_defect_boundary_inclusion (R : ℕ) (w : Fin (R + 1) → Bool) :
    let old := fun i : Fin R => w i.castSucc
    let new := fun i : Fin R => w i.succ
    xor (xor (sharedRule R new) (sharedRule R old)) (!(w (Fin.last R))) = true →
      (∃ c, selected (windowOnes old) R R = some c ∧ c.1 = 0) ∨
      (∃ c, selected (windowOnes new) R R = some c ∧ c.2 = R - 1) ∨
      selected (windowOnes new) R R = none := by
  classical
  dsimp only
  let old : Fin R → Bool := fun i => w i.castSucc
  let new : Fin R → Bool := fun i => w i.succ
  change xor (xor (sharedRule R new) (sharedRule R old)) (!(w (Fin.last R))) = true → _
  intro hdef
  by_contra hboundary
  have hnoOld : ∀ c, selected (windowOnes old) R R = some c → c.1 ≠ 0 := by
    intro c hc hz
    exact hboundary (Or.inl ⟨c, hc, hz⟩)
  have hnoNew : ∀ c, selected (windowOnes new) R R = some c → c.2 ≠ R - 1 := by
    intro c hc hz
    exact hboundary (Or.inr (Or.inl ⟨c, hc, hz⟩))
  have hnonempty : selected (windowOnes new) R R ≠ none := by
    intro he
    exact hboundary (Or.inr (Or.inr he))
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hnonempty
  have hdmem : d ∈ candidates (windowOnes new) R R :=
    Finset.mem_toList.mp (List.argmax_mem (show d ∈
      (candidates (windowOnes new) R R).toList.argmax (score R) from hd))
  have hcan (s : Finset ℕ) (a b : ℕ) :
      (a, b) ∈ candidates s R R ↔ a < R ∧ b < R ∧ Complete s a b := by
    simp [candidates, Finset.mem_product, and_assoc]
  obtain ⟨hda, hdb, hdlen, hdopen, hdclose, hdzero⟩ := (hcan _ _ _).mp hdmem
  have hdaway := hnoNew d hd
  have hdbound : d.2 + 1 < R := by omega
  have hmem {n : ℕ} (v : Fin n → Bool) (x : ℕ) (hx : x < n) :
      x ∈ windowOnes v ↔ v ⟨x, hx⟩ = true := by
    simp only [windowOnes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, he⟩
      have hie : i = ⟨x, hx⟩ := Fin.ext he
      simpa [hie] using hi
    · intro hi
      exact ⟨⟨x, hx⟩, hi, rfl⟩
  have hover (x : ℕ) (hx : x + 1 < R) :
      x ∈ windowOnes new ↔ x + 1 ∈ windowOnes old := by
    rw [hmem _ _ (by omega), hmem _ _ hx]
    rfl
  -- A new candidate whose closing one is not entering was already complete.
  have hdold : (d.1 + 1, d.2 + 1) ∈ candidates (windowOnes old) R R := by
    apply (hcan _ _ _).mpr
    refine ⟨by omega, hdbound, by omega,
      (hover _ (by omega)).mp hdopen, (hover _ hdbound).mp hdclose, ?_⟩
    intro x hx hxb hxm
    have hxp : x - 1 + 1 = x := by omega
    apply hdzero (x - 1) (by omega) (by omega)
    apply (hover (x - 1) (by omega)).mpr
    simpa only [hxp] using hxm
  have holdnonempty : selected (windowOnes old) R R ≠ none := by
    intro he
    have he' := List.argmax_eq_none.mp he
    have hm := Finset.mem_toList.mpr hdold
    rw [he'] at hm
    exact List.not_mem_nil hm
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp holdnonempty
  have hcmem : c ∈ candidates (windowOnes old) R R :=
    Finset.mem_toList.mp (List.argmax_mem (show c ∈
      (candidates (windowOnes old) R R).toList.argmax (score R) from hc))
  obtain ⟨hca, hcb, hclen, hcopen, hcclose, hczero⟩ := (hcan _ _ _).mp hcmem
  have hcaway := hnoOld c hc
  have hcap : c.1 - 1 + 1 = c.1 := by omega
  have hcbp : c.2 - 1 + 1 = c.2 := by omega
  -- An old candidate whose opening one survives is complete in the new window.
  have hcnew : (c.1 - 1, c.2 - 1) ∈ candidates (windowOnes new) R R := by
    apply (hcan _ _ _).mpr
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · apply (hover _ (by omega)).mpr
      simpa only [hcap] using hcopen
    · apply (hover _ (by omega)).mpr
      simpa only [hcbp] using hcclose
    · intro x hx hxb hxm
      exact hczero (x + 1) (by omega) (by omega)
        ((hover x (by omega)).mp hxm)
  have hmaxOld : score R (d.1 + 1, d.2 + 1) ≤ score R c :=
    List.le_of_mem_argmax (Finset.mem_toList.mpr hdold) hc
  have hmaxNew : score R (c.1 - 1, c.2 - 1) ≤ score R d :=
    List.le_of_mem_argmax (Finset.mem_toList.mpr hcnew) hd
  have hlenShiftOld : (d.2 + 1) - (d.1 + 1) - 1 = d.2 - d.1 - 1 := by omega
  have hlenShiftNew : (c.2 - 1) - (c.1 - 1) - 1 = c.2 - c.1 - 1 := by omega
  simp only [score, hlenShiftOld, hlenShiftNew] at hmaxOld hmaxNew
  have hscoreEq : (c.2 - c.1 - 1) * (R + 1) + c.2 =
      (d.2 - d.1 - 1) * (R + 1) + d.2 + 1 := by omega
  have hlength : c.2 - c.1 - 1 = d.2 - d.1 - 1 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hm := Nat.mul_le_mul_right (R + 1) hlt
      nlinarith
    · have hm := Nat.mul_le_mul_right (R + 1) hgt
      nlinarith
  have hcloseEq : c.2 = d.2 + 1 := by rw [hlength] at hscoreEq; omega
  have hopenEq : c.1 = d.1 + 1 := by omega
  -- The strict suffixes correspond under x ↦ x+1, with only the last bit added.
  let zsOld := (Finset.Ioo c.2 R).filter (fun x => x ∉ windowOnes old)
  let zsNew := (Finset.Ioo d.2 R).filter (fun x => x ∉ windowOnes new)
  let zsCommon := (Finset.Ioo d.2 (R - 1)).filter (fun x => x ∉ windowOnes new)
  have hcard : zsCommon.card = zsOld.card := by
    apply Finset.card_bij (fun x _ => x + 1)
    · intro x hx
      simp only [zsCommon, Finset.mem_filter, Finset.mem_Ioo] at hx
      simp only [zsOld, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨by omega, by omega⟩, fun hm => hx.2 ((hover x (by omega)).mpr hm)⟩
    · intro x hx y hy he
      omega
    · intro y hy
      simp only [zsOld, Finset.mem_filter, Finset.mem_Ioo] at hy
      refine ⟨y - 1, ?_, by omega⟩
      simp only [zsCommon, Finset.mem_filter, Finset.mem_Ioo]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hm
      have he := (hover (y - 1) (by omega)).mp hm
      have hyp : y - 1 + 1 = y := by omega
      exact hy.2 (by simpa only [hyp] using he)
  have hlast : (R - 1 ∈ windowOnes new) ↔ w (Fin.last R) = true := by
    rw [hmem _ _ (by omega)]
    have he : (⟨R - 1, by omega⟩ : Fin R).succ = Fin.last R := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    change w _ = true ↔ _
    rw [he]
  have hsplit : zsNew = zsCommon ∪
      (if w (Fin.last R) = true then ∅ else {R - 1}) := by
    ext x
    simp only [zsNew, zsCommon, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioo]
    by_cases hb : w (Fin.last R) = true
    · rw [if_pos hb]
      simp only [Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨⟨hlo, hhi⟩, hz⟩
        refine ⟨⟨hlo, ?_⟩, hz⟩
        have hne : x ≠ R - 1 := by
          intro he
          subst x
          exact hz (hlast.mpr hb)
        omega
      · rintro ⟨⟨hlo, hhi⟩, hz⟩
        exact ⟨⟨hlo, by omega⟩, hz⟩
    · rw [if_neg hb]
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hlo, hhi⟩, hz⟩
        by_cases he : x = R - 1
        · exact Or.inr he
        · exact Or.inl ⟨⟨hlo, by omega⟩, hz⟩
      · rintro (⟨⟨hlo, hhi⟩, hz⟩ | rfl)
        · exact ⟨⟨hlo, by omega⟩, hz⟩
        · exact ⟨⟨by omega, by omega⟩, fun hm => hb (hlast.mp hm)⟩
  have hnot : R - 1 ∉ zsCommon := by simp [zsCommon]
  have hcount : zsNew.card = zsOld.card + if w (Fin.last R) = true then 0 else 1 := by
    rw [hsplit]
    by_cases hb : w (Fin.last R) = true
    · simp [hb, hcard]
    · rw [if_neg hb, if_neg hb, Finset.union_singleton,
        Finset.card_insert_of_notMem hnot, hcard]
  have hdirOld : direction (windowOnes old) R R = zsOld.card % 2 := by
    simp only [direction, hc, transport, zsOld]
  have hdirNew : direction (windowOnes new) R R = zsNew.card % 2 := by
    simp only [direction, hd, transport, zsNew]
  simp only [sharedRule, hdirOld, hdirNew] at hdef
  have hp : zsOld.card % 2 < 2 := Nat.mod_lt _ (by omega)
  cases hb : w (Fin.last R) <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hcount
  · have he : zsNew.card % 2 = (zsOld.card + 1) % 2 := by rw [hcount]
    rw [he] at hdef
    have hcases : zsOld.card % 2 = 0 ∨ zsOld.card % 2 = 1 := by omega
    rcases hcases with hzero | hone
    · have he' : (zsOld.card + 1) % 2 = 1 := by omega
      simp [hb, hzero, he'] at hdef
    · have he' : (zsOld.card + 1) % 2 = 0 := by omega
      simp [hb, hone, he'] at hdef
  · have he : zsNew.card = zsOld.card := by omega
    simp [he, hb] at hdef

end D5.S3.TotalVariation.SharedZeroBoundaryInclusion

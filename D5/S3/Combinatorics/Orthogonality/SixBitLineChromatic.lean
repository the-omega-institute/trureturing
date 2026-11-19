/- GID: D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitLineChromatic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.result; instance=D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check
   digest: Complete six-bit line graph weighted independence bound and exact twelve-color witness. -/

import D5.S3.Combinatorics.Orthogonality.SixBitCatalogue
import D5.S3.Combinatorics.Orthogonality.WeightedIndependentBound

/-! The independent question is O2 of the received PR1 manuscript, lines.tex.
All 63 nonzero masks are used. The include-or-omit checker supplies a current
kernel route to the complete weighted inequality, with no graph samples.
The twelve classes are the original literal source witness, unchanged. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.Orthogonality.SixBitLineChromatic

open BinaryOrthogonality
open WeightedIndependentBound

abbrev LineVertex := {v : Vector // v ≠ 0}

def lineGraph : SimpleGraph LineVertex where
  Adj x y := x ≠ y ∧ dot x.1 y.1 = 0
  symm := ⟨fun x y h => ⟨h.1.symm, (dot_symm y.1 x.1).trans h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def compatible (x y : Vector) : Bool := decide (dot x y ≠ 0)
def weight (x : Vector) : ℕ := if dot x x = 0 then 3 else 4
def allLines : List Vector := (List.finRange 64).filter (fun v => v ≠ 0)

theorem weight_check : bound weight compatible 63 allLines = 19 := by decide +kernel

private theorem even_check :
    bound (fun _ : Vector => 1) compatible 63
      (allLines.filter (fun v => dot v v = 0)) = 5 := by decide +kernel

/-- The universal complete-domain weighted bound. The hypotheses express
precisely a nonzero independent set of the actual six-bit line graph. -/
theorem weighted_bound (S : Finset Vector) (hz : 0 ∉ S)
    (hi : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dot x y ≠ 0) :
    ∑ x ∈ S, weight x ≤ 19 := by
  rw [← weight_check]
  apply sound
  · decide +kernel
  · intro x hx
    have hne : x ≠ 0 := fun h => hz (h ▸ hx)
    simpa [allLines] using hne
  · intro x hx y hy hxy
    simpa [compatible] using hi x hx y hy hxy

/-- The complete parity profile, including the extremal size-six condition. -/
theorem independence_profile (S : Finset Vector) (hz : 0 ∉ S)
    (hi : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dot x y ≠ 0) :
    let t := (S.filter (fun x => dot x x = 0)).card
    let o := (S.filter (fun x => dot x x ≠ 0)).card
    3 * t + 4 * o ≤ 19 ∧ S.card ≤ 6 ∧ (S.card = 6 → t = 5 ∧ o = 1) := by
  classical
  dsimp only
  let t := (S.filter (fun x => dot x x = 0)).card
  let o := (S.filter (fun x => dot x x ≠ 0)).card
  have hp : t + o = S.card := by
    exact Finset.card_filter_add_card_filter_not (s := S) (fun x => dot x x = 0)
  have hw : 3 * t + 4 * o ≤ 19 := by
    have h := weighted_bound S hz hi
    simpa [weight, Finset.sum_ite, t, o, Nat.mul_comm] using h
  have ht : t ≤ 5 := by
    have h := sound (fun _ : Vector => 1) compatible 63
      (allLines.filter (fun v => dot v v = 0)) (by decide +kernel)
      (S.filter (fun x => dot x x = 0)) (by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        have hne : x ≠ 0 := fun h => hz (h ▸ hx'.1)
        simp [allLines, hne, hx'.2]) (by
        intro x hx y hy hxy
        simpa [compatible] using hi x (Finset.mem_filter.mp hx).1
          y (Finset.mem_filter.mp hy).1 hxy)
    rw [even_check] at h
    simpa [t] using h
  change 3 * t + 4 * o ≤ 19 ∧ S.card ≤ 6 ∧
    (S.card = 6 → t = 5 ∧ o = 1)
  omega

/-- The source's exact upper-bound partition, with the original mask order. -/
def classes : Array (List Vector) := #[
  [8,13,29,42,47], [2,26,38,62,63], [20,37,39,45,48],
  [6,11,18,34,53,60], [15,30,46,49,59], [32,40,50,51,54],
  [14,19,24,41,52], [12,27,43,55,57,58], [4,7,28,31,36],
  [16,21,23,56,61], [10,22,25,35,44], [1,3,5,9,17,33]]

def color (v : Vector) : Fin 12 :=
  ((List.finRange 12).find? (fun i => v ∈ classes[i.val]!)).getD 0

private theorem color_check : ∀ x y : Vector,
    x ≠ 0 → y ≠ 0 → x ≠ y → dot x y = 0 → color x ≠ color y := by decide +kernel

private theorem total_weight : ∑ x : LineVertex, weight x.1 = 221 := by decide +kernel

/-- The original twelve classes give a coloring of every nonzero vector. -/
def twelveColoring : lineGraph.Coloring (Fin 12) :=
  SimpleGraph.Coloring.mk (fun x => color x.1) (fun {x y} h =>
    color_check x.1 y.1 x.2 y.2 (fun he => h.1 (Subtype.ext he)) h.2)

/-- Every color class has weight at most nineteen, so all colorings need
at least twelve labels. This consumes the complete weighted certificate. -/
theorem coloring_lower_bound (k : ℕ) (C : lineGraph.Coloring (Fin k)) : 12 ≤ k := by
  classical
  let T (c : Fin k) : Finset LineVertex := Finset.univ.filter (fun x => C x = c)
  have hb (c : Fin k) : ∑ x ∈ T c, weight x.1 ≤ 19 := by
    have hz : 0 ∉ (T c).image Subtype.val := by
      rintro h
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
      exact x.2 he
    have hi : ∀ x ∈ (T c).image Subtype.val,
        ∀ y ∈ (T c).image Subtype.val, x ≠ y → dot x y ≠ 0 := by
      intro x hx y hy hxy hd
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have he : C u = C v := (Finset.mem_filter.mp hu).2.trans
        (Finset.mem_filter.mp hv).2.symm
      exact C.valid ⟨fun h => hxy (congrArg Subtype.val h), hd⟩ he
    have h := weighted_bound ((T c).image Subtype.val) hz hi
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at h
    exact h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hb c)
  have hf := Finset.sum_fiberwise (Finset.univ : Finset LineVertex) C
    (fun x => weight x.1)
  change (∑ c : Fin k, ∑ x ∈ T c, weight x.1) = ∑ x : LineVertex, weight x.1 at hf
  rw [hf, total_weight] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  omega

/-- Exact chromatic number of the complete received six-bit line graph.
The following representation bridge transfers it to coordinate lines. -/
theorem result : lineGraph.chromaticNumber = 12 := by
  apply le_antisymm
  · exact (show lineGraph.Colorable 12 from ⟨twelveColoring⟩).chromaticNumber_le
  · exact SimpleGraph.le_chromaticNumber_iff_colorable.mpr (fun k ⟨C⟩ =>
      coloring_lower_bound k C)

#print axioms weighted_bound
#print axioms result

end D5.S3.Combinatorics.Orthogonality.SixBitLineChromatic

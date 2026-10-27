/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuFamilies
   mirror-E: none(waiver:finite-family-bijection)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: The literal triangular count equals its bounded ordered-edge count. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuClosure

/-! The counted source bridge preserves the entire finite family and first column. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

/-- Strict ordered edges on the vertices 0 through n+1. -/
def edgeTriangle (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 2)).product (Finset.range (n + 2))).filter
    (fun p => p.1 < p.2)

/-- Shift the second coordinate up by one. -/
def edgeSet (Y : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  Y.image (fun p => (p.1, p.2 + 1))

/-- Shift the second coordinate down by one. -/
def pointSet (A : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  A.image (fun p => (p.1, p.2 - 1))

/-- The bounded edge family, with the same first-column statistic. -/
noncomputable def edgeFamily (n k : ℕ) : Finset (Finset (ℕ × ℕ)) := by
  classical
  exact (edgeTriangle n).powerset.filter
    (fun A => Rules (fun a b => (a, b) ∈ A) ∧ firstColumnCard A = k)

private theorem shift_injective :
    Function.Injective (fun p : ℕ × ℕ => (p.1, p.2 + 1)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have : b = d := by omega
  subst d
  rfl

private theorem mem_edgeTriangle {n a b : ℕ} :
    (a, b) ∈ edgeTriangle n ↔ a < b ∧ b ≤ n + 1 := by
  simp [edgeTriangle]
  omega

private theorem pointSet_edgeSet (Y : Finset (ℕ × ℕ)) : pointSet (edgeSet Y) = Y := by
  simp [pointSet, edgeSet, Finset.image_image, Function.comp_def]

private theorem edgeSet_pointSet {A : Finset (ℕ × ℕ)}
    (hA : ∀ {a b}, (a, b) ∈ A → a < b) : edgeSet (pointSet A) = A := by
  unfold edgeSet pointSet
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := A)]
  apply Finset.image_congr
  rintro ⟨a, b⟩ hp
  simp only [Function.comp_apply, Prod.mk.injEq, true_and, id_eq]
  have := hA hp
  omega

private theorem firstColumnCard_edgeSet (Y : Finset (ℕ × ℕ)) :
    firstColumnCard (edgeSet Y) = firstColumnCard Y := by
  unfold firstColumnCard edgeSet
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ shift_injective

private theorem pointEdges_eq_edgeSet {Y : Finset (ℕ × ℕ)}
    (hY : ∀ {a b}, (a, b) ∈ Y → a ≤ b) :
    pointEdges Y = fun a b => (a, b) ∈ edgeSet Y := by
  funext a b
  apply propext
  constructor
  · rintro ⟨hab, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨(a, b - 1), hp, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    omega
  · intro hp
    obtain ⟨⟨c, d⟩, hcd, heq⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨by have := hY hcd; omega, by simpa using hcd⟩

private theorem edgeSet_mem {n k : ℕ} {Y : Finset (ℕ × ℕ)}
    (hY : Y ∈ family n k) : edgeSet Y ∈ edgeFamily n k := by
  classical
  obtain ⟨hbound, hrules, hk⟩ := mem_family_iff.mp hY
  have horder : ∀ {a b}, (a, b) ∈ Y → a ≤ b :=
    fun hp => (mem_triangle.mp (hbound hp)).1
  have hsubset : edgeSet Y ⊆ edgeTriangle n := by
    intro p hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
    apply mem_edgeTriangle.mpr
    have := mem_triangle.mp (hbound hab)
    omega
  have hrules' : Rules (fun a b => (a, b) ∈ edgeSet Y) := by
    rw [← pointEdges_eq_edgeSet horder]
    exact hrules
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsubset,
    hrules', (firstColumnCard_edgeSet Y).trans hk⟩

private theorem pointSet_mem {n k : ℕ} {A : Finset (ℕ × ℕ)}
    (hA : A ∈ edgeFamily n k) : pointSet A ∈ family n k := by
  classical
  obtain ⟨hbound, hrules, hk⟩ := Finset.mem_filter.mp hA
  have hsubset := Finset.mem_powerset.mp hbound
  have horder : ∀ {a b}, (a, b) ∈ A → a < b := fun hp =>
    (mem_edgeTriangle.mp (hsubset hp)).1
  have hpointsubset : pointSet A ⊆ triangle n := by
    intro p hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
    apply mem_triangle.mpr
    have := mem_edgeTriangle.mp (hsubset hab)
    omega
  have hpointorder : ∀ {a b}, (a, b) ∈ pointSet A → a ≤ b := fun hp =>
    (mem_triangle.mp (hpointsubset hp)).1
  have hback := edgeSet_pointSet horder
  apply mem_family_iff.mpr
  refine ⟨hpointsubset, ?_, ?_⟩
  · rw [pointEdges_eq_edgeSet hpointorder, hback]
    exact hrules
  · rw [← firstColumnCard_edgeSet, hback]
    exact hk

/-- Exact cardinal equivalence with the literal finite source, for every n and k. -/
theorem count_eq_edgeFamily_card (n k : ℕ) : count n k = (edgeFamily n k).card := by
  classical
  unfold count
  apply Finset.card_bij (fun Y _ => edgeSet Y)
  · intro Y hY
    exact edgeSet_mem hY
  · intro Y hY Z hZ heq
    have := congrArg pointSet heq
    simpa only [pointSet_edgeSet] using this
  · intro A hA
    refine ⟨pointSet A, pointSet_mem hA, ?_⟩
    exact edgeSet_pointSet (fun hp =>
      (mem_edgeTriangle.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1) hp)).1)

end D5.S3.Combinatorics.MazorchukXu

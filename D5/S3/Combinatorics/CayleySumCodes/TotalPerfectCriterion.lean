/- GID: D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-case total perfect subgroup code criterion for loopless Cayley sum graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Complement

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

/-- A normal subset is conjugation invariant; inverse closure is not required. -/
def NormalSubset (Y : Set G) : Prop :=
  ∀ a x : G, x ∈ Y → a * x * a⁻¹ ∈ Y

/-- The simple sum graph. Equality is excluded even when the square belongs to Y. -/
def sumGraph (Y : Set G) (hY : NormalSubset Y) : SimpleGraph G where
  Adj g h := g ≠ h ∧ g * h ∈ Y
  symm := ⟨by
    intro g h he
    refine ⟨he.1.symm, ?_⟩
    simpa [mul_assoc] using hY g⁻¹ (g * h) he.2⟩
  loopless := ⟨fun g he => he.1 rfl⟩

/-- Exactly one open neighbor in C at every vertex, including vertices of C. -/
def IsTotalPerfectCode (graph : SimpleGraph G) (C : Set G) : Prop :=
  ∀ g : G, ∃! h : G, h ∈ C ∧ graph.Adj g h

/-- Squares of elements of H, as a subset of the ambient group. -/
def squares (H : Subgroup G) : Set G := {z | ∃ h : G, h ∈ H ∧ h * h = z}

private noncomputable def slice [Fintype G] (H : Subgroup G) (Y : Set G) (g : G) :
    Finset G := by
  classical
  exact Finset.univ.filter (fun y => y ∈ Y ∧ g⁻¹ * y ∈ H)

private theorem mem_slice [Fintype G] (H : Subgroup G) (Y : Set G) (g y : G) :
    y ∈ slice H Y g ↔ y ∈ Y ∧ g⁻¹ * y ∈ H := by
  classical
  simp [slice]

private theorem slice_at_member [Fintype G] (H : Subgroup G) (Y : Set G)
    (g : G) (hg : g ∈ H) : slice H Y g = slice H Y 1 := by
  classical
  ext y
  simp only [mem_slice, inv_one, one_mul]
  rw [H.mul_mem_cancel_left (H.inv_mem hg)]

private theorem square_notMem_slice [Fintype G] (H : Subgroup G) (Y : Set G)
    (g : G) (hg : g ∉ H) : g * g ∉ slice H Y g := by
  intro h
  have hm := (mem_slice H Y g (g * g)).mp h
  exact hg (by simpa [mul_assoc] using hm.2)

open scoped Classical in
private theorem neighbors_card [Fintype G] (H : Subgroup G) (Y : Set G) (g : G) :
    (Finset.univ.filter (fun h : G => h ∈ H ∧ g ≠ h ∧ g * h ∈ Y)).card =
      ((slice H Y g).erase (g * g)).card := by
  classical
  apply Finset.card_bij (fun h _ => g * h)
  · intro h hh
    obtain ⟨hH, hne, hY⟩ := Finset.mem_filter.mp hh |>.2
    refine Finset.mem_erase.mpr ⟨?_, (mem_slice H Y g (g * h)).mpr ?_⟩
    · exact fun he => hne (mul_left_cancel he).symm
    · exact ⟨hY, by simpa [mul_assoc] using hH⟩
  · intro h hh h' hh' he
    exact mul_left_cancel he
  · intro y hy
    obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hy
    obtain ⟨hY, hH⟩ := (mem_slice H Y g y).mp hs
    refine ⟨g⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH, ?_, ?_⟩, ?_⟩
    · intro he
      apply hne
      calc
        y = g * (g⁻¹ * y) := by simp
        _ = g * g := by rw [← he]
    · simpa [mul_assoc] using hY
    · simp

open scoped Classical in
private theorem code_iff_slices [Fintype G] (H : Subgroup G) (Y : Set G)
    (hY : NormalSubset Y) :
    IsTotalPerfectCode (sumGraph Y hY) H ↔
      ∀ g : G, ((slice H Y g).erase (g * g)).card = 1 := by
  classical
  constructor
  · intro hc g
    rw [← neighbors_card H Y g]
    obtain ⟨x, hx, hu⟩ := hc g
    apply Finset.card_eq_one.mpr
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hy
      exact hu y hy
    · rintro rfl
      exact hx
  · intro hc g
    have he := neighbors_card H Y g
    rw [hc g] at he
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp he
    have hm : x ∈ H ∧ g ≠ x ∧ g * x ∈ Y := by
      have hmem : x ∈ Finset.univ.filter
          (fun h : G => h ∈ H ∧ g ≠ h ∧ g * h ∈ Y) := by rw [hx]; simp
      exact (Finset.mem_filter.mp hmem).2
    refine ⟨x, hm, ?_⟩
    intro y hy
    have hmem : y ∈ Finset.univ.filter
        (fun h : G => h ∈ H ∧ g ≠ h ∧ g * h ∈ Y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    rw [hx] at hmem
    exact Finset.mem_singleton.mp hmem

private theorem slice_card [Fintype G] (H : Subgroup G) (Y : Set G) (g : G) :
    (slice H Y g).card = Nat.card {y : G // y ∈ Y ∧ g⁻¹ * y ∈ H} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem slice_one_card [Fintype G] (H : Subgroup G) (Y : Set G) :
    (slice H Y 1).card = Nat.card {y : G // y ∈ Y ∧ y ∈ H} := by
  simpa using slice_card H Y 1

/-- The fixed-connection-set criterion, with both necessity and sufficiency
branches. All cosets are actual left cosets: y belongs to gH iff g⁻¹y belongs to H.
The two-element branch is essential in a loopless sum graph. -/
theorem result [Finite G] (H : Subgroup G) (Y : Set G) (hY : NormalSubset Y) :
    IsTotalPerfectCode (sumGraph Y hY) H ↔
      (∀ g : G, g ∉ H → Nat.card {y : G // y ∈ Y ∧ g⁻¹ * y ∈ H} = 1) ∧
      ((∃ z : G, z ∈ H ∧ z ∉ squares H ∧ Y ∩ (H : Set G) = {z}) ∨
        (Nat.card {y : G // y ∈ Y ∧ y ∈ H} = 2 ∧ squares H ⊆ Y ∩ (H : Set G))) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [code_iff_slices]
  let S := slice H Y 1
  have smem (y : G) : y ∈ S ↔ y ∈ Y ∧ y ∈ H := by
    simp [S, mem_slice]
  constructor
  · intro hc
    refine ⟨fun g hg => ?_, ?_⟩
    · have h := hc g
      rw [Finset.erase_eq_of_notMem (square_notMem_slice H Y g hg)] at h
      rwa [slice_card] at h
    · have h1 : (S.erase 1).card = 1 := by simpa [S] using hc 1
      by_cases hi : 1 ∈ S
      · have hS : S.card = 2 := by rw [Finset.card_erase_of_mem hi] at h1; omega
        refine Or.inr ⟨?_, ?_⟩
        · rw [← slice_one_card]; exact hS
        · rintro z ⟨g, hg, rfl⟩
          have h := hc g
          rw [slice_at_member H Y g hg] at h
          change (S.erase (g * g)).card = 1 at h
          have hs : g * g ∈ S := by
            by_contra hn
            rw [Finset.erase_eq_of_notMem hn, hS] at h
            omega
          exact (smem _).mp hs
      · have hS : S.card = 1 := by rwa [Finset.erase_eq_of_notMem hi] at h1
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hS
        have hzS : z ∈ S := by rw [hz]; simp
        refine Or.inl ⟨z, ((smem z).mp hzS).2, ?_, ?_⟩
        · rintro ⟨g, hg, he⟩
          have h := hc g
          rw [slice_at_member H Y g hg] at h
          change (S.erase (g * g)).card = 1 at h
          rw [he, hz] at h
          simp at h
        · ext y
          change (y ∈ Y ∧ y ∈ H) ↔ y = z
          rw [← smem, hz, Finset.mem_singleton]
  · rintro ⟨ho, ha | hb⟩ g
    · by_cases hg : g ∈ H
      · obtain ⟨z, hzH, hzs, he⟩ := ha
        have hS : S = {z} := by
          ext y
          rw [smem]
          change y ∈ Y ∩ (H : Set G) ↔ y ∈ ({z} : Finset G)
          rw [he]
          simp
        have hne : g * g ≠ z := fun h => hzs ⟨g, hg, h⟩
        rw [slice_at_member H Y g hg]
        change (S.erase (g * g)).card = 1
        simp [hS, hne]
      · rw [Finset.erase_eq_of_notMem (square_notMem_slice H Y g hg), slice_card]
        exact ho g hg
    · by_cases hg : g ∈ H
      · have hs : g * g ∈ S := (smem _).mpr (hb.2 ⟨g, hg, rfl⟩)
        have hS : S.card = 2 := by
          change (slice H Y 1).card = 2
          rw [slice_one_card]
          exact hb.1
        rw [slice_at_member H Y g hg]
        change (S.erase (g * g)).card = 1
        rw [Finset.card_erase_of_mem hs, hS]
      · rw [Finset.erase_eq_of_notMem (square_notMem_slice H Y g hg), slice_card]
        exact ho g hg

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

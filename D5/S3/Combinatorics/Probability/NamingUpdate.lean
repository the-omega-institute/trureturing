/- GID: D5/S3/Combinatorics/Probability/NamingUpdate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/NamingUpdate
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A random injective completion stays uniform after observing more assigned names. -/

import D5.S3.Combinatorics.Probability.PartialNameAssignment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion (uniform_equiv uniform_filter)
open D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)

namespace D5.S3.Combinatorics.Probability.NamingUpdate

variable {V N : Type*} [DecidableEq V]

/-- Available names after removing the now assigned values. -/
noncomputable def unused (A : Finset N) (L : Finset V) (expanded : L ↪ N) : Finset N := by
  classical
  exact A \ L.attach.image expanded

/-- The full naming agrees with the observed expanded naming. -/
def agrees {L : Finset V} (expanded : L ↪ N) (f : V ↪ N) : Prop :=
  ∀ x : L, f x = expanded x

private theorem agrees_extended_iff {K L : Finset V} (hKL : K ⊆ L)
    (A : Finset N) (known : K ↪ N) (expanded : L ↪ N)
    (hOld : ∀ x : K, expanded ⟨x.1, hKL x.2⟩ = known x)
    (hNew : ∀ x : L, x.1 ∉ K → expanded x ∈ A) (f : V ↪ N) :
    (((∀ x : K, f x = known x) ∧ ∀ x : {v // v ∉ K}, f x ∈ A) ∧ agrees expanded f) ↔
      (agrees expanded f ∧ ∀ x : {v // v ∉ L}, f x ∈ unused A L expanded) := by
  classical
  constructor
  · rintro ⟨⟨_, hOldAvailable⟩, hObserved⟩
    refine ⟨hObserved, ?_⟩
    intro x
    refine Finset.mem_sdiff.mpr ⟨hOldAvailable ⟨x.1, fun h => x.2 (hKL h)⟩, ?_⟩
    intro h
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp h
    exact x.2 ((f.injective ((hObserved y).trans hy)) ▸ y.2)
  · rintro ⟨hObserved, hAvailable⟩
    refine ⟨⟨?_, ?_⟩, hObserved⟩
    · intro x
      exact (hObserved ⟨x.1, hKL x.2⟩).trans (hOld x)
    · intro x
      by_cases hx : x.1 ∈ L
      · rw [hObserved ⟨x.1, hx⟩]
        exact hNew ⟨x.1, hx⟩ x.2
      · exact (Finset.mem_sdiff.mp (hAvailable ⟨x.1, hx⟩)).1

private def candidatesAfterReveal {K L : Finset V} (hKL : K ⊆ L)
    (A : Finset N) (known : K ↪ N) (expanded : L ↪ N)
    (hOld : ∀ x : K, expanded ⟨x.1, hKL x.2⟩ = known x)
    (hNew : ∀ x : L, x.1 ∉ K → expanded x ∈ A) :
    {f : Candidates K A known // agrees expanded f.1} ≃ Candidates L (unused A L expanded) expanded where
  toFun f := ⟨f.1.1, (agrees_extended_iff hKL A known expanded hOld hNew _).mp ⟨f.1.2, f.2⟩⟩
  invFun f := by
    obtain ⟨hBefore, hObserved⟩ := (agrees_extended_iff hKL A known expanded hOld hNew _).mpr f.2
    exact ⟨⟨f.1, hBefore⟩, hObserved⟩
  left_inv f := Subtype.ext (Subtype.ext rfl)
  right_inv f := Subtype.ext rfl

/-- Filtering on an expanded assignment gives the uniform law on its remaining completions. -/
theorem uniform_after_reveal [Finite V] [Finite N] {K L : Finset V} (hKL : K ⊆ L)
    (A : Finset N) (known : K ↪ N) (expanded : L ↪ N)
    (hOld : ∀ x : K, expanded ⟨x.1, hKL x.2⟩ = known x)
    (hNew : ∀ x : L, x.1 ∉ K → expanded x ∈ A)
    (h : Nonempty {f : Candidates K A known // agrees expanded f.1}) :
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h.map Subtype.val
    let μ := uniformPmf (Candidates K A known)
    let R : Set (Candidates K A known) := {f | agrees expanded f.1}
    let remaining := unused A L expanded
    let New := Candidates L remaining expanded
    ∃ equivalence : {f : Candidates K A known // agrees expanded f.1} ≃ New,
      (∀ f, (equivalence f).1 = f.1.1) ∧
      let _ : Fintype New := Fintype.ofFinite _
      let _ : Nonempty New := h.map equivalence
      ∀ hr : ∃ r ∈ R, r ∈ μ.support,
        ((μ.filter R hr).map (fun f => f.1)) = (uniformPmf New).map Subtype.val := by
  classical
  intro _ _ μ R remaining New
  let equ := candidatesAfterReveal hKL A known expanded hOld hNew
  refine ⟨equ, fun _ => rfl, ?_⟩
  intro _ _ hr
  let _ : Fintype {f : Candidates K A known // agrees expanded f.1} := Fintype.ofFinite _
  let _ : Nonempty {f : Candidates K A known // agrees expanded f.1} := h
  have hFilter := uniform_filter (fun f : Candidates K A known => agrees expanded f.1) hr
  change (μ.filter R hr).map (fun f => f.1) = _
  rw [hFilter]
  calc
    _ = ((uniformPmf {f : Candidates K A known // agrees expanded f.1}).map equ).map
          (fun f : New => f.1) := by
      rw [PMF.map_comp, PMF.map_comp]
      rfl
    _ = _ := by rw [uniform_equiv equ]

end D5.S3.Combinatorics.Probability.NamingUpdate

/- GID: D5/S3/Combinatorics/Graph/Incidence/UnsignedStarInvariantSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/UnsignedStarInvariantSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Attained invariant integer support and pointwise invariant maximum cuts. -/

import D5.S3.Combinatorics.Graph.Incidence.UnsignedStarFixedCokernel
import D5.S3.Combinatorics.Graph.Incidence.UnsignedStarSupport

/-!
Mathematical guidance: Sections 1--5 of the supplied native proof, SHA256
a92cff8d9829617a663f07a5a8576fed5e88049de0805eb61431db62084f3c31.
Integrated from preserved source e375be2a9a9a48876a5b8c2a1a9641902d9d9042342c18ccabd227d4ae554899.
The action and integer injectivity interface is the reviewed compiled supplier
at Git 10e23a4a1e40a497ed2dc4183b694cac85050af2. Its full fixed-cokernel
comparison is not a premise of the support proofs.
Admission basis: escape-witness. Utility none: symbolic unbounded proofs;
finite extremization constructs an optimum, not a census or certified instance.

New inference: actual fixed integer representatives have their actual
potentials fixed; equal-value-respecting odd-sign compression therefore
produces POINTWISE invariant Boolean colorings. Finite maximization gives
the optimum over ALL fixed integer representatives, on ORIGINAL edge IDs.
The acting group need not be finite. The unrestricted sign/support argument,
color arithmetic, injectivity and equivariance are supplier mathematics.
No edge-transitive classification, odd-cycle result, fixed-cokernel descent
or external novelty is asserted as new here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.Incidence.UnsignedStarInvariantSupport

open UnsignedStarTorsion UnsignedStarSupport UnsignedStarFixedCokernel
open scoped Classical

variable {Γ V X : Type*} [Group Γ]

/-- Pointwise invariance, also for Boolean functions (no color swap). -/
def Invariant {I A : Type*} (σ : Γ →* Equiv.Perm I) (f : I → A) : Prop :=
  ∀ γ i, f (σ γ i) = f i

/-- This predicate on integer functions is exactly invariance for the
supplier's actual inverse-coordinate representation. -/
theorem invariant_iff_mem_invariants {I : Type*} (σ : Γ →* Equiv.Perm I)
    (a : I → ℤ) : Invariant σ a ↔ a ∈ (coordinateRep σ).invariants := by
  constructor
  · intro h γ
    funext i
    change a ((σ γ)⁻¹ i) = a i
    simpa only [map_inv] using h γ⁻¹ i
  · intro h γ i
    have he := congrFun (h γ⁻¹) i
    change a ((σ γ⁻¹)⁻¹ i) = a i at he
    simpa only [map_inv, inv_inv] using he

variable {g : Edges V X} (ρ : IndexedAction g Γ)

private theorem invariant_representative (b : V → ℤ)
    (hb : Invariant ρ.vertexPerm b) : Invariant ρ.edgePerm (representative g b) := by
  apply (invariant_iff_mem_invariants _ _).mpr
  have hb' := (invariant_iff_mem_invariants _ _).mp hb
  intro γ
  have he : coordinateRep ρ.edgePerm γ (g.starMap b) = g.starMap b := by
    rw [← ρ.starMap_equivariant, hb' γ]
  funext i
  change 1 + g.starMap b ((ρ.edgePerm γ)⁻¹ i) = 1 + g.starMap b i
  exact congrArg (fun n : ℤ => 1 + n) (congrFun he i)

/-- No correction is assumed: injectivity forces every actual potential
of a fixed representative to be pointwise invariant. -/
theorem invariant_representative_iff
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) (b : V → ℤ) :
    Invariant ρ.edgePerm (representative g b) ↔ Invariant ρ.vertexPerm b := by
  constructor
  · intro hz
    apply (invariant_iff_mem_invariants _ _).mpr
    have hz' := (invariant_iff_mem_invariants _ _).mp hz
    intro γ
    apply g.starMap_injective hc hn
    rw [ρ.starMap_equivariant]
    funext i
    have he := congrFun (hz' γ) i
    change 1 + g.starMap b ((ρ.edgePerm γ)⁻¹ i) = 1 + g.starMap b i at he
    exact add_left_cancel he
  · exact invariant_representative ρ b

/-- Equality in the ACTUAL integral quotient, not a saturated quotient. -/
theorem class_eq_iff_representative (z : X → ℤ) :
    g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ↔
      ∃ b : V → ℤ, representative g b = z := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (Submodule.Quotient.eq g.starMap.range).mp h
    refine ⟨b, funext fun i => ?_⟩
    have hi := congrFun hb i
    change g.starMap b i = z i - 1 at hi
    change 1 + g.starMap b i = z i
    omega
  · rintro ⟨b, rfl⟩
    apply (Submodule.Quotient.eq g.starMap.range).mpr
    refine ⟨b, funext fun i => ?_⟩
    change g.starMap b i = (1 + g.starMap b i) - 1
    omega

/-- An affine bijection onto the actual fixed t-fiber, stated as unique
integer representatives. There is no finiteness assumption on any type. -/
theorem fixed_fiber_iff
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) (z : X → ℤ) :
    (Invariant ρ.edgePerm z ∧
      g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ))) ↔
    ∃! b : V → ℤ, Invariant ρ.vertexPerm b ∧ representative g b = z := by
  constructor
  · rintro ⟨hz, hπ⟩
    obtain ⟨b, rfl⟩ := (class_eq_iff_representative (g := g) z).mp hπ
    refine ⟨b, ⟨(invariant_representative_iff ρ hc hn b).mp hz, rfl⟩, ?_⟩
    intro a ha
    apply g.starMap_injective hc hn
    funext i
    have he := congrFun ha.2 i
    change 1 + g.starMap a i = 1 + g.starMap b i at he
    exact add_left_cancel he
  · rintro ⟨b, ⟨hb, rfl⟩, _⟩
    exact ⟨invariant_representative ρ b hb,
      (class_eq_iff_representative (g := g) _).mpr ⟨b, rfl⟩⟩

private theorem invariant_colorPotential (c : V → Bool)
    (hc : Invariant ρ.vertexPerm c) : Invariant ρ.vertexPerm (colorPotential c) := by
  intro γ v
  simp only [colorPotential, hc γ v]

private theorem invariant_sign_cut (b : V → ℤ) (hb : Invariant ρ.vertexPerm b) :
    ∃ c : V → Bool, Invariant ρ.vertexPerm c ∧
      (cutEdges g c)ᶜ ⊆ Function.support (representative g b) := by
  obtain ⟨c, hequal, hs⟩ := odd_sign_cut g b
  exact ⟨c, fun γ v => hequal _ _ (hb γ v), hs⟩

/-- Every fixed integer representative admits invariant bounded compression
inside its OWN support. The input integer coefficients are unrestricted. -/
theorem fixed_support_compression
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) (z : X → ℤ)
    (hz : Invariant ρ.edgePerm z)
    (hπ : g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ))) :
    ∃ c : V → Bool, Invariant ρ.vertexPerm c ∧
      Invariant ρ.vertexPerm (colorPotential c) ∧
      Invariant ρ.edgePerm (representative g (colorPotential c)) ∧
      g.starMap.range.mkQ (representative g (colorPotential c)) =
        g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ∧
      (∀ v, colorPotential c v = 0 ∨ colorPotential c v = -1) ∧
      (∀ i, representative g (colorPotential c) i = -1 ∨
        representative g (colorPotential c) i = 0 ∨
        representative g (colorPotential c) i = 1) ∧
      Function.support (representative g (colorPotential c)) = (cutEdges g c)ᶜ ∧
      Function.support (representative g (colorPotential c)) ⊆ Function.support z := by
  obtain ⟨b, ⟨hb, rfl⟩, _⟩ := (fixed_fiber_iff ρ hc hn z).mp ⟨hz, hπ⟩
  obtain ⟨c, hci, hs⟩ := invariant_sign_cut ρ b hb
  have hp := invariant_colorPotential ρ c hci
  exact ⟨c, hci, hp, invariant_representative ρ _ hp,
    (class_eq_iff_representative (g := g) _).mpr ⟨colorPotential c, rfl⟩,
    (color_bounds g c).1, (color_bounds g c).2, color_support g c,
    by rwa [color_support g c]⟩

/-- Arbitrary ORIGINAL-ID deletion sets. Ordinary bipartiteness of the
remainder and invariance up to swapping colors are insufficient. -/
theorem fixed_support_criterion
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) (D : Set X) :
    (∃ z : X → ℤ, Invariant ρ.edgePerm z ∧
      g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ∧
      Function.support z ⊆ D) ↔
    ∃ c : V → Bool, Invariant ρ.vertexPerm c ∧ (cutEdges g c)ᶜ ⊆ D := by
  constructor
  · rintro ⟨z, hz, hπ, hs⟩
    obtain ⟨c, hci, _, _, _, _, _, he, hsub⟩ := fixed_support_compression ρ hc hn z hz hπ
    refine ⟨c, hci, ?_⟩
    rw [← he]
    exact hsub.trans hs
  · rintro ⟨c, hci, hs⟩
    refine ⟨representative g (colorPotential c),
      invariant_representative ρ _ (invariant_colorPotential ρ c hci),
      (class_eq_iff_representative (g := g) _).mpr ⟨colorPotential c, rfl⟩, ?_⟩
    rwa [color_support g c]

/-- A maximum is CONSTRUCTED from the finite nonempty set of invariant
Boolean functions. It simultaneously attains both minima and the exact
|X|-maximum-cut formula, counting every original parallel ID. -/
theorem attained_invariant_support_maxcut [Fintype V] [Fintype X]
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) :
    ∃ c : V → Bool, Invariant ρ.vertexPerm c ∧
      Invariant ρ.vertexPerm (colorPotential c) ∧
      Invariant ρ.edgePerm (representative g (colorPotential c)) ∧
      g.starMap.range.mkQ (representative g (colorPotential c)) =
        g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ∧
      (∀ v, colorPotential c v = 0 ∨ colorPotential c v = -1) ∧
      (∀ i, representative g (colorPotential c) i = -1 ∨
        representative g (colorPotential c) i = 0 ∨
        representative g (colorPotential c) i = 1) ∧
      IsLeast {n : ℕ | ∃ z : X → ℤ, Invariant ρ.edgePerm z ∧
        g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ∧
        (Function.support z).ncard = n}
        (Function.support (representative g (colorPotential c))).ncard ∧
      IsLeast {n : ℕ | ∃ D : Set X,
        (∃ d : V → Bool, Invariant ρ.vertexPerm d ∧ (cutEdges g d)ᶜ ⊆ D) ∧ D.ncard = n}
        (Function.support (representative g (colorPotential c))).ncard ∧
      IsGreatest {n : ℕ | ∃ d : V → Bool, Invariant ρ.vertexPerm d ∧
        (cutEdges g d).ncard = n} (cutEdges g c).ncard ∧
      (Function.support (representative g (colorPotential c))).ncard =
        Fintype.card X - (cutEdges g c).ncard := by
  let C : Finset (V → Bool) := Finset.univ.filter (Invariant ρ.vertexPerm)
  have hC : C.Nonempty := ⟨fun _ => false, by simp [C, Invariant]⟩
  obtain ⟨c, hcC, hmax'⟩ := Finset.exists_max_image C (fun d => (cutEdges g d).ncard) hC
  have hci : Invariant ρ.vertexPerm c := (Finset.mem_filter.mp hcC).2
  have hmax (d : V → Bool) (hd : Invariant ρ.vertexPerm d) :
      (cutEdges g d).ncard ≤ (cutEdges g c).ncard :=
    hmax' d (by simp [C, hd])
  have hcomp (d : V → Bool) : (cutEdges g d)ᶜ.ncard =
      Fintype.card X - (cutEdges g d).ncard := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_compl (cutEdges g d)
  have hlow (d : V → Bool) (hd : Invariant ρ.vertexPerm d) :
      (Function.support (representative g (colorPotential c))).ncard ≤
        (cutEdges g d)ᶜ.ncard := by
    rw [color_support g c, hcomp c, hcomp d]
    exact Nat.sub_le_sub_left (hmax d hd) _
  have hmin (z : X → ℤ) (hz : Invariant ρ.edgePerm z)
      (hπ : g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ))) :
      (Function.support (representative g (colorPotential c))).ncard ≤
        (Function.support z).ncard := by
    obtain ⟨d, hd, hs⟩ := (fixed_support_criterion ρ hc hn (Function.support z)).mp
      ⟨z, hz, hπ, Set.Subset.rfl⟩
    exact (hlow d hd).trans (Set.ncard_mono hs)
  have hp := invariant_colorPotential ρ c hci
  have hz := invariant_representative ρ _ hp
  have hπ := (class_eq_iff_representative (g := g) _).mpr ⟨colorPotential c, rfl⟩
  refine ⟨c, hci, hp, hz, hπ, (color_bounds g c).1, (color_bounds g c).2,
    ⟨⟨_, hz, hπ, rfl⟩, ?_⟩, ⟨?_, ?_⟩, ⟨⟨c, hci, rfl⟩, ?_⟩, ?_⟩
  · rintro n ⟨z, hzi, hπz, rfl⟩
    exact hmin z hzi hπz
  · exact ⟨Function.support (representative g (colorPotential c)),
      ⟨c, hci, by rw [color_support g c]⟩, rfl⟩
  · rintro n ⟨D, ⟨d, hd, hs⟩, rfl⟩
    exact (hlow d hd).trans (Set.ncard_mono hs)
  · rintro n ⟨d, hd, rfl⟩
    exact hmax d hd
  · rw [color_support g c, hcomp c]

/-- All translates must lie in D: complete orbits, not orbits meeting D. -/
def invariantCore {I : Type*} (σ : Γ →* Equiv.Perm I) (D : Set I) : Set I :=
  {i | ∀ γ, σ γ i ∈ D}

theorem invariantCore_subset {I : Type*} (σ : Γ →* Equiv.Perm I) (D : Set I) :
    invariantCore σ D ⊆ D := by
  intro i hi
  simpa using hi 1

/-- Universal property of the largest invariant subset of D. -/
theorem subset_invariantCore_iff {I : Type*} (σ : Γ →* Equiv.Perm I)
    (S D : Set I) (hS : ∀ γ i, σ γ i ∈ S ↔ i ∈ S) :
    S ⊆ invariantCore σ D ↔ S ⊆ D := by
  constructor
  · exact fun h => h.trans (invariantCore_subset σ D)
  · intro h i hi γ
    exact h ((hS γ i).mpr hi)

/-- Arbitrary D can be replaced by its invariant CORE in the actual fixed
t-fiber criterion; no partial-orbit image is used. -/
theorem fixed_support_core_criterion
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) (D : Set X) :
    (∃ z : X → ℤ, Invariant ρ.edgePerm z ∧
      g.starMap.range.mkQ z = g.starMap.range.mkQ (fun _ : X => (1 : ℤ)) ∧
      Function.support z ⊆ D) ↔
    ∃ c : V → Bool, Invariant ρ.vertexPerm c ∧
      (cutEdges g c)ᶜ ⊆ invariantCore ρ.edgePerm D := by
  have hcore (z : X → ℤ) (hz : Invariant ρ.edgePerm z) :
      Function.support z ⊆ invariantCore ρ.edgePerm D ↔ Function.support z ⊆ D :=
    subset_invariantCore_iff ρ.edgePerm _ D (fun γ i => by
      change z (ρ.edgePerm γ i) ≠ 0 ↔ z i ≠ 0
      rw [hz γ i])
  constructor
  · rintro ⟨z, hz, hπ, hs⟩
    exact (fixed_support_criterion ρ hc hn _).mp ⟨z, hz, hπ, (hcore z hz).mpr hs⟩
  · intro h
    obtain ⟨z, hz, hπ, hs⟩ := (fixed_support_criterion ρ hc hn _).mpr h
    exact ⟨z, hz, hπ, (hcore z hz).mp hs⟩

end D5.S3.Combinatorics.Graph.Incidence.UnsignedStarInvariantSupport

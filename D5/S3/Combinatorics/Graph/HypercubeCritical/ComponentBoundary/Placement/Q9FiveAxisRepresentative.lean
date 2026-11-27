/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisRepresentative
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisRepresentative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The stabilizer moves the contact layer to its orbit representative. The normalized supports retain separation, cubical regularity, the contact masks, the midpoint and translation laws, and the exterior sign cancellation. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisLayerAction
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedRows

/-! Transport the actual geometric and signed data to a representative. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisRepresentative

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9FiveAxisOrbitCover (Word representatives)
open Q9FiveAxisOrbitGeometry (MidpointCounts ContactTranslations family exists_covered_normalization)
open private mem_evenWords_iff cube_root_zero cube_root_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry
open Q9FiveAxisLayerAction (LayerMatches reaches_representative)
open Q9FiveAxisMissingContact (Geometry)
open Q9TightDistanceTwoCNF (support)
open Q9TightDistanceTwoNormalized (parity_normalize normalize_minimumDisplacements)
open Q9RootStabilizer (normalize_comp normalize_regular)
open Q9SharedContactNormalized (LocalRules)
open private normalize_hammingDist normalize_local_rules from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter
open Q9FiveAxisSignedNormalization (exists_normalized_signing)
open Q9FiveAxisSignedRows (Signing)

open Classical in
private theorem local_rules {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) : LocalRules S :=
  ⟨fun _ hs => regular_directions S hr hs, exterior_even S hr hb,
    fun _ _ _ hij hx hi hj hxy => no_selected_square hb hij hx hi hj hxy⟩

open Classical in
/-- A separated actual pair with nine masks on five axes can be put in a
representative frame while retaining its midpoint, translation and signing data. -/
theorem exists_signed_representative {C D : Finset (Q 9)} {b : Bool}
    {A : Finset (Fin 9)} (hA : A.card = 5)
    (hnine : (minimumDisplacements C D b 2).card = 9)
    (haxes : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    ∃ (X Y : Finset (Q 9)) (f : Bool → Q 9 → ℤ) (r : Q9FiveAxisOrbitCover.Pattern),
      r ∈ representatives ∧ LayerMatches X Y r ∧ Geometry X Y ∧
      minimumDisplacements X Y false 2 = family ∧ MidpointCounts X Y ∧ ContactTranslations X Y ∧
      (∀ s, ((hypercube 9).induce (support X Y s : Set (Q 9))).IsRegularOfDegree 3) ∧
      ∀ s, Signing (support X Y s) (f s) := by
  obtain ⟨o, σ, ho, _, hfamily, _, _, r, hr, p, hp, hmatch⟩ :=
    exists_covered_normalization hA hnine haxes hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  let e := normalize σ o
  let U := C.map e.toEmbedding
  let V := D.map e.toEmbedding
  have layer : LayerMatches U V p := by
    intro s w hw
    obtain ⟨hsize, hpar⟩ := (mem_evenWords_iff w).mp hw
    exact hmatch s w hsize hpar
  obtain ⟨τ, z, t, hz, hperm, hR⟩ := reaches_representative hp layer
  let K := support C D t
  let L := support C D (!t)
  let u := e.symm z
  let ρ := τ.trans σ
  let X := K.map (normalize ρ u).toEmbedding
  let Y := L.map (normalize ρ u).toEmbedding
  have hcomp : e.trans (normalize τ z) = normalize ρ u := normalize_comp σ τ o z
  have hleft : support U V t = K.map e.toEmbedding := by cases t <;> rfl
  have hright : support U V (!t) = L.map e.toEmbedding := by cases t <;> rfl
  simp only [hleft, hright, Finset.map_map, ← Equiv.trans_toEmbedding, hcomp] at hR
  have hordered : minimumDisplacements (support U V t) (support U V (!t)) false 2 = family := by
    cases t
    · exact hfamily
    · exact (minimumDisplacements_swap_two U V false).symm.trans hfamily
  have hM := normalize_minimumDisplacements τ z (support U V t) (support U V (!t)) false 2
  rw [hz, show (false : Bool) + false = false by decide, hordered, hperm] at hM
  simp only [hleft, hright, Finset.map_map, ← Equiv.trans_toEmbedding, hcomp] at hM
  have hregK : ((hypercube 9).induce (K : Set (Q 9))).IsRegularOfDegree 3 := by
    cases t <;> assumption
  have hregL : ((hypercube 9).induce (L : Set (Q 9))).IsRegularOfDegree 3 := by
    cases t <;> assumption
  have hbalK : IsBalanced K := by cases t <;> assumption
  have hbalL : IsBalanced L := by cases t <;> assumption
  have hconnK : ((hypercube 9).induce (K : Set (Q 9))).Connected := by cases t <;> assumption
  have hconnL : ((hypercube 9).induce (L : Set (Q 9))).Connected := by cases t <;> assumption
  have hdetK : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w K false)).det = 0 := by
    cases t <;> assumption
  have hdetL : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w L false)).det = 0 := by
    cases t <;> assumption
  have hsepKL : ∀ x ∈ K, ∀ y ∈ L, 2 ≤ hammingDist x y := by
    cases t
    · exact hsep
    · intro x hx y hy
      rw [hammingDist_comm]
      exact hsep y hy x hx
  have hr00 : ∀ q ∈ representatives, (0 : Word) ∈ q.1 ∧ (3 : Word) ∈ q.2 := by
    decide +kernel
  obtain ⟨h0, h3⟩ := hr00 r hr
  have hGeom : Geometry X Y := by
    refine ⟨?_, ?_, normalize_local_rules ρ u _ (local_rules hregK hbalK),
      normalize_local_rules ρ u _ (local_rules hregL hbalL), ?_⟩
    · rw [← cube_root_zero]
      exact (hR false 0 (by decide +kernel)).mpr h0
    · rw [← cube_root_three]
      exact (hR true 3 (by decide +kernel)).mpr h3
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
      change 2 ≤ hammingDist (normalize ρ u x') (normalize ρ u y')
      rw [normalize_hammingDist]
      exact hsepKL x' hx' y' hy'
  have hu : parity u = b := by
    have hz' : parity (normalize σ o u) = false := by simpa [u, e] using hz
    rw [parity_normalize, ho] at hz'
    cases b <;> cases h : parity u <;> simp_all
  have hK (j : Fin 9) :=
    exists_both_parity_supported_of_signed_defect_singular
      K hregK hconnK hbalK (fun k => if k = j then 2 else 1)
      (fun k => by split <;> norm_num) (hdetK _) b
  have hL :=
    exists_both_parity_supported_of_signed_defect_singular
      L hregL hconnL hbalL (fun _ => 1) (fun _ => by norm_num) (hdetL _) b
  obtain ⟨counts, translates, _⟩ :=
    Q9FiveAxisOrbitGeometry.covers_of_normalization ρ u hu hsepKL hregK hregL
      hbalK hbalL hK hL hGeom hM
  obtain ⟨fK, hk₁, hk₂, hk₃, hk₄⟩ := exists_normalized_signing K ρ u hregK hbalK
  obtain ⟨fL, hl₁, hl₂, hl₃, hl₄⟩ := exists_normalized_signing L ρ u hregL hbalL
  refine ⟨X, Y, (fun s => if s then fL else fK), r, hr, hR, hGeom, hM, counts,
    translates, ?_, ?_⟩
  · intro s
    cases s
    · exact normalize_regular hregK ρ u
    · exact normalize_regular hregL ρ u
  · intro s
    cases s
    · exact ⟨hk₁, hk₂, hk₃, hk₄⟩
    · exact ⟨hl₁, hl₂, hl₃, hl₄⟩

#print axioms exists_signed_representative

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisRepresentative

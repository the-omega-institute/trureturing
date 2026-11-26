/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A cube translation and axis permutation preserve the local conditions of shared contacts. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactAxisOrbits
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization

/-! Transport the local constraints of a shared contact to canonical coordinates. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open Q9SharedContactAxisOrbits (canonicalDifference canonicalLeft canonicalRight exists_axis_permutation)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (normalize origin)
open private normalize_center normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
open private directions_subset_agreement from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

private theorem normalize_hammingDist (σ : Equiv.Perm (Fin 9)) (center x y : Q 9) :
    hammingDist (normalize σ center x) (normalize σ center y) = hammingDist x y := by
  have hne (i : Fin 9) :
      normalize σ center x i ≠ normalize σ center y i ↔ x (σ i) ≠ y (σ i) := by
    change ((x (σ i) != center (σ i)) ≠ (y (σ i) != center (σ i))) ↔ _
    cases x (σ i) <;> cases y (σ i) <;> cases center (σ i) <;> decide
  unfold hammingDist
  simp_rw [hne]
  apply card_bij (fun i _ => σ i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, mem_filter.mpr ⟨mem_univ _, ?_⟩, σ.apply_symm_apply j⟩
    simpa only [Equiv.apply_symm_apply] using (mem_filter.mp hj).2

/-- The local restrictions used in the finite shared-contact cases. -/
structure LocalRules (C : Finset (Q 9)) : Prop where
  occupied_degree : ∀ x ∈ C, (directions C x).card = 3
  exterior_degree : ∀ x ∉ C, Even (directions C x).card
  no_square : ∀ (x : Q 9) (i j : Fin 9), i ≠ j → x ∈ C →
    flip x i ∈ C → flip x j ∈ C → flip (flip x i) j ∉ C

private theorem normalize_local_rules
    (σ : Equiv.Perm (Fin 9)) (o : Q 9) (C : Finset (Q 9))
    (hC : LocalRules C) : LocalRules (C.map (normalize σ o).toEmbedding) := by
  classical
  let e := normalize σ o
  let D := C.map e.toEmbedding
  have hmem (x : Q 9) : e x ∈ D ↔ x ∈ C := by
    simp [D]
  have hflip (x : Q 9) (i : Fin 9) : e (flip x i) = flip (e x) (σ.symm i) := by
    simpa [e] using normalize_flip σ.symm o x i
  have hdirs (x : Q 9) : (directions D (e x)).card = (directions C x).card := by
    have he : directions D (e x) = (directions C x).map σ.symm.toEmbedding := by
      ext j
      have hh := hflip x (σ j)
      rw [Equiv.symm_apply_apply] at hh
      rw [mem_directions, ← hh, hmem, ← mem_directions]
      constructor
      · intro hj
        exact mem_map.mpr ⟨σ j, hj, σ.symm_apply_apply j⟩
      · intro hj
        obtain ⟨i, hi, heq⟩ := mem_map.mp hj
        change σ.symm i = j at heq
        simpa only [← heq, σ.apply_symm_apply] using hi
    rw [he, card_map]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [hdirs]
    exact hC.occupied_degree u ((hmem u).mp hx)
  · intro x hx
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [hdirs]
    exact hC.exterior_degree u (fun hu => hx ((hmem u).mpr hu))
  · intro x i j hij hx hi hj hdouble
    obtain ⟨u, rfl⟩ := e.surjective x
    have heq (v : Q 9) (a : Fin 9) : flip (e v) a = e (flip v (σ a)) := by
      symm
      simpa only [Equiv.symm_apply_apply] using hflip v (σ a)
    rw [heq] at hi hj
    rw [heq u i, heq] at hdouble
    exact hC.no_square u (σ i) (σ j) (fun he => hij (σ.injective he))
      ((hmem u).mp hx) ((hmem _).mp hi) ((hmem _).mp hj) ((hmem _).mp hdouble)

open Classical in
/-- A distance-three pair with a shared occupied direction gives one of the
three canonical local problems under a cube translation and axis permutation. -/
theorem exists_normalized_shared_contact
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hd : hammingDist x y = 3)
    (hshare : (directions C x ∩ directions D y).Nonempty) :
    ∃ (k : Fin 3) (A B : Finset (Q 9)),
      LocalRules A ∧ LocalRules B ∧
      (∀ u ∈ A, ∀ v ∈ B, 3 ≤ hammingDist u v) ∧
      canonicalDifference ∈ A ∧ origin ∈ B ∧
      (∀ i, canonicalLeft k i = true → flip canonicalDifference i ∈ A) ∧
      (∀ i, canonicalRight i = true → flip origin i ∈ B) := by
  let T : Finset (Fin 9) := univ.filter fun i => x i ≠ y i
  let A := directions C x
  let B := directions D y
  have hT : T.card = 3 := hd
  have hmin u hu v hv := hd.le.trans (hsep u hu v hv)
  have ha := directions_subset_agreement hy hmin
  have hb := directions_subset_agreement hx (C := D) (D := C) (x := y)
    (fun u hu v hv => by simpa only [hammingDist_comm] using hmin v hv u hu)
  have hTA : Disjoint T A := disjoint_left.mpr fun _ hT hA =>
    (mem_filter.mp hT).2 (mem_filter.mp (ha hA)).2
  have hTB : Disjoint T B := disjoint_left.mpr fun _ hT hB =>
    (mem_filter.mp hT).2 (mem_filter.mp (hb hB)).2.symm
  obtain ⟨k, σ, _, hs⟩ :=
    exists_axis_permutation hT (regular_directions C hrC hx) (regular_directions D hrD hy)
      hTA hTB hshare
  let e := normalize σ y
  have hex : e x = canonicalDifference := by
    funext i
    have hi := (hs i).1
    change ((x (σ i) != y (σ i)) = canonicalDifference i)
    simp only [T, mem_filter, mem_univ, true_and] at hi
    cases hxi : x (σ i) <;> cases hyi : y (σ i) <;>
      cases hci : canonicalDifference i <;> simp_all
  have hey : e y = origin := normalize_center σ y
  have hflip (v : Q 9) (i : Fin 9) : e (flip v (σ i)) = flip (e v) i := by
    simpa [e] using normalize_flip σ.symm y v (σ i)
  have hlocal {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) : LocalRules S :=
    ⟨fun _ hs => regular_directions S hr hs, exterior_even S hr hb,
      fun _ _ _ hij hx hi hj hxy => no_selected_square hb hij hx hi hj hxy⟩
  refine ⟨k, C.map e.toEmbedding, D.map e.toEmbedding,
    normalize_local_rules σ y C (hlocal hrC hbC),
    normalize_local_rules σ y D (hlocal hrD hbD), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hv
    change 3 ≤ hammingDist (normalize σ y a) (normalize σ y b)
    rw [normalize_hammingDist]
    exact hsep a ha b hb
  · exact mem_map.mpr ⟨x, hx, hex⟩
  · exact mem_map.mpr ⟨y, hy, hey⟩
  · intro i hi
    have hc := (mem_directions C x (σ i)).mp ((hs i).2.1.mpr hi)
    exact mem_map.mpr ⟨flip x (σ i), hc, (hflip x i).trans (congrArg (fun a : Q 9 => BalancedCriticalSpectrum.flip a i) hex)⟩
  · intro i hi
    have hc := (mem_directions D y (σ i)).mp ((hs i).2.2.mpr hi)
    exact mem_map.mpr ⟨flip y (σ i), hc, (hflip y i).trans (congrArg (fun a : Q 9 => BalancedCriticalSpectrum.flip a i) hey)⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized

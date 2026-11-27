/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisFourLeafSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisFourLeafSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The shared faces produce a coherent four-term fragment. Degree eight is tight and every remaining occupied direction contributes the negative of the axis-zero term. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisCoherentHub
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedNormalization
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! Signed consequences of four complementary leaves in the normalized five-axis branch. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec cubeBitVec_xor_single)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves (toggle)
open BalancedCriticalSpectrum (Q flip flip_adj flip_flip IsBalanced IsSwitching gamma gamma_apply switchingVector)
open BalancedCubeGirth (adjacent_exists_flip flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9IsotropicHuang (parity flipSign)
open Q9FiveAxisSignedNormalization (rupFlipSign)
open Q9FiveAxisCoherentHub (card_le_four_of_shared_faces)
open Q9SharedMidpointFiveAxes (two_neighbors_each)
open Q9CoherentExteriorFragment (terms_eq_of_tight_coherent_exterior_fragment)
open private parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private alternatingCharacter alternatingCharacter_sq cast_rupFlipSign from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSignedNormalization

/-- The two stars in the four-leaf input generator have axes (0, low, 3, 4). -/
def star (low : Fin 9) : Finset (Fin 9) := {0, low, 3, 4}

/-- The antipode XOR masks for low = 1 and low = 2, respectively. -/
def starMask (low : Fin 9) : BitVec 9 := if low = 1 then 27 else 29

private theorem card_star : ∀ low : Fin 9, low = 1 ∨ low = 2 → (star low).card = 4 := by
  decide +kernel

/-- For the face through axes 0 and j, one of the other two axes leads
to a complementary leaf on the opposite shore. This check involves only
the masks at the zero word, and XOR transports it to every hub. -/
private theorem shared_face_mask :
    ∀ low : Fin 9, low = 1 ∨ low = 2 →
    ∀ j ∈ star low, (0 : Fin 9) ≠ j →
      ∃ k l : Fin 9, l ∈ star low ∧
        toggle (toggle (toggle 0 0) j) k = toggle 0 l ^^^ starMask low := by
  decide +kernel

private theorem step_cube (w : BitVec 9) (i : Fin 9) :
    cubeBitVec 9 (toggle w i) = flip (cubeBitVec 9 w) i :=
  cubeBitVec_xor_single w i

private theorem rupFlipSign_zero (x : Q 9) : rupFlipSign 0 x = 1 := by
  simp [rupFlipSign]

/-- The alternating character is its own inverse, so the supplied
integer signing yields a switching function for Huang's coefficients. -/
private theorem switching_of_rup_signing
    {C : Finset (Q 9)} {s : Q 9 → ℤ}
    (hunit : ∀ x ∈ C, s x = 1 ∨ s x = -1)
    (hedge : ∀ x ∈ C, ∀ i : Fin 9, flip x i ∈ C →
      rupFlipSign i x = s x * s (flip x i)) :
    IsSwitching C (fun x => alternatingCharacter x * (s x : ℝ)) := by
  constructor
  · intro x hx
    rcases sq_eq_one_iff.mp (alternatingCharacter_sq x) with h | h <;>
      rcases hunit x hx with hs | hs <;> simp [h, hs]
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    have he : (rupFlipSign i x : ℝ) = (s x : ℝ) * (s (flip x i) : ℝ) := by
      exact_mod_cast hedge x hx i hy
    rw [← flipSign_cast]
    calc
      (flipSign i x : ℝ) =
          alternatingCharacter x ^ 2 * (flipSign i x : ℝ) *
            alternatingCharacter (flip x i) ^ 2 := by
              rw [alternatingCharacter_sq, alternatingCharacter_sq, one_mul, mul_one]
      _ = alternatingCharacter x * (rupFlipSign i x : ℝ) *
            alternatingCharacter (flip x i) := by rw [cast_rupFlipSign]; ring
      _ = _ := by rw [he]; ring

open Classical in
/-- The four-leaf premises of the little-endian input generator imply
exactly eight occupied directions at an exterior hub. Any two outward
directions therefore contain an occupied direction. For each occupied
outward direction its signed contribution is the negative of the axis-0
leaf sign. Swapping the two supports gives the other shore's clauses. -/
theorem coherent_exterior_four_leaves
    {C D : Finset (Q 9)} {s : Q 9 → ℤ} {w : BitVec 9} {low : Fin 9}
    {I : Finset (Fin 9)} (hlow : low = 1 ∨ low = 2)
    (hI : I.card ≤ 5) (hm : ∀ T ∈ minimumDisplacements C D false 2, T ⊆ I)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbD : IsBalanced D)
    (hunit : ∀ x ∈ C, s x = 1 ∨ s x = -1)
    (hedge : ∀ x ∈ C, ∀ i : Fin 9, flip x i ∈ C →
      rupFlipSign i x = s x * s (flip x i))
    (hp : parity (cubeBitVec 9 w) = true)
    (hleft : ∀ i ∈ star low, cubeBitVec 9 (toggle w i) ∈ C)
    (hright : ∀ i ∈ star low, cubeBitVec 9 (toggle w i ^^^ starMask low) ∈ D) :
    cubeBitVec 9 w ∉ C ∧ (directions C (cubeBitVec 9 w)).card = 8 ∧
      (∀ a b : Fin 9, a ≠ b →
        cubeBitVec 9 (toggle w a) ∈ C ∨ cubeBitVec 9 (toggle w b) ∈ C) ∧
      (∀ a : Fin 9, a ∉ star low → cubeBitVec 9 (toggle w a) ∈ C →
        rupFlipSign a (cubeBitVec 9 w) * s (cubeBitVec 9 (toggle w a)) =
          -s (cubeBitVec 9 (toggle w 0))) := by
  let h := cubeBitVec 9 w
  let A := star low
  let σ : Q 9 → ℝ := fun x => alternatingCharacter x * (s x : ℝ)
  have hs : IsSwitching C σ := switching_of_rup_signing hunit hedge
  have hbC : IsBalanced C := ⟨σ, hs⟩
  have hzero : (0 : Fin 9) ∈ A := by simp [A, star]
  have hcard : A.card = 4 := card_star low hlow
  have hleaf (a : Fin 9) (ha : a ∈ A) : flip h a ∈ C := by
    simpa only [step_cube] using hleft a ha
  have hsub : A ⊆ directions C h :=
    fun a ha => (mem_directions C h a).mpr (hleaf a ha)
  have hpar : parity (flip h 0) = false := by
    rw [parity_flip]
    simp [h, hp]
  have hshared (j : Fin 9) (hj : j ∈ A) (hj0 : (0 : Fin 9) ≠ j) :
      ∃ k : Fin 9, flip (flip (flip h 0) j) k ∈ D := by
    obtain ⟨k, l, hl, he⟩ := shared_face_mask low hlow j hj hj0
    have hw : toggle (toggle (toggle w 0) j) k =
        toggle w l ^^^ starMask low := by
      simp [toggle, BitVec.xor_assoc] at he ⊢
      exact he
    have hv := congrArg (cubeBitVec 9) hw
    simp only [step_cube] at hv
    exact ⟨k, hv.symm ▸ hright l hl⟩
  obtain ⟨hh, hdegree⟩ :=
    (card_le_four_of_shared_faces hzero hsub hI hm hsep hrC hrD hbC hbD hpar hshared).2 hcard
  have hfaces (j : Fin 9) (hj : j ∈ A) (hj0 : (0 : Fin 9) ≠ j) :
      flip (flip h 0) j ∉ C ∧ directions C (flip (flip h 0) j) = {0, j} := by
    let v := flip (flip h 0) j
    obtain ⟨k, hk⟩ := hshared j hj hj0
    change flip v k ∈ D at hk
    have hvj : flip v j ∈ C := by simpa only [v, BalancedCriticalSpectrum.flip_flip] using hleaf 0 hzero
    have hv0 : flip v 0 ∈ C := by
      change flip (flip (flip h 0) j) 0 ∈ C
      rw [flip_comm h 0 j, BalancedCriticalSpectrum.flip_flip]
      exact hleaf j hj
    have hvpar : parity (flip v j) = false := by simpa only [v, BalancedCriticalSpectrum.flip_flip] using hpar
    have hvc := (two_neighbors_each hI hm hsep hrC hrD hbC hbD hvj hk hvpar).1
    have hvs : ({0, j} : Finset (Fin 9)) ⊆ directions C v := by
      intro a ha
      rcases mem_insert.mp ha with he | he
      · subst a
        exact (mem_directions C v 0).mpr hv0
      · have he' := mem_singleton.mp he
        subst a
        exact (mem_directions C v j).mpr hvj
    change v ∉ C ∧ directions C v = {0, j}
    refine ⟨?_, (eq_of_subset_of_card_le hvs ?_).symm⟩
    · intro hv
      have hdist := hsep v hv _ hk
      have hadj : hammingDist v (flip v k) = 1 := flip_adj v k
      omega
    · rw [hvc, card_pair hj0]
  have htight : (directions C h).card = 2 * A.card := by
    rw [hdegree, hcard]
  have hopposite := terms_eq_of_tight_coherent_exterior_fragment
    hrC hs hh hzero hsub hfaces htight
  have hterm (a : Fin 9) (ha : flip h a ∈ C) :
      ((rupFlipSign a h * s (flip h a) : ℤ) : ℝ) =
        alternatingCharacter h * gamma a (switchingVector C σ) h := by
    rw [Int.cast_mul, cast_rupFlipSign, gamma_apply, ← flipSign_cast,
      switchingVector, ite_eq_left ha]
    dsimp only [σ]
    ring
  refine ⟨hh, hdegree, ?_, ?_⟩
  · intro a b hab
    simp only [step_cube]
    by_contra hn
    obtain ⟨ha, hb⟩ := not_or.mp hn
    have hcap : directions C h ⊆ (univ : Finset (Fin 9)) \ {a, b} := by
      intro k hk
      have hkC := (mem_directions C h k).mp hk
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact ha hkC
      · exact hb hkC
    have hle := card_le_card hcap
    rw [hdegree, card_univ_sdiff, Fintype.card_fin, card_pair hab] at hle
    omega
  · intro a ha hac
    have hac' : flip h a ∈ C := by simpa only [step_cube] using hac
    have hmem : a ∈ directions C h \ A :=
      mem_sdiff.mpr ⟨(mem_directions C h a).mpr hac', ha⟩
    have he : rupFlipSign a h * s (flip h a) =
        -(rupFlipSign 0 h * s (flip h 0)) := by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_neg, hterm a hac', hterm 0 (hleaf 0 hzero), hopposite a hmem]
      ring
    simpa only [step_cube, rupFlipSign_zero, one_mul] using he

#print axioms coherent_exterior_four_leaves

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisFourLeafSigns

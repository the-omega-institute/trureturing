/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: No singleton parity intersection of XOR-translated balanced cubic Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction

/-! Ternary kernel words for balanced cubic supports constrain their relative XOR placements. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip_adj IsBalanced switchingVector switching_sq)
open ComponentBoundary.Q9IsotropicHuang (parity weightedAction weightedLinear_apply)
open ComponentBoundary.Q9WeightedBoundaryGram (signed signed_transpose signed_mulVec)
open private huangMatrix cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private translate translate_translate translate_flip diagonalSign diagonalSign_sq
  edge_covariance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction

private theorem kernel_pairing (f g : Q 9 → ZMod 3)
    (hf : weightedAction (fun _ => 1) f = 0) (hg : weightedAction (fun _ => 1) g = 0) :
    f ⬝ᵥ g = 0 := by
  let w : Fin 9 → ZMod 3 := fun _ => 1
  have hw : ∑ i, w i ^ 2 = 0 := by
    norm_num [w, Finset.sum_const, nsmul_eq_mul]
    decide
  have hmem : f ∈ Set.range (weightedAction w) := by
    rw [ComponentBoundary.Q9IsotropicHuang.weightedAction_image_eq_kernel w hw 0 (by simp [w])]
    exact hf
  obtain ⟨u, rfl⟩ := hmem
  have hsym : (signed w).IsSymm := signed_transpose w
  have hlink (v : Q 9 → ZMod 3) :
      (signed w).mulVec v = weightedAction w v := by
    rw [signed_mulVec, weightedLinear_apply]
  rw [← hlink u, dotProduct_comm, hsym.dotProduct_mulVec_comm, hlink g, hg, dotProduct_zero]

open Classical in
private theorem exists_signed_parity_word (C : Finset (Q 9))
    (hC : IsBalanced C) (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (b : Bool) : ∃ f : Q 9 → ZMod 3,
      weightedAction (fun _ => 1) f = 0 ∧
      ∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b := by
  classical
  obtain ⟨s, hs⟩ := hC
  let z (x : Q 9) : ℤ := if x ∈ C then if s x = 1 then 1 else -1 else 0
  have hz (x : Q 9) : (z x : ℝ) = switchingVector C s x := by
    by_cases hx : x ∈ C
    · rcases hs.1 x hx with h | h <;> norm_num [z, switchingVector, hx, h]
    · simp [z, switchingVector, hx]
  have hreal : weightedAction (fun _ => (1 : ℝ)) (switchingVector C s) =
      (3 : ℝ) • switchingVector C s := by
    rw [← weightedLinear_apply, ComponentBoundary.Q9SignedContactCells.unit_weight]
    exact BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C s hreg hs
  have hint (x : Q 9) : weightedAction (fun _ => (1 : ℤ)) z x = 3 * z x := by
    apply Int.cast_injective (α := ℝ)
    simpa only [weightedAction, one_mul, Int.cast_sum, Int.cast_mul, Int.cast_id,
      Int.cast_ofNat, hz, Pi.smul_apply, smul_eq_mul] using congrFun hreal x
  let v (x : Q 9) : ZMod 3 := z x
  have hv (x : Q 9) : weightedAction (fun _ => (1 : ZMod 3)) v x = 0 := by
    have h := congrArg (fun k : ℤ => (k : ZMod 3)) (hint x)
    simpa [weightedAction, v, Int.cast_sum, Int.cast_mul, show (3 : ZMod 3) = 0 by decide] using h
  refine ⟨fun x => if parity x = b then v x else 0, ?_, ?_⟩
  · funext x
    have hpar (i : Fin 9) : parity (BalancedCriticalSpectrum.flip x i) = !parity x :=
      (Bool.not_eq_iff.mpr (cubeParity_ne_of_adj (flip_adj x i))).symm
    by_cases hx : (!parity x) = b
    · simpa only [weightedAction, hpar, hx, ite_true, Pi.zero_apply] using hv x
    · simp [weightedAction, hpar, hx]
  · intro x
    by_cases hx : x ∈ C
    · by_cases hp : parity x = b
      · by_cases hsx : s x = 1 <;> norm_num [v, z, hx, hp, hsx]
      · simp [hp]
    · simp [v, z, hx]

private theorem translate_adj {a x y : Q 9} :
    (hypercube 9).Adj (translate a x) (translate a y) ↔ (hypercube 9).Adj x y := by
  have forward (u v : Q 9) (h : (hypercube 9).Adj u v) :
      (hypercube 9).Adj (translate a u) (translate a v) := by
    obtain ⟨i, rfl⟩ := BalancedCubeGirth.adjacent_exists_flip h
    rw [translate_flip]
    exact flip_adj _ _
  exact ⟨fun h => by simpa only [translate_translate] using forward _ _ h, forward x y⟩

open Classical in
private theorem translate_support (D : Finset (Q 9)) (a : Q 9)
    (hD : IsBalanced D) (hreg : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3) :
    IsBalanced (D.image (translate a)) ∧
      ((hypercube 9).induce (D.image (translate a) : Set (Q 9))).IsRegularOfDegree 3 := by
  classical
  have hmem (x : Q 9) : x ∈ D.image (translate a) ↔ translate a x ∈ D := by
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      rwa [translate_translate]
    · intro hx
      exact Finset.mem_image.mpr ⟨translate a x, hx, translate_translate a x⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ := hD
    refine ⟨fun x => diagonalSign a (translate a x) * s (translate a x), ?_, ?_⟩
    · intro x hx
      have hsquare : (diagonalSign a (translate a x) * s (translate a x)) ^ 2 = 1 := by
        rw [mul_pow, diagonalSign_sq, switching_sq hs ((hmem x).mp hx), mul_one]
      exact sq_eq_one_iff.mp hsquare
    · intro x hx y hy hxy
      have h := (translate_adj (a := a)).mpr hxy
      obtain ⟨i, hi⟩ := BalancedCubeGirth.adjacent_exists_flip h
      have he := edge_covariance a (translate a x) i
      rw [← hi, translate_translate, translate_translate,
        hs.2 _ ((hmem x).mp hx) _ ((hmem y).mp hy) h] at he
      have hsign := switching_sq hs ((hmem x).mp hx)
      have hsign' := switching_sq hs ((hmem y).mp hy)
      calc
        huangMatrix 9 x y = (s (translate a x) * s (translate a y)) *
            ((s (translate a x) * s (translate a y)) * huangMatrix 9 x y) := by
          rw [← mul_assoc, ← pow_two, mul_pow, hsign, hsign', one_mul, one_mul]
        _ = _ := by rw [he]; ring
  · let e : ((hypercube 9).induce (D.image (translate a) : Set (Q 9))) ≃g
        ((hypercube 9).induce (D : Set (Q 9))) :=
        { toEquiv :=
            { toFun := fun x => ⟨translate a x, (hmem x).mp x.property⟩
              invFun := fun x => ⟨translate a x, (hmem _).mpr
                (by simpa only [translate_translate] using Finset.mem_coe.mp x.property)⟩
              left_inv := fun x => Subtype.ext (translate_translate a x)
              right_inv := fun x => Subtype.ext (translate_translate a x) }
          map_rel_iff' := fun {x y} => translate_adj (a := a) (x := x) (y := y) }
    intro x
    exact (e.degree_eq x).symm.trans (hreg.degree_eq (e x))

open Classical in
/-- On either parity, a balanced induced cubic support and any XOR translate of
another such support cannot meet in exactly one vertex. -/
theorem parity_overlap_card_ne_one (a : Q 9) (b : Bool) (C D : Finset (Q 9))
    (hC : IsBalanced C) (hD : IsBalanced D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3) :
    (((C ∩ D.image (fun x i => Bool.xor (a i) (x i))).filter
      (fun x => parity x = b)).card) ≠ 1 := by
  classical
  let T := D.image (translate a)
  obtain ⟨hT, hrT⟩ := translate_support D a hD hrD
  obtain ⟨f, hf, hsf⟩ := exists_signed_parity_word C hC hrC b
  obtain ⟨g, hg, hsg⟩ := exists_signed_parity_word T hT hrT b
  intro hcard
  change ((C ∩ T).filter (fun x => parity x = b)).card = 1 at hcard
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hprod (y : Q 9) : f y * g y ≠ 0 ↔ y ∈ (C ∩ T).filter (fun z => parity z = b) := by
    rw [mul_ne_zero_iff, hsf, hsg, Finset.mem_filter, Finset.mem_inter]
    tauto
  have hxne : f x * g x ≠ 0 := (hprod x).mpr (by rw [hx]; exact Finset.mem_singleton_self x)
  have hpair := kernel_pairing f g hf hg
  unfold dotProduct at hpair
  rw [Finset.sum_eq_single x] at hpair
  · exact hxne hpair
  · intro y _ hy
    by_contra h
    have hmem := (hprod y).mp h
    rw [hx, Finset.mem_singleton] at hmem
    exact hy hmem
  · simp

end D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ParityOverlap

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourAxisOrder
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourSearchCoverage

/-! Normalize actual halves and place them in the verified embedding search. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9GrayPlacementNormalForm (normalize normalize_hammingDist origin)
open private normalize_center from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private normalize_axis_order from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourAxisOrder
open private modelAt distance valid_model walk_of_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances
open private model_of_half from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelCoverage
open private hamming_encoded walk_dist liftPoint oppositeSize_lift from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCubeMetric
open private respects_prefix embedding_of_order from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourSearchCoverage
open private hamming embeddings mem_embeddings checked_placement models from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
open private cube_action_regular_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe

local notation "cubeFlip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable

private def liftPerm (σ : Equiv.Perm (Fin 8)) : Equiv.Perm (Fin 9) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv := Fin.cases (by simp) (fun i => by simp)
  right_inv := Fin.cases (by simp) (fun i => by simp)

private def omitCut (x : Q 9) : Q 8 := fun i => x i.succ

private theorem omit_flip (x : Q 9) (a : Fin 8) :
    omitCut (cubeFlip x a.succ) = cubeFlip (omitCut x) a := by
  funext i
  by_cases h : i = a
  · subst i
    simp [omitCut]
  · have hs : i.succ ≠ a.succ := fun he => h (Fin.succ_injective _ he)
    simp [omitCut, BalancedCriticalSpectrum.flip, h, hs]

private theorem omit_hamming {x y : Q 9} (h : x 0 = y 0) :
    hammingDist (omitCut x) (omitCut y) = hammingDist x y := by
  unfold hammingDist
  refine Finset.card_bij (fun i _ => i.succ) ?_ ?_ ?_
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · intro i hi j hj e
    exact Fin.succ_injective _ e
  · intro j hj
    induction j using Fin.cases with
    | zero => exact ((mem_filter.mp hj).2 h).elim
    | succ i => exact ⟨i, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩, rfl⟩

set_option maxRecDepth 4096 in
private theorem liftPoint_apply (x : BitVec 8) (i : Fin 9) :
    cubeBitVec 9 (liftPoint x.toNat) i = Fin.cases false (cubeBitVec 8 x) i := by
  decide +revert +kernel

private theorem encodeNormalized {x : Q 9} (h : x 0 = false) :
    cubeBitVec 9 (liftPoint ((cubeBitVec 8).symm (omitCut x)).toNat) = x := by
  funext i
  rw [liftPoint_apply]
  induction i using Fin.cases with
  | zero => exact h.symm
  | succ i => simp only [Fin.cases_succ, Equiv.apply_symm_apply, omitCut]

private theorem encode_flip (x : Q 9) (a : Fin 8) :
    ((cubeBitVec 8).symm (omitCut (cubeFlip x a.succ))).toNat =
      ((cubeBitVec 8).symm (omitCut x)).toNat ^^^ (1 <<< a.val) := by
  let u := (cubeBitVec 8).symm (omitCut x)
  have hu : (cubeBitVec 8).symm (omitCut (cubeFlip x a.succ)) =
      u ^^^ BitVec.ofNat 8 (2 ^ a.val) := by
    apply (cubeBitVec 8).injective
    rw [Equiv.apply_symm_apply, cubeBitVec_xor_single, omit_flip]
    simp only [u, Equiv.apply_symm_apply, BalancedCriticalSpectrum.flip]
  rw [hu, BitVec.toNat_xor, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) a.isLt),
    Nat.shiftLeft_eq, Nat.one_mul]

private theorem normalized_half_embedding {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    ∃ (index : Fin 53) (g : Q 9 ≃ Q 9) (σ : Equiv.Perm (Fin 9)) (placed : List Nat),
      (∀ x i, g (cubeFlip x i) = cubeFlip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      placed ∈ embeddings (modelAt index) [0] 0 ∧
      (∀ p ∈ placed, p < 256) ∧ (placed.map liftPoint).Nodup ∧
      (∀ x : BitVec 9, x ∈ placed.map liftPoint ↔
        cubeBitVec 9 x ∈ coordinateSlice (C.image g) false) := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  obtain ⟨index, point, hpoint⟩ := model_of_half hC hr hb b hs
  let model := modelAt index
  obtain ⟨hmodel, _, _, _, _, hparent, hpath⟩ := valid_model index
  change model.length = 23 at hmodel
  have hplane (i : Fin 24) : (point i).val 0 = b := (mem_filter.mp (point i).property).2
  let next (i : Fin 23) : Fin 24 := ⟨i.val + 1, by omega⟩
  let prev (i : Fin 23) : Fin 24 := ⟨model[i.val]!.1, (hparent i).1.trans (next i).isLt⟩
  have hlink (i : Fin 23) :
      ∃ a : Fin 8, (point (next i)).val = cubeFlip (point (prev i)).val a.succ := by
    have he := (hpoint (next i) (prev i)).mp (hparent i).2
    obtain ⟨axis, ha⟩ := adjacent_exists_flip he.symm
    induction axis using Fin.cases with
    | zero =>
      have hh := congrFun ha 0
      rw [BalancedCriticalSpectrum.flip_apply_same, hplane, hplane] at hh
      cases b <;> cases hh
    | succ i => exact ⟨i, ha⟩
  let edgeAxis (i : Fin 23) : Fin 8 := (hlink i).choose
  let axes := List.ofFn edgeAxis
  obtain ⟨p, hp⟩ := normalize_axis_order axes
  let σ := liftPerm p
  let o := (point 0).val
  let g := normalize σ.symm o
  have gflip := normalize_flip σ o
  have hcut (x : Q 9) : g x 0 = false ↔ x 0 = b := by
    change (x 0 != o 0) = false ↔ x 0 = b
    rw [show o 0 = b from hplane 0]
    cases x 0 <;> cases b <;> decide
  have hfalse (i : Fin 24) : g (point i).val 0 = false := (hcut _).mpr (hplane i)
  let bits (i : Fin 24) := (cubeBitVec 8).symm (omitCut (g (point i).val))
  let placed := List.ofFn (fun i => (bits i).toNat)
  have hencode (i : Fin 24) : cubeBitVec 9 (liftPoint (bits i).toNat) = g (point i).val :=
    encodeNormalized (hfalse i)
  have hroot : (bits 0).toNat = 0 := by
    have he : bits 0 = 0 := by
      apply (cubeBitVec 8).injective
      simp only [bits, Equiv.apply_symm_apply]
      rw [show g (point 0).val = origin from normalize_center σ.symm o]
      funext i
      exact (Nat.zero_testBit i.val).symm
    rw [he]
    rfl
  have hstep (i : Fin 23) : (bits (next i)).toNat =
      (bits (prev i)).toNat ^^^ (1 <<< (p (edgeAxis i)).val) := by
    change ((cubeBitVec 8).symm (omitCut (g (point (next i)).val))).toNat = _
    rw [(hlink i).choose_spec, gflip]
    exact encode_flip _ _
  have hdist (i j : Fin 24) (hij : i ≠ j) :
      let d := distance model i.val j.val
      let h := hamming (bits i).toNat (bits j).toNat
      0 < h ∧ h ≤ d ∧ (h = 1 ↔ d = 1) ∧ h % 2 = d % 2 := by
    have hham : hamming (bits i).toNat (bits j).toNat =
        hammingDist (point i).val (point j).val := by
      rw [hamming_encoded]
      simp only [bits, Equiv.apply_symm_apply]
      rw [omit_hamming ((hfalse i).trans (hfalse j).symm), normalize_hammingDist]
    obtain ⟨w, hw⟩ := walk_of_distance (G := G) model point
      (fun i j h => (hpoint i j).mp h) hpath i j
    obtain ⟨hle, hpar⟩ := walk_dist (G := G) Subtype.val (fun h => h) w
    rw [hw] at hle hpar
    dsimp only
    rw [hham]
    exact ⟨hammingDist_pos.mpr (fun he => hij (point.injective (Subtype.ext he))),
      hle, (hpoint i j).symm, hpar⟩
  have hplacedLen : placed.length = 24 := List.length_ofFn
  have hposition (i : Fin 24) : placed[i.val]'(hplacedLen.symm ▸ i.isLt) = (bits i).toNat :=
    List.getElem_ofFn _
  let used (k : Nat) := ((axes.take k).map Fin.val).eraseDups.length
  let axis (k : Nat) := (p (axes[k]!)).val
  have hm : placed ∈ embeddings model [0] 0 := by
    apply embedding_of_order model placed axis used (by omega)
    · rw [getElem!_pos placed 0 (by omega)]
      exact (hposition (0 : Fin 24)).trans hroot
    · rfl
    · intro k hk
      let i : Fin 23 := ⟨k, hmodel ▸ hk⟩
      have hai : k < axes.length := by
        rw [show axes.length = 23 from List.length_ofFn]
        exact i.isLt
      have he : axes[k]'hai = edgeAxis i := List.getElem_ofFn _
      have harm := hp k hai
      change (p (axes[k]'hai)).val < min (used k + 1) 8 ∧
        max (used k) ((p (axes[k]'hai)).val + 1) = used (k + 1) at harm
      have ha : axis k = (p (edgeAxis i)).val := by
        dsimp only [axis]
        rw [getElem!_pos axes k hai, he]
      rw [he, ← ha] at harm
      have hP : model[k].1 < k + 1 := by
        have hp := (hparent i).1
        change model[k]!.1 < k + 1 at hp
        simpa only [getElem!_pos model k hk] using hp
      refine ⟨hP, harm.1, harm.2.symm, ?_, ?_⟩
      · have hpv : (prev i).val = model[k].1 := by
          simp only [prev, show i.val = k from rfl, getElem!_pos model k hk]
        have hp1 : placed[model[k].1]! = (bits (prev i)).toNat :=
          (congrArg (fun j => placed[j]!) hpv.symm).trans
            ((getElem!_pos placed (prev i).val (hplacedLen.symm ▸ (prev i).isLt)).trans
              (hposition (prev i)))
        exact (hposition (next i)).trans ((hstep i).trans (by rw [ha, hp1]))
      · apply respects_prefix
        intro j hj
        let j' : Fin 24 := ⟨j, by omega⟩
        have hne : next i ≠ j' := fun h => by
          have he := congrArg Fin.val h
          change k + 1 = j at he
          omega
        simpa only [← hposition (next i), ← hposition j'] using hdist (next i) j' hne
  have hall : ∀ p ∈ placed, p < 256 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact (bits i).isLt
  have hinj : Function.Injective (fun i : Fin 24 => liftPoint (bits i).toNat) := by
    intro i j he
    apply point.injective
    apply Subtype.ext
    apply g.injective
    exact (hencode i).symm.trans ((congrArg (cubeBitVec 9) he).trans (hencode j))
  have hmap : placed.map liftPoint = List.ofFn (fun i => liftPoint (bits i).toNat) := by
    simp only [placed, List.map_ofFn, Function.comp_def]
  refine ⟨index, g, σ, placed, gflip, hcut, hm, hall, ?_, ?_⟩
  · rw [hmap, List.ofFn_eq_map]
    exact (List.nodup_finRange _).map hinj
  · intro x
    rw [hmap, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hencode]
      exact mem_filter.mpr ⟨mem_image.mpr ⟨(point i).val,
        (mem_filter.mp (point i).property).1, rfl⟩, hfalse i⟩
    · intro hx
      obtain ⟨hy, hzero⟩ := mem_filter.mp hx
      obtain ⟨y, hy, hgy⟩ := mem_image.mp hy
      have hb' : y 0 = b := (hcut _).mp (hgy ▸ hzero)
      let i := point.symm ⟨y, mem_filter.mpr ⟨hy, hb'⟩⟩
      refine ⟨i, (cubeBitVec 9).injective ?_⟩
      rw [hencode, point.apply_symm_apply]
      exact hgy

private theorem catalog_member (index : Fin 53) : modelAt index ∈ models := by
  have hsize : models.length = 53 := by decide +kernel
  change models[index.val]! ∈ models
  have hi := index.isLt.trans_eq hsize.symm
  rw [getElem!_pos models index.val hi]
  exact List.getElem_mem hi

/-- A balanced induced cubic support of order 72 has no coordinate cut
with a 24-vertex half. The reconstruction of such a half would require
at least 52 vertices in the opposite half. -/
theorem no_twenty_four_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) : (coordinateSlice C b).card ≠ 24 := by
  classical
  intro hs
  obtain ⟨index, g, σ, placed, hflip, hcut, hp, hbound, hn, hmem⟩ :=
    normalized_half_embedding hC hr hb b hs
  have h52 := checked_placement (catalog_member index) ((mem_embeddings _ _ _ _).mp hp)
  have hT := cube_action_regular_balanced g σ hflip hr hb
  rw [oppositeSize_lift placed hbound, Q9TwentyTwoReconstruction.reconstruction_size
    hT.1 hT.2 (placed.map liftPoint) hn hmem] at h52
  have hone (x : Q 9) : g x 0 = true ↔ x 0 = !b := by
    have h := hcut x
    cases hg : g x 0 <;> cases hx : x 0 <;> cases b <;> simp_all
  have he : coordinateSlice (C.image g) true = (coordinateSlice C (!b)).image g := by
    ext y
    constructor
    · intro hy
      obtain ⟨hy, hcut⟩ := mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, (hone x).mp hcut⟩, rfl⟩
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      obtain ⟨hx, hb⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_image.mpr ⟨x, hx, rfl⟩, (hone x).mpr hb⟩
  rw [he, card_image_of_injective _ g.injective] at h52
  have hparts : (coordinateSlice C b).card + (coordinateSlice C (!b)).card = C.card := by
    unfold coordinateSlice
    have h : C.filter (fun x => x 0 = !b) = C.filter (fun x => ¬x 0 = b) := by
      ext x
      cases b <;> cases hx : x 0 <;> simp [hx]
    rw [h]
    exact card_filter_add_card_filter_not (s := C) (fun x => x 0 = b)
  omega

#print axioms normalized_half_embedding
#print axioms no_twenty_four_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding

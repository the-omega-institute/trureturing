/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: At order 72, a lower bound of 28 in every half forces all pair patterns. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairFourStarShape
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairParallelHalf
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarOccupancy
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjectionOrbit
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding

/-! Pair coverage and the four-axis projection bound at the 28-point half threshold. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionSharp

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open HuangBalancedSymmetry (cube_action_regular_balanced)
open Q9MissingPairSignedFibers (prefixBits q9_missing_pair_zero_fiber_parity)
open Q9MissingPairFourStarShape
open Q9PairProjectionRefinement (missing_pair_halves_eq_twenty_eight)
open Q7FourStarOccupancy (Separated FourStarDecomposition leadingStar
  occupiedDirections neighborParity four_star_occupancy_product)
open Q7ParallelStarHalf (starIndicator)
open Q9MissingPairParallelHalf (q9_missing_pair_parallel_true_half_card)
open private append_prefix_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9MissingPairFourStarShape
open private normalize_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding
open private four_projection_card_ge_ten_of_pair_coverage from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjectionOrbit

local notation "cubeNormalize" => Q9GrayPlacementNormalForm.normalize
local notation "encodedStar" => Q7FourStarOccupancy.star
local notation "flip" => BalancedCriticalSpectrum.flip

private instance : Fintype (BitVec 7) :=
  Fintype.ofEquiv (Fin (2 ^ 7)) (BitVec.equivFin (m := 7)).toEquiv.symm

private theorem decode_flip {n : ℕ} (x : BitVec n) (i : Fin n) :
    cubeBitVec n (x ^^^ BitVec.twoPow n i.val) = flip (cubeBitVec n x) i := by
  have h : BitVec.twoPow n i.val = BitVec.ofNat n (2 ^ i.val) :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat])
  rw [h]
  exact cubeBitVec_xor_single x i

private theorem decode_append (low : BitVec 3) (high : BitVec 4) :
    cubeBitVec 7 (high ++ low) = Fin.append (cubeBitVec 3 low) (cubeBitVec 4 high) := by
  funext i
  refine Fin.addCases (m := 3) (n := 4) ?_ ?_ i
  · intro j
    rw [Fin.append_left]
    change (high ++ low).getLsbD j.val = low.getLsbD j.val
    rw [BitVec.getLsbD_append, ite_eq_left j.isLt]
  · intro j
    rw [Fin.append_right]
    change (high ++ low).getLsbD (3 + j.val) = high.getLsbD j.val
    rw [BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]

private def axisMask (axes : Finset (Fin 7)) : BitVec 7 :=
  (cubeBitVec 7).symm (fun i => decide (i ∈ axes))

private theorem decode_axisMask (axes : Finset (Fin 7)) (i : Fin 7) :
    (axisMask axes).getLsbD i.val = true ↔ i ∈ axes := by
  have h := congrFun ((cubeBitVec 7).apply_symm_apply (fun i => decide (i ∈ axes))) i
  change (axisMask axes).getLsbD i.val = decide (i ∈ axes) at h
  rw [h, decide_eq_true_eq]

private theorem axisMask_cpop {axes : Finset (Fin 7)} (h : axes.card = 3) :
    (axisMask axes).cpop = 3 := by
  have check : ∀ x : Fin 128,
      let v : BitVec 7 := BitVec.ofFin x
      (Finset.univ.filter fun i : Fin 7 => v.getLsbD i.val = true).card = 3 →
        v.cpop = 3 := by decide +kernel
  apply check (axisMask axes).toFin
  have he : (Finset.univ.filter fun i : Fin 7 => (axisMask axes).getLsbD i.val = true) = axes := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decode_axisMask]
  rw [he, h]

private theorem axisMask_root : axisMask {0, 1, 2} = 7 := by
  apply (cubeBitVec 7).injective
  rw [show axisMask {0, 1, 2} = (cubeBitVec 7).symm
    (fun i => decide (i ∈ ({0, 1, 2} : Finset (Fin 7)))) from rfl, Equiv.apply_symm_apply]
  funext i
  fin_cases i <;> decide +kernel

private theorem mem_encoded_star (x : BitVec 7) (c : Q 7) (a : Finset (Fin 7)) :
    x ∈ encodedStar ((cubeBitVec 7).symm c) (axisMask a) ↔ cubeBitVec 7 x ∈ starVertices c a := by
  simp only [Q7FourStarOccupancy.star, starVertices, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter,
    Finset.mem_univ, true_and, decode_axisMask]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl ((cubeBitVec 7).apply_symm_apply c)
    · exact Or.inr ⟨i, hi, by rw [decode_flip, Equiv.apply_symm_apply]⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact Or.inl ((cubeBitVec 7).injective (hx.trans ((cubeBitVec 7).apply_symm_apply c).symm))
    · exact Or.inr ⟨i, hi, (cubeBitVec 7).injective (by
        rw [decode_flip, Equiv.apply_symm_apply, hx])⟩

private theorem encoded_four_stars {T : Finset (Q 9)} {c : Fin 4 → Q 7}
    {a : Fin 4 → Finset (Fin 7)}
    (h : FourStarShape (fun x => Fin.append (prefixBits false false) x ∈ T) c a)
    (hc : c 0 = fun _ => false) (ha : a 0 = {0, 1, 2}) :
    let S := Finset.univ.filter (fun x : BitVec 7 =>
      Fin.append (prefixBits false false) (cubeBitVec 7 x) ∈ T)
    let enc := (cubeBitVec 7).symm ∘ c
    FourStarDecomposition S (enc 1) (enc 2) (enc 3)
      (axisMask (a 1)) (axisMask (a 2)) (axisMask (a 3)) := by
  let enc := (cubeBitVec 7).symm ∘ c
  let stars (i : Fin 4) := encodedStar (enc i) (axisMask (a i))
  have hroot : stars 0 = encodedStar 0 7 := by
    have hzero : enc 0 = 0 := by
      apply (cubeBitVec 7).injective
      simp only [enc, Function.comp_apply, Equiv.apply_symm_apply, hc]
      funext i
      exact (BitVec.getLsbD_zero).symm
    simp only [stars, hzero, ha, axisMask_root]
  have hsep {i j : Fin 4} (hij : i ≠ j) : Separated (stars i) (stars j) := by
    intro x hx y hy
    obtain ⟨hne, hedge⟩ := h.separated hij ((mem_encoded_star x _ _).mp hx)
      ((mem_encoded_star y _ _).mp hy)
    refine ⟨fun he => hne (congrArg (cubeBitVec 7) he), fun k he => hedge k ?_⟩
    rw [← decode_flip, he]
  refine ⟨?_, axisMask_cpop (h.axes_card 1), axisMask_cpop (h.axes_card 2),
    axisMask_cpop (h.axes_card 3), hroot ▸ hsep (by decide : (0 : Fin 4) ≠ 1),
    hroot ▸ hsep (by decide : (0 : Fin 4) ≠ 2), hroot ▸ hsep (by decide : (0 : Fin 4) ≠ 3),
    hsep (by decide : (1 : Fin 4) ≠ 2), hsep (by decide : (1 : Fin 4) ≠ 3),
    hsep (by decide : (2 : Fin 4) ≠ 3)⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change _ ↔ x ∈ encodedStar 0 7 ∪ stars 1 ∪ stars 2 ∪ stars 3
  rw [← hroot, h.mem_iff]
  simp only [Finset.mem_union]
  constructor
  · rintro ⟨i, hi, _⟩
    have hm : x ∈ stars i := (mem_encoded_star x _ _).mpr hi
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl hm))
    · exact Or.inl (Or.inl (Or.inr hm))
    · exact Or.inl (Or.inr hm)
    · exact Or.inr hm
  · intro hx
    have hmem : ∃ i, x ∈ stars i := by
      rcases hx with ((h₀ | h₁) | h₂) | h₃
      · exact ⟨0, h₀⟩
      · exact ⟨1, h₁⟩
      · exact ⟨2, h₂⟩
      · exact ⟨3, h₃⟩
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, (mem_encoded_star x _ _).mp hi, fun j hj => ?_⟩
    by_contra hij
    exact ((hsep hij) x ((mem_encoded_star x _ _).mpr hj) x hi).1 rfl

private theorem half_card_normalize (S : Finset (Q 9)) (p : Equiv.Perm (Fin 9))
    (o : Q 9) (k : Fin 9) (b : Bool) :
    ((S.image (cubeNormalize p.symm o)).filter (fun x => x k = b)).card =
      (S.filter (fun x => x (p.symm k) = (b != o (p.symm k)))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ (cubeNormalize p.symm o).injective]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  change (x (p.symm k) != o (p.symm k)) = b ↔ x (p.symm k) = (b != o (p.symm k))
  cases x (p.symm k) <;> cases o (p.symm k) <;> cases b <;> decide

private def suffixPermutation (p : Equiv.Perm (Fin 7)) : Equiv.Perm (Fin 9) :=
  (finSumFinEquiv (m := 2) (n := 7)).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) p).trans finSumFinEquiv)

private theorem suffixPermutation_symm_left (p : Equiv.Perm (Fin 7)) (i : Fin 2) :
    (suffixPermutation p).symm (i.castAdd 7) = i.castAdd 7 := by
  change finSumFinEquiv (Sum.map id p.symm
    ((finSumFinEquiv (m := 2) (n := 7)).symm (i.castAdd 7))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem suffixPermutation_symm_right (p : Equiv.Perm (Fin 7)) (i : Fin 7) :
    (suffixPermutation p).symm (i.natAdd 2) = (p.symm i).natAdd 2 := by
  change finSumFinEquiv (Sum.map id p.symm
    ((finSumFinEquiv (m := 2) (n := 7)).symm (i.natAdd 2))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

private theorem coordinateAction_eq_normalize (p : Equiv.Perm (Fin 7)) (o : Q 7) :
    coordinateAction p o = cubeNormalize (suffixPermutation p).symm
      (Fin.append (fun _ : Fin 2 => false) o) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨u, v⟩, rfl⟩ := (Fin.appendEquiv 2 7).surjective x
  change coordinateAction p o (Fin.append u v) = cubeNormalize (suffixPermutation p).symm
    (Fin.append (fun _ : Fin 2 => false) o) (Fin.append u v)
  rw [coordinateAction_append]
  funext i
  refine Fin.addCases (m := 2) (n := 7) ?_ ?_ i
  · intro j
    change Fin.append u (suffixAction p o v) (j.castAdd 7) =
      (Fin.append u v ((suffixPermutation p).symm (j.castAdd 7)) !=
        Fin.append (fun _ : Fin 2 => false) o ((suffixPermutation p).symm (j.castAdd 7)))
    simp only [suffixPermutation_symm_left, Fin.append_left, Bool.bne_false]
  · intro j
    change Fin.append u (suffixAction p o v) (j.natAdd 2) =
      (Fin.append u v ((suffixPermutation p).symm (j.natAdd 2)) !=
        Fin.append (fun _ : Fin 2 => false) o ((suffixPermutation p).symm (j.natAdd 2)))
    simp only [suffixPermutation_symm_right, Fin.append_right]
    rfl

open Classical in
/-- An absent 11 prefix with both TRUE prefix halves of size at least 28
forces a coordinate half of size 20. -/
theorem exists_half_card_twenty_of_missing_prefix {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hmissing : ∀ x : Q 7, Fin.append (prefixBits true true) x ∉ S)
    (h0 : 28 ≤ (S.filter fun x => x 0 = true).card)
    (h1 : 28 ≤ (S.filter fun x => x 1 = true).card) :
    ∃ (k : Fin 9) (b : Bool), (S.filter fun x => x k = b).card = 20 := by
  obtain ⟨c, a, hshape⟩ := missing_pair_four_star_shape hsize hreg hb hmissing h0 h1
  obtain ⟨p, hshape', hc, ha⟩ := hshape.normalize
  let g := coordinateAction p (c 0)
  let T := S.image g
  have hmap : S.map g.toEmbedding = T := Finset.map_eq_image g.toEmbedding S
  change FourStarShape (fun x => Fin.append (prefixBits false false) x ∈ S.map g.toEmbedding)
    (suffixAction p (c 0) ∘ c) (fun i => (a i).map p.toEmbedding) at hshape'
  rw [hmap] at hshape'
  let q := suffixPermutation p
  let o : Q 9 := Fin.append (fun _ : Fin 2 => false) (c 0)
  have hg : g = cubeNormalize q.symm o := coordinateAction_eq_normalize p (c 0)
  obtain ⟨hrT, hbT⟩ := cube_action_regular_balanced g q
    (fun x i => by rw [hg, normalize_flip]) hreg hb
  have hsizeT : T.card = 72 := (Finset.card_image_of_injective S g.injective).trans hsize
  have hhalf (k : Fin 9) (b : Bool) :
      (T.filter (fun x => x k = b)).card =
        (S.filter (fun x => x (q.symm k) = (b != o (q.symm k)))).card := by
    simpa only [T, hg] using half_card_normalize S q o k b
  have hprefix (i : Fin 2) :
      (T.filter (fun x => x (i.castAdd 7) = true)).card =
        (S.filter (fun x => x (i.castAdd 7) = true)).card := by
    simpa only [q, suffixPermutation_symm_left, o, Fin.append_left, Bool.bne_false]
      using hhalf (i.castAdd 7) true
  have hmissingT (x : Q 7) : Fin.append (prefixBits true true) x ∉ T := by
    obtain ⟨y, rfl⟩ := (suffixAction p (c 0)).surjective x
    rw [← coordinateAction_append]
    rintro hx
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hx
    exact hmissing y (g.injective he ▸ hv)
  have hmissingT' : ¬ ∃ x ∈ T, x 0 = true ∧ x 1 = true := by
    rintro ⟨x, hx, hp⟩
    obtain ⟨y, rfl⟩ := (append_prefix_iff true true x).mpr hp
    exact hmissingT y hx
  obtain ⟨h0T, _, _⟩ := missing_pair_halves_eq_twenty_eight hsizeT hrT hbT
    (by decide : (0 : Fin 9) ≠ 1) hmissingT' ((hprefix 0).symm ▸ h0) ((hprefix 1).symm ▸ h1)
  let A := Finset.univ.filter (fun x : BitVec 7 =>
    Fin.append (prefixBits false false) (cubeBitVec 7 x) ∈ T)
  have hA (x : BitVec 7) :
      x ∈ A ↔ Fin.append (prefixBits false false) (cubeBitVec 7 x) ∈ T := by simp [A]
  have hpar (x : BitVec 7) : decide (x ∈ A) = neighborParity A x := by
    have hdirs : occupiedDirections A x = Finset.univ.filter (fun i : Fin 7 =>
        Fin.append (prefixBits false false) (flip (cubeBitVec 7 x) i) ∈ T) := by
      ext i
      simp only [occupiedDirections, Finset.mem_filter, hA, decode_flip]
    unfold neighborParity
    rw [hdirs, q9_missing_pair_zero_fiber_parity (C := T) hrT hbT hmissingT]
    by_cases hx : Fin.append (prefixBits false false) (cubeBitVec 7 x) ∈ T
    · rw [ite_eq_left hx, decide_eq_true ((hA x).2 hx)]
      rfl
    · have hn : x ∉ A := fun hm => hx ((hA x).1 hm)
      rw [ite_eq_right hx, decide_eq_false hn]
      rfl
  obtain ⟨P, hP, _, hind, hproduct⟩ :=
    four_star_occupancy_product (encoded_four_stars hshape' hc ha) hpar
  change A = _ at hproduct
  let centers := P.map (cubeBitVec 4).toEmbedding
  have hindependent (y : Q 4) (hy : y ∈ centers) (j : Fin 4) : flip y j ∉ centers := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    change flip (cubeBitVec 4 v) j ∉ centers
    rw [← decode_flip]
    intro hz
    have hvj : v ^^^ BitVec.twoPow 4 j.val ∈ P := by
      exact (Finset.mem_map' (cubeBitVec 4).toEmbedding).mp hz
    have hne : v ≠ v ^^^ BitVec.twoPow 4 j.val := by
      intro he
      have hbit := congrFun (congrArg (cubeBitVec 4) he) j
      rw [decode_flip, BalancedCriticalSpectrum.flip_apply_same] at hbit
      have hne' : ∀ b : Bool, b ≠ !b := by decide
      exact hne' _ hbit
    exact hind hv hvj hne j rfl
  have hstar : ∀ x : Q 3, x ∈ leadingStar.map (cubeBitVec 3).toEmbedding ↔
      starIndicator x = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := (cubeBitVec 3).surjective x
    rw [show cubeBitVec 3 v = (cubeBitVec 3).toEmbedding v from rfl, Finset.mem_map']
    let i := v.toFin
    change BitVec.ofFin (w := 3) i ∈ leadingStar ↔ starIndicator (cubeBitVec 3 (BitVec.ofFin i)) = 1
    clear_value i
    fin_cases i <;> decide +kernel
  have hstars (x : Q 3) (y : Q 4) :
      Fin.append (prefixBits false false) (Fin.append x y) ∈ T ↔
        starIndicator x = 1 ∧ y ∈ centers := by
    obtain ⟨l, rfl⟩ := (cubeBitVec 3).surjective x
    obtain ⟨u, rfl⟩ := (cubeBitVec 4).surjective y
    rw [← decode_append, ← hA, hproduct, ← hstar]
    change (u ++ l) ∈ (leadingStar ×ˢ P).image (fun v => v.2 ++ v.1) ↔
      (cubeBitVec 3).toEmbedding l ∈ leadingStar.map (cubeBitVec 3).toEmbedding ∧
      (cubeBitVec 4).toEmbedding u ∈ P.map (cubeBitVec 4).toEmbedding
    rw [Finset.mem_map', Finset.mem_map']
    constructor
    · intro hx
      obtain ⟨⟨l', u'⟩, hm, he⟩ := Finset.mem_image.mp hx
      have he' := congrArg (cubeBitVec 7) he
      simp only [decode_append] at he'
      change (Fin.appendEquiv 3 4) (cubeBitVec 3 l', cubeBitVec 4 u') =
        (Fin.appendEquiv 3 4) (cubeBitVec 3 l, cubeBitVec 4 u) at he'
      have hpair := (Fin.appendEquiv 3 4).injective he'
      have hl := (cubeBitVec 3).injective (congrArg Prod.fst hpair)
      have hu := (cubeBitVec 4).injective (congrArg Prod.snd hpair)
      subst l'
      subst u'
      exact Finset.mem_product.mp hm
    · intro hx
      exact Finset.mem_image.mpr ⟨(l, u), Finset.mem_product.mpr hx, rfl⟩
  let k := ((0 : Fin 3).castAdd 4).natAdd 2
  have h20 := q9_missing_pair_parallel_true_half_card hrT hbT hmissingT h0T centers
    ((Finset.card_map _).trans hP) hindependent hstars 0
  exact ⟨q.symm k, (true != o (q.symm k)), (hhalf k true).symm.trans h20⟩

open Classical in
/-- Every assignment on two distinct coordinates occurs at the 28-point half threshold. -/
theorem pair_projection_surjective_of_twenty_eight {S : Finset (Q 9)}
    (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (k : Fin 9) (r : Bool), 28 ≤ (S.filter (fun x => x k = r)).card)
    {i j : Fin 9} (hij : i ≠ j) (b c : Bool) :
    ∃ x ∈ S, x i = b ∧ x j = c := by
  by_contra hmissing
  let axes : Fin 2 → Fin 9 := Fin.cases i (fun _ => j)
  let target : Fin 2 → Fin 9 := fun k => k.castAdd 7
  have hinj : Function.Injective axes := by
    intro k l h
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hij h).elim
    · exact (hij h.symm).elim
    · rfl
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair axes target hinj
    (Fin.castAdd_injective 2 7)
  have hp0 : p.symm 0 = i := p.symm_apply_eq.mpr (hp 0).symm
  have hp1 : p.symm 1 = j := p.symm_apply_eq.mpr (hp 1).symm
  let o : Q 9 := fun k => if k = i then !b else !c
  let g := cubeNormalize p.symm o
  let T := S.image g
  obtain ⟨hrT, hbT⟩ := cube_action_regular_balanced g p (normalize_flip p o) hreg hb
  have hsizeT : T.card = 72 := (Finset.card_image_of_injective S g.injective).trans hsize
  have hhalfT (k : Fin 9) (r : Bool) : 28 ≤ (T.filter (fun x => x k = r)).card :=
    (half_card_normalize S p o k r).symm ▸ hhalf (p.symm k) (r != o (p.symm k))
  have hforce (r s : Bool) (h : (r != !s) = true) : r = s := by
    cases r <;> cases s <;> simp_all
  have hmissingT (y : Q 7) : Fin.append (prefixBits true true) y ∉ T := by
    intro hy
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hy
    have hx0 : (x (p.symm 0) != o (p.symm 0)) = true := congrFun he 0
    have hx1 : (x (p.symm 1) != o (p.symm 1)) = true := congrFun he 1
    rw [hp0, show o i = !b by simp [o]] at hx0
    rw [hp1, show o j = !c by simp [o, hij.symm]] at hx1
    exact hmissing ⟨x, hx, hforce _ _ hx0, hforce _ _ hx1⟩
  obtain ⟨k, r, h20⟩ := exists_half_card_twenty_of_missing_prefix hsizeT hrT hbT hmissingT
    (hhalfT 0 true) (hhalfT 1 true)
  exact (by decide : ¬ 28 ≤ 20) (h20 ▸ hhalfT k r)

open Classical in
/-- Every four-axis projection realizes at least ten patterns at the 28-point half threshold. -/
theorem four_projection_card_ge_ten_of_twenty_eight {S : Finset (Q 9)}
    (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (k : Fin 9) (b : Bool), 28 ≤ (S.filter (fun x => x k = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    10 ≤ (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card := by
  apply four_projection_card_ge_ten_of_pair_coverage hsize hreg hb
    (fun k b => (by decide : 24 < 28).trans_le (hhalf k b)) axes
  intro i j hij b c
  exact pair_projection_surjective_of_twenty_eight hsize hreg hb hhalf
    (axes.injective.ne hij) b c

#print axioms exists_half_card_twenty_of_missing_prefix
#print axioms pair_projection_surjective_of_twenty_eight
#print axioms four_projection_card_ge_ten_of_twenty_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionSharp

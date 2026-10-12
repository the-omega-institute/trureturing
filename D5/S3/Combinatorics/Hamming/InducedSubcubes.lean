/- GID: D5/S3/Combinatorics/Hamming/InducedSubcubes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/InducedSubcubes
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Induced subcubes of the Boolean hypercube are coordinate down-cubes. -/

/-
Declaration classifications after expansion of both same-delivery modules.
toggle: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): edgeDir, edgeDir_constant, edgeDir_injective, edgeDir_spec, hamming_one_iff_toggle, invariant_of_toggles, mapped_coordinate, mapped_fixed, mapped_toggle, toggle_injective, toggle_other, toggle_same, toggle_twice.
toggle_same: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir_constant, edgeDir_spec, hamming_one_iff_toggle, mapped_coordinate, toggle_injective, toggle_twice.
toggle_other: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir_spec, hamming_one_iff_toggle, mapped_coordinate, mapped_fixed, toggle_injective, toggle_twice.
toggle_twice: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir_constant.
toggle_injective: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir_constant, edgeDir_injective.
hamming_one_iff_toggle: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir, edgeDir_spec.
edgeDir: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): directions, edgeDir_constant, edgeDir_injective, edgeDir_spec, mapped_toggle.
edgeDir_spec: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): edgeDir_constant, edgeDir_injective, mapped_toggle.
edgeDir_injective: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): directions_injective.
invariant_of_toggles: proof_shape: content; reason: Finite-set induction connects arbitrary Boolean words; no frozen constancy theorem supplies the generic statement. Consumer(s): mapped_coordinate, mapped_fixed.
edgeDir_constant: proof_shape: bind-only; reason: Applies CapacityBoxOneBitRigidity.colour_depends_only_on_layer at constant capacities one, using finTwoEquiv and reversal of one Boolean edge. Consumer(s): mapped_toggle.
directions: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): cube_map_image, mapped_coordinate, mapped_fixed, mapped_toggle.
directions_injective: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): cube_map_image, mapped_coordinate.
mapped_toggle: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): mapped_coordinate, mapped_fixed.
mapped_coordinate: proof_shape: content; reason: Same-delivery invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cube_map_image.
mapped_fixed: proof_shape: content; reason: Same-delivery invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): cube_map_image.
cube_map_image: proof_shape: content; reason: Same-delivery invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): induced_cube_coordinates.
induced_cube_coordinates: proof_shape: content; reason: Same-delivery invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): induced_cube_downCube.
coordinateSet: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): coordinateIso, downCube_eq_coordinateSet, downCube_is_cube, induced_cube_downCube.
coordinateIso: proof_shape: content; reason: Constructs the free-coordinate equivalence and proves its Hamming-distance preservation by a coordinate bijection. Consumer(s): downCube_is_cube.
erase: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): CubeData, all_erasures_iff_endpoints, endpointDataEquiv, erase_endpoints_admissible, erase_false, erase_insert_flip, instFintypeCubeData, realize, realizeCube, realizeCube_bijective, realize_wordSet, downCube, downCube_eq_coordinateSet, downCube_le_top, downCube_unique, erase_empty, top_mem_downCube.
downCube: proof_shape: bind-only; reason: Defining expression or consumed construction from existing types and operations; no independent content claim. Consumer(s): am_cube_iff, realize, realizeCube, realizeCube_bijective, realize_wordSet, downCube_eq_coordinateSet, downCube_is_cube, downCube_le_top, downCube_unique, induced_cube_downCube, induced_cube_iff.
erase_empty: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): all_erasures_iff_endpoints, endpointDataEquiv, erase_endpoints_admissible, top_mem_downCube.
top_mem_downCube: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): downCube_unique.
downCube_eq_coordinateSet: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): downCube_is_cube, induced_cube_downCube.
induced_cube_downCube: proof_shape: content; reason: Same-delivery invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): induced_cube_iff.
downCube_is_cube: proof_shape: content; reason: Same-delivery coordinateIso survives expansion and the normalization bypass test. Consumer(s): induced_cube_iff.
downCube_le_top: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): downCube_unique.
downCube_unique: proof_shape: bind-only; reason: Instantiation, logical projection or normalization of frozen/Mathlib facts and consumed bind-only helpers. Consumer(s): realizeCube, realizeCube_bijective, induced_cube_iff.
induced_cube_iff: proof_shape: content; reason: Same-delivery coordinateIso, invariant_of_toggles survives expansion and the normalization bypass test. Consumer(s): am_cube_iff.
escape_witness: invariant_of_toggles, coordinateIso, cube_map_image; each survives the frozen-fact normalization bypass test.
admission_basis: escape-witness
Direct frozen dependencies of cube_map_image: D5/S1/Ledger/BoundedTimeSlice.TailBox declaration statement_id sha256:620077c2b062d7fe99c8f2b63a7de76d46b66b50be885158d6789d33674e0286; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding declaration statement_id sha256:a382277d81d40c7eb5f352799d8c10bdde5b5649714064ff9e0885d7d67fdbe7; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.map_unitEdge declaration statement_id sha256:767b7fc5a4102b476eb54cecb7fe3e0a06d112370bb9a3b3394d7d150612f373; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.mk declaration statement_id sha256:e4c3d965229119470ae5f69ebb1e015ad2684edfa8fbe6d18bba0de6eb334fad; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.toFun declaration statement_id sha256:3e37a2305777f9f61aa663652629c9c460a1bdcafa91439d6f2bc062cd4ed071; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge declaration statement_id sha256:457db4d7949335f6c43fa28b765a322e169ba2b8122789fc1c0ea9a2007fe639; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer declaration statement_id sha256:756a195ca04f1f89025d96b4fa6b88f2e91e02baca9fc208167fffe1994b895d; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour declaration statement_id sha256:abe4bfcc54e3a0011447fcd2c82806ae732c85e31b1a12547da2b525b09c211c; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise declaration statement_id sha256:6a4867e887abad6d640d288504030c6930ab4631bcd86fa3d882216fcbabed43; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity._proof_1 declaration statement_id sha256:a0d1eec21077c6eec5b3e628b462854a639d42698e64694f38657df573238a25; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour declaration statement_id sha256:ea64aea534233b0857077988bfc0b75da4e3471c43ee925e69dc824648c33e9c.
Direct frozen dependencies of erase_empty: none.
Direct frozen dependencies of top_mem_downCube: none.
Direct frozen dependencies of downCube_unique: none.
Direct frozen dependencies of induced_cube_iff: D5/S1/Ledger/BoundedTimeSlice.TailBox declaration statement_id sha256:620077c2b062d7fe99c8f2b63a7de76d46b66b50be885158d6789d33674e0286; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding declaration statement_id sha256:a382277d81d40c7eb5f352799d8c10bdde5b5649714064ff9e0885d7d67fdbe7; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.map_unitEdge declaration statement_id sha256:767b7fc5a4102b476eb54cecb7fe3e0a06d112370bb9a3b3394d7d150612f373; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.mk declaration statement_id sha256:e4c3d965229119470ae5f69ebb1e015ad2684edfa8fbe6d18bba0de6eb334fad; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.toFun declaration statement_id sha256:3e37a2305777f9f61aa663652629c9c460a1bdcafa91439d6f2bc062cd4ed071; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge declaration statement_id sha256:457db4d7949335f6c43fa28b765a322e169ba2b8122789fc1c0ea9a2007fe639; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.colour_depends_only_on_layer declaration statement_id sha256:756a195ca04f1f89025d96b4fa6b88f2e91e02baca9fc208167fffe1994b895d; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour declaration statement_id sha256:abe4bfcc54e3a0011447fcd2c82806ae732c85e31b1a12547da2b525b09c211c; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise declaration statement_id sha256:6a4867e887abad6d640d288504030c6930ab4631bcd86fa3d882216fcbabed43; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity._proof_1 declaration statement_id sha256:a0d1eec21077c6eec5b3e628b462854a639d42698e64694f38657df573238a25; D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour declaration statement_id sha256:ea64aea534233b0857077988bfc0b75da4e3471c43ee925e69dc824648c33e9c; D5/S3/Combinatorics/Graph/Hypercube.hypercube declaration statement_id sha256:e70c1ce92111881fa6bcced6ddb8eeb908912e4c390ec989d4c1880ebc362345.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15283; typed realization and sensitivity evidence is not supplied.
-/

import D5.S3.Combinatorics.Graph.Hypercube
import D5.S3.Arith.Coding.CapacityBoxOneBitRigidity

namespace D5.S3.Combinatorics.Hamming.InducedSubcubes

open D5.S3.Combinatorics.Graph.Hypercube
open scoped BigOperators
noncomputable section
open Classical
set_option maxHeartbeats 2000000

private def toggle {ι : Type*} [DecidableEq ι] (u : ι → Bool) (i : ι) : ι → Bool :=
  Function.update u i (!u i)

@[simp] private theorem toggle_same {ι : Type*} [DecidableEq ι] (u : ι → Bool) (i : ι) :
    toggle u i i = !u i := by simp [toggle]

@[simp] private theorem toggle_other {ι : Type*} [DecidableEq ι] (u : ι → Bool) (i j : ι)
    (h : j ≠ i) : toggle u i j = u j := by simp [toggle, Function.update_of_ne h]

@[simp] private theorem toggle_twice {ι : Type*} [DecidableEq ι] (u : ι → Bool) (i : ι) :
    toggle (toggle u i) i = u := by
  funext j
  by_cases h : j = i <;> simp [h, toggle_other]


private theorem toggle_injective {ι : Type*} [DecidableEq ι] (u : ι → Bool) :
    Function.Injective (toggle u) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp [toggle_other, hij, ne_comm] at hh

private theorem hamming_one_iff_toggle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → Bool) : hammingDist u v = 1 ↔ ∃ i, v = toggle u i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine ⟨i, ?_⟩
    funext j
    have he : u j ≠ v j ↔ j = i := by
      have hj := Finset.ext_iff.mp hi j
      simpa using hj
    by_cases hj : j = i
    · subst j
      have hne := he.mpr rfl
      cases hu : u i <;> cases hv : v i <;> simp_all
    · have hh : u j = v j := by tauto
      simpa [toggle_other, hj] using hh.symm
  · rintro ⟨i, rfl⟩
    change (Finset.univ.filter (fun j => u j ≠ toggle u i j)).card = 1
    have hs : Finset.univ.filter (fun j => u j ≠ toggle u i j) = {i} := by
      ext j
      by_cases hj : j = i <;> simp [hj, toggle_other]
    rw [hs, Finset.card_singleton]



variable {k n : ℕ} (f : (Fin k → Bool) → (Fin n → Bool))
    (hf : Function.Injective f)
    (he : ∀ u v, hammingDist u v = 1 → hammingDist (f u) (f v) = 1)

private def edgeDir (u : Fin k → Bool) (i : Fin k) : Fin n :=
  D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.edgeColour
    (he u (toggle u i) ((hamming_one_iff_toggle u (toggle u i)).mpr ⟨i, rfl⟩))

private theorem edgeDir_spec (u : Fin k → Bool) (i : Fin k) :
    f (toggle u i) = toggle (f u) (edgeDir f he u i) := by
  have h := he u (toggle u i) ((hamming_one_iff_toggle u (toggle u i)).mpr ⟨i, rfl⟩)
  have hs : Finset.univ.filter (fun q => f u q ≠ f (toggle u i) q) =
      {edgeDir f he u i} := Classical.choose_spec (Finset.card_eq_one.mp h)
  funext q
  have heq : f u q ≠ f (toggle u i) q ↔ q = edgeDir f he u i := by
    have hh := Finset.ext_iff.mp hs q
    simpa using hh
  by_cases hq : q = edgeDir f he u i
  · subst q
    have hne := heq.mpr rfl
    cases ha : f u (edgeDir f he u i) <;>
      cases hb : f (toggle u i) (edgeDir f he u i) <;> simp_all
  · have hh : f u q = f (toggle u i) q := by tauto
    simpa [toggle_other, hq] using hh.symm

include hf in
private theorem edgeDir_injective (u : Fin k → Bool) :
    Function.Injective (edgeDir f he u) := by
  intro i j h
  apply toggle_injective u
  apply hf
  rw [edgeDir_spec f he u i, edgeDir_spec f he u j, h]


/-- A function on a finite Boolean cube invariant under every coordinate toggle is constant. -/
private theorem invariant_of_toggles {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → Bool) → α) (hg : ∀ u i, g (toggle u i) = g u)
    (u v : ι → Bool) : g u = g v := by
  have h : ∀ s : Finset ι, ∀ a b : ι → Bool,
      (∀ i, i ∉ s → a i = b i) → g a = g b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a b hab
      exact congrArg g (funext (fun i => hab i (by simp)))
    | @insert i s hi ih =>
      intro a b hab
      let c := Function.update a i (b i)
      have hac : g a = g c := by
        by_cases hbit : a i = b i
        · have hc : c = a := by simp [c, ← hbit]
          rw [hc]
        · have hc : c = toggle a i := by
            change Function.update a i (b i) = Function.update a i (!a i)
            apply congrArg (Function.update a i)
            cases hai : a i <;> cases hbi : b i <;> simp_all
          rw [hc, hg]
      refine hac.trans (ih c b ?_)
      intro j hj
      by_cases hji : j = i
      · simp [c, hji]
      · rw [show c j = a j by simp [c, Function.update_of_ne hji]]
        exact hab j (by simp [hji, hj])
  exact h Finset.univ u v (by simp)

include hf in
private theorem edgeDir_constant (u : Fin k → Bool) (i : Fin k) :
    edgeDir f he u i = edgeDir f he (fun _ => false) i := by
  let decode := fun a : D5.S1.Ledger.BoundedTimeSlice.TailBox (fun _ : Fin k => 1) =>
    fun j => finTwoEquiv (a j)
  let φ : D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.OneBitEmbedding
      (fun _ : Fin k => 1) n := {
    toFun := fun a => f (decode a)
    injective := by
      intro a b h
      funext j
      exact finTwoEquiv.injective (congrFun (hf h) j)
    map_unitEdge := by
      intro p a b hab
      apply he
      change (Finset.univ.filter (fun j => decode a j ≠ decode b j)).card = 1
      have hs : Finset.univ.filter (fun j => decode a j ≠ decode b j) = {p} := by
        ext j
        by_cases hj : j = p
        · subst j
          have ha : (a p).val < 2 := (a p).isLt
          have hb : (b p).val < 2 := (b p).isLt
          have hp := hab.1
          have ha0 : (a p).val = 0 := by omega
          have hb1 : (b p).val = 1 := by omega
          simp [decode, show a p = 0 from Fin.ext ha0, show b p = 1 from Fin.ext hb1, finTwoEquiv]
        · simp [decode, hab.2 j hj, hj]
      rw [hs, Finset.card_singleton] }
  have colour_eq : ∀ a (ha : (a i).val < 1),
      D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.unitEdgeColour φ a i ha =
        edgeDir f he (decode a) i := by
    intro a ha
    have hr : decode (D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise a i ha) =
        toggle (decode a) i := by
      funext j
      by_cases hj : j = i
      · subst j
        have ha0 : (a i).val = 0 := by omega
        simp [decode, D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise,
          toggle, finTwoEquiv, show a i = 0 from Fin.ext ha0]
      · simp [decode, D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise,
          toggle, hj]
    have hh : Finset.univ.filter
        (fun q => f (decode a) q ≠ f (decode
          (D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise a i ha)) q) =
        {D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.unitEdgeColour φ a i ha} :=
      Classical.choose_spec (Finset.card_eq_one.mp
        (φ.map_unitEdge i a (D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise a i ha)
          (by
            constructor
            · simp [D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise]
            · intro q hq
              simp [D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise, hq])))
    have hm : edgeDir f he (decode a) i ∈ Finset.univ.filter
        (fun q => f (decode a) q ≠ f (decode
          (D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.raise a i ha)) q) := by
      rw [hr, edgeDir_spec f he]
      simp [toggle_same]
    rw [hh, Finset.mem_singleton] at hm
    exact hm.symm
  let a : D5.S1.Ledger.BoundedTimeSlice.TailBox (fun _ : Fin k => 1) :=
    fun j => if j = i then 0 else finTwoEquiv.symm (u j)
  let b : D5.S1.Ledger.BoundedTimeSlice.TailBox (fun _ : Fin k => 1) := fun _ => 0
  have ha : (a i).val < 1 := by simp [a]
  have hb : (b i).val < 1 := by simp [b]
  have hl := D5.S3.Arith.Coding.CapacityBoxOneBitRigidity.colour_depends_only_on_layer
    φ a b i ha hb (by simp [a, b])
  rw [colour_eq a ha, colour_eq b hb] at hl
  have hdb : decode b = (fun _ => false) := by funext j; simp [decode, b, finTwoEquiv]
  rw [hdb] at hl
  have hda : decode a = Function.update u i false := by
    funext j
    by_cases hj : j = i
    · simp [decode, a, hj, finTwoEquiv]
    · simp [decode, a, hj]
  rw [hda] at hl
  by_cases hu : u i = false
  · simpa [← hu] using hl
  · have ht : Function.update u i false = toggle u i := by
      unfold toggle
      cases hui : u i <;> simp_all
    rw [ht] at hl
    have hs : edgeDir f he (toggle u i) i = edgeDir f he u i := by
      apply toggle_injective (f u)
      have h := edgeDir_spec f he (toggle u i) i
      rw [toggle_twice] at h
      have hh := congrArg (fun w => toggle w (edgeDir f he (toggle u i) i)) h
      rw [toggle_twice] at hh
      exact hh.trans (edgeDir_spec f he u i)
    exact hs.symm.trans hl

private def directions : Fin k → Fin n := edgeDir f he (fun _ => false)

include hf in
private theorem directions_injective : Function.Injective (directions f he) :=
  edgeDir_injective f hf he (fun _ => false)

include hf in
private theorem mapped_toggle (u : Fin k → Bool) (i : Fin k) :
    f (toggle u i) = toggle (f u) (directions f he i) := by
  rw [edgeDir_spec f he, edgeDir_constant f hf he]
  rfl

include hf in
private theorem mapped_coordinate (u : Fin k → Bool) (i : Fin k) :
    f u (directions f he i) = (f (fun _ => false) (directions f he i)).xor (u i) := by
  have hi := directions_injective f hf he
  have hinv : ∀ v j, (f (toggle v j) (directions f he i)).xor (toggle v j i) =
      (f v (directions f he i)).xor (v i) := by
    intro v j
    rw [mapped_toggle f hf he]
    by_cases hji : j = i
    · subst j
      simp only [toggle_same]
      cases h1 : f v (directions f he i) <;> cases h2 : v i <;> decide
    · rw [toggle_other _ _ _ (fun h => hji (hi h).symm), toggle_other _ _ _ (Ne.symm hji)]
  have hh := invariant_of_toggles
    (fun v => (f v (directions f he i)).xor (v i)) hinv u (fun _ => false)
  simp only [Bool.xor_false] at hh
  cases h1 : f u (directions f he i) <;>
    cases h2 : f (fun _ => false) (directions f he i) <;> cases h3 : u i <;>
    simp_all

include hf in
private theorem mapped_fixed (u : Fin k → Bool) (q : Fin n)
    (hq : ∀ i, directions f he i ≠ q) : f u q = f (fun _ => false) q := by
  apply invariant_of_toggles (fun v => f v q) _ u (fun _ => false)
  intro v i
  rw [mapped_toggle f hf he, toggle_other _ _ _ (Ne.symm (hq i))]

/-- The image of an injective edge-preserving Boolean cube map is a coordinate subcube. -/
theorem cube_map_image (f : (Fin k → Bool) → (Fin n → Bool))
    (hf : Function.Injective f)
    (he : ∀ u v, hammingDist u v = 1 → hammingDist (f u) (f v) = 1) :
    ∃ d : Fin k ↪ Fin n, ∀ w : Fin n → Bool,
      w ∈ Set.range f ↔ ∀ q, q ∉ Set.range d → w q = f (fun _ => false) q := by
  let d : Fin k ↪ Fin n := ⟨directions f he, directions_injective f hf he⟩
  refine ⟨d, ?_⟩
  intro w
  constructor
  · rintro ⟨u, rfl⟩ q hq
    exact mapped_fixed f hf he u q (fun i hi => hq ⟨i, hi⟩)
  · intro hw
    let u : Fin k → Bool := fun i => (f (fun _ => false) (d i)).xor (w (d i))
    refine ⟨u, ?_⟩
    funext q
    by_cases hq : q ∈ Set.range d
    · obtain ⟨i, rfl⟩ := hq
      change f u (directions f he i) = w (directions f he i)
      rw [mapped_coordinate f hf he]
      change (f (fun _ => false) (d i)).xor
        ((f (fun _ => false) (d i)).xor (w (d i))) = w (d i)
      cases f (fun _ => false) (d i) <;> cases w (d i) <;> rfl
    · exact (mapped_fixed f hf he u q (fun i hi => hq ⟨i, hi⟩)).trans (hw q hq).symm

private theorem induced_cube_coordinates {k n : ℕ} (U : Set (Fin n → Bool))
    (e : (hypercube n).induce U ≃g hypercube k) :
    ∃ (S : Finset (Fin n)) (b : Fin n → Bool), S.card = k ∧
      U = {w | ∀ q, q ∉ S → w q = b q} := by
  let f : (Fin k → Bool) → (Fin n → Bool) := fun u => (e.symm u).val
  have hf : Function.Injective f := by
    intro u v h
    exact e.symm.injective (Subtype.ext h)
  have he : ∀ u v, hammingDist u v = 1 → hammingDist (f u) (f v) = 1 := by
    intro u v h
    exact e.symm.map_rel_iff.mpr h
  obtain ⟨d, hd⟩ := cube_map_image f hf he
  let S := Finset.univ.map d
  refine ⟨S, f (fun _ => false), by simp [S], ?_⟩
  ext w
  have hr : w ∈ U ↔ w ∈ Set.range f := by
    constructor
    · intro hw
      refine ⟨e ⟨w, hw⟩, ?_⟩
      simp [f]
    · rintro ⟨u, rfl⟩
      exact (e.symm u).property
  rw [hr, hd]
  simp only [Set.mem_setOf_eq]
  have hs : ∀ q, q ∈ S ↔ q ∈ Set.range d := by simp [S]
  simp_rw [hs]

private def coordinateSet {n : ℕ} (S : Finset (Fin n)) (b : Fin n → Bool) : Set (Fin n → Bool) :=
  {w | ∀ q, q ∉ S → w q = b q}

/-- A coordinate subcube is isomorphic to the cube of its number of free coordinates. -/
private def coordinateIso {k n : ℕ} (S : Finset (Fin n)) (b : Fin n → Bool) (hS : S.card = k) :
    hypercube k ≃g (hypercube n).induce (coordinateSet S b) := by
  let e := Finset.equivFinOfCardEq hS
  let lift : (Fin k → Bool) → (Fin n → Bool) :=
    fun u q => if hq : q ∈ S then u (e ⟨q,hq⟩) else b q
  let f : (Fin k → Bool) → coordinateSet S b := fun u =>
    ⟨lift u, by intro q hq; simp [lift, hq]⟩
  have hinj : Function.Injective f := by
    intro u v h
    funext i
    have hh := congrArg (fun w : coordinateSet S b => w.val (e.symm i).val) h
    simpa [f, lift, (e.symm i).property] using hh
  have hsurj : Function.Surjective f := by
    intro w
    refine ⟨fun i => w.val (e.symm i).val, Subtype.ext ?_⟩
    funext q
    by_cases hq : q ∈ S
    · simp [f, lift, hq]
    · simp [f, lift, hq, w.property q hq]
  have hdist : ∀ u v, hammingDist (lift u) (lift v) = hammingDist u v := by
    intro u v
    symm
    apply Finset.card_bij (fun i _ => (e.symm i).val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simpa [lift, (e.symm i).property] using hi
    · intro i hi j hj hij
      exact e.symm.injective (Subtype.ext hij)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hqs : q ∈ S := by
        by_contra hqs
        simp [lift, hqs] at hq
      refine ⟨e ⟨q,hqs⟩, ?_, ?_⟩
      · simpa [lift, hqs] using hq
      · simp
  refine { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_rel_iff' := ?_ }
  intro u v
  change hammingDist (lift u) (lift v) = 1 ↔ hammingDist u v = 1
  rw [hdist]

def erase {n : ℕ} (v : Fin n → Bool) (T : Finset (Fin n)) : Fin n → Bool :=
  fun q => if q ∈ T then false else v q

def downCube {n : ℕ} (v : Fin n → Bool) (S : Finset (Fin n)) : Set (Fin n → Bool) :=
  {w | ∃ T : Finset (Fin n), T ⊆ S ∧ w = erase v T}

@[simp] theorem erase_empty {n : ℕ} (v : Fin n → Bool) : erase v ∅ = v := by
  funext q
  simp [erase]

@[simp] theorem top_mem_downCube {n : ℕ} (v : Fin n → Bool) (S : Finset (Fin n)) :
    v ∈ downCube v S := ⟨∅, Finset.empty_subset _, (erase_empty v).symm⟩

private theorem downCube_eq_coordinateSet {n : ℕ} (v : Fin n → Bool) (S : Finset (Fin n))
    (hS : S ⊆ (Finset.univ.filter (fun q => v q = true))) : downCube v S = coordinateSet S v := by
  ext w
  constructor
  · rintro ⟨T, hT, rfl⟩ q hq
    simp [erase, show q ∉ T from fun h => hq (hT h)]
  · intro hw
    let T := S.filter (fun q => w q = false)
    refine ⟨T, Finset.filter_subset _ _, ?_⟩
    funext q
    by_cases hq : q ∈ S
    · have hv : v q = true := (Finset.mem_filter.mp (hS hq)).2
      cases hbit : w q <;> simp [erase, T, hq, hbit, hv]
    · simp [erase, T, hq, hw q hq]

/-- Every induced Boolean cube has a top vertex and exactly its dimension's free coordinates. -/
private theorem induced_cube_downCube {k n : ℕ} (U : Set (Fin n → Bool))
    (e : (hypercube n).induce U ≃g hypercube k) :
    ∃ (v : Fin n → Bool) (S : Finset (Fin n)),
      S.card = k ∧ S ⊆ (Finset.univ.filter (fun q => v q = true)) ∧ U = downCube v S := by
  obtain ⟨S, b, hS, hU⟩ := induced_cube_coordinates U e
  let v : Fin n → Bool := fun q => if q ∈ S then true else b q
  have hSv : S ⊆ (Finset.univ.filter (fun q => v q = true)) := by
    intro q hq
    simp [v, hq]
  refine ⟨v, S, hS, hSv, ?_⟩
  rw [downCube_eq_coordinateSet v S hSv, hU]
  ext w
  simp only [coordinateSet, Set.mem_setOf_eq]
  constructor <;> intro hw q hq <;> simpa [v, hq] using hw q hq

/-- Conversely every down-cube with one bits at the free coordinates is an induced cube. -/
private theorem downCube_is_cube {k n : ℕ} (v : Fin n → Bool) (S : Finset (Fin n))
    (hS : S.card = k) (hv : S ⊆ (Finset.univ.filter (fun q => v q = true))) :
    Nonempty ((hypercube n).induce (downCube v S) ≃g hypercube k) := by
  rw [downCube_eq_coordinateSet v S hv]
  exact ⟨(coordinateIso S v hS).symm⟩

private theorem downCube_le_top {n : ℕ} {v w : Fin n → Bool} {S : Finset (Fin n)}
    (hw : w ∈ downCube v S) : ∀ q, w q = true → v q = true := by
  obtain ⟨T, hT, rfl⟩ := hw
  intro q hq
  by_cases h : q ∈ T
  · simp [erase, h] at hq
  · simpa [erase, h] using hq

/-- The top vertex and direction set of a down-cube are unique. -/
theorem downCube_unique {n : ℕ} (v v' : Fin n → Bool) (S S' : Finset (Fin n))
    (hS : S ⊆ (Finset.univ.filter (fun q => v q = true))) (hS' : S' ⊆ (Finset.univ.filter (fun q => v' q = true)))
    (h : downCube v S = downCube v' S') : v = v' ∧ S = S' := by
  have hv : v = v' := by
    have hvv' := downCube_le_top (h ▸ top_mem_downCube v S)
    have hv'v := downCube_le_top (h.symm ▸ top_mem_downCube v' S')
    funext q
    cases h1 : v q <;> cases h2 : v' q <;> simp_all
  refine ⟨hv, ?_⟩
  subst v'
  have hsub : ∀ A B : Finset (Fin n), A ⊆ (Finset.univ.filter (fun q => v q = true)) →
      downCube v A = downCube v B → A ⊆ B := by
    intro A B hA hAB q hq
    have hvm : v q = true := (Finset.mem_filter.mp (hA hq)).2
    have hdel : erase v {q} ∈ downCube v A := ⟨{q}, by simpa, rfl⟩
    rw [hAB] at hdel
    obtain ⟨T, hT, hTval⟩ := hdel
    have hh := congrFun hTval q
    have hqT : q ∈ T := by
      by_contra hqT
      simp [erase, hqT, hvm] at hh
    exact hT hqT
  exact Finset.Subset.antisymm (hsub S S' hS h) (hsub S' S hS' h.symm)

/-- Classification of induced hypercubes, including uniqueness of the top and directions. -/
theorem induced_cube_iff {k n : ℕ} (U : Set (Fin n → Bool)) :
    Nonempty ((hypercube n).induce U ≃g hypercube k) ↔
    ∃! p : (Fin n → Bool) × Finset (Fin n),
      p.2.card = k ∧ p.2 ⊆ (Finset.univ.filter (fun q => p.1 q = true)) ∧ U = downCube p.1 p.2 := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨v, S, hcard, hS, hU⟩ := induced_cube_downCube U e
    refine ⟨(v,S), ⟨hcard, hS, hU⟩, ?_⟩
    rintro ⟨v', S'⟩ ⟨hcard', hS', hU'⟩
    obtain ⟨hv, hSS⟩ := downCube_unique v' v S' S hS' hS (hU'.symm.trans hU)
    exact Prod.ext hv hSS
  · rintro ⟨⟨v,S⟩, ⟨hcard, hS, hU⟩, _⟩
    rw [hU]
    exact downCube_is_cube v S hcard hS

end
end D5.S3.Combinatorics.Hamming.InducedSubcubes

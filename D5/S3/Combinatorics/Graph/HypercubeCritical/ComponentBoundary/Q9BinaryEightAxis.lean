/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BinaryEightAxis
   generality: G
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Isotropic parity block rank and the binary eight-axis test for separated Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicParityTransfer
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents

/-! The signed isotropic blocks give a common parity constraint at each choice
of inactive axis in a separated cubic pair of total order 258. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced directionEdges direction_edge_count)
open Q9MixedBoundaryCollisions (Separated)
open Q9IsotropicHuang (flipSign weightedAction exists_one_parity_word
  weightedAction_parity_image_eq_kernel)
open Q9IsotropicParityTransfer (ParityVertices parityCode columnRestrictionKernel
  exists_common_parity_codeword)
open Q9ParityFoldedBoundary (parity parityPart cubic_parityPart_card)
open Q9WeightedHuangComponents (exists_supported_eigenvectors)
open private flipSign_cast flip_off_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private mem_supported_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedHuangComponents
open private parityPartInclusion finrank_map_add_finrank_inf_ker from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicParityTransfer
open private huangMatrix huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- Weighted signed adjacency from parity `b` to its opposite. -/
def parityBlock (w : Fin 9 → F) (b : Bool) :
    Matrix (ParityVertices (!b)) (ParityVertices b) F :=
  fun x y => ∑ i, if flip x.1 i = y.1 then w i * (flipSign i x.1 : F) else 0

/-- Weighted signed adjacency from odd vertices to even vertices. -/
abbrev parityMatrix (w : Fin 9 → F) := parityBlock w true

private theorem coeff_symmetric (w : Fin 9 → F) (x y : Q 9) (i : Fin 9) :
    (if flip x i = y then w i * (flipSign i x : F) else 0) =
      (if flip y i = x then w i * (flipSign i y : F) else 0) := by
  by_cases h : flip x i = y
  · subst y
    have hs : flipSign i x = flipSign i (flip x i) := by
      apply Int.cast_injective (α := ℝ)
      rw [flipSign_cast, flipSign_cast, BalancedCriticalSpectrum.flip_flip,
        huangMatrix_symmetric x (flip x i)]
    rw [ite_eq_left rfl, ite_eq_left (BalancedCriticalSpectrum.flip_flip x i), ← hs]
  · have hn : flip y i ≠ x := fun he => h (by rw [← he, BalancedCriticalSpectrum.flip_flip])
    rw [ite_eq_right h, ite_eq_right hn]

private theorem false_block_eq_transpose (w : Fin 9 → F) :
    parityBlock w false = (parityMatrix w)ᵀ := by
  ext x y
  exact Finset.sum_congr rfl (fun i _ => coeff_symmetric w x.1 y.1 i)

private theorem parityMatrix_support (w : Fin 9 → F) (x : ParityVertices false)
    (y : ParityVertices true) (h : ¬ (hypercube 9).Adj x.1 y.1) : parityMatrix w x y = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hn : flip x.1 i ≠ y.1 := by
    intro he
    exact h (he ▸ flip_adj x.1 i)
  exact ite_eq_right hn

private def extendParity {b : Bool} (g : ParityVertices b → F) (x : Q 9) : F :=
  if hx : parity x = b then g ⟨x, hx⟩ else 0

private theorem extendParity_apply {b : Bool} (g : ParityVertices b → F)
    (x : ParityVertices b) : extendParity g x.1 = g x := dite_eq_left x.2

private theorem extendParity_off {b : Bool} (g : ParityVertices b → F) {x : Q 9}
    (hx : parity x ≠ b) : extendParity g x = 0 := dite_eq_right hx

private theorem parityBlock_mulVec (w : Fin 9 → F) {b : Bool} {g : Q 9 → F}
    (hg : ∀ x, parity x ≠ b → g x = 0) (x : ParityVertices (!b)) :
    (parityBlock w b).mulVec (fun y => g y.1) x = weightedAction w g x.1 := by
  classical
  simp only [Matrix.mulVec, dotProduct, parityBlock, weightedAction, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  let s := (Finset.univ : Finset (Q 9)).filter (fun y => parity y = b)
  let term (y : Q 9) := (if flip x.1 i = y then w i * (flipSign i x.1 : F) else 0) * g y
  change (∑ y : ParityVertices b, term y.1) = _
  rw [← Finset.sum_subtype s (fun y => by simp [s]) term]
  calc
    _ = ∑ y : Q 9, term y := Finset.sum_subset (Finset.subset_univ s) (fun y _ hy => by
      have h := hg y (by simpa [s] using hy)
      simp [term, h])
    _ = _ := by
      rw [Finset.sum_eq_single (flip x.1 i)]
      · simp [term]
      · intro y _ hy
        simp [term, Ne.symm hy]
      · simp

private theorem weightedAction_off (w : Fin 9 → F) {b : Bool} {g : Q 9 → F}
    (hg : ∀ x, parity x ≠ b → g x = 0) {x : Q 9} (hx : parity x ≠ !b) :
    weightedAction w g x = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [hg _ (flip_off_parity j hx), mul_zero]

private theorem parityBlock_transpose_mulVec (w : Fin 9 → F) {b : Bool} {g : Q 9 → F}
    (hg : ∀ x, parity x ≠ !b → g x = 0) (x : ParityVertices b) :
    (parityBlock w b)ᵀ.mulVec (fun y => g y.1) x = weightedAction w g x.1 := by
  cases b
  · rw [false_block_eq_transpose, Matrix.transpose_transpose]
    exact parityBlock_mulVec w (b := true) hg x
  · rw [← false_block_eq_transpose]
    exact parityBlock_mulVec w (b := false) hg x

/-- On each parity the image of the transpose equals the kernel of the outgoing block. -/
theorem range_transpose_eq_ker (w : Fin 9 → F) (hw : ∑ i, w i ^ 2 = 0)
    (i : Fin 9) (hi : w i ≠ 0) (b : Bool) :
    LinearMap.range (parityBlock w b)ᵀ.mulVecLin = LinearMap.ker (parityBlock w b).mulVecLin := by
  have h := weightedAction_parity_image_eq_kernel w hw i hi (!b)
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    have him : weightedAction w (extendParity f) ∈
        weightedAction w '' {v | ∀ x, parity x ≠ !b → v x = 0} :=
      ⟨_, fun _ => extendParity_off f, rfl⟩
    rw [h] at him
    have hrestrict : (parityBlock w b)ᵀ.mulVec f =
        fun y : ParityVertices b => weightedAction w (extendParity f) y.1 := by
      funext y
      simpa only [extendParity_apply] using
        parityBlock_transpose_mulVec w (b := b) (fun _ => extendParity_off f) y
    have hv : ∀ y, parity y ≠ b → weightedAction w (extendParity f) y = 0 := by
      simpa only [Bool.not_not] using him.2
    apply LinearMap.mem_ker.mpr
    change (parityBlock w b).mulVec ((parityBlock w b)ᵀ.mulVec f) = 0
    rw [hrestrict]
    exact funext fun x => (parityBlock_mulVec w (b := b) hv x).trans (congrFun him.1 x.1)
  · intro hg
    have hBg : (parityBlock w b).mulVec g = 0 := LinearMap.mem_ker.mp hg
    have hkernel : weightedAction w (extendParity g) = 0 := by
      funext x
      by_cases hx : parity x = !b
      · let y : ParityVertices (!b) := ⟨x, hx⟩
        have hrow := parityBlock_mulVec w (b := b) (fun _ => extendParity_off g) y
        simp only [extendParity_apply] at hrow
        exact hrow.symm.trans (congrFun hBg y)
      · exact weightedAction_off w (b := b) (fun _ => extendParity_off g) hx
    have hker : extendParity g ∈
        {v | weightedAction w v = 0 ∧ ∀ x, parity x ≠ !(!b) → v x = 0} :=
      ⟨hkernel, fun x hx => extendParity_off g (by simpa only [Bool.not_not] using hx)⟩
    rw [← h] at hker
    obtain ⟨f, hf, he⟩ := hker
    refine ⟨fun x => f x.1, funext fun x => ?_⟩
    exact (parityBlock_transpose_mulVec w (b := b) hf x).trans
      ((congrFun he x.1).trans (extendParity_apply g x))

private theorem card_parityVertices (b : Bool) : Fintype.card (ParityVertices b) = 256 := by
  cases b <;> decide +kernel

/-- A nonzero isotropic weight vector gives rank 128 on the actual signed parity matrix. -/
theorem parityMatrix_rank (w : Fin 9 → F) (hw : ∑ i, w i ^ 2 = 0)
    (i : Fin 9) (hi : w i ≠ 0) : (parityMatrix w).rank = 128 := by
  have h := (parityMatrix w).mulVecLin.finrank_range_add_finrank_ker
  rw [← range_transpose_eq_ker w hw i hi true] at h
  change (parityMatrix w).rank + (parityMatrix w)ᵀ.rank =
    Module.finrank F (ParityVertices true → F) at h
  rw [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card, card_parityVertices] at h
  omega

private theorem supported_action_word_to_code (w : Fin 9 → F) (S : Finset (Q 9))
    {b : Bool} {g : Q 9 → F} (hg : g ≠ 0) (hS : ∀ x ∉ S, g x = 0)
    (hb : ∀ x, parity x ≠ b → g x = 0) (hker : weightedAction w g = 0) :
    ∃ v : parityCode (parityMatrix w) S b, v ≠ 0 := by
  let u (y : parityPart S b) := g y.1
  have hz : ((parityBlock w b).submatrix id (parityPartInclusion S b)).mulVec u = 0 := by
    funext x
    change (∑ y : parityPart S b, parityBlock w b x (parityPartInclusion S b y) * u y) = 0
    let part : Finset (ParityVertices b) := Finset.univ.filter (fun y => y.1 ∈ S)
    let e : ↥(parityPart S b) ≃ {y : ParityVertices b // y.1 ∈ S} :=
      { toFun := fun y => ⟨parityPartInclusion S b y, (Finset.mem_filter.mp y.2).1⟩
        invFun := fun y => ⟨y.1.1, Finset.mem_filter.mpr ⟨y.2, y.1.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let term (y : ParityVertices b) := parityBlock w b x y * g y.1
    change (∑ y : parityPart S b, term (e y).1) = 0
    rw [e.sum_comp (fun y => term y.1)]
    rw [← Finset.sum_subtype part (fun y => by simp [part]) term]
    calc
      _ = ∑ y : ParityVertices b, term y := Finset.sum_subset
        (Finset.subset_univ part) (fun y _ hy => by
          have h := hS y.1 (by simpa [part] using hy)
          simp [term, h])
      _ = _ := (parityBlock_mulVec w hb x).trans (congrFun hker x.1)
  have hm : u ∈ parityCode (parityMatrix w) S b := by
    cases b
    · rw [false_block_eq_transpose] at hz
      exact LinearMap.mem_ker.mpr hz
    · exact LinearMap.mem_ker.mpr hz
  refine ⟨⟨u, hm⟩, fun h => hg (funext fun x => ?_)⟩
  by_cases hxS : x ∈ S
  · by_cases hxb : parity x = b
    · exact congrFun (congrArg Subtype.val h) ⟨x, Finset.mem_filter.mpr ⟨hxS, hxb⟩⟩
    · exact hb x hxb
  · exact hS x hxS

/-- The binary specialization with exactly the axis `k` inactive. -/
def eightAxisWeights (k : Fin 9) (i : Fin 9) : ZMod 2 :=
  if i = k then 0 else 1

private theorem eightAxisWeights_isotropic (k : Fin 9) :
    ∑ i, eightAxisWeights k i ^ 2 = 0 := by
  simp only [eightAxisWeights, apply_ite (fun z : ZMod 2 => z ^ 2), zero_pow (by decide : 2 ≠ 0),
    one_pow]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ k)]
  decide

private theorem eightAxisWeights_nonzero (k : Fin 9) : ∃ i, eightAxisWeights k i ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_ne k
  exact ⟨i, by simp [eightAxisWeights, hi]⟩

private def integerWeights (k : Fin 9) (A : Finset (Fin 9)) (i : Fin 9) : ℤ :=
  if i = k then 2 else if i ∈ A then 3 else 1

private theorem integerWeights_sq_sum (k : Fin 9) (A : Finset (Fin 9))
    (hk : k ∉ A) (hA : A.card = 3) : ∑ i, integerWeights k A i ^ 2 = 36 := by
  have hterm (i : Fin 9) : integerWeights k A i ^ 2 =
      1 + (if i = k then 3 else 0) + (if i ∈ A then 8 else 0) := by
    by_cases hi : i = k
    · subst i
      norm_num [integerWeights, hk]
    · by_cases ha : i ∈ A <;> norm_num [integerWeights, hi, ha]
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_ite, Finset.sum_ite]
  have hkcard : ((Finset.univ : Finset (Fin 9)).filter (fun i => i = k)).card = 1 := by
    rw [show ((Finset.univ : Finset (Fin 9)).filter (fun i => i = k)) = {k} by
      ext i
      simp]
    simp
  norm_num [hA, hkcard]

private theorem integerWeights_mod_two (k : Fin 9) (A : Finset (Fin 9)) (i : Fin 9) :
    (integerWeights k A i : ZMod 2) = eightAxisWeights k i := by
  by_cases hi : i = k
  · simpa [integerWeights, eightAxisWeights, hi] using (show ((2 : ℤ) : ZMod 2) = 0 by decide)
  · by_cases ha : i ∈ A
    · simpa [integerWeights, eightAxisWeights, hi, ha] using
        (show ((3 : ℤ) : ZMod 2) = 1 by decide)
    · simp [integerWeights, eightAxisWeights, hi, ha]

/-- For any inactive axis, the actual binary eight-axis parity matrix gives nonzero
words on a common parity of the two separated cubic supports. -/
theorem exists_eight_axis_common_parity (k : Fin 9) {C D : Finset (Q 9)}
    (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ p, (∃ v : parityCode (parityMatrix (eightAxisWeights k)) C p, v ≠ 0) ∧
      (∃ v : parityCode (parityMatrix (eightAxisWeights k)) D p, v ≠ 0) := by
  have hthree : 3 ≤ (Finset.univ.erase k).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
    decide
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hthree
  have hkA : k ∉ A := fun h => Finset.notMem_erase k _ (hA h)
  let t := integerWeights k A
  have ht (i : Fin 9) : 0 < (t i : ℝ) := by
    by_cases hi : i = k <;> by_cases ha : i ∈ A <;> norm_num [t, integerWeights, hi, ha]
  have hnorm : ∑ i, t i ^ 2 = 36 := integerWeights_sq_sum k A hkA hAcard
  have hnormReal : ∑ i, (t i : ℝ) ^ 2 = 36 := by exact_mod_cast hnorm
  have hroot : Real.sqrt (∑ i, (t i : ℝ) ^ 2) = 6 := by rw [hnormReal]; norm_num
  have hcast (i : Fin 9) : (t i : ZMod 2) = eightAxisWeights k i := integerWeights_mod_two k A i
  obtain ⟨i, hi⟩ := eightAxisWeights_nonzero k
  have hrank := parityMatrix_rank (eightAxisWeights k) (eightAxisWeights_isotropic k) i hi
  have word (S : Finset (Q 9)) {v : Q 9 → ℝ}
      (hv : v ∈ Q9WeightedHuangSaturation.supportedWeightedEigenSpace (fun i => (t i : ℝ)) S)
      (hn : v ≠ 0) : ∃ p, ∃ g : parityCode (parityMatrix (eightAxisWeights k)) S p, g ≠ 0 := by
    obtain ⟨heigen, hsupport⟩ := (mem_supported_iff _ S v).mp hv
    rw [hroot] at heigen
    have heven : (2 : ℤ) ∣ 6 := by norm_num
    obtain ⟨p, g, hg, hgS, hgp, hker⟩ :=
      exists_one_parity_word (p := 2) t S heven hn hsupport
        (by simpa [Q9WeightedHuangSaturation.weightedHuang] using heigen)
    rw [show (fun i => (t i : ZMod 2)) = eightAxisWeights k from funext hcast] at hker
    exact ⟨p, supported_action_word_to_code (eightAxisWeights k) S hg hgS hgp hker⟩
  obtain ⟨⟨v, hv, hvne⟩, ⟨u, hu, hune⟩⟩ :=
    exists_supported_eigenvectors (fun i => (t i : ℝ)) ht hcard hsep hc hd hbC hbD
  exact exists_common_parity_codeword _ hrank (parityMatrix_support _) hsep hcard
    hrC hrD hbC hbD (word C hv hvne) (word D hu hune)

private theorem parityCode_rank_add_nullity (w : Fin 9 → F) (S : Finset (Q 9)) (b : Bool) :
    ((parityBlock w b).submatrix id (parityPartInclusion S b)).rank +
      Module.finrank F (parityCode (parityMatrix w) S b) = (parityPart S b).card := by
  cases b
  · rw [false_block_eq_transpose]
    let M := (parityMatrix w)ᵀ.submatrix id (parityPartInclusion S false)
    have h := M.mulVecLin.finrank_range_add_finrank_ker
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  · let M := (parityMatrix w).submatrix id (parityPartInclusion S true)
    have h := M.mulVecLin.finrank_range_add_finrank_ker
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-- For a selection of 129 parity coordinates, the complementary supported
kernel has dimension one less than the selected supported kernel. -/
theorem complement_nullity_add_one (w : Fin 9 → F) (hw : ∑ i, w i ^ 2 = 0)
    (i : Fin 9) (hi : w i ≠ 0) (S : Finset (Q 9)) (b : Bool) (hS : (parityPart S b).card = 129) :
    Module.finrank F ↥(LinearMap.ker (parityBlock w b).mulVecLin ⊓
        LinearMap.ker (LinearMap.funLeft F F (parityPartInclusion S b))) + 1 =
      Module.finrank F (parityCode (parityMatrix w) S b) := by
  let B := parityBlock w b
  let P := LinearMap.funLeft F F (parityPartInclusion S b)
  let M := B.submatrix id (parityPartInclusion S b)
  have hrank : B.rank = 128 := by
    cases b
    · exact (congrArg Matrix.rank (false_block_eq_transpose w)).trans
        ((Matrix.rank_transpose _).trans (parityMatrix_rank w hw i hi))
    · exact parityMatrix_rank w hw i hi
  have h := finrank_map_add_finrank_inf_ker (LinearMap.range Bᵀ.mulVecLin) P
  have hmap : (LinearMap.range Bᵀ.mulVecLin).map P = LinearMap.range Mᵀ.mulVecLin := by
    rw [← LinearMap.range_comp]
    rfl
  rw [hmap] at h
  change Mᵀ.rank + Module.finrank F
    ↥(LinearMap.range Bᵀ.mulVecLin ⊓ LinearMap.ker P) = Bᵀ.rank at h
  rw [Matrix.rank_transpose, Matrix.rank_transpose, hrank,
    show LinearMap.range Bᵀ.mulVecLin = LinearMap.ker B.mulVecLin from
      range_transpose_eq_ker w hw i hi b] at h
  have hselected := parityCode_rank_add_nullity w S b
  rw [hS] at hselected
  change M.rank + Module.finrank F (parityCode (parityMatrix w) S b) = 129 at hselected
  change Module.finrank F ↥(LinearMap.ker B.mulVecLin ⊓ LinearMap.ker P) + 1 = _
  omega

private theorem parityCode_finrank_union_ge (w : Fin 9 → F) (C D : Finset (Q 9)) (b : Bool)
    (hdisj : Disjoint C D) :
    Module.finrank F (parityCode (parityMatrix w) C b) +
      Module.finrank F (parityCode (parityMatrix w) D b) ≤
      Module.finrank F (parityCode (parityMatrix w) (C ∪ D) b) := by
  let M (S : Finset (Q 9)) := (parityBlock w b).submatrix id (parityPartInclusion S b)
  let cols (S : Finset (Q 9)) := Set.range (M S).col
  have hcols : cols (C ∪ D) = cols C ∪ cols D := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨hx, hp⟩ := Finset.mem_filter.mp x.2
      rcases Finset.mem_union.mp hx with hc | hd
      · exact Or.inl ⟨⟨x.1, Finset.mem_filter.mpr ⟨hc, hp⟩⟩, rfl⟩
      · exact Or.inr ⟨⟨x.1, Finset.mem_filter.mpr ⟨hd, hp⟩⟩, rfl⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · obtain ⟨hx, hp⟩ := Finset.mem_filter.mp x.2
        exact ⟨⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_union_left D hx, hp⟩⟩, rfl⟩
      · obtain ⟨hx, hp⟩ := Finset.mem_filter.mp x.2
        exact ⟨⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_union_right C hx, hp⟩⟩, rfl⟩
  have hrank : (M (C ∪ D)).rank ≤ (M C).rank + (M D).rank := by
    simp only [Matrix.rank_eq_finrank_span_cols]
    change Module.finrank F (Submodule.span F (cols (C ∪ D))) ≤
      Module.finrank F (Submodule.span F (cols C)) + Module.finrank F (Submodule.span F (cols D))
    rw [hcols, Submodule.span_union]
    exact Nat.le.intro (Submodule.finrank_sup_add_finrank_inf_eq _ _)
  have hcard : (parityPart (C ∪ D) b).card = (parityPart C b).card + (parityPart D b).card := by
    rw [parityPart, Finset.filter_union]
    exact Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hu := parityCode_rank_add_nullity w (C ∪ D) b
  have hc := parityCode_rank_add_nullity w C b
  have hd := parityCode_rank_add_nullity w D b
  rw [hcard] at hu
  change (M (C ∪ D)).rank + _ = _ at hu
  change (M C).rank + _ = _ at hc
  change (M D).rank + _ = _ at hd
  omega

/-- The common parity also has a nonzero binary kernel word supported outside
both components. -/
theorem exists_eight_axis_complement_word (k : Fin 9) {C D : Finset (Q 9)}
    (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ p, (∃ v : parityCode (parityMatrix (eightAxisWeights k)) C p, v ≠ 0) ∧
      (∃ v : parityCode (parityMatrix (eightAxisWeights k)) D p, v ≠ 0) ∧
      ∃ g : ParityVertices p → ZMod 2, g ≠ 0 ∧ (∀ x, x.1 ∈ C ∪ D → g x = 0) ∧
        (parityBlock (eightAxisWeights k) p).mulVec g = 0 := by
  let w := eightAxisWeights k
  obtain ⟨p, hpC, hpD⟩ :=
    exists_eight_axis_common_parity k hsep hcard hc hd hrC hrD hbC hbD
  have hpCpos := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr hpC
  have hpDpos := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mpr hpD
  have hge := parityCode_finrank_union_ge w C D p hsep.1
  have hCcard := (direction_edge_count (d := 3) C hrC hbC 0).symm
  have hDcard := (direction_edge_count (d := 3) D hrD hbD 0).symm
  have hU : (parityPart (C ∪ D) p).card = 129 := by
    rw [Finset.card_union_of_disjoint hsep.1] at hcard
    rw [parityPart, Finset.filter_union, Finset.card_union_of_disjoint
      (hsep.1.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    change (parityPart C p).card + (parityPart D p).card = 129
    rw [cubic_parityPart_card hCcard hrC, cubic_parityPart_card hDcard hrD]
    omega
  obtain ⟨i, hi⟩ := eightAxisWeights_nonzero k
  have hdim := complement_nullity_add_one w (eightAxisWeights_isotropic k) i hi (C ∪ D) p hU
  let V := LinearMap.ker (parityBlock w p).mulVecLin ⊓
    LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) (parityPartInclusion (C ∪ D) p))
  have hpos : 0 < Module.finrank (ZMod 2) V := by
    change Module.finrank (ZMod 2) V + 1 = _ at hdim
    change 0 < Module.finrank (ZMod 2) (parityCode (parityMatrix w) C p) at hpCpos
    change 0 < Module.finrank (ZMod 2) (parityCode (parityMatrix w) D p) at hpDpos
    omega
  obtain ⟨g, hg⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp hpos
  have hm : g.val ∈ V := g.property
  refine ⟨p, hpC, hpD, g.val, fun h => hg (Subtype.ext h), ?_, LinearMap.mem_ker.mp hm.1⟩
  intro x hx
  exact congrFun (LinearMap.mem_ker.mp hm.2)
    ⟨x.1, Finset.mem_filter.mpr ⟨hx, x.2⟩⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis

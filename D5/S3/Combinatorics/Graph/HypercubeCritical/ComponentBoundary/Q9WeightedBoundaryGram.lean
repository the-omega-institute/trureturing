/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Weighted boundary Gram and rooted cofactor product for separated cubic supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-! Coordinate-weighted Huang boundary identities for the 72- and 186-vertex supports
in the nine-cube branch of Hong–Wu–Xia Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
open Q9BoundaryGram (Interior Exterior)
open Q9IsotropicHuang (flipSign weightedLinear weightedAction)
open private weightedLinear_apply weightedLinear_square flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private huangMatrix_symmetric cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private regular_parity_card interior_card cube_opposite_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram

variable {R : Type*} [CommRing R]

private def signed (w : Fin 9 → R) : Matrix (Q 9) (Q 9) R :=
  fun x y => ∑ a, if flip x a = y then w a * (flipSign a x : R) else 0

private theorem signed_transpose (w : Fin 9 → R) : (signed w)ᵀ = signed w := by
  ext x y
  simp only [Matrix.transpose_apply, signed]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : flip x a = y
  · subst y
    rw [ite_eq_left (BalancedCriticalSpectrum.flip_flip x a), ite_eq_left rfl]
    congr 1
    apply congrArg (fun z : ℤ => (z : R))
    apply Int.cast_injective (α := ℝ)
    rw [flipSign_cast, flipSign_cast, BalancedCriticalSpectrum.flip_flip, huangMatrix_symmetric]
  · have h' : flip y a ≠ x := fun he => h (by rw [← he, BalancedCriticalSpectrum.flip_flip])
    rw [ite_eq_right h', ite_eq_right h]

private theorem signed_mulVec (w : Fin 9 → R) (f : Q 9 → R) :
    (signed w).mulVec f = weightedLinear w f := by
  rw [weightedLinear_apply]
  funext x
  simp only [Matrix.mulVec, dotProduct, signed, weightedAction, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (flip x a)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

private theorem signed_square (w : Fin 9 → R) :
    signed w * signed w = (∑ a, w a ^ 2) • 1 := by
  apply Matrix.ext_of_mulVec_single
  intro y
  rw [← Matrix.mulVec_mulVec, signed_mulVec, signed_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  exact congrArg (fun L : Module.End R (Q 9 → R) => L (Pi.single y 1))
    (weightedLinear_square w)

private def switched (w : Fin 9 → R) (s : Q 9 → ℤ) : Matrix (Q 9) (Q 9) R :=
  fun x y => (s x : R) * signed w x y * (s y : R)

private theorem switched_gram (w : Fin 9 → R) (s : Q 9 → ℤ)
    (hs : ∀ x, s x * s x = 1) :
    switched w s * (switched w s)ᵀ = (∑ a, w a ^ 2) • 1 := by
  have hsign (x : Q 9) : (s x : R) * (s x : R) = 1 := by
    simpa only [Int.cast_mul, Int.cast_one] using congrArg (fun z : ℤ => (z : R)) (hs x)
  have hsym (x y : Q 9) : signed w y x = signed w x y :=
    congrFun (congrFun (signed_transpose w) x) y
  ext x y
  calc
    _ = (s x : R) * (signed w * signed w) x y * (s y : R) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul,
        switched]
      apply Finset.sum_congr rfl
      intro z _
      rw [hsym z y]
      calc
        _ = ((s z : R) * (s z : R)) *
            ((s x : R) * (signed w x z * signed w z y) * (s y : R)) := by ring
        _ = _ := by rw [hsign, one_mul]
    _ = _ := by
      rw [signed_square]
      by_cases h : x = y
      · subst y
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [mul_comm (s x : R), mul_assoc, hsign, mul_one]
      · simp [h]

private theorem switched_same_parity (w : Fin 9 → R) (s : Q 9 → ℤ) {x y : Q 9}
    (h : cubeParity x = cubeParity y) : switched w s x y = 0 := by
  have hz : signed w x y = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    refine ite_eq_right ?_
    rintro rfl
    exact cubeParity_ne_of_adj (flip_adj x a) h
  simp [switched, hz]

private def unsigned (w : Fin 9 → R) (x y : Q 9) : R :=
  ∑ a, if flip x a = y then w a else 0

private theorem unsigned_zero (w : Fin 9 → R) {x y : Q 9}
    (h : ¬ (hypercube 9).Adj x y) : unsigned w x y = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  refine ite_eq_right ?_
  rintro rfl
  exact h (flip_adj x a)

/-- The retained vertices of parity `b` after deleting the chosen root. -/
abbrev RootedRows (S : Finset (Q 9)) (b : Bool) (c : (S : Set (Q 9))) :=
  ↥((paritySide S b).erase c)

/-- The underlying vertex of a retained row from either support. -/
def rowVertex {C D : Finset (Q 9)} {b : Bool} {c : (C : Set (Q 9))} {d : (D : Set (Q 9))} :
    RootedRows C b c ⊕ RootedRows D b d → Q 9 :=
  Sum.elim (fun x => x.1.1) (fun x => x.1.1)

/-- The ordinary coordinate-weighted biadjacency with one root row removed. -/
def rootedBiadjacency (w : Fin 9 → R) (S : Finset (Q 9)) (b : Bool)
    (c : (S : Set (Q 9))) : Matrix (RootedRows S b c) (Interior S b) R :=
  fun x y => unsigned w x.1.1 y.1.1

private theorem rooted_parity {S : Finset (Q 9)} {b : Bool} {c : (S : Set (Q 9))}
    (x : RootedRows S b c) : cubeParity x.1.1 = b :=
  (Finset.mem_filter.mp (Finset.mem_of_mem_erase x.property)).2

open Classical in
private theorem rooted_card (S : Finset (Q 9)) (b : Bool) (c : (S : Set (Q 9)))
    (hc : cubeParity c.1 = b)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) :
    2 * (Fintype.card (RootedRows S b c) + 1) = S.card := by
  have hmem : c ∈ paritySide S b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rw [Fintype.card_coe, Finset.card_erase_of_mem hmem]
  have h := regular_parity_card S b (d := 3) (by decide) hr
  have hp := Finset.card_pos.mpr ⟨c, hmem⟩
  omega

private noncomputable def interiorUnion {C D : Finset (Q 9)} (b : Bool) (hdisj : Disjoint C D) :
    Interior C b ⊕ Interior D b ≃ Interior (C ∪ D) b :=
  Equiv.ofBijective
    (Sum.elim (fun x => ⟨x.1, Finset.mem_union_left _ x.property⟩)
      (fun x => ⟨x.1, Finset.mem_union_right _ x.property⟩)) (by
    constructor
    · intro x y h
      have hval := congrArg Subtype.val h
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext hval)
        | inr y => exact (Finset.disjoint_left.mp hdisj x.property
            (congrArg Subtype.val hval ▸ y.property)).elim
      | inr x =>
        cases y with
        | inl y => exact (Finset.disjoint_left.mp hdisj y.property
            (congrArg Subtype.val hval ▸ x.property)).elim
        | inr y => exact congrArg Sum.inr (Subtype.ext hval)
    · intro x
      rcases Finset.mem_union.mp x.property with hC | hD
      · exact ⟨Sum.inl ⟨x.1, hC⟩, Subtype.ext rfl⟩
      · exact ⟨Sum.inr ⟨x.1, hD⟩, Subtype.ext rfl⟩)

private theorem balanced_union {C D : Finset (Q 9)} (hdisj : Disjoint C D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (hbC : IsBalanced C) (hbD : IsBalanced D) : IsBalanced (C ∪ D) := by
  obtain ⟨σC, hσC⟩ := hbC
  obtain ⟨σD, hσD⟩ := hbD
  have hnot (x : Q 9) (hx : x ∈ D) : x ∉ C :=
    fun hxC => Finset.disjoint_left.mp hdisj hxC hx
  refine ⟨fun x => if x ∈ C then σC x else σD x, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa only [ite_eq_left hx] using hσC.1 x hx
    · simpa only [ite_eq_right (hnot x hx)] using hσD.1 x hx
  · intro x hx y hy ha
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · simpa only [ite_eq_left hx, ite_eq_left hy] using hσC.2 x hx y hy ha
    · exact (hsep x hx y hy ha).elim
    · exact (hsep y hy x hx ha.symm).elim
    · simpa only [ite_eq_right (hnot x hx), ite_eq_right (hnot y hy)] using hσD.2 x hx y hy ha

private theorem balanced_switch (S : Finset (Q 9)) (hb : IsBalanced S) :
    ∃ s : Q 9 → ℤ, (∀ x, s x * s x = 1) ∧
      ∀ (w : Fin 9 → R) (x : Q 9), x ∈ S → ∀ y ∈ S, switched w s x y = unsigned w x y := by
  obtain ⟨σ, hσ⟩ := hb
  let s : Q 9 → ℤ := fun x => if σ x = 1 then 1 else -1
  have hs (x : Q 9) : s x * s x = 1 := by
    by_cases hx : σ x = 1 <;> norm_num [s, hx]
  have hcast (x : Q 9) (hx : x ∈ S) : (s x : ℝ) = σ x := by
    rcases hσ.1 x hx with h | h <;> norm_num [s, h]
  refine ⟨s, hs, fun w x hx y hy => ?_⟩
  simp only [switched, signed, unsigned, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : flip x a = y
  · subst y
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hflip : flipSign a x = s x * s (flip x a) := by
      apply Int.cast_injective (α := ℝ)
      rw [flipSign_cast, Int.cast_mul, hcast _ hx, hcast _ hy]
      exact hσ.2 x hx (flip x a) hy (flip_adj x a)
    have hsq (z : Q 9) : (s z : R) * (s z : R) = 1 := by
      simpa only [Int.cast_mul, Int.cast_one] using congrArg (fun z : ℤ => (z : R)) (hs z)
    rw [hflip, Int.cast_mul]
    calc
      _ = w a * ((s x : R) * (s x : R)) * ((s (flip x a) : R) * (s (flip x a) : R)) := by ring
      _ = _ := by rw [hsq, hsq, mul_one, mul_one]
  · simp [he]

private theorem gram_split {ι : Type*} [DecidableEq ι]
    (w : Fin 9 → R) (s : Q 9 → ℤ) (hs : ∀ x, s x * s x = 1)
    (S : Finset (Q 9)) (b : Bool) (r : ι ↪ Q 9) (hr : ∀ i, cubeParity (r i) = b) :
    let H := switched w s
    let K := H.submatrix r (fun y : Exterior S b => y.1.1)
    let M := H.submatrix r (fun y : Interior S b => y.1.1)
    K * Kᵀ = (∑ a, w a ^ 2) • 1 - M * Mᵀ := by
  dsimp only
  let H := switched w s
  let W := H.submatrix r (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1)
  have hW : W * Wᵀ = (∑ a, w a ^ 2) • 1 := by
    ext i j
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x : Q 9 => cubeParity x ≠ b)
      (fun x => H (r i) x * H (r j) x)
    have hz : (∑ x : {x : Q 9 // ¬ cubeParity x ≠ b}, H (r i) x.1 * H (r j) x.1) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      change switched w s (r i) x.1 * _ = 0
      rw [switched_same_parity w s ((hr i).trans (not_ne_iff.mp x.property).symm), zero_mul]
    rw [hz, add_zero] at hsplit
    calc
      _ = (H * Hᵀ) (r i) (r j) := hsplit
      _ = _ := by
        rw [switched_gram w s hs]
        simp [Matrix.one_apply, r.injective.eq_iff]
  apply eq_sub_of_add_eq
  rw [add_comm, ← hW]
  ext i j
  exact Fintype.sum_subtype_add_sum_subtype (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1 ∈ S)
    (fun x => H (r i) x.1 * H (r j) x.1)

-- The two dependent reindexings of the interior and exterior elaborate together here.
set_option maxHeartbeats 950000 in
open Classical in
/-- The square factor is the switched weighted boundary on the actual exterior.
Its Gram is block diagonal and its determinant squared is the product of the
two rooted defects. Coordinate weights can be specialized in any commutative ring. -/
theorem separated_cubic_weighted_boundary_factorization
    (C D : Finset (Q 9)) (b : Bool)
    (hC : C.card = 72) (hD : D.card = 186) (hdisj : Disjoint C D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (c : (C : Set (Q 9))) (d : (D : Set (Q 9)))
    (hc : cubeParity c.1 = b) (hd : cubeParity d.1 = b) :
    let Rows := RootedRows C b c ⊕ RootedRows D b d
    ∃ (s : Q 9 → ℤ) (e : Rows ≃ Exterior (C ∪ D) b),
      (∀ x, s x * s x = 1) ∧ Fintype.card Rows = 127 ∧ ∀ w : Fin 9 → R,
      let q := ∑ a, w a ^ 2
      let M_C := rootedBiadjacency w C b c
      let M_D := rootedBiadjacency w D b d
      let B_C := q • 1 - M_C * M_Cᵀ
      let B_D := q • 1 - M_D * M_Dᵀ
      let Z : Matrix Rows Rows R := fun i j =>
        let x := rowVertex i
        let y := (e j).1.1
        (s x : R) * (∑ a, if flip x a = y then w a * (flipSign a x : R) else 0) * (s y : R)
      Z * Zᵀ = Matrix.fromBlocks B_C 0 0 B_D ∧ B_C.det * B_D.det = Z.det ^ 2 := by
  classical
  dsimp only
  let Rows := RootedRows C b c ⊕ RootedRows D b d
  let r : Rows ↪ Q 9 := ⟨rowVertex, by
    intro i j hij
    cases i with
    | inl x =>
      cases j with
      | inl y => exact congrArg Sum.inl (Subtype.ext (Subtype.ext hij))
      | inr y => exact (Finset.disjoint_left.mp hdisj x.1.property
          ((show x.1.1 = y.1.1 from hij) ▸ y.1.property)).elim
    | inr x =>
      cases j with
      | inl y => exact (Finset.disjoint_left.mp hdisj y.1.property
          ((show x.1.1 = y.1.1 from hij) ▸ x.1.property)).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext (Subtype.ext hij))⟩
  have hr (i : Rows) : cubeParity (r i) = b := by
    cases i with
    | inl x => exact rooted_parity x
    | inr x => exact rooted_parity x
  have hrows : Fintype.card Rows = 127 := by
    have hrc := rooted_card C b c hc hrC
    have hrd := rooted_card D b d hd hrD
    rw [Fintype.card_sum]
    omega
  let f := interiorUnion b hdisj
  have hout : Fintype.card (Exterior (C ∪ D) b) = 127 := by
    have hpc := regular_parity_card C (!b) (d := 3) (by decide) hrC
    have hpd := regular_parity_card D (!b) (d := 3) (by decide) hrD
    have hcomp := Fintype.card_subtype_compl
      (fun y : {x : Q 9 // cubeParity x ≠ b} => y.1 ∈ C ∪ D)
    change Fintype.card (Exterior (C ∪ D) b) =
      Fintype.card {x : Q 9 // cubeParity x ≠ b} - Fintype.card (Interior (C ∪ D) b) at hcomp
    rw [hcomp, cube_opposite_card, ← Fintype.card_congr f, Fintype.card_sum,
      interior_card, interior_card]
    omega
  let e : Rows ≃ Exterior (C ∪ D) b := Fintype.equivOfCardEq (hrows.trans hout.symm)
  obtain ⟨s, hs, hswitch⟩ := balanced_switch (R := R) (C ∪ D)
    (balanced_union hdisj hsep hbC hbD)
  refine ⟨s, e, hs, hrows, fun w => ?_⟩
  let H := switched w s
  let K := H.submatrix r (fun y : Exterior (C ∪ D) b => y.1.1)
  let M := H.submatrix r (fun y : Interior (C ∪ D) b => y.1.1)
  let Z := K.submatrix id e
  let q := ∑ a, w a ^ 2
  let M_C := rootedBiadjacency w C b c
  let M_D := rootedBiadjacency w D b d
  let B_C := q • 1 - M_C * M_Cᵀ
  let B_D := q • 1 - M_D * M_Dᵀ
  change Z * Zᵀ = Matrix.fromBlocks B_C 0 0 B_D ∧ B_C.det * B_D.det = Z.det ^ 2
  have hM : M.submatrix id f = Matrix.fromBlocks M_C 0 0 M_D := by
    ext (i | i) (j | j)
    · exact hswitch w _ (Finset.mem_union_left _ i.1.property)
        _ (Finset.mem_union_left _ j.property)
    · exact (hswitch w _ (Finset.mem_union_left _ i.1.property)
        _ (Finset.mem_union_right _ j.property)).trans
        (unsigned_zero w (hsep _ i.1.property _ j.property))
    · exact (hswitch w _ (Finset.mem_union_right _ i.1.property)
        _ (Finset.mem_union_left _ j.property)).trans
        (unsigned_zero w fun ha => hsep _ j.property _ i.1.property ha.symm)
    · exact hswitch w _ (Finset.mem_union_right _ i.1.property)
        _ (Finset.mem_union_right _ j.property)
  have hblock : Z * Zᵀ = Matrix.fromBlocks B_C 0 0 B_D := by
    rw [show Z * Zᵀ = K * Kᵀ from Matrix.submatrix_mul_transpose_submatrix e K]
    have hGram : K * Kᵀ = q • 1 - M * Mᵀ := gram_split w s hs (C ∪ D) b r hr
    have hreindex : M.submatrix id f * (M.submatrix id f)ᵀ = M * Mᵀ := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    have hprod : M * Mᵀ = Matrix.fromBlocks (M_C * M_Cᵀ) 0 0 (M_D * M_Dᵀ) := by
      calc
        _ = M.submatrix id f * (M.submatrix id f)ᵀ := hreindex.symm
        _ = _ := by
          rw [hM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
          simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [hGram, hprod]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, B_C, B_D]
  refine ⟨hblock, ?_⟩
  rw [← Matrix.det_fromBlocks_zero₂₁ B_C 0 B_D, ← hblock, Matrix.det_mul, Matrix.det_transpose,
    pow_two]

#print axioms separated_cubic_weighted_boundary_factorization

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Universal weighted Gram singularity for separated cubic supports of total size 258. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Universal weighted Gram singularity for two separated cubic supports in the nine-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9BoundaryGram (Interior Exterior)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedBoundaryGram (RootedRows rootedBiadjacency)
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private regular_parity_card interior_card cube_opposite_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BoundaryGram
open private gram_split switched signed signed_mulVec signed_transpose balanced_switch
  balanced_union interiorUnion unsigned unsigned_zero rooted_parity rooted_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open private unit_line unit_weight weighted_cross from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

variable {R : Type*} [CommRing R]

/-- All vertices of a support on the retained parity. -/
abbrev Rows (S : Finset (Q 9)) (b : Bool) := ↥(paritySide S b)

private def biadjacencyOn {ι : Type*} (w : Fin 9 → R) (S : Finset (Q 9)) (b : Bool)
    (r : ι → Q 9) : Matrix ι (Interior S b) R :=
  fun i j => unsigned w (r i) j.1.1

/-- The coordinate-weighted biadjacency from the full parity side of the support. -/
def biadjacency (w : Fin 9 → R) (S : Finset (Q 9)) (b : Bool) :
    Matrix (Rows S b) (Interior S b) R :=
  biadjacencyOn w S b (fun x => x.1.1)

private def defect {ι κ : Type*} [DecidableEq ι] [Fintype κ] (w : Fin 9 → R)
    (M : Matrix ι κ R) : Matrix ι ι R :=
  (∑ a, w a ^ 2) • 1 - M * Mᵀ

private theorem eval_defect_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Fin 9 → ℝ) (S : Finset (Q 9)) (b : Bool) (r : ι → Q 9) :
    let w : Fin 9 → MvPolynomial (Fin 9) ℝ := MvPolynomial.X
    MvPolynomial.eval v (defect w (biadjacencyOn w S b r)).det =
      (defect v (biadjacencyOn v S b r)).det := by
  dsimp only
  let w : Fin 9 → MvPolynomial (Fin 9) ℝ := MvPolynomial.X
  let e := MvPolynomial.eval v
  change e (defect w (biadjacencyOn w S b r)).det = _
  have hM : (biadjacencyOn w S b r).map e = biadjacencyOn v S b r := by
    ext i j
    change e (unsigned w (r i) j.1.1) = unsigned v (r i) j.1.1
    unfold unsigned
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [e, w]
  have hq : e (∑ a, w a ^ 2) = ∑ a, v a ^ 2 := by
    simp only [map_sum, map_pow, e, w, MvPolynomial.eval_X]
  rw [RingHom.map_det]
  congr 1
  change (defect w (biadjacencyOn w S b r)).map e = defect v (biadjacencyOn v S b r)
  unfold defect
  rw [Matrix.map_sub e (map_sub e), Matrix.map_smul' e _ _ (map_mul e),
    Matrix.map_one e (map_zero e) (map_one e), hq, Matrix.map_mul, Matrix.transpose_map, hM]

open Classical in
private theorem rooted_unit_det_ne_zero (S : Finset (Q 9)) (b : Bool)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (S : Set (Q 9))).Connected)
    (hb : IsBalanced S) (d : (S : Set (Q 9))) (hd : parity d.1 = b) :
    (defect (fun _ => (1 : ℝ)) (rootedBiadjacency (fun _ => (1 : ℝ)) S b d)).det ≠ 0 := by
  classical
  let w : Fin 9 → ℝ := fun _ => 1
  let r : RootedRows S b d ↪ Q 9 :=
    ⟨fun i => i.1.1, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  let M := rootedBiadjacency w S b d
  change (defect w M).det ≠ 0
  obtain ⟨s, hs, hswitch⟩ := balanced_switch (R := ℝ) S hb
  have hsReal (x : Q 9) : (s x : ℝ) * (s x : ℝ) = 1 := by
    simpa only [Int.cast_mul, Int.cast_one] using congrArg (fun z : ℤ => (z : ℝ)) (hs x)
  let A := switched w s
  let K := A.submatrix r (fun y : Exterior S b => y.1.1)
  have hM : A.submatrix r (fun y : Interior S b => y.1.1) = M := by
    ext i j
    exact hswitch w _ i.1.property _ j.property
  have hGram : K * Kᵀ = defect w M := by
    change K * Kᵀ = (∑ a, w a ^ 2) • 1 - M * Mᵀ
    rw [← hM]
    exact gram_split w s hs S b r (fun i => rooted_parity i)
  intro hdet
  obtain ⟨u, hu, hzero⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := defect w M)).mpr hdet
  have hker : u ∈ LinearMap.ker ((Kᵀ)ᵀ * Kᵀ).mulVecLin := by
    rw [Matrix.transpose_transpose, hGram, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hzero
  rw [Matrix.ker_mulVecLin_transpose_mul_self Kᵀ] at hker
  have hKu : Kᵀ *ᵥ u = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hker
  let f := Function.extend r (fun i => (s (r i) : ℝ) * u i) 0
  have hfrow (i : RootedRows S b d) : f (r i) = (s (r i) : ℝ) * u i :=
    r.injective.extend_apply _ _ i
  have hfzero (x : Q 9) (hx : ¬ ∃ i, r i = x) : f x = 0 :=
    Function.extend_apply' _ _ _ hx
  have hfs (x : Q 9) (hx : x ∉ S) : f x = 0 := by
    apply hfzero
    rintro ⟨i, rfl⟩
    exact hx i.1.property
  have hfb (x : Q 9) (hx : parity x ≠ b) : f x = 0 := by
    apply hfzero
    rintro ⟨i, rfl⟩
    exact hx (rooted_parity i)
  have hfd : f d.1 = 0 := by
    apply hfzero
    rintro ⟨i, hi⟩
    exact (Finset.mem_erase.mp i.property).1 (Subtype.ext hi)
  have hcross (x : Q 9) (hx : x ∉ S) : weightedLinear w f x = 0 := by
    by_cases hxb : parity x = b
    · apply weighted_cross w hfb x
      rw [hxb]
      cases b <;> decide
    · let y : Exterior S b := ⟨⟨x, hxb⟩, hx⟩
      have hK : (Kᵀ *ᵥ u) y = 0 := congrFun hKu y
      have hsym (z : Q 9) : signed w x z = signed w z x :=
        congrFun (congrFun (signed_transpose w) z) x
      rw [← signed_mulVec]
      change (∑ z, signed w x z * f z) = 0
      calc
        _ = ∑ i, signed w x (r i) * f (r i) := by
          symm
          refine Fintype.sum_of_injective r r.injective _ _ ?_ (fun _ => rfl)
          intro z hz
          rw [hfzero z hz, mul_zero]
        _ = (s x : ℝ) * (Kᵀ *ᵥ u) y := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hfrow, hsym]
          change signed w (r i) x * ((s (r i) : ℝ) * u i) =
            (s x : ℝ) * (((s (r i) : ℝ) * signed w (r i) x * (s x : ℝ)) * u i)
          rw [show (s x : ℝ) * (((s (r i) : ℝ) * signed w (r i) x * (s x : ℝ)) * u i) =
            ((s x : ℝ) * (s x : ℝ)) * (signed w (r i) x * ((s (r i) : ℝ) * u i)) by ring,
            hsReal, one_mul]
        _ = 0 := by rw [hK, mul_zero]
  obtain ⟨σ, hσ⟩ := hb
  have hline := unit_line hr hc hσ hfs hfb (by simpa only [w, unit_weight] using hcross)
    d.1 d.property hd
  rw [hfd, zero_mul, zero_smul] at hline
  apply hu
  funext i
  have hi : f (r i) = 0 := congrFun hline (r i)
  rw [hfrow] at hi
  have hsi := hsReal (r i)
  exact (mul_eq_zero.mp hi).resolve_left fun h => by simp [h] at hsi

open Classical in
/-- The weighted Gram defect on either full parity side of a balanced cubic support
is singular whenever a separated connected balanced cubic partner brings the total
size to 258. The weights may be any real numbers. -/
theorem separated_cubic_weighted_gram_singular
    (C D : Finset (Q 9)) (b : Bool) (hsize : C.card + D.card = 258)
    (hdisj : Disjoint C D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (v : Fin 9 → ℝ) :
    let M := biadjacency v C b
    (((∑ a, v a ^ 2) • 1 : Matrix (Rows C b) (Rows C b) ℝ) - M * Mᵀ).det = 0 := by
  classical
  have hCb := regular_parity_card C b (d := 3) (by decide) hrC
  have hDb := regular_parity_card D b (d := 3) (by decide) hrD
  have hDpos : 0 < D.card := by
    obtain ⟨x⟩ := hcD.nonempty
    exact Finset.card_pos.mpr ⟨x.1, x.property⟩
  obtain ⟨d, hdmem⟩ : (paritySide D b).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hd : parity d.1 = b := (Finset.mem_filter.mp hdmem).2
  let I := Rows C b ⊕ RootedRows D b d
  let r : I ↪ Q 9 := ⟨Sum.elim (fun x => x.1.1) (fun x => x.1.1), by
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
  have hr (i : I) : parity (r i) = b := by
    cases i with
    | inl x => exact (Finset.mem_filter.mp x.property).2
    | inr x => exact rooted_parity x
  have hrows : Fintype.card I = 128 := by
    have hrd := rooted_card D b d hd hrD
    change Fintype.card (Rows C b ⊕ RootedRows D b d) = 128
    rw [Fintype.card_sum, show Fintype.card (Rows C b) = (paritySide C b).card from
      Fintype.card_coe _]
    omega
  let e := interiorUnion b hdisj
  have hcols : Fintype.card (Exterior (C ∪ D) b) = 127 := by
    have hpc := regular_parity_card C (!b) (d := 3) (by decide) hrC
    have hpd := regular_parity_card D (!b) (d := 3) (by decide) hrD
    have hcomp := Fintype.card_subtype_compl
      (fun y : {x : Q 9 // parity x ≠ b} => y.1 ∈ C ∪ D)
    change Fintype.card (Exterior (C ∪ D) b) =
      Fintype.card {x : Q 9 // parity x ≠ b} - Fintype.card (Interior (C ∪ D) b) at hcomp
    rw [hcomp, cube_opposite_card, ← Fintype.card_congr e, Fintype.card_sum,
      interior_card, interior_card]
    omega
  let P := MvPolynomial (Fin 9) ℝ
  let w : Fin 9 → P := MvPolynomial.X
  obtain ⟨s, hs, hswitch⟩ := balanced_switch (R := P) (C ∪ D)
    (balanced_union hdisj hsep hbC hbD)
  let A := switched w s
  let K := A.submatrix r (fun y : Exterior (C ∪ D) b => y.1.1)
  let M := A.submatrix r (fun y : Interior (C ∪ D) b => y.1.1)
  let MC := biadjacency w C b
  let MD := rootedBiadjacency w D b d
  let BC := defect w MC
  let BD := defect w MD
  have hM : M.submatrix id e = Matrix.fromBlocks MC 0 0 MD := by
    apply Matrix.ext
    rintro (i | i) (j | j)
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
  have hGram : K * Kᵀ = (∑ a, w a ^ 2) • 1 - M * Mᵀ :=
    gram_split w s hs (C ∪ D) b r hr
  have hprod : M * Mᵀ = Matrix.fromBlocks (MC * MCᵀ) 0 0 (MD * MDᵀ) := by
    calc
      _ = M.submatrix id e * (M.submatrix id e)ᵀ := by
        symm
        rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
      _ = _ := by
        rw [hM, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
        simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  have hblock : K * Kᵀ = Matrix.fromBlocks BC 0 0 BD := by
    rw [hGram, hprod]
    apply Matrix.ext
    rintro (i | i) (j | j) <;> simp [Matrix.one_apply, BC, BD, defect]
  have hdet : (K * Kᵀ).det = 0 := by
    by_contra hne
    have hfull := Matrix.rank_of_det_ne_zero hne
    have hrank := (Matrix.rank_mul_le_left K Kᵀ).trans (Matrix.rank_le_card_width K)
    rw [hfull, hrows, hcols] at hrank
    omega
  have hdetprod : BC.det * BD.det = 0 := by
    rw [hblock] at hdet
    exact (Matrix.det_fromBlocks_zero₂₁ BC 0 BD).symm.trans hdet
  have hBD : BD.det ≠ 0 := by
    intro hz
    have he := eval_defect_det (fun _ => (1 : ℝ)) D b (fun i : RootedRows D b d => i.1.1)
    have he' : MvPolynomial.eval (fun _ => (1 : ℝ)) BD.det =
        (defect (fun _ => (1 : ℝ)) (rootedBiadjacency (fun _ => (1 : ℝ)) D b d)).det := he
    rw [hz, map_zero] at he'
    exact rooted_unit_det_ne_zero D b hrD hcD hbD d hd he'.symm
  have hBC := (mul_eq_zero.mp hdetprod).resolve_right hBD
  have he := eval_defect_det v C b (fun i : Rows C b => i.1.1)
  have he' : MvPolynomial.eval v BC.det = (defect v (biadjacency v C b)).det := he
  rw [hBC, map_zero] at he'
  exact he'.symm

#print axioms separated_cubic_weighted_gram_singular

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

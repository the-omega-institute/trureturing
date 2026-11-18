/- GID: D5/S3/Geometry/FlatlandImageClosure
   generality: G
   mirror-B: D5/B/S3/Geometry/FlatlandImageClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial deformations and linear algebra for two-camera image closure. -/

/-
admission_basis: escape-witness
escape_witness: diagonal_rank_two_closure (used by singular_compatible_closure)
Direct frozen dependencies: C = D5/S3/Arith/Lattices/CofactorKernel.cofactor @
  sha256:3166337f4d6d020e4b4c7683bf2c13d3987b090b3e99f722181e1790e47736fd.
The matrix cofactorMatrix reshapes C by column vectorization.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30117
Declaration classifications (same-delivery helpers expanded; C denotes the declaration above):
diagonal_rank_two_closure | proof_shape: content; escape_witness: diagonal_rank_two_closure; Direct frozen dependencies: none; consumers: normalized_rank_one_closure, normalRankTwo_closure.
normalized_rank_one_closure | proof_shape: content; escape_witness: diagonal_rank_two_closure; Direct frozen dependencies: none; consumers: normalRankOne_closure.
linearCoordinatePolynomial | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: linearCoordinatePolynomial_homogeneous, linearCoordinatePolynomial_eval, imageClosure_postcompose.
linearCoordinatePolynomial_homogeneous | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_postcompose.
linearCoordinatePolynomial_eval | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_postcompose.
postcomposeConfiguration | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: postcompose_actual, imageClosure_postcompose, postcompose_restore, compatible_coordinate_change, closure_from_bilinear_normal_form.
postcompose_actual | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: imageClosure_postcompose.
imageClosure_postcompose | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closure_from_bilinear_normal_form.
Compatible | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: compatible_coordinate_change, closure_from_bilinear_normal_form, normalRankOne_closure, normalRankTwo_closure, singular_compatible_closure.
postcompose_restore | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closure_from_bilinear_normal_form.
compatible_coordinate_change | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: closure_from_bilinear_normal_form.
closure_from_bilinear_normal_form | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: singular_compatible_closure.
normalRankOne | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: normalRankOne_closure, permute_rank_normal_form, nonzero_singular_normal_form, singular_compatible_closure.
normalRankTwo | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: normalRankTwo_closure, permute_rank_normal_form, nonzero_singular_normal_form, singular_compatible_closure.
normalRankOne_closure | proof_shape: content; escape_witness: diagonal_rank_two_closure; Direct frozen dependencies: none; consumers: singular_compatible_closure.
normalRankTwo_closure | proof_shape: content; escape_witness: diagonal_rank_two_closure; Direct frozen dependencies: none; consumers: singular_compatible_closure.
permute_rank_normal_form | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: nonzero_singular_normal_form.
nonzero_singular_normal_form | proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: singular_compatible_closure.
singular_compatible_closure | proof_shape: content; escape_witness: diagonal_rank_two_closure; Direct frozen dependencies: none; consumers: D5.S3.Geometry.FlatlandImageEquations.equations_imply_imageClosure.
-/

import D5.S3.Geometry.FlatlandImageAlgebra
import Mathlib.Data.Matrix.PEquiv

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Geometry.FlatlandImageClosure
open D5.S3.Geometry.FlatlandImageAlgebra

section
open Matrix
open scoped Classical

/-- Every canonical rank-two-compatible configuration, including epipoles, is in the multihomogeneous image closure. -/
private theorem diagonal_rank_two_closure {n : ℕ} (c : ℂ) (hc : c ≠ 0) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : ∀ j, (p j 0).rep 0 * (p j 1).rep 0 +
      c * (p j 0).rep 1 * (p j 1).rep 1 = 0) : p ∈ imageClosure n := by
  choose Xc Yc hX hY hn hr using fun j => diagonal_rank_two_pair_curves c hc
    (p j 0).rep (p j 1).rep (p j 0).rep_nonzero (p j 1).rep_nonzero (hp j)
  let z : (Fin n × Fin 2) → Fin 3 → _root_.Polynomial ℂ :=
    fun b => if b.2 = 0 then Xc b.1 else Yc b.1
  have hz : ∀ t b, (fun k => (z b k).eval t) ≠ 0 := by
    intro t b
    rcases b with ⟨j,i⟩
    fin_cases i
    · simpa [z] using (hn j t).1
    · simpa [z] using (hn j t).2
  have hstart : (fun j i => Projectivization.mk ℂ (fun a => (z (j,i) a).eval 0)
      (hz 0 (j,i))) = p := by
    funext j i
    fin_cases i
    · simpa [z, hX j] using (p j 0).mk_rep
    · simpa [z, hY j] using (p j 1).mk_rep
  rw [← hstart]
  apply imageClosure_polynomial_specialization z hz
  intro t ht
  choose q a b ha hb hA hB using fun j => hr j t ht
  let A : Fin 2 → Matrix (Fin 3) (Fin 4) ℂ := ![canonicalA, diagonalB c]
  have hA0 : ∀ i, A i ≠ 0 := by
    intro i he
    have hh := congrFun (congrFun he 2) 2
    fin_cases i <;> simp [A, canonicalA, diagonalB] at hh
  have himage : ∀ j i, A i *ᵥ q j ≠ 0 := by
    intro j i
    fin_cases i
    · change canonicalA *ᵥ q j ≠ 0
      rw [hA j]
      exact smul_ne_zero (ha j) (hn j t).1
    · change diagonalB c *ᵥ q j ≠ 0
      rw [hB j]
      exact smul_ne_zero (hb j) (hn j t).2
  have hq : ∀ j, q j ≠ 0 := by
    intro j he
    apply himage j 0
    rw [he, mulVec_zero]
  obtain ⟨s, hs⟩ := raw_imaging_realization A q hA0 hq himage
  have heq : theta s = fun j i => Projectivization.mk ℂ
      (fun k => (z (j,i) k).eval t) (hz t (j,i)) := by
    rw [hs]
    funext j i
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
    fin_cases i
    · exact ⟨a j, (hA j).symm⟩
    · exact ⟨b j, (hB j).symm⟩
  rw [← heq]
  intro f hf hvan
  exact hvan s
end

section
/-- Every normalized rank-one-compatible configuration is in the multihomogeneous image closure. -/
private theorem normalized_rank_one_closure {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : ∀ j, (p j 0).rep 0 * (p j 1).rep 0 = 0) : p ∈ imageClosure n := by
  exact rank_one_closure_from_rank_two
    (fun t ht => diagonal_rank_two_closure (t ^ 2) (pow_ne_zero 2 ht)) p hp
end

section
open Matrix
open scoped BigOperators Classical

private def linearCoordinatePolynomial {n : ℕ} (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (k : ((Fin n × Fin 2) × Fin 3)) : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) :=
  ∑ a : Fin 3, MvPolynomial.C (L k.1.2 k.2 a) * MvPolynomial.X (k.1,a)

private theorem linearCoordinatePolynomial_homogeneous {n : ℕ}
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) (k : ((Fin n × Fin 2) × Fin 3)) (b : Fin n × Fin 2) :
    (linearCoordinatePolynomial L k).IsWeightedHomogeneous
      (fun k' : ((Fin n × Fin 2) × Fin 3) => if k'.1 = b then (1 : ℕ) else 0)
      (if k.1 = b then (1 : ℕ) else 0) := by
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro a ha
  exact (MvPolynomial.isWeightedHomogeneous_X ℂ _ (k.1,a)).C_mul _

private theorem linearCoordinatePolynomial_eval {n : ℕ}
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) (z : ((Fin n × Fin 2) × Fin 3) → ℂ) (k : ((Fin n × Fin 2) × Fin 3)) :
    MvPolynomial.eval z (linearCoordinatePolynomial L k) =
      L k.1.2 k.2 ⬝ᵥ (fun a => z (k.1,a)) := by
  simp [linearCoordinatePolynomial, dotProduct]

private def postcomposeConfiguration {n : ℕ} (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hL : ∀ i, Function.Injective (L i).mulVecLin) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)) :=
  fun j i => Projectivization.map (L i).mulVecLin (hL i) (p j i)

private theorem postcompose_actual {n : ℕ}
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hL : ∀ i, Function.Injective (L i).mulVecLin) (s : ImagingDomain n) :
    ∃ s' : ImagingDomain n, theta s' = postcomposeConfiguration L hL (theta s) := by
  let A : Fin 2 → Matrix (Fin 3) (Fin 4) ℂ := fun i => L i * (s.val.2 i).rep
  let q : Fin n → Fin 4 → ℂ := fun j => (s.val.1 j).rep
  have hA : ∀ i, A i ≠ 0 := by
    intro i he
    apply (s.val.2 i).rep_nonzero
    funext a b
    have hh : L i *ᵥ (fun c => (s.val.2 i).rep c b) = L i *ᵥ 0 := by
      funext c
      simpa [A, mul_apply, mulVec, dotProduct] using congrFun (congrFun he c) b
    change (L i).mulVecLin (fun c => (s.val.2 i).rep c b) = (L i).mulVecLin 0 at hh
    exact congrFun (hL i hh) a
  have himage : ∀ j i, A i *ᵥ q j ≠ 0 := by
    intro j i he
    apply s.property j i
    apply hL i
    simpa [A, q, mulVec_mulVec] using he
  obtain ⟨s', hs'⟩ := raw_imaging_realization A q hA (fun j => (s.val.1 j).rep_nonzero) himage
  refine ⟨s', ?_⟩
  rw [hs']
  funext j i
  simp only [postcomposeConfiguration, theta, Projectivization.map_mk]
  congr 1
  exact (Matrix.mulVec_mulVec _ _ _).symm

/-- Independent injective linear changes in the two image planes preserve the multihomogeneous closure. -/
private theorem imageClosure_postcompose {n : ℕ}
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ)
    (hL : ∀ i, Function.Injective (L i).mulVecLin) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : p ∈ imageClosure n) : postcomposeConfiguration L hL p ∈ imageClosure n := by
  intro f hf hvan
  obtain ⟨D,hD⟩ := hf
  let g : (MvPolynomial ((Fin n × Fin 2) × Fin 3) ℂ) := MvPolynomial.eval₂ MvPolynomial.C (linearCoordinatePolynomial L) f
  have hg : Multihomogeneous g := by
    refine ⟨D, fun b => ?_⟩
    exact homogeneous_substitution _ _ f (D b) (hD b) (linearCoordinatePolynomial L)
      (fun k => linearCoordinatePolynomial_homogeneous L k b)
  have heval (q : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) :
      MvPolynomial.eval (coordinates (postcomposeConfiguration L hL q)) f = 0 ↔
        MvPolynomial.eval (coordinates q) g = 0 := by
    let z : (Fin n × Fin 2) → Fin 3 → ℂ := fun b => L b.2 *ᵥ (q b.1 b.2).rep
    have hz : ∀ b, z b ≠ 0 := by
      intro b he
      exact (q b.1 b.2).rep_nonzero (hL b.2 (by simpa [z] using he))
    have hh := eval_projective_representatives_zero_iff f D hD z hz
    have hm : (fun k : ((Fin n × Fin 2) × Fin 3) =>
        (Projectivization.mk ℂ (z k.1) (hz k.1)).rep k.2) =
      coordinates (postcomposeConfiguration L hL q) := by
      funext k
      simp only [coordinates, postcomposeConfiguration]
      have he : Projectivization.mk ℂ (z k.1) (hz k.1) =
          Projectivization.map (L k.1.2).mulVecLin (hL k.1.2) (q k.1.1 k.1.2) := by
        conv_rhs => rw [← (q k.1.1 k.1.2).mk_rep, Projectivization.map_mk]
        try rfl
      rw [he]
    rw [hm] at hh
    have hev : MvPolynomial.eval (coordinates q) g =
        MvPolynomial.eval (fun k => z k.1 k.2) f := by
      change MvPolynomial.eval (coordinates q)
        (MvPolynomial.eval₂ MvPolynomial.C (linearCoordinatePolynomial L) f) = _
      rw [← MvPolynomial.eval_assoc]
      apply congrArg (fun w : ((Fin n × Fin 2) × Fin 3) → ℂ => MvPolynomial.eval w f)
      funext k
      exact linearCoordinatePolynomial_eval L (coordinates q) k
    rw [hev]
    exact hh
  apply (heval p).2
  apply hp g hg
  intro s
  apply (heval (theta s)).1
  obtain ⟨s',hs'⟩ := postcompose_actual L hL s
  rw [← hs']
  exact hvan s'
end

section
open Matrix Module
open scoped BigOperators Classical

def Compatible {n : ℕ} (F : Matrix (Fin 3) (Fin 3) ℂ) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) : Prop :=
  ∀ j, (p j 1).rep ⬝ᵥ (F *ᵥ (p j 0).rep) = 0

private theorem postcompose_restore {n : ℕ}
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) (hL : ∀ i, IsUnit (L i))
    (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) :
    postcomposeConfiguration (fun i => (L i)⁻¹)
      (fun i => Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr (hL i)))
      (postcomposeConfiguration L (fun i => Matrix.mulVec_injective_iff_isUnit.mpr (hL i)) p) = p := by
  funext j i
  change Projectivization.map _ _ (Projectivization.map _ _ (p j i)) = p j i
  refine Projectivization.ind (fun v hv => ?_) (p j i)
  simp only [Projectivization.map_mk]
  have he : (L i)⁻¹ *ᵥ ((L i) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hL i)),
      Matrix.one_mulVec]
  change Projectivization.mk ℂ ((L i)⁻¹ *ᵥ ((L i) *ᵥ v)) _ = Projectivization.mk ℂ v hv
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨1, by simpa only [one_smul] using he.symm⟩

private theorem compatible_coordinate_change {n : ℕ}
    (E : Matrix (Fin 3) (Fin 3) ℂ)
    (L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ) (hL : ∀ i, IsUnit (L i))
    (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : Compatible ((L 1).transpose * E * L 0) p) :
    Compatible E (postcomposeConfiguration L
      (fun i => Matrix.mulVec_injective_iff_isUnit.mpr (hL i)) p) := by
  intro j
  let x := L 0 *ᵥ (p j 0).rep
  let y := L 1 *ᵥ (p j 1).rep
  have hx : x ≠ 0 := by
    intro hh
    exact (p j 0).rep_nonzero (Matrix.mulVec_injective_iff_isUnit.mpr (hL 0) (by simpa [x] using hh))
  have hy : y ≠ 0 := by
    intro hh
    exact (p j 1).rep_nonzero (Matrix.mulVec_injective_iff_isUnit.mpr (hL 1) (by simpa [y] using hh))
  have hn (i : Fin 2) : L i *ᵥ (p j i).rep ≠ 0 := by
    intro hh
    apply (p j i).rep_nonzero
    apply Matrix.mulVec_injective_iff_isUnit.mpr (hL i)
    simpa using hh
  have hmk (i : Fin 2) : postcomposeConfiguration L
      (fun i => Matrix.mulVec_injective_iff_isUnit.mpr (hL i)) p j i =
      Projectivization.mk ℂ (L i *ᵥ (p j i).rep) (hn i) := by
    unfold postcomposeConfiguration
    conv_lhs => rw [← (p j i).mk_rep]
    rfl
  rw [hmk 0,hmk 1]
  apply (bilinear_projective_mk_zero_iff E x y hx hy).2
  change (L 1 *ᵥ (p j 1).rep) ⬝ᵥ (E *ᵥ (L 0 *ᵥ (p j 0).rep)) = 0
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  change ((L 1).transpose *ᵥ (E *ᵥ (L 0 *ᵥ (p j 0).rep))) ⬝ᵥ (p j 1).rep = 0
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,dotProduct_comm]
  exact hp j

/-- Closure membership transports back from any invertible bilinear normal form. -/
private theorem closure_from_bilinear_normal_form {n : ℕ}
    (F E U V : Matrix (Fin 3) (Fin 3) ℂ) (hU : IsUnit U) (hV : IsUnit V)
    (hN : V * F * U = E)
    (hE : ∀ q : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)), Compatible E q → q ∈ imageClosure n)
    (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (hp : Compatible F p) : p ∈ imageClosure n := by
  let L : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ := ![U⁻¹,(V⁻¹).transpose]
  have hL : ∀ i, IsUnit (L i) := by
    intro i
    fin_cases i
    · exact Matrix.isUnit_nonsing_inv_iff.mpr hU
    · exact (Matrix.isUnit_transpose _).mpr (Matrix.isUnit_nonsing_inv_iff.mpr hV)
  have heq : (L 1).transpose * E * L 0 = F := by
    change V⁻¹ * E * U⁻¹ = F
    rw [← hN]
    calc
      _ = (V⁻¹ * V) * F * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = F := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hV),
          Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
          Matrix.one_mul,Matrix.mul_one]
  have hq := compatible_coordinate_change E L hL p (by rwa [heq])
  have hc := imageClosure_postcompose (fun i => (L i)⁻¹)
    (fun i => Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr (hL i)))
    _ (hE _ hq)
  rwa [postcompose_restore L hL p] at hc

private def normalRankOne : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,0,0]

private def normalRankTwo : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,1,0]

private theorem normalRankOne_closure {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : Compatible normalRankOne p) : p ∈ imageClosure n := by
  apply normalized_rank_one_closure p
  intro j
  simpa [Compatible,normalRankOne,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm]
    using hp j

private theorem normalRankTwo_closure {n : ℕ} (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ)))
    (hp : Compatible normalRankTwo p) : p ∈ imageClosure n := by
  apply diagonal_rank_two_closure 1 one_ne_zero p
  intro j
  simpa [Compatible,normalRankTwo,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,mul_comm]
    using hp j

private theorem permute_rank_normal_form
    (F U V : Matrix (Fin 3) (Fin 3) ℂ) (r : ℕ) (hcases : r = 1 ∨ r = 2)
    (e : Fin 3 ≃ Fin r ⊕ Fin (3-r)) (hU : IsUnit U) (hV : IsUnit V)
    (hN : V * F * U = (Matrix.fromBlocks 1 0 0 0).submatrix e e) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, IsUnit U ∧ IsUnit V ∧
      (V * F * U = normalRankOne ∨ V * F * U = normalRankTwo) := by
  let e0 : Fin 3 ≃ Fin r ⊕ Fin (3-r) :=
    (finCongr (show 3 = r + (3-r) by omega)).trans finSumFinEquiv.symm
  let g : Fin 3 ≃ Fin 3 := e0.trans e.symm
  let P : Matrix (Fin 3) (Fin 3) ℂ := g.toPEquiv.toMatrix
  have hP : IsUnit P := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    rw [PEquiv.toMatrix_toPEquiv_mulVec,PEquiv.toMatrix_toPEquiv_mulVec] at hxy
    funext k
    simpa using congrFun hxy (g.symm k)
  refine ⟨U * P.transpose,P * V,hU.mul ((Matrix.isUnit_transpose _).mpr hP),hP.mul hV,?_⟩
  have heq : (P * V) * F * (U * P.transpose) =
      (Matrix.fromBlocks 1 0 0 0).submatrix e0 e0 := by
    calc
      _ = P * (V * F * U) * P.transpose := by simp only [Matrix.mul_assoc]
      _ = P * ((Matrix.fromBlocks 1 0 0 0).submatrix e e) * P.transpose := by rw [hN]
      _ = (Matrix.fromBlocks 1 0 0 0).submatrix e0 e0 := by
        rw [show P.transpose = g.symm.toPEquiv.toMatrix by
          exact (PEquiv.toMatrix_symm g.toPEquiv).symm]
        rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
        ext i j
        simp [Matrix.submatrix,g]
  rcases hcases with rfl | rfl
  · left
    rw [heq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e0,normalRankOne,Matrix.submatrix,Matrix.fromBlocks,finSumFinEquiv,Fin.addCases,Matrix.diagonal]
  · right
    rw [heq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [e0,normalRankTwo,Matrix.submatrix,Matrix.fromBlocks,finSumFinEquiv,Fin.addCases,Matrix.diagonal]

/-- Rank normal form for a nonzero singular three by three matrix has one or two unit entries. -/
private theorem nonzero_singular_normal_form (F : Matrix (Fin 3) (Fin 3) ℂ)
    (hF : F ≠ 0) (hs : F.det = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, IsUnit U ∧ IsUnit V ∧
      (V * F * U = normalRankOne ∨ V * F * U = normalRankTwo) := by
  have hpos : 1 ≤ F.rank := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    apply hF
    have hz : F.mulVecLin = 0 := LinearMap.range_eq_bot.mp he
    apply Matrix.mulVec_injective
    funext x
    simpa using LinearMap.congr_fun hz x
  obtain ⟨v,hv,hkv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
  let W := LinearMap.ker F.mulVecLin
  have hW : 1 ≤ Module.finrank ℂ W := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    have hh : v ∈ W := hkv
    rw [he,Submodule.mem_bot] at hh
    exact hv hh
  have hd := LinearMap.finrank_range_add_finrank_ker F.mulVecLin
  change F.rank + Module.finrank ℂ W = Module.finrank ℂ (Fin 3 → ℂ) at hd
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hd
  obtain ⟨V,U,e,hV,hU,hN⟩ := Matrix.exists_rank_normal_form F
  have hcases : F.rank = 1 ∨ F.rank = 2 := by omega
  exact permute_rank_normal_form F U V F.rank hcases e hU hV hN

/-- Every configuration compatible with a nonzero singular bilinear form lies in the multihomogeneous closure. -/
theorem singular_compatible_closure {n : ℕ} (F : Matrix (Fin 3) (Fin 3) ℂ)
    (hF : F ≠ 0) (hs : F.det = 0) (p : (Fin n → Fin 2 → Projectivization ℂ (Fin 3 → ℂ))) (hp : Compatible F p) :
    p ∈ imageClosure n := by
  obtain ⟨U,V,hU,hV,he|he⟩ := nonzero_singular_normal_form F hF hs
  · exact closure_from_bilinear_normal_form F normalRankOne U V hU hV he normalRankOne_closure p hp
  · exact closure_from_bilinear_normal_form F normalRankTwo U V hU hV he normalRankTwo_closure p hp
end
end D5.S3.Geometry.FlatlandImageClosure

/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Alternating-form coordinates express the integral rank-three obstruction as a reduced matrix kernel. -/

import D5.S3.Combinatorics.Matroids.RankThreeOmissionRelations
import D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.UniformCircuitResidueDiagonal
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

private noncomputable def marker {I R : Type*} [Zero R] [One R] (x y : I) : R :=
  open Classical in if x = y then 1 else 0

private noncomputable def edgeDet {I R : Type*} [Ring R] (i j x y : I) : R :=
  marker x i * marker y j - marker y i * marker x j

private theorem row_eq_edge_determinants {I R : Type*} [Ring R] (p : Fin 3 → I)
    (hp : Function.Injective p) (x y : I) :
    row p (1 : R) x y = edgeDet (p 0) (p 1) x y + edgeDet (p 1) (p 2) x y +
      edgeDet (p 2) (p 0) x y := by
  classical
  have h01 := hp.ne (by decide : (0 : Fin 3) ≠ 1)
  have h12 := hp.ne (by decide : (1 : Fin 3) ≠ 2)
  have h20 := hp.ne (by decide : (2 : Fin 3) ≠ 0)
  by_cases hx : x ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hx
    by_cases hy : y ∈ Set.range p
    · obtain ⟨j, rfl⟩ := hy
      fin_cases i <;> fin_cases j <;>
        simp [row, forward, edgeDet, marker, h01, h01.symm, h12, h12.symm, h20, h20.symm]
    · have nh (j : Fin 3) : p j ≠ y := fun h => hy ⟨j, h⟩
      simp [row, forward, edgeDet, marker, nh, fun j => (nh j).symm]
  · have nh (i : Fin 3) : p i ≠ x := fun h => hx ⟨i, h⟩
    simp [row, forward, edgeDet, marker, nh, fun i => (nh i).symm]

/-- Each reduced row entry is the determinant of the corresponding two
quotient coordinates of the two differences of the triangle. -/
private theorem reducedMatrix_eq_determinant {I T R : Type*} [LinearOrder I] [CommRing R]
    (points : T → Fin 3 → I) (root anchor : I) (t : T)
    (ht : Function.Injective (points t)) (ij : RemainingPair root anchor) :
    let s (p x : I) : R := marker p x - marker anchor x
    let delta (k : Fin 3) (p : I) := s p (points t k) - s p (points t 0)
    (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) R) t ij =
      delta 1 ij.val.1 * delta 2 ij.val.2 - delta 1 ij.val.2 * delta 2 ij.val.1 := by
  intro s delta
  change row (points t) (1 : R) ij.val.1 ij.val.2 -
    row (points t) 1 anchor ij.val.2 + row (points t) 1 anchor ij.val.1 = _
  simp only [row_eq_edge_determinants _ ht, edgeDet, delta, s]
  ring


open Set.powersetCard

/-- The two active indices of a basis coordinate, taken in increasing order. -/
noncomputable def pairIndexEquiv {I : Type*} [LinearOrder I] (root anchor : I) :
    RemainingPair root anchor ≃ {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val} := by
  classical
  let asEmb : RemainingPair root anchor →
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} := fun p => by
    let e : Fin 2 → I := ![p.val.1, p.val.2]
    have he : StrictMono e := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (lt_irrefl _ hij).elim
      · exact p.prop.1
      · exact ((by decide : ¬ (1 : Fin 2) < 0) hij).elim
      · exact (lt_irrefl _ hij).elim
    refine ⟨OrderEmbedding.ofStrictMono e he, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact p.prop.2.1
      · exact p.prop.2.2.1
    · intro i
      fin_cases i
      · exact p.prop.2.2.2.1
      · exact p.prop.2.2.2.2
  let fromEmb :
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} →
        RemainingPair root anchor := fun e =>
    ⟨(e.val 0, e.val 1), e.val.strictMono (by decide), e.prop.1 0, e.prop.1 1,
      e.prop.2 0, e.prop.2 1⟩
  let embedded : RemainingPair root anchor ≃
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} :=
    { toFun := asEmb
      invFun := fromEmb
      left_inv := fun _ => rfl
      right_inv := by
        intro e
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl }
  let subsets : {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} ≃
      {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val} := by
    apply ofFinEmbEquiv.subtypeEquiv
    intro e
    change ((∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)) ↔
      root ∉ ofFinEmbEquiv e ∧ anchor ∉ ofFinEmbEquiv e
    simp only [mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range, not_exists]
  exact embedded.trans subsets

private theorem pairIndexEquiv_first {I : Type*} [LinearOrder I] (root anchor : I)
    (ij : RemainingPair root anchor) :
    ofFinEmbEquiv.symm ((pairIndexEquiv root anchor) ij).val 0 = ij.val.1 := by
  simp [pairIndexEquiv]
  rfl

private theorem pairIndexEquiv_second {I : Type*} [LinearOrder I] (root anchor : I)
    (ij : RemainingPair root anchor) :
    ofFinEmbEquiv.symm ((pairIndexEquiv root anchor) ij).val 1 = ij.val.2 := by
  simp [pairIndexEquiv]
  rfl

open Finset CircuitDifferenceBasis

/-- In the unit-weight case the root, total difference vector, and the other
point differences form an explicit integral basis. -/
private theorem unit_difference_basis {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor : I) (h : anchor ≠ root) :
    ∃ b : Module.Basis I ℤ (I → ℤ),
      b root = Pi.single root 1 ∧
      b anchor = ∑ i ∈ univ.erase root, (Pi.single i 1 - Pi.single root 1) ∧
      ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1 := by
  obtain ⟨c, hc0, hc, _⟩ := exists_difference_basis {anchor} root anchor
    (by simpa [eq_comm] using h) (by simp)
  have hc' (i : I) (hi : i ≠ root) : c i = Pi.single i 1 - Pi.single root 1 := by
    simpa using hc i hi
  let w := ∑ i ∈ univ.erase root, c i
  let u := w - c anchor
  have hker : c.coord anchor u = 0 := by
    dsimp [u, w]
    rw [map_sub, map_sum]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, h]
  let b := c.map (LinearEquiv.transvection hker)
  have hb (i : I) : b i = c i + c.coord anchor (c i) • u := by
    rw [Module.Basis.map_apply]
    rfl
  have hcoord (i : I) : c.coord anchor (c i) = if i = anchor then 1 else 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb, hcoord, ite_eq_right h.symm, zero_smul, add_zero, hc0]
  · rw [hb, hcoord, ite_eq_left rfl, one_smul]
    have hadd : c anchor + u = w := by dsimp [u]; abel
    rw [hadd]
    apply sum_congr rfl
    intro i hi
    exact hc' i (ne_of_mem_erase hi)
  · intro i hi ha
    rw [hb, hcoord, ite_eq_right ha, zero_smul, add_zero, hc' i hi]

/-- The active coordinates of each original point difference have a
unit contribution at that point and a negative contribution at the anchor. -/
private theorem active_difference_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor k x : I) (hne : anchor ≠ root) (hk : k ≠ root) (hka : k ≠ anchor)
    (b : Module.Basis I ℤ (I → ℤ))
    (ha : b anchor = ∑ i ∈ univ.erase root, (Pi.single i 1 - Pi.single root 1))
    (hb : ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1) :
    b.coord k (Pi.single x 1 - Pi.single root 1) =
      (if x = k then 1 else 0) - (if x = anchor then 1 else 0) := by
  have eval (i : I) : b.coord k (b i) = if i = k then 1 else 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have haMem : anchor ∈ univ.erase root := mem_erase.mpr ⟨hne, mem_univ _⟩
  by_cases hx : x = root
  · subst x
    simp [hk.symm, hne.symm]
  by_cases hxa : x = anchor
  · subst x
    have split :
        (∑ i ∈ (univ.erase root).erase anchor, b i) +
          (Pi.single anchor 1 - Pi.single root 1 : I → ℤ) = b anchor := by
      rw [ha, ← sum_erase_add _ _ haMem]
      congr 1
      apply sum_congr rfl
      intro i hi
      exact hb i (ne_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase hi)
    have hcast := congrArg (b.coord k) split
    simp only [map_add, map_sum, eval, hka.symm] at hcast
    have hsum : (∑ i ∈ (univ.erase root).erase anchor, if i = k then (1 : ℤ) else 0) = 1 := by
      simp [mem_erase, hka, hk]
    rw [hsum] at hcast
    simp [hka.symm, ← neg_eq_of_add_eq_zero_right hcast]
  · rw [← hb x hx hxa, eval, ite_eq_right hxa, sub_zero]

open Finset UniformCircuitResidueForms Set.powersetCard

/-- Expand an alternating form by the determinants of its input coordinates
in the integral basis. -/
private theorem form_eval_eq_sum_det {I M N : Type*} [Fintype I] [LinearOrder I]
    [AddCommGroup M] [AddCommGroup N] {k : ℕ} (b : Module.Basis I ℤ M)
    (f : M [⋀^Fin k]→ₗ[ℤ] N) (v : Fin k → M) :
    f v = ∑ s : Set.powersetCard I k,
      (Matrix.of fun i j => b.coord (ofFinEmbEquiv.symm s j) (v i)).det •
        (basisFormEquiv b).symm f s := by
  classical
  let extBasis := b.exteriorPower k
  let form := exteriorPower.alternatingMapLinearEquiv f
  let z := exteriorPower.ιMulti ℤ k v
  have hsum := congrArg form (extBasis.sum_repr z)
  rw [map_sum] at hsum
  simp only [map_smul] at hsum
  calc
    f v = form z := by exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).symm
    _ = ∑ s, extBasis.repr z s • form (extBasis s) := hsum.symm
    _ = _ := by
      apply sum_congr rfl
      intro s _
      rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
      congr 1

open UniformCircuitResidueForms

/-- A two-form vanishing at the two eliminated vectors reads each omitted
triangle through the corresponding row of the reduced matrix. -/
private theorem reduced_readout {I T N : Type*} [Fintype I] [LinearOrder I] [AddCommGroup N]
    (points : T → Fin 3 → I) (t : T) (ht : Function.Injective (points t))
    (root anchor : I) (hne : anchor ≠ root) [Fintype (RemainingPair root anchor)]
    (b : Module.Basis I ℤ (I → ℤ))
    (ha : b anchor = ∑ i ∈ Finset.univ.erase root, (Pi.single i 1 - Pi.single root 1))
    (hb : ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1)
    (f : (I → ℤ) [⋀^Fin 2]→ₗ[ℤ] N)
    (hfroot : f.curryLeft (b root) = 0) (hfanchor : f.curryLeft (b anchor) = 0) :
    let dif (i : I) := Pi.single i (1 : ℤ) - Pi.single root 1
    let term (p : RemainingPair root anchor) := (basisFormEquiv b).symm f ((pairIndexEquiv root anchor) p).val
    f ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] =
      ∑ ij, (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij • term ij := by
  classical
  intro dif term
  let vv : Fin 2 → I → ℤ :=
    ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)]
  let C (s : Set.powersetCard I 2) :=
    (Matrix.of fun i j => b.coord (ofFinEmbEquiv.symm s j) (vv i)).det • (basisFormEquiv b).symm f s
  let admissible (s : Set.powersetCard I 2) := root ∉ s.val ∧ anchor ∉ s.val
  have coord_zero (i : I) (hz : f.curryLeft (b i) = 0)
      (s : Set.powersetCard I 2) (hs : i ∈ s.val) : (basisFormEquiv b).symm f s = 0 := by
    have hh := ((curryLeft_smul_basis_eq_zero_iff b f (1 : ℤ) i).mp
      (by simpa only [one_smul] using hz)) s hs
    simpa only [one_smul] using hh
  have excluded : (∑ s : {s // ¬ admissible s}, C s.val) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    have hs : root ∈ s.val.val ∨ anchor ∈ s.val.val := by
      by_cases hr : root ∈ s.val.val
      · exact Or.inl hr
      · exact Or.inr (Classical.not_not.mp fun h => s.prop ⟨hr, h⟩)
    rcases hs with h | h
    · dsimp [C]
      rw [coord_zero _ hfroot _ h, smul_zero]
    · dsimp [C]
      rw [coord_zero _ hfanchor _ h, smul_zero]
  change f vv = _
  rw [form_eval_eq_sum_det b f vv]
  change (∑ s, C s) = _
  rw [← Fintype.sum_subtype_add_sum_subtype admissible C, excluded, add_zero]
  symm
  refine Fintype.sum_equiv (pairIndexEquiv root anchor) _ _ ?_
  intro ij
  change _ • term ij = C ((pairIndexEquiv root anchor) ij).val
  have markerCoord (k x : I) (hk : k ≠ root) (hka : k ≠ anchor) :
      b.coord k (dif x) = (marker k x : ℤ) - marker anchor x := by
    dsimp [dif, marker]
    rw [active_difference_coordinate root anchor k x hne hk hka b ha hb]
    by_cases hx : x = k
    · subst x
      simp [hka, hka.symm]
    by_cases hxa : x = anchor
    · subst x
      simp [hka, hka.symm]
    simp [hx, hxa, Ne.symm (show x ≠ k from hx), Ne.symm (show x ≠ anchor from hxa)]
  have coord1 (x : I) : b.coord ij.val.1 (dif x) =
      (marker ij.val.1 x : ℤ) - marker anchor x :=
    markerCoord _ _ ij.prop.2.1 ij.prop.2.2.2.1
  have coord2 (x : I) : b.coord ij.val.2 (dif x) =
      (marker ij.val.2 x : ℤ) - marker anchor x :=
    markerCoord _ _ ij.prop.2.2.1 ij.prop.2.2.2.2
  congr 1
  rw [reducedMatrix_eq_determinant points root anchor t ht ij]
  simp only [Matrix.det_fin_two, Matrix.of_apply, pairIndexEquiv_first,
    pairIndexEquiv_second, vv, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, coord1, coord2]

open UniformCircuitResidueDiagonal

private noncomputable def activeCoordinates {I N : Type*} [LinearOrder I] [AddCommGroup N]
    (root anchor : I) (n : ℤ) :
    diagonalCoordinates N 2 root anchor n 1 ≃ₗ[ℤ]
      (RemainingPair root anchor → ↥(Submodule.torsionBy ℤ N n)) := by
  let P := Submodule.torsionBy ℤ N n
  let Q := P ⊓ Submodule.torsionBy ℤ N 1
  haveI : Subsingleton ↥Q := ⟨fun x y => Subtype.ext (by
    have hx : (1 : ℤ) • x.val = 0 := x.prop.2
    have hy : (1 : ℤ) • y.val = 0 := y.prop.2
    simpa only [one_smul] using hx.trans hy.symm)⟩
  let A := {F : Set.powersetCard I 2 // root ∉ F ∧ anchor ∈ F}
  letI : Unique (A → Q) := ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  exact ((diagonalCoordinatesEquiv (N := N) (r := 2) root anchor n 1).trans
    LinearEquiv.uniqueProd).trans
      (LinearEquiv.piCongrLeft' ℤ (fun _ => ↥P) (pairIndexEquiv root anchor).symm)

private theorem activeCoordinates_apply {I N : Type*} [LinearOrder I] [AddCommGroup N]
    (root anchor : I) (n : ℤ) (x : diagonalCoordinates N 2 root anchor n 1)
    (ij : RemainingPair root anchor) :
    ((activeCoordinates (N := N) root anchor n x ij) : N) = x.val ((pairIndexEquiv root anchor) ij).val := rfl

noncomputable instance instRemainingPairFintype {I : Type*} [Fintype I] [LinearOrder I]
    (root anchor : I) : Fintype (RemainingPair root anchor) := by
  classical
  let e := pairIndexEquiv root anchor
  exact Fintype.ofEquiv _ e.symm

private theorem unit_total_vector {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor : I) (b : Module.Basis I ℤ (I → ℤ))
    (hr : b root = Pi.single root 1)
    (ha : b anchor = ∑ i ∈ Finset.univ.erase root, (Pi.single i 1 - Pi.single root 1)) :
    (∑ i, Pi.single i (1 : ℤ)) = (Fintype.card I : ℤ) • b root + b anchor := by
  rw [hr, ha, Finset.sum_sub_distrib, Finset.sum_const]
  have hn : ((Finset.univ.erase root : Finset I).card : ℤ) + 1 = Fintype.card I := by
    exact_mod_cast (by rw [Finset.card_erase_add_one (Finset.mem_univ root), Finset.card_univ] :
      (Finset.univ.erase root : Finset I).card + 1 = Fintype.card I)
  rw [← hn, add_zsmul, one_zsmul, Nat.cast_smul_eq_nsmul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)]
  abel



open Function Matrix
open scoped Matroid
open SparsePavingCircuitCoordinates ParallelCircuitObstruction UniformCircuitBasis
open RationalJointCircuitImage (RationalResidue)
open RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod gcd_torsion_iff)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

/-- The integral joint lifting obstruction for a rank-three sparse-paving matroid
with singleton parallel classes is the kernel of its reduced omitted-triangle matrix. -/
theorem rank_three_lifting_obstruction_equiv_kernel {I T : Type*}
    [Fintype I] [LinearOrder I] (M : Matroid I) (triangles : T → Fin 3 ↪o I)
    (root anchor : I) (hne : anchor ≠ root) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val) :
    Nonempty ((JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))) ≃ₗ[ℤ]
      ((reducedMatrix (fun t => triangles t) root anchor :
        Matrix T (RemainingPair root anchor) (ZMod (Fintype.card I))).mulVecLin.ker.restrictScalars ℤ)) := by
  classical
  let n := Fintype.card I
  have hn0 : n ≠ 0 := by omega
  let _ : Nonempty I := ⟨root⟩
  let points (t : T) : Fin 3 → I := triangles t
  let holes : Set (Finset I) := Set.range fun t => (ofFinEmbEquiv (triangles t)).val
  have hsize (H : Finset I) (hH : H ∈ holes) : H.card = 3 := by
    obtain ⟨t, rfl⟩ := hH
    exact (ofFinEmbEquiv (triangles t)).prop
  have hnonloop (i : I) : M.IsNonloop i := by
    apply Matroid.indep_singleton.mp
    rw [← coe_singleton, indep_iff_card_and_allowed (holes := holes) hn hsize hsparse hbase]
    refine ⟨by simp, fun h => ?_⟩
    have := hsize _ h
    simp at this
  have hground : M.E = Set.univ := Set.eq_univ_of_forall fun i => (hnonloop i).mem_ground
  obtain ⟨comparison, _⟩ := parallel_lifting_obstruction (M := M) Function.surjective_id
    (fun {_ _} h => h) hnonloop
  let standard := Pi.basisFun ℤ I
  let a := sumCovector I
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun]
  let idx (H : holes) : T := H.prop.choose
  have hidx (H : holes) : (ofFinEmbEquiv (triangles (idx H))).val = H.val := H.prop.choose_spec
  let rep (H : holes) : I := triangles (idx H) 0
  have hrep (H : holes) : rep H ∈ H.val := by
    rw [← hidx H]
    exact (mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨0, rfl⟩
  obtain ⟨pivot⟩ := sparse_paving_pivot_forms_equiv (id : I → I) (d := 1) hn
    hsize hsparse hground hbase standard a ha root rep hrep
  let y := ∑ i, (univ.filter fun x : I => id x = i).card • standard i
  have hstd (i : I) : standard i = Pi.single i 1 := Pi.basisFun_apply ℤ I i
  have hy : y = ∑ i, standard i := by
    simp only [y, id_eq, filter_eq', mem_univ, ite_true, card_singleton, one_nsmul]
  have hay : a y = n := by
    rw [hy, map_sum]
    simp [ha, n]
  obtain ⟨b, hbroot, hbanchor, hb⟩ := unit_difference_basis root anchor hne
  have hy' : y = (n : ℤ) • b root + b anchor :=
    hy.trans ((Finset.sum_congr rfl fun i _ => hstd i).trans
      (unit_total_vector root anchor b hbroot hbanchor))
  let F := (I → ℤ) [⋀^Fin 2]→ₗ[ℤ] RationalResidue
  let P := ((insertVector (N := RationalResidue) (n := 1) (standard root)).ker ⊓
    (insertVector y).ker) ⊓ Submodule.torsionBy ℤ F (a y)
  let tuple (H : holes) (i : Fin 2) :=
    let S : Set.powersetCard I 2 := ⟨H.val.erase (rep H), by
      change (H.val.erase (rep H)).card = 2
      rw [card_erase_of_mem (hrep H), hsize H.val H.prop]⟩
    standard (ofFinEmbEquiv.symm S i) - standard (rep H)
  let eval (H : holes) : F →ₗ[ℤ] RationalResidue :=
    { toFun := fun f => f (tuple H)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change weightedCircuitResidues M (id : I → I) ≃ₗ[ℤ] ↥(P ⊓ ⨅ H, (eval H).ker) at pivot
  let D := diagonalCoordinates RationalResidue 2 root anchor n 1
  have diag (f : F) : f ∈ P ↔ (basisFormEquiv b).symm f ∈ D := by
    change (f.curryLeft (standard root) = 0 ∧ f.curryLeft y = 0) ∧ a y • f = 0 ↔ _
    rw [hay]
    have hr : standard root = b root := (hstd root).trans hbroot.symm
    rw [hr, hy']
    simpa only [one_smul, and_assoc] using (reduced_equations b root anchor n 1 f)
  let diagonal : P ≃ₗ[ℤ] D := (basisFormEquiv b).symm.ofSubmodules P D (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext g
    change (basisFormEquiv b) g ∈ P ↔ g ∈ D
    rw [diag, LinearEquiv.symm_apply_apply])
  obtain ⟨zmod⟩ := residueTorsion_equiv_zmod n hn0
  let coord := (diagonal.trans (activeCoordinates root anchor n)).trans
    (LinearEquiv.piCongrRight fun _ : RemainingPair root anchor => zmod)
  let A : Matrix T (RemainingPair root anchor) (ZMod n) := reducedMatrix points root anchor
  let K := A.mulVecLin.ker.restrictScalars ℤ
  let dif (i : I) : I → ℤ := Pi.single i 1 - Pi.single root 1
  have read (f : P) (t : T) :
      A.mulVec (coord f) t = 0 ↔
        f.val ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] = 0 := by
    have hr : f.val.curryLeft (b root) = 0 := by
      rw [hbroot, ← hstd]
      exact f.prop.1.1
    have hyzero : f.val.curryLeft y = 0 := f.prop.1.2
    have hfanchor : f.val.curryLeft (b anchor) = 0 := by
      rwa [hy', map_add, map_smul, hr, smul_zero, zero_add] at hyzero
    let v := activeCoordinates (N := RationalResidue) root anchor (n : ℤ) (diagonal f)
    let w : ResidueTorsion n := ∑ ij,
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij • v ij
    have hz : A.mulVec (coord f) t = zmod w := by
      change (∑ ij, A t ij * zmod (v ij)) = zmod w
      simp only [w, map_sum, map_zsmul, zsmul_eq_mul, reducedMatrix_intCast, A]
    have hw : (w : RationalResidue) =
        f.val ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] := by
      rw [reduced_readout points t (triangles t).injective root anchor hne b hbanchor hb f.val hr hfanchor]
      change ((ResidueTorsion n).subtype w) = _
      simp only [w, map_sum, map_zsmul, v, activeCoordinates_apply]
      rfl
    rw [hz, ← hw, ← zmod.map_zero, zmod.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext (by exact h)⟩
  have tuple_eq (t : T) (H : holes) (hH : (ofFinEmbEquiv (triangles t)).val = H.val)
      (he : triangles t = triangles (idx H)) :
      tuple H = ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] := by
    let E := (Fin.succAboveOrderEmb (0 : Fin 3)).trans (triangles t)
    have hr : triangles t 0 = rep H := congrArg (fun e : Fin 3 ↪o I => e 0) he
    have herm : (ofFinEmbEquiv E).val = H.val.erase (rep H) := by
      rw [face_embedding_erase, hH, hr]
    have hS : ofFinEmbEquiv E = ⟨H.val.erase (rep H), by
        change (H.val.erase (rep H)).card = 2
        rw [card_erase_of_mem (hrep H), hsize H.val H.prop]⟩ := Subtype.ext herm
    funext i
    dsimp only [tuple]
    rw [← hS, Equiv.symm_apply_apply, ← hr]
    simp only [hstd]
    fin_cases i <;> simp [E, dif, points] <;> abel
  have hcoord (f : P) : f.val ∈ (⨅ H, (eval H).ker) ↔ coord f ∈ K := by
    simp only [K, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    change (∀ H, f.val (tuple H) = 0) ↔ A.mulVec (coord f) = 0
    rw [funext_iff]
    constructor
    · intro h t
      let H : holes := ⟨_, ⟨t, rfl⟩⟩
      have he : triangles t = triangles (idx H) :=
        ofFinEmbEquiv.injective (Subtype.ext (hidx H).symm)
      exact (read f t).mpr (tuple_eq t H rfl he ▸ h H)
    · intro h H
      rw [tuple_eq (idx H) H (hidx H) rfl]
      exact (read f (idx H)).mp (h _)
  let P' := (⨅ H, (eval H).ker).comap P.subtype
  let restrict : ↥(P ⊓ ⨅ H, (eval H).ker) ≃ₗ[ℤ] P' :=
    { toFun := fun f => ⟨⟨f.val, f.prop.1⟩, f.prop.2⟩
      invFun := fun f => ⟨f.val.val, ⟨f.val.prop, f.prop⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let finish := coord.ofSubmodules P' K (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext z
    change (coord.symm z).val ∈ (⨅ H, (eval H).ker) ↔ _
    rw [hcoord, LinearEquiv.apply_symm_apply])
  exact ⟨comparison.trans (pivot.trans (restrict.trans finish))⟩


end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

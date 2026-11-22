/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The cyclic factors of the joint lifting obstruction for a uniform core. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitBasis
public import D5.S3.Combinatorics.Matroids.UniformCircuitCoordinateCount
public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueDiagonal
public import D5.S3.Combinatorics.Matroids.UniformMatroidCircuitCoordinates
public import Mathlib.Data.Fintype.EquivFin

/-! The explicit lifting obstruction of a uniform-core parallel expansion. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitInvariantFactors

open Finset
open scoped Matroid
open RankTwoCircuitInvariantFactors UniformCircuitBasis UniformCircuitCoordinateCount
open UniformCircuitResidueForms UniformCircuitResidueDiagonal UniformMatroidCircuitCoordinates
open ParallelCircuitObstruction
open RationalJointCircuitImage (RationalResidue)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

set_option autoImplicit false

/-- An expansion of a rank-`r+2` uniform matroid on `k+2` classes has
`k.choose r` factors of order the gcd of the class sizes and `k.choose (r+1)`
factors of order the ground size. -/
theorem uniform_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k r : ℕ} (hrk : r ≤ k) {S : Matroid (Fin (k + 2))}
    (hground : S.E = Set.univ)
    (hbases : ∀ B : Finset (Fin (k + 2)), S.IsBase (B : Set (Fin (k + 2))) ↔ B.card = r + 2)
    (p : V → Fin (k + 2)) (hsurj : Function.Surjective p)
    (horder : ∀ ⦃u v⦄, p u < p v → u < v) :
    Nonempty ((JointSaturatedImage (S.comap p) ⧸ JointImageInSaturation (S.comap p)) ≃ₗ[ℤ]
      ((Fin (k.choose r) → ZMod (univ.gcd (classSize p))) ×
        (Fin (k.choose (r + 1)) → ZMod (Fintype.card V)))) := by
  classical
  let I := Fin (k + 2)
  let w := classSize p
  let n := Fintype.card V
  let d := univ.gcd (fun i : Fin (k + 1) => w i.succ)
  let g := univ.gcd w
  have hcard : n = ∑ i, w i := by
    simpa only [w, classSize, card_univ] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset I))
        (f := p) (fun _ _ => mem_univ _))
  have hgcd : n.gcd d = g := gcd_card_tail_eq p
  have hw (i : I) : 0 < w i := by
    obtain ⟨x, hx⟩ := hsurj i
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
  have hn : 0 < n := by
    let _ : Nonempty V := ⟨(hsurj 0).choose⟩
    exact Fintype.card_pos
  have hg : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro h
    have hdvd : g ∣ w (0 : I) := gcd_dvd (mem_univ (0 : I))
    rw [h, zero_dvd_iff] at hdvd
    exact (hw 0).ne' hdvd
  have hr : r + 2 ≤ Fintype.card I := by simpa [I] using hrk
  have hnon (v : V) : S.IsNonloop (p v) := by
    apply Matroid.indep_singleton.mp
    simpa only [coe_singleton] using
      (indep_iff_card_le hbases hr ({p v} : Finset I)).mpr (by simp)
  let _ : Nonempty V := ⟨(hsurj 0).choose⟩
  obtain ⟨obstruction, _⟩ := parallel_lifting_obstruction hsurj horder hnon
  let standard := Pi.basisFun ℤ I
  let a := sumCovector I
  let y : I → ℤ := fun i => w i
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun]
  have hy : (∑ i, (univ.filter (fun x => p x = i)).card • standard i) = y := by
    funext j
    simp [standard, Pi.basisFun, y, w, classSize, Pi.single_apply, nsmul_eq_mul, mul_ite]
  let forms := uniformWeightedFormsEquiv p hbases hground hr standard a ha
  obtain ⟨b, hb0, hby⟩ := exists_adapted_weight_basis k w hw
  have hsum : a y = ((∑ i : Fin (k + 2), w i : ℕ) : ℤ) := by
    change (∑ i : Fin (k + 2), (w i : ℤ)) = _
    exact (Nat.cast_sum ..).symm
  have hy' : y = a y • b 0 + (d : ℤ) • b (Fin.succ 0) := by
    rw [hsum]
    exact hby
  let diag := diagonalFormEquiv (N := RationalResidue) (r := r) b a 0 (Fin.succ 0) d y hb0 hy'
  have hay : a y = (n : ℤ) := hsum.trans (congrArg (fun m : ℕ => (m : ℤ)) hcard.symm)
  let A := {F : Set.powersetCard I (r + 1) // (0 : I) ∉ F ∧ (1 : I) ∈ F}
  let B := {F : Set.powersetCard I (r + 1) // (0 : I) ∉ F ∧ (1 : I) ∉ F}
  have hA : Fintype.card A = k.choose r := by
    rw [← Nat.card_eq_fintype_card]
    simpa [A, I] using card_include_nonpivot (0 : I) 1 Fin.zero_ne_one r
  have hB : Fintype.card B = k.choose (r + 1) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [B, I] using card_avoid_both (0 : I) 1 Fin.zero_ne_one (r + 1)
  have ht : ResidueTorsion n ⊓ ResidueTorsion d = ResidueTorsion g := by
    ext x
    change ((n : ℤ) • x = 0 ∧ (d : ℤ) • x = 0) ↔ (g : ℤ) • x = 0
    rw [← hgcd, gcd_torsion_iff]
  obtain ⟨eG⟩ := residueTorsion_equiv_zmod g hg.ne'
  obtain ⟨eN⟩ := residueTorsion_equiv_zmod n hn.ne'
  let eT : ↥(ResidueTorsion n ⊓ ResidueTorsion d) ≃ₗ[ℤ] ZMod g :=
    (LinearEquiv.ofEq _ _ ht).trans eG
  let eA := (LinearEquiv.piCongrRight fun _ : A => eT).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : A => ZMod g) (Fintype.equivFinOfCardEq hA))
  let eB := (LinearEquiv.piCongrRight fun _ : B => eN).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : B => ZMod n) (Fintype.equivFinOfCardEq hB))
  have hf :
      weightedCircuitResidues S p ≃ₗ[ℤ]
        ↥((covectorWedgeLinear (N := RationalResidue) (n := r + 2) a).ker ⊓
          (insertVector y).ker) := by
    rw [← hy]
    exact forms.symm
  have hd :
      diagonalCoordinates RationalResidue (r + 1) (0 : I) 1 (a y) d ≃ₗ[ℤ]
        (A → ↥(ResidueTorsion n ⊓ ResidueTorsion d)) × (B → ResidueTorsion n) := by
    rw [hay]
    exact diagonalCoordinatesEquiv (0 : I) 1 (n : ℤ) d
  exact ⟨obstruction.trans (hf.trans (diag.trans (hd.trans (eA.prodCongr eB))))⟩

end D5.S3.Combinatorics.Matroids.UniformCircuitInvariantFactors

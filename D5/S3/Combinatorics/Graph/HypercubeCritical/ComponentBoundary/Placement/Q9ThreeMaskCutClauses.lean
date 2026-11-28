import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay

/-! Companion, translation, and forbidden-square clauses for a three-mask cut
in the normalized even slice.

With an exact family hypothesis `minimumDisplacements C D false 2 = recipe.family`,
unfold `cutMasks` and rewrite by that hypothesis to reduce `hcut` to a cut of the recipe.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutClauses

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9ContactMaskCut (cutMasks three_mask_cut_preserves_contact_fibre)
open Q9IsotropicHuang (parity)
open Q9SharedContactCNF (Axis Word Variable pos neg)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9WeightedSaturation (defect signedBiadjacency)
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF
open private valuation occupied_value from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskSixAxisReplay
open private cutMasks_swap translate parity_translate translate_involution
  other_contact_of_three_mask_cut no_alternating_square_of_small_cut from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut

private abbrev occ := Variable.occupied

private def translateWord (w : Word) (p : Axis × Axis) : Word :=
  adjacentWord (adjacentWord w p.1) p.2

private theorem translateWord_spec (w : Word) (p : Axis × Axis) :
    cubeBitVec 9 (translateWord w p) = translate p (cubeBitVec 9 w) := by
  simp only [translateWord, adjacentWord_spec, translate]

open Classical in
/-- The contact from `x` through `p` forces a companion in `D` through `q` or `r`. -/
theorem companionRightClause {recipe : Recipe} {C D : Finset (Q 9)} {A : Finset Axis}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hregular : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced D) (x : Word) (p q r : Axis × Axis)
    (hx : parity (cubeBitVec 9 x) = false)
    (hp : p ∈ A.product (Finset.univ \ A)) (hq : q ∈ A.product (Finset.univ \ A))
    (hr : r ∈ A.product (Finset.univ \ A))
    (hcut : cutMasks C D false A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}}) :
    let y := translateWord x p
    (valuation recipe C D).satisfies
      [neg (occ false x), neg (occ true y),
        pos (occ true (translateWord x q)), pos (occ true (translateWord x r))] := by
  intro y hxC hyD hnq hnr
  have hxC' : cubeBitVec 9 x ∈ C := (occupied_value recipe C D false x).mp hxC
  have hyD' : cubeBitVec 9 y ∈ D := (occupied_value recipe C D true y).mp hyD
  have hpD : translate p (cubeBitVec 9 x) ∈ D := by
    simpa only [y, translateWord_spec] using hyD'
  rcases other_contact_of_three_mask_cut (A := A) (p := p) (q := q) (r := r)
    hsep hregular hbalanced hxC' hx hp hq hr hcut hpD with hqD | hrD
  · apply hnq
    apply (occupied_value recipe C D true (translateWord x q)).mpr
    change cubeBitVec 9 (translateWord x q) ∈ D
    rwa [translateWord_spec]
  · apply hnr
    apply (occupied_value recipe C D true (translateWord x r)).mpr
    change cubeBitVec 9 (translateWord x r) ∈ D
    rwa [translateWord_spec]

open Classical in
/-- The endpoint `x` translated through `p` has a companion in `C` through `q` or `r`. -/
theorem companionLeftClause {recipe : Recipe} {C D : Finset (Q 9)} {A : Finset Axis}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hregular : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbalanced : IsBalanced C) (x : Word) (p q r : Axis × Axis)
    (hx : parity (cubeBitVec 9 x) = false)
    (hp : p ∈ A.product (Finset.univ \ A)) (hq : q ∈ A.product (Finset.univ \ A))
    (hr : r ∈ A.product (Finset.univ \ A))
    (hcut : cutMasks C D false A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}}) :
    let y := translateWord x p
    (valuation recipe C D).satisfies
      [neg (occ false x), neg (occ true y),
        pos (occ false (translateWord y q)), pos (occ false (translateWord y r))] := by
  intro y hxC hyD hnq hnr
  have hxC' : cubeBitVec 9 x ∈ C := (occupied_value recipe C D false x).mp hxC
  have hyD' : cubeBitVec 9 y ∈ D := (occupied_value recipe C D true y).mp hyD
  have hy : cubeBitVec 9 y = translate p (cubeBitVec 9 x) := translateWord_spec x p
  have hyb : parity (cubeBitVec 9 y) = false := by
    rw [hy, parity_translate]
    exact hx
  have hpC : translate p (cubeBitVec 9 y) ∈ C := by
    rw [hy, translate_involution]
    exact hxC'
  have hsep' (v : Q 9) (hv : v ∈ D) (u : Q 9) (hu : u ∈ C) :
      2 ≤ hammingDist v u := by
    rw [hammingDist_comm v u]
    exact hsep u hu v hv
  have hcut' : cutMasks D C false A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}} :=
    (cutMasks_swap D C false A).trans hcut
  rcases other_contact_of_three_mask_cut (A := A) (p := p) (q := q) (r := r)
    hsep' hregular hbalanced hyD' hyb hp hq hr hcut' hpC with hqC | hrC
  · apply hnq
    apply (occupied_value recipe C D false (translateWord y q)).mpr
    change cubeBitVec 9 (translateWord y q) ∈ C
    rwa [translateWord_spec]
  · apply hnr
    apply (occupied_value recipe C D false (translateWord y r)).mpr
    change cubeBitVec 9 (translateWord y r) ∈ C
    rwa [translateWord_spec]

open Classical in
/-- The product of the two companion translations preserves both endpoints of the contact. -/
theorem translationClause {recipe : Recipe} {C D : Finset (Q 9)} {A : Finset Axis}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (s : Bool) (x : Word) (p q r : Axis × Axis)
    (hx : parity (cubeBitVec 9 x) = false)
    (hp : p.1 ∈ A ∧ p.2 ∉ A) (hq : q.1 ∈ A ∧ q.2 ∉ A)
    (hr : r.1 ∈ A ∧ r.2 ∉ A) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D false A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}}) :
    let y := translateWord x p
    let z := translateWord (translateWord x r) q
    (valuation recipe C D).satisfies
      [neg (occ false x), neg (occ true y), pos (occ s (if s then translateWord z p else z))] := by
  intro y z hxC hyD hn
  have hxC' : cubeBitVec 9 x ∈ C := (occupied_value recipe C D false x).mp hxC
  have hyD' : cubeBitVec 9 y ∈ D := (occupied_value recipe C D true y).mp hyD
  have hpD : translate p (cubeBitVec 9 x) ∈ D := by
    simpa only [y, translateWord_spec] using hyD'
  have hshift := three_mask_cut_preserves_contact_fibre A p q r hp hq hr hpq hpr hqr
    hcut hsep hrC hrD hcD hbC hbD hdetD hxC' hx hpD
  apply hn
  cases s
  · apply (occupied_value recipe C D false z).mpr
    change cubeBitVec 9 z ∈ C
    simpa only [z, translateWord_spec, translate] using hshift.1
  · apply (occupied_value recipe C D true (translateWord z p)).mpr
    change cubeBitVec 9 (translateWord z p) ∈ D
    simpa only [z, translateWord_spec, translate] using hshift.2.2

open Classical in
/-- For a cut with at most three masks, the second crossing mask cannot complete
an alternating square through the contact given by the first mask. -/
theorem forbiddenSquareClause {recipe : Recipe} {C D : Finset (Q 9)} {A : Finset Axis}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (x : Word) (p q r : Axis × Axis)
    (hx : parity (cubeBitVec 9 x) = false)
    (hp : p ∈ A.product (Finset.univ \ A)) (hq : q ∈ A.product (Finset.univ \ A))
    (hpq : p ≠ q)
    (hcut : cutMasks C D false A = {{p.1, p.2}, {q.1, q.2}, {r.1, r.2}}) :
    let y := translateWord x p
    (valuation recipe C D).satisfies
      [neg (occ false x), neg (occ true y),
        neg (occ false (translateWord y q)), neg (occ true (translateWord x q))] := by
  intro y hxC hyD hyqC hxqD
  have hxC' : cubeBitVec 9 x ∈ C := (occupied_value recipe C D false x).mp hxC
  have hyD' : cubeBitVec 9 y ∈ D := (occupied_value recipe C D true y).mp hyD
  have hyqC' : cubeBitVec 9 (translateWord y q) ∈ C :=
    (occupied_value recipe C D false (translateWord y q)).mp hyqC
  have hxqD' : cubeBitVec 9 (translateWord x q) ∈ D :=
    (occupied_value recipe C D true (translateWord x q)).mp hxqD
  have hcard : (cutMasks C D false A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  exact no_alternating_square_of_small_cut (A := A) (p := p) (q := q)
    hsep hrD hcD hbD hdetD hxC' hx hcard hp hq hpq
    (by simpa only [y, translateWord_spec] using hyD')
    (by simpa only [translateWord_spec] using hxqD')
    (by simpa only [y, translateWord_spec] using hyqC')

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutClauses

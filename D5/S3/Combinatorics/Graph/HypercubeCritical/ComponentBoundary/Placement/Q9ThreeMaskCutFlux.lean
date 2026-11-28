import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutSign

/-! The signed contact flux is negated by the three-mask cut translation. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeMaskCutFlux

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedSaturation (defect signedBiadjacency)
open Placement.Q9ContactMaskCut (cutMasks)
open private mask translate cutMasks_swap parity_translate
  two_contact_row cutTerm other_contact_of_three_mask_cut no_alternating_square_of_small_cut
  abs_cutTerm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut
open private direction direction_apply from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

open Q9ThreeMaskCutSign (CrossingPair)
open Q9ThreeMaskCutSign.CrossingPair (operator operator_square)
open private step step_involution step_comm coefficient operator_eval crossing_pair_mem from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ThreeMaskCutSign

/-- The signed edge term with both endpoint amplitudes included. -/
def flux {A : Set (Fin 9)} (f g : Q 9 → ℝ) (p : CrossingPair A) (x : Q 9) : ℝ :=
  f x * operator p g x

private theorem coefficient_reverse {A : Set (Fin 9)} (p : CrossingPair A) (x : Q 9) :
    coefficient p (step p x) = -coefficient p x := by
  have hs : coefficient p x * coefficient p (step p x) = -1 := by
    have h := congrArg (fun L : Module.End ℝ (Q 9 → ℝ) => L (fun _ => 1) x)
      (operator_square (R := ℝ) p)
    simpa only [Module.End.mul_apply, operator_eval, step_involution, mul_one,
      LinearMap.neg_apply, Module.End.one_apply, Pi.neg_apply] using h
  have ha : |coefficient p x| = 1 := by
    have h := abs_cutTerm (w := fun _ => 1) (fun _ => zero_lt_one)
      (fun _ => 1) x p.val
    simpa only [cutTerm, one_mul, mul_one, abs_one, coefficient] using h
  have hsq : coefficient p x * coefficient p x = 1 := by
    rw [← pow_two, ← sq_abs, ha, one_pow]
  calc
    _ = (coefficient p x * coefficient p x) * coefficient p (step p x) := by
      rw [hsq, one_mul]
    _ = -coefficient p x := by rw [mul_assoc, hs]; ring

private theorem flux_reverse {A : Set (Fin 9)} (f g : Q 9 → ℝ)
    (p : CrossingPair A) (x : Q 9) : flux g f p (step p x) = -flux f g p x := by
  simp only [flux, operator_eval, step_involution, coefficient_reverse]
  ring

private theorem flux_neg_of_row {A : Set (Fin 9)} (f g : Q 9 → ℝ)
    (p q : CrossingPair A) (x : Q 9)
    (h : operator (R := ℝ) p g x + operator (R := ℝ) q g x = 0) :
    flux f g p x = -flux f g q x := by
  have h' := congrArg (f x * ·) h
  simp only [mul_add, mul_zero] at h'
  exact eq_neg_of_add_eq_zero_left h'

open Classical in
private theorem flux_of_companion
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    {p q r : CrossingPair (A : Set (Fin 9))} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A = {mask p.val, mask q.val, mask r.val})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    {f g : Q 9 → ℝ}
    (hfout : ∀ v ∉ C, f v = 0)
    (hgout : ∀ v ∉ D, g v = 0)
    (hAf : ∀ v ∉ C, weightedLinear (fun _ => 1) f v = 0)
    (hAg : ∀ v ∉ D, weightedLinear (fun _ => 1) g v = 0)
    {x : Q 9} (hx : x ∈ C) (hxb : parity x = b)
    (hpx : step p x ∈ D) (hqx : step q x ∈ D) :
    flux f g p (step q (step r x)) = -flux f g p x := by
  have hp := crossing_pair_mem p
  have hq := crossing_pair_mem q
  have hr := crossing_pair_mem r
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  have hpr' : p.val ≠ r.val := fun h => hpr (Subtype.ext h)
  have hqr' : q.val ≠ r.val := fun h => hqr (Subtype.ext h)
  have hcard : (cutMasks C D b A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  have hsep' (u : Q 9) (hu : u ∈ D) (v : Q 9) (hv : v ∈ C) :
      2 ≤ hammingDist u v := by
    rw [hammingDist_comm]
    exact hsep v hv u hu
  have hswap : cutMasks D C b A = {mask p.val, mask q.val, mask r.val} :=
    (cutMasks_swap D C b A).trans hcut
  let y := step p x
  let z := step r y
  have hyb : parity y = b := (parity_translate p.val _).trans hxb
  have hyp : step p y ∈ C := step_involution p x ▸ hx
  have hz : z ∈ C :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep' hrC hbC hpx hyb hp hq hr hswap hyp)
      (no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD hx hxb hcard hp hq hpq' hpx hqx)
  have hzb : parity z = b := (parity_translate r.val _).trans hyb
  have hzr : step r z ∈ D := step_involution r y ▸ hpx
  have hzp : step p z ∉ D := by
    intro h
    have hback : step p (step r z) ∈ C := by
      change step p (step r (step r y)) ∈ C
      rw [step_involution]
      exact hyp
    exact no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD
      hz hzb hcard hr hp hpr'.symm hzr h hback
  have hcutR : cutMasks C D b A = {mask r.val, mask p.val, mask q.val} := by
    rw [hcut]
    ext s
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hzq : step q z ∈ D :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep hrD hbD hz hzb hr hp hq hcutR hzr) hzp

  let v := step q z
  let t := step p v
  have hvb : parity v = b := (parity_translate q.val _).trans hzb
  have hvq : step q v ∈ C := step_involution q z ▸ hz
  have hcutQ : cutMasks D C b A = {mask q.val, mask p.val, mask r.val} := by
    rw [hswap, Finset.insert_comm (mask p.val)]
  have hvp : t ∈ C :=
    Or.resolve_right (other_contact_of_three_mask_cut hsep' hrC hbC hzq hvb hq hp hr hcutQ hvq)
      (no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD hz hzb hcard
        hq hr hqr' hzq hzr)
  have htEq : t = step q (step r x) := by
    change step p (step q (step r (step p x))) = _
    rw [step_comm p q, step_comm p r, step_involution]
  have hcard' : (cutMasks D C b A).card ≤ 3 := hswap.symm ▸ Finset.card_le_three
  have rowY : operator (R := ℝ) p f y + operator (R := ℝ) r f y = 0 := by
    simpa only [operator, cutTerm, translate, Module.End.mul_apply, direction_apply, one_mul] using
      two_contact_row hsep' hrC hbC hpx hyb hcard' hfout hAf hp hr hpr' hyp hz
  have rowZ : operator (R := ℝ) r g z + operator (R := ℝ) q g z = 0 := by
    simpa only [operator, cutTerm, translate, Module.End.mul_apply, direction_apply, one_mul] using
      two_contact_row hsep hrD hbD hz hzb hcard hgout hAg hr hq hqr'.symm hzr hzq
  have rowV : operator (R := ℝ) q f v + operator (R := ℝ) p f v = 0 := by
    simpa only [operator, cutTerm, translate, Module.End.mul_apply, direction_apply, one_mul] using
      two_contact_row hsep' hrC hbC hzq hvb hcard' hfout hAf hq hp hpq'.symm hvq hvp
  have h₁ := flux_neg_of_row g f p r y rowY
  change flux g f p (step p x) = -flux g f r y at h₁
  rw [flux_reverse f g p x] at h₁
  have h₁' := flux_reverse f g r z
  rw [show step r z = y from step_involution r y] at h₁'
  have h₂ := flux_neg_of_row f g r q z rowZ
  have h₃ := flux_neg_of_row g f q p v rowV
  have h₃' := flux_reverse f g q z
  have h₄ := flux_reverse g f p v
  change flux f g p t = -flux g f p v at h₄
  rw [← htEq]
  change flux g f q v = -flux f g q z at h₃'
  linarith only [h₁, h₁', h₂, h₃, h₃', h₄]

open Classical in
/-- For a contact across a three-mask cut, translation by the other two
masks reverses the signed product of the endpoint amplitudes. The
functions need only satisfy the unit-weight exterior equations. -/
theorem contact_flux_negated_by_three_mask_cut
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    (p q r : CrossingPair (A : Set (Fin 9))) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A = {mask p.val, mask q.val, mask r.val})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    {f g : Q 9 → ℝ}
    (hfout : ∀ v ∉ C, f v = 0)
    (hgout : ∀ v ∉ D, g v = 0)
    (hAf : ∀ v ∉ C, weightedLinear (fun _ => 1) f v = 0)
    (hAg : ∀ v ∉ D, weightedLinear (fun _ => 1) g v = 0)
    {x : Q 9} (hx : x ∈ C) (hxb : parity x = b) (hpx : step p x ∈ D) :
    flux f g p (step q (step r x)) = -flux f g p x := by
  rcases other_contact_of_three_mask_cut hsep hrD hbD hx hxb
    (crossing_pair_mem p) (crossing_pair_mem q) (crossing_pair_mem r) hcut hpx with h | h
  · exact flux_of_companion hpq hpr hqr hcut hsep hrC hrD hcD hbC hbD hdetD
      hfout hgout hAf hAg hx hxb hpx h
  · have hcut' : cutMasks C D b A = {mask p.val, mask r.val, mask q.val} := by
      rw [hcut, Finset.pair_comm (mask q.val)]
    rw [step_comm q r]
    exact flux_of_companion hpr hpq hqr.symm hcut' hsep hrC hrD hcD hbC hbD hdetD
      hfout hgout hAf hAg hx hxb hpx h

#print axioms contact_flux_negated_by_three_mask_cut

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeMaskCutFlux

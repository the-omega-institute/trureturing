/- GID: D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/AraujoBrauerHalfTriangles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Brauer complete-mapping existence constructions and classification. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles.half_diagram_supported_triangle_structure
proof_shape: content — odd_fibre_triangle_structure, half_diagram_supported_triangle_structure
proof_shape: bind-only — odd_doubleFactorial, card_matching_fibre_odd, threeCycle, threeCycle_cube, threeCycle_no_fixed, liftPair, liftPair_involutive, liftPair_fixed, liftPairPerm, liftPairFixedEquiv, OneTrianglePermutation, ThreeFixedReplacement, replace_three_fixed, odd_card_single_fixed_involution, matchingRelabel, matchingRelabelEquiv, ThroughSets, HalfDiagram, complement_card, halfDiagramEquiv, subsetPairingPerm, subsetPairingPerm_fixed_card, OneTrianglePermutation.map, ThroughCompatible, triangle_image_adjacent, baseTwo_triangle_data, baseThree_triangle_data, triangle_image_card_rank, OneTrianglePermutation.perm, OneTrianglePermutation.triangle, OneTrianglePermutation.triangleCard, OneTrianglePermutation.triangleInvariant, OneTrianglePermutation.noFixed, OneTrianglePermutation.triangleCube, OneTrianglePermutation.outsideSquare, ThreeFixedReplacement.triangleEq, ThreeFixedReplacement.outsideEq
Direct frozen dependencies (declaration statement_id):
D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution sha256:6a2fd619f7f0c220bed4d3b853cca9527379a8bd42cefa9403ca65d4b3210aac
D5.S3.Zeros.Convolution.PerfectMatchingCount.card_fixedPointFreeInvolution_mul sha256:f668778ce789801ae29ef9f459aca650eb978ac4b6ca4160af5447a4367a38a9
D5.S3.Zeros.Convolution.PerfectMatchingCount.instFintypeFixedPointFreeInvolution sha256:662e2e6ff37d64412b2e0ed0ce1cccc25fbfa080efcb06596f49226b5ef90dbc
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24053
-/

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Lean.Elab.Tactic.LibrarySearch
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Order.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Lucas
import D5.S3.Zeros.Convolution.PerfectMatchingCount
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
import D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles

open Equiv
open scoped BigOperators
open D5.S3.Zeros.Convolution.PerfectMatchingCount
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSourceMonoids
open D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerSubsetPairing


private theorem odd_doubleFactorial (h : ℕ) : Odd (Nat.doubleFactorial (2 * h + 1)) := by
  induction h with
  | zero => exact ⟨0,rfl⟩
  | succ h ih =>
    have he : 2 * (h + 1) + 1 = (2 * h + 1) + 2 := by exact Nat.add_left_inj.mpr rfl
    rw [he, Nat.doubleFactorial_add_two]
    exact Odd.mul ⟨h+1,by omega⟩ ih

theorem card_matching_fibre_odd {X : Type*} [Fintype X] [DecidableEq X]
    (h : ℕ) (hc : Fintype.card X = 2 * h) :
    Odd (Fintype.card (FixedPointFreeInvolution X)) := by
  cases h with
  | zero =>
    have hd := card_fixedPointFreeInvolution_mul 0 hc
    simp only [Nat.factorial_zero, pow_zero, Nat.mul_one, Nat.mul_zero] at hd
    rw [hd]
    exact ⟨0,rfl⟩
  | succ h =>
    have hd := card_fixedPointFreeInvolution_mul (h+1) hc
    have he : 2 * (h+1) = (2*h+1)+1 := by exact Eq.symm (Nat.succ_add (2 * h) 1)
    have hf := Nat.factorial_eq_mul_doubleFactorial (2*h+1)
    rw [← he, Nat.doubleFactorial_two_mul] at hf
    have hm : Fintype.card (FixedPointFreeInvolution X) =
        Nat.doubleFactorial (2*h+1) := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < (h+1).factorial * 2^(h+1) by positivity)
      calc
        Fintype.card (FixedPointFreeInvolution X) * ((h+1).factorial * 2^(h+1)) =
            (2*(h+1)).factorial := hd
        _ = Nat.doubleFactorial (2*h+1) * ((h+1).factorial * 2^(h+1)) := by
          rw [hf]
          ac_rfl
    rw [hm]
    exact odd_doubleFactorial h

attribute [local instance] Classical.propDecidable

private def threeCycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private theorem threeCycle_cube : ∀ x, threeCycle (threeCycle (threeCycle x)) = x := by decide
private theorem threeCycle_no_fixed : ∀ x, threeCycle x ≠ x := by decide
private noncomputable def liftPair {I F : Type*} (p : Equiv.Perm I) (f : Equiv.Perm F) :
    I × F → I × F := fun x => if p x.1 = x.1 then (x.1,f x.2) else (p x.1,x.2)

private theorem liftPair_involutive {I F : Type*} (p : Equiv.Perm I) (f : Equiv.Perm F)
    (hp : Function.Involutive p) (hf : Function.Involutive f) :
    Function.Involutive (liftPair p f) := by
  intro ⟨i,x⟩
  by_cases hi : p i = i
  · simp [liftPair, hi, hf x]
  · have hi' : p (p i) ≠ p i := fun h => hi (p.injective h)
    simp [liftPair, hi, hp i, Ne.symm hi]

private theorem liftPair_fixed {I F : Type*} (p : Equiv.Perm I) (f : Equiv.Perm F) (x : I × F) :
    liftPair p f x = x ↔ p x.1 = x.1 ∧ f x.2 = x.2 := by
  rcases x with ⟨i,x⟩
  by_cases hi : p i = i <;> simp [liftPair,hi]

private noncomputable def liftPairPerm {I F : Type*} (p : Equiv.Perm I) (f : Equiv.Perm F)
    (hp : Function.Involutive p) (hf : Function.Involutive f) : Equiv.Perm (I × F) :=
  Function.Involutive.toPerm (liftPair p f) (liftPair_involutive p f hp hf)

private noncomputable def liftPairFixedEquiv {I F : Type*} (p : Equiv.Perm I) (f : Equiv.Perm F)
    (hp : Function.Involutive p) (hf : Function.Involutive f) :
    Function.fixedPoints (liftPairPerm p f hp hf) ≃
      Function.fixedPoints p × Function.fixedPoints f where
  toFun x := ⟨⟨x.val.1, ((liftPair_fixed p f x.val).mp x.property).1⟩,
    ⟨x.val.2, ((liftPair_fixed p f x.val).mp x.property).2⟩⟩
  invFun x := ⟨(x.1.val,x.2.val), (liftPair_fixed p f _).mpr ⟨x.1.property,x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A permutation with exactly one orbit of length three and all other orbits of length two,
expressed without selecting a cycle-list representation. -/
structure OneTrianglePermutation (X : Type*) where
  perm : Equiv.Perm X
  triangle : Set X
  triangleCard : Nat.card triangle = 3
  triangleInvariant : ∀ x, x ∈ triangle ↔ perm x ∈ triangle
  noFixed : ∀ x, perm x ≠ x
  triangleCube : ∀ x, x ∈ triangle → perm (perm (perm x)) = x
  outsideSquare : ∀ x, x ∉ triangle → perm (perm x) = x

private structure ThreeFixedReplacement {X : Type*} (s : Equiv.Perm X)
    extends OneTrianglePermutation X where
  triangleEq : triangle = Function.fixedPoints s
  outsideEq : ∀ x, x ∉ triangle → perm x = s x

private noncomputable def replace_three_fixed {X : Type*} [Fintype X]
    (s : Equiv.Perm X) (hs : Function.Involutive s)
    (hc : Nat.card (Function.fixedPoints s) = 3) : ThreeFixedReplacement s := by
  classical
  let e : Function.fixedPoints s ≃ Fin 3 := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_eq_nat_card, Nat.card_fin] using hc)
  let t : Equiv.Perm (Function.fixedPoints s) := (e.trans threeCycle).trans e.symm
  let sn : Equiv.Perm {x : X // s x ≠ x} := s.subtypePerm (by
    intro x
    constructor
    · intro h hh
      exact h (by rw [hh]; exact hh)
    · intro h hh
      exact h (s.injective hh))
  let rho := t.subtypeCongr sn
  have hleft (x : Function.fixedPoints s) : rho x = t x := by
    exact Equiv.Perm.subtypeCongr.left_apply_subtype t sn x
  have hright (x : {x : X // s x ≠ x}) : rho x = s x := by
    exact Equiv.Perm.subtypeCongr.right_apply_subtype t sn x
  have ht_no (x : Function.fixedPoints s) : t x ≠ x := by
    intro h
    apply threeCycle_no_fixed (e x)
    have := congrArg e h
    simpa [t] using this
  have ht_cube (x : Function.fixedPoints s) : t (t (t x)) = x := by
    apply e.injective
    simpa [t] using threeCycle_cube (e x)
  refine {
    perm := rho
    triangle := Function.fixedPoints s
    triangleCard := hc
    triangleInvariant := ?_
    noFixed := ?_
    triangleCube := ?_
    outsideSquare := ?_
    triangleEq := rfl
    outsideEq := ?_ }
  · intro x
    by_cases hx : s x = x
    · constructor
      · intro _
        rw [hleft ⟨x,hx⟩]
        exact (t ⟨x,hx⟩).property
      · intro _; exact hx
    · constructor
      · exact fun h => (hx h).elim
      · intro h
        rw [hright ⟨x,hx⟩] at h
        exact (hx (s.injective h)).elim
  · intro x h
    by_cases hx : s x = x
    · have he : t ⟨x,hx⟩ = ⟨x,hx⟩ := Subtype.ext ((hleft ⟨x,hx⟩).symm.trans h)
      exact ht_no ⟨x,hx⟩ he
    · exact hx ((hright ⟨x,hx⟩).symm.trans h)
  · intro x hx
    rw [hleft ⟨x,hx⟩, hleft (t ⟨x,hx⟩), hleft (t (t ⟨x,hx⟩))]
    exact congrArg Subtype.val (ht_cube ⟨x,hx⟩)
  · intro x hx
    have hx' : s (s x) ≠ s x := fun h => hx (s.injective h)
    rw [hright ⟨x,hx⟩, hright ⟨s x,hx'⟩]
    exact hs x
  · intro x hx
    exact hright ⟨x,hx⟩

private theorem odd_card_single_fixed_involution {F : Type*} [Fintype F]
    (hF : Odd (Fintype.card F)) :
    ∃ f : Equiv.Perm F, Function.Involutive f ∧ Nat.card (Function.fixedPoints f) = 1 := by
  classical
  obtain ⟨m,hm⟩ := hF
  let e : F ≃ (Unit ⊕ (Bool × Fin m)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_unit,
      Fintype.card_bool, Fintype.card_fin]
    omega)
  let bn : Equiv.Perm Bool := ⟨Bool.not, Bool.not, by decide, by decide⟩
  let q : Equiv.Perm (Unit ⊕ (Bool × Fin m)) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr bn (Equiv.refl _))
  let f : Equiv.Perm F := (e.trans q).trans e.symm
  have hq : Function.Involutive q := (inv_eq_self_iff_involutive q).mp rfl
  have hf : Function.Involutive f := (inv_eq_self_iff_involutive f).mp rfl
  have hfix : ∀ x, f x = x ↔ x = e.symm (Sum.inl ()) := by
    intro x
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    generalize hy : e x = y at *
    rw [hx]
    cases y with
    | inl y => cases y; simp [f,q]
    | inr y =>
      rcases y with ⟨b,i⟩
      cases b <;> simp [f,q,bn]
  refine ⟨f,hf,?_⟩
  calc
    Nat.card (Function.fixedPoints f) = Nat.card {x : F // x = e.symm (Sum.inl ())} :=
      Nat.card_congr (Equiv.subtypeEquivRight hfix)
    _ = 1 := Nat.card_unique

private theorem odd_fibre_triangle_structure {I F : Type*} [Fintype I] [Fintype F]
    (p : Equiv.Perm I) (hp : Function.Involutive p)
    (hc : Nat.card (Function.fixedPoints p) = 3)
    (hF : Odd (Fintype.card F)) (R : I → I → Prop)
    (hdiag : ∀ i, R i i) (hpair : ∀ i, R i (p i))
    (htri : ∀ i j, p i = i → p j = j → R i j) :
    ∃ w : OneTrianglePermutation (I × F),
      (∀ x, R x.1 (w.perm x).1) ∧
      (∀ x ∈ w.triangle, p x.1 = x.1) ∧
      (∀ x ∈ w.triangle, ∀ y ∈ w.triangle, x.1 = y.1 → x = y) := by
  classical
  obtain ⟨f,hf,hfc⟩ := odd_card_single_fixed_involution hF
  let s := liftPairPerm p f hp hf
  have hs : Function.Involutive s := liftPair_involutive p f hp hf
  have hsc : Nat.card (Function.fixedPoints s) = 3 := by
    calc
      Nat.card (Function.fixedPoints s) =
          Nat.card (Function.fixedPoints p × Function.fixedPoints f) :=
        Nat.card_congr (liftPairFixedEquiv p f hp hf)
      _ = 3 := by rw [Nat.card_prod, hc, hfc, Nat.mul_one]
  let w := replace_three_fixed s hs hsc
  refine ⟨w.toOneTrianglePermutation, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ w.triangle
    · have hy := (w.triangleInvariant x).mp hx
      rw [w.triangleEq] at hx hy
      have hpx := ((liftPair_fixed p f x).mp hx).1
      have hpy := ((liftPair_fixed p f (w.perm x)).mp hy).1
      exact htri _ _ hpx hpy
    · rw [w.outsideEq x hx]
      change R x.1 (liftPair p f x).1
      by_cases hi : p x.1 = x.1
      · simpa only [liftPair, if_pos hi] using hdiag x.1
      · simpa only [liftPair, if_neg hi] using hpair x.1
  · intro x hx
    rw [w.triangleEq] at hx
    exact ((liftPair_fixed p f x).mp hx).1
  · intro x hx y hy hxy
    rw [w.triangleEq] at hx hy
    have hfx := ((liftPair_fixed p f x).mp hx).2
    have hfy := ((liftPair_fixed p f y).mp hy).2
    obtain ⟨z,hz⟩ := Nat.card_eq_one_iff_exists.mp hfc
    have hval : x.2 = y.2 := congrArg Subtype.val
      ((hz ⟨x.2,hfx⟩).trans (hz ⟨y.2,hfy⟩).symm)
    exact Prod.ext hxy hval


private noncomputable def matchingRelabel {X Y : Type*} (e : X ≃ Y)
    (p : FixedPointFreeInvolution X) : FixedPointFreeInvolution Y :=
  ⟨(e.symm.trans p.val).trans e, by
    constructor
    · intro y
      simpa only [Equiv.trans_apply, e.symm_apply_apply, e.apply_symm_apply] using congrArg e (p.property.1 (e.symm y))
    · intro y hy
      apply p.property.2 (e.symm y)
      have := congrArg e.symm hy
      simpa only [Equiv.trans_apply, e.symm_apply_apply] using this⟩

private noncomputable def matchingRelabelEquiv {X Y : Type*} (e : X ≃ Y) :
    FixedPointFreeInvolution X ≃ FixedPointFreeInvolution Y where
  toFun := matchingRelabel e
  invFun := matchingRelabel e.symm
  left_inv p := by
    apply Subtype.ext
    ext x
    simp [matchingRelabel]
  right_inv p := by
    apply Subtype.ext
    ext x
    simp [matchingRelabel]

abbrev ThroughSets (n r : ℕ) :=
  D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration.PositionSet n r
abbrev HalfDiagram (n r : ℕ) :=
  (T : ThroughSets n r) × FixedPointFreeInvolution {x : Fin n // x ∉ T.val}

theorem complement_card {n r : ℕ} (T : ThroughSets n r) :
    Fintype.card {x : Fin n // x ∉ T.val} = n-r := by
  classical
  rw [Fintype.card_subtype_compl]
  simp [T.property]

noncomputable def halfDiagramEquiv (n r : ℕ) :
    HalfDiagram n r ≃ ThroughSets n r × FixedPointFreeInvolution (Fin (n-r)) :=
  (Equiv.sigmaCongrRight fun T => matchingRelabelEquiv
    (Fintype.equivOfCardEq (by rw [complement_card T, Fintype.card_fin]))).trans
      (Equiv.sigmaEquivProd _ _)

private noncomputable def subsetPairingPerm {n r : ℕ} {tri : Finset (Finset (Fin n))}
    (h : SubsetPairing (Fin n) r tri) : Equiv.Perm (ThroughSets n r) :=
  Function.Involutive.toPerm
    (fun T => ⟨h.pair T, (h.card T).trans T.property⟩)
    (fun T => Subtype.ext (h.involutive T))

private theorem subsetPairingPerm_fixed_card {n r : ℕ} {tri : Finset (Finset (Fin n))}
    (h : SubsetPairing (Fin n) r tri) (ht : tri.card = 3)
    (hr : ∀ T ∈ tri, T.card = r) :
    Nat.card (Function.fixedPoints (subsetPairingPerm h)) = 3 := by
  classical
  let e : Function.fixedPoints (subsetPairingPerm h) ≃ tri := {
    toFun := fun T => ⟨T.val.val, (h.fixed _ T.val.property).mp (congrArg Subtype.val T.property)⟩
    invFun := fun T => ⟨⟨T.val,hr T.val T.property⟩, Subtype.ext ((h.fixed _ (hr T.val T.property)).mpr T.property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card (Function.fixedPoints (subsetPairingPerm h)) = Nat.card tri := Nat.card_congr e
    _ = 3 := by simp [Nat.card_eq_fintype_card, ht]

private noncomputable def OneTrianglePermutation.map {X Y : Type*} (w : OneTrianglePermutation X)
    (e : X ≃ Y) : OneTrianglePermutation Y := by
  let q : Equiv.Perm Y := (e.symm.trans w.perm).trans e
  let tri : Set Y := {y | e.symm y ∈ w.triangle}
  let et : w.triangle ≃ tri := {
    toFun := fun x => ⟨e x, by simpa only [tri, Set.mem_setOf_eq, e.symm_apply_apply] using x.property⟩
    invFun := fun y => ⟨e.symm y,y.property⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  refine ⟨q,tri, (Nat.card_congr et).symm.trans w.triangleCard, ?_, ?_, ?_, ?_⟩
  · intro y
    simpa [q,tri] using w.triangleInvariant (e.symm y)
  · intro y hy
    apply w.noFixed (e.symm y)
    simpa [q] using congrArg e.symm hy
  · intro y hy
    apply e.symm.injective
    simpa [q,tri] using w.triangleCube (e.symm y) hy
  · intro y hy
    apply e.symm.injective
    simpa [q,tri] using w.outsideSquare (e.symm y) hy


def ThroughCompatible {n r : ℕ} (T U : ThroughSets n r) : Prop :=
  T.val = U.val ∨ (T.val ∩ U.val).card + 1 = r

theorem half_diagram_supported_triangle_structure {n r : ℕ} {tri : Finset (Finset (Fin n))}
    (h : SubsetPairing (Fin n) r tri) (ht : tri.card = 3)
    (hr : ∀ T ∈ tri, T.card = r) (he : Even (n-r))
    (ha : ∀ T ∈ tri, ∀ U ∈ tri, T = U ∨ (T ∩ U).card + 1 = r) :
    ∃ w : OneTrianglePermutation (HalfDiagram n r),
      (∀ D, ThroughCompatible D.1 (w.perm D).1) ∧
      (∀ D ∈ w.triangle, D.1.val ∈ tri) ∧
      (∀ D ∈ w.triangle, ∀ E ∈ w.triangle, D.1 = E.1 → D = E) := by
  classical
  obtain ⟨d,hd⟩ := he
  have hc : Fintype.card (Fin (n-r)) = 2*d := by simpa only [Fintype.card_fin, two_mul] using hd
  let p := subsetPairingPerm h
  have hp : Function.Involutive p := fun T => Subtype.ext (h.involutive T)
  have hdiag : ∀ T : ThroughSets n r, ThroughCompatible T T := fun _ => Or.inl rfl
  have hpair : ∀ T : ThroughSets n r, ThroughCompatible T (p T) := by
    intro T
    by_cases hf : h.pair T.val = T.val
    · exact Or.inl hf.symm
    · right
      exact h.adjacent T.val T.property (fun hm => hf ((h.fixed _ T.property).mpr hm))
  have htri : ∀ T U, p T = T → p U = U → ThroughCompatible T U := by
    intro T U hT hU
    exact ha _ ((h.fixed _ T.property).mp (congrArg Subtype.val hT))
      _ ((h.fixed _ U.property).mp (congrArg Subtype.val hU))
  obtain ⟨w,hw,htw,hiw⟩ := odd_fibre_triangle_structure (F := FixedPointFreeInvolution (Fin (n-r)))
    p hp (subsetPairingPerm_fixed_card h ht hr) (card_matching_fibre_odd d hc)
    ThroughCompatible hdiag hpair htri
  let e := halfDiagramEquiv n r
  refine ⟨w.map e.symm, ?_, ?_, ?_⟩
  · intro D
    have hD : (e D).1 = D.1 := rfl
    have hE : ∀ y, (e.symm y).1 = y.1 := fun _ => rfl
    simpa only [OneTrianglePermutation.map, Equiv.trans_apply, Equiv.symm_symm, hE, hD]
      using hw (e D)
  · intro D hD
    change e D ∈ w.triangle at hD
    have hfix := htw (e D) hD
    exact (h.fixed D.1.val D.1.property).mp (congrArg Subtype.val hfix)
  · intro D hD E hE hDE
    change e D ∈ w.triangle at hD
    change e E ∈ w.triangle at hE
    apply e.injective
    exact hiw (e D) hD (e E) hE hDE

theorem triangle_image_adjacent {n m r : ℕ} (tri : Finset (Finset (Fin n)))
    (e : Fin n ↪ Fin m)
    (ha : ∀ T ∈ tri, ∀ U ∈ tri, T = U ∨ (T ∩ U).card + 1 = r) :
    ∀ T ∈ tri.image (fun s => s.map e), ∀ U ∈ tri.image (fun s => s.map e),
      T = U ∨ (T ∩ U).card + 1 = r := by
  intro T hT U hU
  obtain ⟨T,hT0,rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨U,hU0,rfl⟩ := Finset.mem_image.mp hU
  rcases ha T hT0 U hU0 with h | h
  · exact Or.inl (congrArg (fun s => s.map e) h)
  · right
    simpa only [← Finset.map_inter, Finset.card_map] using h

set_option maxRecDepth 100000 in
theorem baseTwo_triangle_data :
    baseTwoTriangle.card = 3 ∧
    (∀ T ∈ baseTwoTriangle, T.card = 2) ∧
    (∀ T ∈ baseTwoTriangle, ∀ U ∈ baseTwoTriangle,
      T = U ∨ (T ∩ U).card + 1 = 2) := by decide

set_option maxRecDepth 100000 in
theorem baseThree_triangle_data :
    baseThreeTriangle.card = 3 ∧
    (∀ T ∈ baseThreeTriangle, T.card = 3) ∧
    (∀ T ∈ baseThreeTriangle, ∀ U ∈ baseThreeTriangle,
      T = U ∨ (T ∩ U).card + 1 = 3) := by decide

theorem triangle_image_card_rank {n m r : ℕ} (tri : Finset (Finset (Fin n)))
    (e : Fin n ↪ Fin m) (ht : tri.card = 3) (hr : ∀ T ∈ tri, T.card = r) :
    (tri.image (fun s => s.map e)).card = 3 ∧
    ∀ T ∈ tri.image (fun s => s.map e), T.card = r := by
  constructor
  · rw [Finset.card_image_of_injective]
    · exact ht
    · intro s t h
      exact Finset.map_injective e h
  · intro T hT
    obtain ⟨T,hT0,rfl⟩ := Finset.mem_image.mp hT
    simpa using hr T hT0

end D5.S3.Combinatorics.PerfectMatchings.AraujoBrauerHalfTriangles

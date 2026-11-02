/- GID: D5/S3/Geometry/Gluing/PairedTriangleCornerCycles
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/PairedTriangleCornerCycles
   mirror-E: none(waiver:finite-paired-triangle-corner-cycles)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic, mathlib/module/Mathlib.Dynamics.PeriodicPts.Lemmas]
   utility: none
   digest: Actual triangle corner fibers have positive cyclic coordinates given by powers of the two-matching walk. -/

/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler

Adapted from RS.relPairing_not_sameCycle in
LeanPool/RegtsSevenster/RS/Novel/Skein/OrientExistence.lean,
revision 766a994003f161b1013109977cd615b06d0dd5a9.
The two permutations are explicit parameters in this formulation.
Full license and upstream notice:
docs/reports/paired-triangle-corner-cycles/lean-pool-LICENSE.txt
docs/reports/paired-triangle-corner-cycles/lean-pool-NOTICE.txt
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Quot
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases


namespace D5.S3.Geometry.Gluing.PairedTriangleCornerCycles

set_option autoImplicit false
namespace MatchingOrbitSeparation

-- Replace this port by a direct import when this repository's pinned Mathlib
-- contains the two fixed-point-free involution orbit-separation theorem.
private theorem pairing_not_sameCycle {X : Type*} [Finite X]
    (a b : Equiv.Perm X) (ha : a * a = 1) (hb : b * b = 1)
    (freea : ∀ x, a x ≠ x) (freeb : ∀ x, b x ≠ x) (x : X) :
    ¬ (b * a).SameCycle x (a x) := by
  let p := b * a
  have ainv : a⁻¹ = a :=
    mul_left_cancel (a := a) (by rw [mul_inv_cancel, ha])
  have binv : b⁻¹ = b :=
    mul_left_cancel (a := b) (by rw [mul_inv_cancel, hb])
  have conj : a * p * a = p⁻¹ := by
    dsimp only [p]
    calc
      a * (b * a) * a = a * b * (a * a) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      _ = a * b := by rw [ha, mul_one]
      _ = (b * a)⁻¹ := by rw [mul_inv_rev, ainv, binv]
  have conjpow (n : ℤ) : a * p ^ n * a = p ^ (-n) := by
    calc
      a * p ^ n * a = a * p ^ n * a⁻¹ := by rw [ainv]
      _ = (MulAut.conj a) (p ^ n) := rfl
      _ = ((MulAut.conj a) p) ^ n :=
        map_zpow (MulAut.conj a).toMonoidHom p n
      _ = p⁻¹ ^ n := by
        congr 1
        change a * p * a⁻¹ = p⁻¹
        rw [ainv]
        exact conj
      _ = p ^ (-n) := inv_zpow' p n
  intro hsame
  obtain ⟨m, _hmpos, _hmbound, hm⟩ := hsame.exists_pow_eq''
  have hm' : (p ^ (m : ℤ)) x = a x := by
    rw [zpow_natCast]
    exact hm
  have hconj (n : ℤ) : a ((p ^ n) (a x)) = (p ^ (-n)) x := by
    have h := congrArg (fun e : Equiv.Perm X => e x) (conjpow n)
    simpa only [Equiv.Perm.mul_apply] using h
  have hshift (n : ℤ) : a ((p ^ (n + ↑m)) x) = (p ^ (-n)) x := by
    rw [zpow_add, Equiv.Perm.mul_apply, hm']
    exact hconj n
  rcases Nat.even_or_odd m with ⟨j,hj⟩ | ⟨j,hj⟩
  · have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) := by omega
    rw [harith, neg_neg] at key
    exact freea _ key
  · have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) + 1 := by omega
    rw [harith, neg_neg] at key
    have hstep : (p ^ ((j : ℤ) + 1)) x = p ((p ^ (j : ℤ)) x) := by
      conv_lhs => rw [show (j : ℤ) + 1 = 1 + (j : ℤ) from by ring]
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rw [hstep] at key
    set y := (p ^ (j : ℤ)) x
    have hval : a (b (a y)) = y := by
      simpa only [p, Equiv.Perm.mul_apply] using key
    have hinvol (z : X) : a (a z) = z := by
      have h := congrArg (fun e : Equiv.Perm X => e z) ha
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
    have hfix : b (a y) = a y := by
      have h := congrArg a hval
      simpa only [hinvol] using h
    exact freeb _ hfix

end MatchingOrbitSeparation


set_option autoImplicit false
noncomputable section

namespace PairedTriangles

universe u
abbrev Side (F : Type u) := F × Fin 3
abbrev LocalCorner (F : Type u) := F × Fin 3

-- Side s is opposite corner s; endpoint occurrences remain separate even
-- when their quotient vertex classes agree.
def sideCorner (s : Fin 3) (i : Fin 2) : Fin 3 :=
  ![![1,2], ![2,0], ![0,1]] s i

structure Pairing (F : Type u) where
  pair : Side F → Side F
  involutive : Function.Involutive pair
  fixedPointFree : ∀ s, pair s ≠ s
  endpointTransport : Side F → Equiv.Perm (Fin 2)
  compatible : ∀ s i, endpointTransport (pair s) (endpointTransport s i) = i

namespace Pairing
variable {F : Type u} (q : Pairing F)

def cornerAt (s : Side F) (i : Fin 2) : LocalCorner F :=
  (s.1, sideCorner s.2 i)

def cornerRel (a b : LocalCorner F) : Prop :=
  ∃ s i, cornerAt s i = a ∧
    cornerAt (q.pair s) (q.endpointTransport s i) = b

abbrev Vertex := Quotient (Relation.EqvGen.setoid q.cornerRel)

def vertexClass (c : LocalCorner F) : q.Vertex := Quotient.mk _ c


end Pairing
end PairedTriangles



namespace PairedTriangles
universe u

abbrev Flag (F : Type u) := Side F × Fin 2

def localTurn (p : Fin 3 × Fin 2) : Fin 3 × Fin 2 :=
  ![![(2,1),(1,0)], ![(0,1),(2,0)], ![(1,1),(0,0)]] p.1 p.2

private theorem localTurn_involutive : Function.Involutive localTurn := by
  exact (show ∀ p : Fin 3 × Fin 2, localTurn (localTurn p) = p from by decide)

private theorem localTurn_fixedPointFree (p : Fin 3 × Fin 2) : localTurn p ≠ p := by
  exact (show ∀ p : Fin 3 × Fin 2, localTurn p ≠ p from by decide) p

private theorem localTurn_corner (p : Fin 3 × Fin 2) :
    sideCorner (localTurn p).1 (localTurn p).2 = sideCorner p.1 p.2 := by
  exact (show ∀ p : Fin 3 × Fin 2,
    sideCorner (localTurn p).1 (localTurn p).2 = sideCorner p.1 p.2 from by decide) p

namespace Pairing
variable {F : Type u} (q : Pairing F)

def cross (f : Flag F) : Flag F :=
  (q.pair f.1, q.endpointTransport f.1 f.2)

def turn (f : Flag F) : Flag F :=
  let p := localTurn (f.1.2,f.2)
  ((f.1.1,p.1),p.2)

private theorem cross_involutive : Function.Involutive q.cross := by
  rintro ⟨s,i⟩
  simp only [cross, q.compatible]
  rw [q.involutive s]

private theorem cross_fixedPointFree (f : Flag F) : q.cross f ≠ f := by
  intro h
  exact q.fixedPointFree f.1 (congrArg Prod.fst h)

private theorem turn_involutive : Function.Involutive (turn (F := F)) := by
  rintro ⟨⟨f,s⟩,i⟩
  exact congrArg (fun p : Fin 3 × Fin 2 => ((f,p.1),p.2))
    (localTurn_involutive (s,i))

private theorem turn_fixedPointFree (f : Flag F) : turn f ≠ f := by
  intro h
  have hp := congrArg (fun a : Flag F => (a.1.2,a.2)) h
  exact localTurn_fixedPointFree (f.1.2,f.2) hp

private theorem turn_corner (f : Flag F) : cornerAt (turn f).1 (turn f).2 = cornerAt f.1 f.2 := by
  apply Prod.ext
  · rfl
  · exact localTurn_corner (f.1.2,f.2)

def crossEquiv : Equiv.Perm (Flag F) := q.cross_involutive.toPerm q.cross

def turnEquiv : Equiv.Perm (Flag F) := (turn_involutive (F := F)).toPerm turn

private theorem walk_orbit_excludes_cross [Finite F] (f : Flag F) :
    ¬ ((turnEquiv (F := F) * q.crossEquiv : Equiv.Perm (Flag F))).SameCycle f (q.crossEquiv f) := by
  apply MatchingOrbitSeparation.pairing_not_sameCycle q.crossEquiv (turnEquiv (F := F))
  · apply Equiv.ext
    intro g
    exact q.cross_involutive g
  · apply Equiv.ext
    intro g
    exact turn_involutive g
  · exact q.cross_fixedPointFree
  · exact turn_fixedPointFree

end Pairing
end PairedTriangles
namespace TwoMatchingNormalForm
universe u v
variable {X : Type u} {C : Type v}

def Connected (a b : X → X) : X → X → Prop :=
  Relation.EqvGen (fun f g => a f = g ∨ b f = g)

def ProjectedCrossRel (a : X → X) (c : X → C) (u v : C) : Prop :=
  ∃ f, c f = u ∧ c (a f) = v

private theorem projected_eqvGen_iff_connected
    (a b : X → X) (c : X → C) (hc : Function.Surjective c)
    (fiber : ∀ f g : X, c f = c g ↔ g = f ∨ g = b f)
    (f g : X) :
    Relation.EqvGen (ProjectedCrossRel a c) (c f) (c g) ↔ Connected a b f g := by
  have sameFiber {x y : X} (h : c x = c y) : Connected a b x y := by
    rcases (fiber x y).mp h with h | h
    · subst y
      exact Relation.EqvGen.refl x
    · exact Relation.EqvGen.rel x y (Or.inr h.symm)
  constructor
  · intro h
    let r := Relation.EqvGen.setoid (fun x y => a x = y ∨ b x = y)
    have hm : Equivalence (Relation.Map r c c) :=
      Relation.map_equivalence r.iseqv c hc (fun x y h => sameFiber h)
    have mapped : Relation.Map r c c (c f) (c g) := by
      apply (hm.eqvGen_iff).mp
      apply Relation.EqvGen.mono (r := ProjectedCrossRel a c) (p := Relation.Map r c c) ?_ _ _ h
      rintro u v ⟨x,hx,hax⟩
      exact ⟨x,a x,Relation.EqvGen.rel _ _ (Or.inl rfl),hx,hax⟩
    obtain ⟨x,y,hxy,hx,hy⟩ := mapped
    exact Relation.EqvGen.trans _ _ _ (sameFiber hx.symm)
      (Relation.EqvGen.trans _ _ _ hxy (sameFiber hy))
  · intro h
    induction h with
    | rel x y h =>
        rcases h with h | h
        · exact Relation.EqvGen.rel _ _ ⟨x,rfl,congrArg c h⟩
        · have he : c x = c y := (fiber x y).mpr (Or.inr h.symm)
          rw [he]
          exact Relation.EqvGen.refl _
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
end TwoMatchingNormalForm

namespace PairedTriangles
universe u

private theorem localTurn_fiber (p r : Fin 3 × Fin 2) :
    sideCorner p.1 p.2 = sideCorner r.1 r.2 ↔ r = p ∨ r = localTurn p := by
  exact (show ∀ p r : Fin 3 × Fin 2,
    sideCorner p.1 p.2 = sideCorner r.1 r.2 ↔ r = p ∨ r = localTurn p from by decide) p r

def cornerProjection {F : Type u} (f : Flag F) : LocalCorner F := Pairing.cornerAt f.1 f.2

def cornerSection {F : Type u} (d : LocalCorner F) : Flag F :=
  ((d.1, ![1,2,0] d.2),1)

private theorem cornerProjection_section {F : Type u} (d : LocalCorner F) :
    cornerProjection (cornerSection d) = d := by
  rcases d with ⟨f,c⟩
  fin_cases c <;> rfl

private theorem cornerProjection_surjective {F : Type u} :
    Function.Surjective (cornerProjection (F := F)) := by
  intro d
  exact ⟨cornerSection d,cornerProjection_section d⟩

private theorem cornerProjection_fiber {F : Type u} (f g : Flag F) :
    cornerProjection f = cornerProjection g ↔ g = f ∨ g = Pairing.turn f := by
  constructor
  · rcases f with ⟨⟨f,s⟩,i⟩
    rcases g with ⟨⟨g,t⟩,j⟩
    intro h
    have hf : f = g := congrArg Prod.fst h
    subst g
    have hk : sideCorner s i = sideCorner t j := congrArg Prod.snd h
    rcases (localTurn_fiber (s,i) (t,j)).mp hk with ht | ht
    · exact Or.inl (congrArg (fun p : Fin 3 × Fin 2 => ((f,p.1),p.2)) ht)
    · exact Or.inr (congrArg (fun p : Fin 3 × Fin 2 => ((f,p.1),p.2)) ht)
  · rintro (rfl | rfl)
    · rfl
    · exact (Pairing.turn_corner f).symm

namespace Pairing
variable {F : Type u} (q : Pairing F)

private theorem cornerRel_eq_projected : q.cornerRel =
    TwoMatchingNormalForm.ProjectedCrossRel q.cross cornerProjection := by
  funext u v
  apply propext
  constructor
  · rintro ⟨s,i,hu,hv⟩
    exact ⟨(s,i),hu,hv⟩
  · rintro ⟨⟨s,i⟩,hu,hv⟩
    exact ⟨s,i,hu,hv⟩


end Pairing
end PairedTriangles

namespace TwoMatchingNormalForm
open Equiv.Perm
universe u
variable {X : Type u}

private theorem connected_two_orbits (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    {x y : X} (hxy : Connected a b x y) :
    (b * a).SameCycle x y ∨ (b * a).SameCycle x (b y) := by
  let p := b * a
  let P : X → Prop := fun z => p.SameCycle x z ∨ p.SameCycle x (b z)
  have stepA (z : X) : P (a z) ↔ P z := by
    have hpa : p (a z) = b z := by change b (a (a z)) = b z; rw [ha z]
    have h₁ : p.SameCycle x (a z) ↔ p.SameCycle x (b z) := by
      rw [← hpa, sameCycle_apply_right]
    have h₂ : p.SameCycle x (b (a z)) ↔ p.SameCycle x z :=
      sameCycle_apply_right
    exact (or_congr h₁ h₂).trans or_comm
  have stepB (z : X) : P (b z) ↔ P z := by
    change (p.SameCycle x (b z) ∨ p.SameCycle x (b (b z))) ↔ _
    rw [hb z, or_comm]
  have transport : ∀ {s t : X}, Connected a b s t → (P s ↔ P t) := by
    intro s t h
    induction h with
    | rel s t h =>
        rcases h with h | h
        · subst t; exact (stepA s).symm
        · subst t; exact (stepB s).symm
    | refl s => exact Iff.rfl
    | symm s t _ ih => exact ih.symm
    | trans s t w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (transport hxy).mp (Or.inl (SameCycle.refl p x))

def orbitPoint (p : Equiv.Perm X) (x : X)
    (i : Fin (Function.minimalPeriod p x)) : X := (p ^ (i : ℕ)) x

private theorem orbitPoint_injective (p : Equiv.Perm X) (x : X) :
    Function.Injective (orbitPoint p x) := by
  intro i j h
  apply Fin.ext
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp
  simpa only [orbitPoint, Equiv.Perm.coe_pow] using h

private theorem orbitPoint_exists [Finite X] {p : Equiv.Perm X} {x y : X}
    (h : p.SameCycle x y) :
    ∃ i : Fin (Function.minimalPeriod p x), orbitPoint p x i = y := by
  obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
  have hn := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)
  refine ⟨⟨k % Function.minimalPeriod p x,Nat.mod_lt _ hn⟩,?_⟩
  simpa only [orbitPoint, Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq] using hk

def normalForm (a b : Equiv.Perm X) (x : X)
    (z : Fin (Function.minimalPeriod (b * a) x) × Fin 2) : X :=
  if z.2 = 0 then orbitPoint (b * a) x z.1 else b (orbitPoint (b * a) x z.1)

private theorem normalForm_exists [Finite X] (a b : Equiv.Perm X)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    {x y : X} (h : Connected a b x y) :
    ∃ z : Fin (Function.minimalPeriod (b * a) x) × Fin 2, normalForm a b x z = y := by
  rcases connected_two_orbits a b ha hb h with h | h
  · obtain ⟨i,hi⟩ := orbitPoint_exists h
    exact ⟨(i,0),hi⟩
  · obtain ⟨i,hi⟩ := orbitPoint_exists h
    refine ⟨(i,1),?_⟩
    change b (orbitPoint (b * a) x i) = y
    rw [hi,hb y]

private theorem orbit_excludes_turn (a b : Equiv.Perm X)
    (ha : Function.Involutive a)
    (sep : ∀ z : X, ¬ (b * a).SameCycle z (a z)) (z : X) :
    ¬ (b * a).SameCycle z (b z) := by
  intro h
  apply sep z
  apply SameCycle.of_apply_right
  simpa only [mul_apply,ha z] using h

private theorem normalForm_injective (a b : Equiv.Perm X)
    (ha : Function.Involutive a)
    (sep : ∀ z : X, ¬ (b * a).SameCycle z (a z)) (x : X) :
    Function.Injective (normalForm a b x) := by
  have same (i : Fin (Function.minimalPeriod (b * a) x)) :
      (b * a).SameCycle x (orbitPoint (b * a) x i) :=
    (SameCycle.refl (b * a) x).pow_right
  have disjoint (i j : Fin (Function.minimalPeriod (b * a) x)) :
      orbitPoint (b * a) x i ≠ b (orbitPoint (b * a) x j) := by
    intro h
    apply orbit_excludes_turn a b ha sep (orbitPoint (b * a) x j)
    exact (same j).symm.trans (h ▸ same i)
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  fin_cases s <;> fin_cases t <;> norm_num [normalForm] at h
  · exact Prod.ext (orbitPoint_injective _ _ h) rfl
  · exact False.elim (disjoint i j h)
  · exact False.elim (disjoint j i h.symm)
  · exact Prod.ext (orbitPoint_injective _ _ h) rfl

end TwoMatchingNormalForm

namespace TwoMatchingNormalForm
open Equiv.Perm
universe u v
variable {X : Type u} {C : Type v}

private theorem normalForm_connected (a b : Equiv.Perm X) (x : X)
    (z : Fin (Function.minimalPeriod (b * a) x) × Fin 2) :
    Connected a b x (normalForm a b x z) := by
  have hp : ∀ k : ℕ, Connected a b x (((b * a) ^ k) x) := by
    intro k
    induction k with
    | zero => exact Relation.EqvGen.refl _
    | succ k ih =>
        rw [pow_succ',mul_apply,mul_apply]
        exact Relation.EqvGen.trans _ _ _ ih
          (Relation.EqvGen.trans _ _ _
            (Relation.EqvGen.rel _ _ (Or.inl rfl))
            (Relation.EqvGen.rel _ _ (Or.inr rfl)))
  rcases z with ⟨i,s⟩
  fin_cases s
  · exact hp i
  · exact Relation.EqvGen.trans _ _ _ (hp i)
      (Relation.EqvGen.rel _ _ (Or.inr rfl))

noncomputable def cornerCycleEquiv [Finite X]
    (a b : Equiv.Perm X) (ha : Function.Involutive a) (hb : Function.Involutive b)
    (sep : ∀ z : X, ¬ (b * a).SameCycle z (a z))
    (c : X → C) (hc : Function.Surjective c)
    (fiber : ∀ f g : X, c f = c g ↔ g = f ∨ g = b f) (x : X) :
    Fin (Function.minimalPeriod (b * a) x) ≃
      {d : C // Relation.EqvGen (ProjectedCrossRel a c) (c x) d} := by
  let f : Fin (Function.minimalPeriod (b * a) x) →
      {d : C // Relation.EqvGen (ProjectedCrossRel a c) (c x) d} := fun i =>
    ⟨c (orbitPoint (b * a) x i),
      (projected_eqvGen_iff_connected a b c hc fiber x _).mpr
        (normalForm_connected a b x (i,0))⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have he : c (orbitPoint (b * a) x i) = c (orbitPoint (b * a) x j) :=
      congrArg Subtype.val h
    rcases (fiber _ _).mp he with he | he
    · exact orbitPoint_injective _ _ he.symm
    · have hn : normalForm a b x (j,0) = normalForm a b x (i,1) := he
      have hrow := congrArg Prod.snd (normalForm_injective a b ha sep x hn)
      exact False.elim (by have hh := congrArg Fin.val hrow; norm_num at hh)
  · intro d
    obtain ⟨y,hy⟩ := hc d.val
    have hxy : Connected a b x y :=
      (projected_eqvGen_iff_connected a b c hc fiber x y).mp (by simpa only [hy] using d.property)
    obtain ⟨⟨i,s⟩,hi⟩ := normalForm_exists a b ha hb hxy
    refine ⟨i,Subtype.ext ?_⟩
    change c (orbitPoint (b * a) x i) = d.val
    rw [←hy,←hi]
    fin_cases s
    · rfl
    · exact (fiber _ _).mpr (Or.inr rfl)

end TwoMatchingNormalForm

namespace PairedTriangles.Pairing
universe u
variable {F : Type u} [Finite F] (q : Pairing F)

noncomputable def actualCornerCycleEquiv (f : Flag F) :
    Fin (Function.minimalPeriod ((turnEquiv (F := F) * q.crossEquiv : Equiv.Perm (Flag F))) f) ≃
      {d : LocalCorner F // q.vertexClass d = q.vertexClass (cornerProjection f)} := by
  let e := TwoMatchingNormalForm.cornerCycleEquiv q.crossEquiv (turnEquiv (F := F))
    q.cross_involutive turn_involutive q.walk_orbit_excludes_cross
    cornerProjection cornerProjection_surjective cornerProjection_fiber f
  apply e.trans
  apply Equiv.subtypeEquivRight
  intro d
  have he : Relation.EqvGen q.cornerRel (cornerProjection f) d ↔
      q.vertexClass d = q.vertexClass (cornerProjection f) := by
    exact ⟨fun h => (Quotient.sound h).symm,fun h => Quotient.exact h.symm⟩
  rw [cornerRel_eq_projected] at he
  exact he

theorem actual_corner_cycle (f : Flag F) :
    ∃ n : ℕ, 0 < n ∧ ∃ e : Fin n ≃
      {d : LocalCorner F // q.vertexClass d = q.vertexClass (cornerProjection f)},
      ∀ i : Fin n, (e i).val =
        cornerProjection ((((turnEquiv (F := F) * q.crossEquiv : Equiv.Perm (Flag F))) ^ (i : ℕ)) f) := by
  let p := (turnEquiv (F := F) * q.crossEquiv : Equiv.Perm (Flag F))
  have hn : 0 < Function.minimalPeriod p f :=
    Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts f)
  refine ⟨Function.minimalPeriod p f,hn,q.actualCornerCycleEquiv f,?_⟩
  intro i
  rfl

end PairedTriangles.Pairing

#print axioms TwoMatchingNormalForm.connected_two_orbits
#print axioms PairedTriangles.Pairing.actual_corner_cycle

end D5.S3.Geometry.Gluing.PairedTriangleCornerCycles

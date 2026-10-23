/- GID: D5/S3/Geometry/Gluing/ActualCornerPointPeriods
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualCornerPointPeriods
   mirror-E: none(waiver:actual-oriented-corner-point-period)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Lemmas]
   utility: none
   digest: Actual ordered corner components follow minimal point periods. -/

import D5.S3.Geometry.Gluing.ActualLinkCornerChains
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic

set_option autoImplicit false
noncomputable section
open scoped Fin.NatCast
namespace D5.S3.Geometry.Gluing.ActualCornerPointPeriods
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- Rows are L0, L1, H2, H0; the endpoints are ordered. -/
def corner (c : Fin 4) (s : Fin 3) : Fin 4 :=
  ![![0,2,1], ![1,3,2], ![2,0,3], ![0,3,1]] c s

def tip (c : Fin 4) (s : Fin 3) : Fin 4 :=
  ![![1,3,2], ![0,2,1], ![0,3,1], ![2,0,3]] c s

def outgoing (c : Fin 4) (s : Fin 3) : Fin 4 :=
  ![![2,0,0], ![2,0,0], ![1,1,0], ![1,1,0]] c s

def incoming (c : Fin 4) (s : Fin 3) : Fin 4 :=
  ![![3,1,3], ![3,1,3], ![3,2,2], ![3,2,2]] c s

def returnWord (u v : G) (c : Fin 4) : G :=
  ![v⁻¹ * u^2, v⁻¹ * u^2, v^2 * u, v^2 * u] c

def offset (u v : G) (c : Fin 4) (s : Fin 3) : G :=
  ![![1,v⁻¹,v⁻¹*u], ![1,v⁻¹,v⁻¹*u], ![1,v,v^2], ![1,v,v^2]] c s

/-- The root coordinate changes only on the third crossing. -/
def tour (u v : G) (c : Fin 4) : Equiv.Perm (Ω × Fin 3) where
  toFun x := if x.2 = 2 then (act x.1 (returnWord u v c), 0) else (x.1, x.2+1)
  invFun x := if x.2 = 0 then (act x.1 (returnWord u v c)⁻¹, 2) else (x.1, x.2-1)
  left_inv := by
    rintro ⟨x,s⟩
    fin_cases s <;> simp [act_mul]
  right_inv := by
    rintro ⟨x,s⟩
    fin_cases s <;> simp [act_mul]

def encode (u v : G) (c : Fin 4) (x : Ω × Fin 3) : Dart Ω :=
  ((act x.1 (offset u v c x.2), corner c x.2), tip c x.2)

private theorem corner_injective (c : Fin 4) : Function.Injective (corner c) := by
  intro s t h
  fin_cases c <;> fin_cases s <;> fin_cases t <;> simp_all [corner]

private theorem encode_injective (u v : G) (c : Fin 4) :
    Function.Injective (encode (Ω := Ω) u v c) := by
  rintro ⟨x,s⟩ ⟨y,t⟩ h
  have hs := corner_injective c (congrArg (fun d : Dart Ω => d.1.2) h)
  dsimp [encode] at hs
  subst t
  have hx := congrArg (fun d : Dart Ω => act d.1.1 (offset u v c s)⁻¹) h
  simpa [encode, act_mul] using hx

private theorem allowed_faces (c : Fin 4) (s : Fin 3) (f : Fin 4) :
    (f ≠ corner c s ∧ f ≠ tip c s) ↔ f = outgoing c s ∨ f = incoming c s := by
  fin_cases c <;> fin_cases s <;> fin_cases f <;> decide

private theorem forward_move (u v : G) (c : Fin 4) (x : Ω × Fin 3) :
    dartMove u v (outgoing c x.2) (encode u v c x) = encode u v c (tour u v c x) := by
  rcases x with ⟨x,s⟩
  fin_cases c <;> fin_cases s <;>
    simp [dartMove, encode, outgoing, corner, tip, facePerm, faceWord,
      tour, offset, returnWord, act_mul, pow_two, mul_assoc]

private theorem backward_move (u v : G) (c : Fin 4) (x : Ω × Fin 3) :
    dartMove u v (incoming c x.2) (encode u v c x) =
      encode u v c ((tour u v c).symm x) := by
  rcases x with ⟨x,s⟩
  fin_cases c <;> fin_cases s <;>
    simp [dartMove, encode, incoming, corner, tip, facePerm, faceWord,
      tour, offset, returnWord, act_mul, pow_two, mul_assoc]

private theorem coded_step (u v : G) (c : Fin 4) (x : Ω × Fin 3) (d : Dart Ω) :
    DartStep u v (encode u v c x) d ↔
      d = encode u v c (tour u v c x) ∨ d = encode u v c ((tour u v c).symm x) := by
  constructor
  · rintro ⟨f,hj,hk,hd⟩
    rcases (allowed_faces c x.2 f).mp ⟨hj,hk⟩ with rfl | rfl
    · exact Or.inl (hd.trans (forward_move u v c x))
    · exact Or.inr (hd.trans (backward_move u v c x))
  · rintro (rfl | rfl)
    · obtain ⟨hj,hk⟩ := (allowed_faces c x.2 (outgoing c x.2)).mpr (Or.inl rfl)
      exact ⟨outgoing c x.2,hj,hk,(forward_move u v c x).symm⟩
    · obtain ⟨hj,hk⟩ := (allowed_faces c x.2 (incoming c x.2)).mpr (Or.inr rfl)
      exact ⟨incoming c x.2,hj,hk,(backward_move u v c x).symm⟩

private theorem dart_step_symm (u v : G) {d e : Dart Ω} (h : DartStep u v d e) :
    DartStep u v e d := by
  obtain ⟨f,hj,hk,rfl⟩ := h
  have hf : facePerm f f = reverseFace f := by fin_cases f <;> rfl
  refine ⟨reverseFace f, ?_, ?_, ?_⟩
  · change reverseFace f ≠ facePerm f d.1.2
    rw [← hf]
    exact (facePerm f).injective.ne hj
  · change reverseFace f ≠ facePerm f d.2
    rw [← hf]
    exact (facePerm f).injective.ne hk
  · rcases d with ⟨⟨x,j⟩,k⟩
    fin_cases f <;> fin_cases j <;> fin_cases k <;>
      simp [dartMove, reverseFace, facePerm, faceWord, act_mul]

private theorem component_forward (u v : G) (c : Fin 4) (x : Ω × Fin 3)
    {d : Dart Ω} (h : DartRelated u v (encode u v c x) d) :
    ∃ y, d = encode u v c y ∧ (tour u v c).SameCycle x y := by
  let P : Dart Ω → Prop := fun d => ∃ y, d = encode u v c y ∧ (tour u v c).SameCycle x y
  have next {a b : Dart Ω} (hab : DartStep u v a b) (ha : P a) : P b := by
    obtain ⟨y,rfl,hy⟩ := ha
    rcases (coded_step u v c y b).mp hab with hb | hb
    · exact ⟨_,hb,hy.apply_right⟩
    · exact ⟨_,hb,hy.symm_apply_right⟩
  have invariant {a b : Dart Ω} (hab : DartRelated u v a b) : P a ↔ P b := by
    induction hab with
    | rel a b hab => exact ⟨next hab, next (dart_step_symm u v hab)⟩
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (invariant h).mp ⟨x,rfl,Equiv.Perm.SameCycle.refl _ _⟩

private theorem iterate_reachable (u v : G) (c : Fin 4) (x : Ω × Fin 3) (n : ℕ) :
    DartRelated u v (encode u v c x) (encode u v c ((tour u v c)^[n] x)) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.EqvGen.trans _ _ _ ih
      (Relation.EqvGen.rel _ _ ((coded_step u v c _ _).mpr (Or.inl rfl)))

/-- The exponent is an actual point return, with no equation in the acting group. -/
def pointPeriod (u v : G) (c : Fin 4) (x : Ω) : ℕ :=
  Function.minimalPeriod (fun y : Ω => act y (returnWord u v c)) x

private theorem iterate_tour (u v : G) (c : Fin 4) (x : Ω) (n : ℕ) :
    (tour u v c)^[n] (x,0) =
      ((fun y : Ω => act y (returnWord u v c))^[n/3] x, (n : Fin 3)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hm := Nat.mod_lt n (by decide : 0 < 3)
    have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn with hn | hn | hn
    · have hdiv : (n+1)/3 = n/3 := by omega
      have hphase : (n : Fin 3) = 0 := Fin.ext hn
      simp [tour, hphase, hdiv, Nat.cast_add, Nat.cast_one]
    · have hdiv : (n+1)/3 = n/3 := by omega
      have hphase : (n : Fin 3) = 1 := Fin.ext hn
      simp [tour, hphase, hdiv, Nat.cast_add, Nat.cast_one]
    · have hdiv : (n+1)/3 = n/3+1 := by omega
      have hphase : (n : Fin 3) = 2 := Fin.ext hn
      simp [tour, hphase, hdiv, Nat.cast_add, Nat.cast_one, Function.iterate_succ_apply']

private theorem tour_period (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Function.minimalPeriod (tour u v c) (x,0) = 3 * pointPeriod u v c x := by
  let R : Ω → Ω := fun y => act y (returnWord u v c)
  have hi : Function.Injective R := by
    intro a b h
    have hh := congrArg (fun y => act y (returnWord u v c)⁻¹) h
    simpa [R,act_mul] using hh
  have hr := Function.minimalPeriod_pos_of_mem_periodicPts (hi.mem_periodicPts x)
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts
    ((tour u v c).injective.mem_periodicPts (x,0))
  apply Nat.le_antisymm
  · have hr' : 0 < pointPeriod u v c x := hr
    apply Function.IsPeriodicPt.minimalPeriod_le (Nat.mul_pos (by decide) hr')
    change (tour u v c)^[3 * pointPeriod u v c x] (x,0) = (x,0)
    rw [iterate_tour]
    simp [pointPeriod, Function.iterate_minimalPeriod]
  · let m := Function.minimalPeriod (tour u v c) (x,0)
    have hret : (tour u v c)^[m] (x,0) = (x,0) := Function.iterate_minimalPeriod
    rw [iterate_tour] at hret
    have hmod : m % 3 = 0 := congrArg (fun z : Ω × Fin 3 => z.2.val) hret
    have hretR : R^[m/3] x = x := congrArg Prod.fst hret
    have hpos : 0 < m/3 := by dsimp [m] at *; omega
    have hle : pointPeriod u v c x ≤ m/3 :=
      Function.IsPeriodicPt.minimalPeriod_le hpos hretR
    change 3 * pointPeriod u v c x ≤ m
    omega

/-- The actual ordered dart at the indexed crossing, including the point-period wrap. -/
def occurrence (u v : G) (c : Fin 4) (x : Ω) (i : Fin (3 * pointPeriod u v c x)) : Dart Ω :=
  encode u v c ((tour u v c)^[i.val] (x,0))

/-- The entire original component, not a supplied cyclic subrelation. -/
theorem actual_component_enumeration (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    0 < pointPeriod u v c x ∧
    Function.Injective (occurrence u v c x) ∧
    (∀ d : Dart Ω, DartRelated u v (encode u v c (x,0)) d ↔
      ∃ i : Fin (3 * pointPeriod u v c x), occurrence u v c x i = d) ∧
    (∀ j k : Fin 4, j ≠ k ↔
      ∃! cs : Fin 4 × Fin 3, corner cs.1 cs.2 = j ∧ tip cs.1 cs.2 = k) ∧
    (∀ (y : Ω × Fin 3) (d : Dart Ω), DartStep u v (encode u v c y) d ↔
      d = encode u v c (tour u v c y) ∨ d = encode u v c ((tour u v c).symm y)) ∧
    Function.minimalPeriod (tour u v c) (x,0) = 3 * pointPeriod u v c x ∧
    (∀ i : Fin (3 * pointPeriod u v c x), occurrence u v c x i =
      encode u v c (((fun y : Ω => act y (returnWord u v c))^[i.val/3] x),
        (i.val : Fin 3))) := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts
    ((tour u v c).injective.mem_periodicPts (x,0))
  have hperiod := tour_period u v c x
  refine ⟨by omega, ?_, ?_, ?_, coded_step u v c, hperiod, ?_⟩
  · intro i j hij
    apply Fin.ext
    apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by omega : i.val < Function.minimalPeriod (tour u v c) (x,0))
      (by omega : j.val < Function.minimalPeriod (tour u v c) (x,0))).mp
    exact encode_injective u v c hij
  · intro d
    constructor
    · intro hd
      obtain ⟨y,rfl,hy⟩ := component_forward u v c (x,0) hd
      obtain ⟨n,hn⟩ := hy.exists_nat_pow_eq
      let m := Function.minimalPeriod (tour u v c) (x,0)
      have hm : n % m < m := Nat.mod_lt _ hp
      refine ⟨⟨n % m, by simpa only [m,hperiod] using hm⟩, ?_⟩
      dsimp [occurrence]
      rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hn]
    · rintro ⟨i,rfl⟩
      exact iterate_reachable u v c (x,0) i.val
  · intro j k
    fin_cases j <;> fin_cases k <;>
      simp [ExistsUnique, Prod.exists, Prod.forall, Fin.exists_fin_succ,
        Fin.forall_fin_succ, corner, tip]
  · intro i
    simp only [occurrence, iterate_tour]

end D5.S3.Geometry.Gluing.ActualCornerPointPeriods

/- GID: D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Alternating vectors give the honeycomb degree L-1 eigenvalue. -/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
admission_basis: open-problem-resolution (#28063; Proved)
Registration audit (CLAUDE.md §3.9): result is declared_unresolved (IE-C050);
the unfinished audit is recorded in issue #28118.
escape_witness: none; admission uses the external open-problem resolution.
direct_frozen_dependencies: none
Square.result denotes ChangShrockToroidalSquare.result in the same Potts namespace.
Coeff: proof_shape=definition; consumers=q,v,Space
q: proof_shape=definition; consumers=detach,result
v: proof_shape=definition; consumers=vertical,horizontal,result
Adjacent: proof_shape=definition; consumers=Native
Native: proof_shape=definition; consumers=State,ket
State: proof_shape=definition; consumers=Space
Space: proof_shape=definition; consumers=transfer,result
singletonState: proof_shape=definition; consumers=alternatingVector
ket: proof_shape=definition; consumers=join,detach
join: proof_shape=definition; consumers=horizontal,join_singleton_swap
detach: proof_shape=definition; consumers=vertical,detach_singleton
vertical: proof_shape=definition; consumers=transfer,vertical_singleton
horizontal: proof_shape=definition; consumers=transfer,horizontal_alternating
transfer: proof_shape=definition; consumers=result
alternatingVector: proof_shape=definition; consumers=result
singletonState_injective: proof_shape=bind-only; consumers=alternatingVector_ne_zero
alternatingVector_ne_zero: proof_shape=bind-only; consumers=result,Square.result
detach_singleton: proof_shape=bind-only; consumers=vertical_singleton
update_swap: proof_shape=bind-only; consumers=join_singleton_swap
join_singleton_swap: proof_shape=bind-only; consumers=join_alternating
join_alternating: proof_shape=bind-only; consumers=horizontal_alternating,Square.result
list_prod_on_vector: proof_shape=bind-only; consumers=vertical_singleton,
  horizontal_alternating,Square.result
vertical_singleton: proof_shape=bind-only; consumers=vertical_alternating
vertical_alternating: proof_shape=bind-only; consumers=result,Square.result
horizontal_alternating: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=registered claim #28063
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb

open scoped BigOperators
open Equiv

/-- The two independent Potts variables over the integers. -/
abbrev Coeff := MvPolynomial (Fin 2) ℤ

noncomputable def q : Coeff := MvPolynomial.X 0
noncomputable def v : Coeff := MvPolynomial.X 1

/-- Adjacency on the cyclic slice, including the seam. -/
def Adjacent {L : ℕ} (i j : Fin L) : Prop :=
  (i.val + 1) % L = j.val ∨ (j.val + 1) % L = i.val

/-- Zero denotes an unmarked singleton; other symbols are the distinct bridge labels.
At degree L-1 a diagram is a permutation, or has exactly one adjacent marked double block. -/
def Native (L : ℕ) [NeZero L] (f : Fin L → Fin L) : Prop :=
  (∃ σ : Perm (Fin L), f = σ) ∨
  ∃ (σ : Perm (Fin L)) (i j : Fin L),
    i ≠ j ∧ Adjacent i j ∧ σ i = 0 ∧ f = Function.update (σ : Fin L → Fin L) i (σ j)

abbrev State (L : ℕ) [NeZero L] := {f : Fin L → Fin L // Native L f}
abbrev Space (L : ℕ) [NeZero L] := State L →₀ Coeff

noncomputable section

variable {L : ℕ} [NeZero L]

private def singletonState (σ : Perm (Fin L)) : State L := ⟨σ, Or.inl ⟨σ, rfl⟩⟩

/-- A basis vector; diagrams outside this degree block are projected to zero. -/
def ket (f : Fin L → Fin L) : Space L :=
  open Classical in
  if h : Native L f then Finsupp.single ⟨f, h⟩ 1 else 0

/-- Join current components; distinct marked components cannot be joined in this block. -/
def join (i j : Fin L) : Module.End Coeff (Space L) :=
  Finsupp.linearCombination Coeff fun s =>
    if s.val i = s.val j then Finsupp.single s 1
    else if s.val i = 0 then ket (Function.update s.val i (s.val j))
    else if s.val j = 0 then ket (Function.update s.val j (s.val i))
    else 0

/-- Detach a site. Closing an unmarked component gives q; losing a bridge gives zero. -/
def detach (i : Fin L) : Module.End Coeff (Space L) :=
  Finsupp.linearCombination Coeff fun s =>
    if s.val i = 0 then q • Finsupp.single s 1
    else if ∃ j, j ≠ i ∧ s.val j = s.val i then ket (Function.update s.val i 0)
    else 0

/-- The longitudinal product in source equation (2.34), in increasing site order. -/
def vertical (L : ℕ) [NeZero L] : Module.End Coeff (Space L) :=
  (List.ofFn fun i : Fin L => v • (1 : Module.End Coeff (Space L)) + detach i).prod

/-- The two alternating bond products in source equation (2.34), with zero-based sites. -/
def horizontal (L : ℕ) [NeZero L] (second : Bool) : Module.End Coeff (Space L) :=
  (List.ofFn fun k : Fin (L / 2) =>
    (1 : Module.End Coeff (Space L)) + v •
      join (Fin.ofNat L (2 * k.val + if second then 1 else 0))
        (Fin.ofNat L (2 * k.val + (if second then 1 else 0) + 1))).prod

/-- The native degree L-1 honeycomb transfer operator, source equation (2.35). -/
def transfer (L : ℕ) [NeZero L] : Module.End Coeff (Space L) :=
  (vertical L * horizontal L true) * (vertical L * horizontal L false)

/-- The alternating sum over all arrangements of the unmarked symbol and bridge labels. -/
def alternatingVector (L : ℕ) [NeZero L] : Space L :=
  ∑ σ : Perm (Fin L),
    Finsupp.single (singletonState σ) (((Perm.sign σ : ℤˣ) : ℤ) : Coeff)

private theorem singletonState_injective :
    Function.Injective (singletonState : Perm (Fin L) → State L) := by
  intro σ τ h
  exact Equiv.ext (congrFun (congrArg Subtype.val h))

theorem alternatingVector_ne_zero : alternatingVector L ≠ 0 := by
  classical
  intro h
  have hh := congrArg (fun a : Space L => a (singletonState 1)) h
  have hcoeff : alternatingVector L (singletonState 1) = 1 := by
    simp [alternatingVector, Finsupp.single_apply, singletonState_injective.eq_iff]
  simp [hcoeff] at hh

private theorem detach_singleton (i : Fin L) (σ : Perm (Fin L)) (c : Coeff) :
    detach i (Finsupp.single (singletonState σ) c) =
      (if σ i = 0 then q else 0) • Finsupp.single (singletonState σ) c := by
  classical
  by_cases hi : σ i = 0 <;>
    simp [detach, singletonState, hi, mul_comm]

omit [NeZero L] in
private theorem update_swap (σ : Perm (Fin L)) (i j : Fin L) (hij : i ≠ j) :
    Function.update (σ * swap i j : Perm (Fin L)) j (σ j) =
      Function.update (σ : Fin L → Fin L) i (σ j) := by
  funext x
  by_cases hxi : x = i
  · subst x; simp [hij]
  by_cases hxj : x = j
  · subst x; simp [hij.symm]
  simp [Function.update_of_ne, hxi, hxj,
    swap_apply_of_ne_of_ne hxi hxj]

private theorem join_singleton_swap (i j : Fin L) (hij : i ≠ j)
    (σ : Perm (Fin L)) :
    join i j (Finsupp.single (singletonState (σ * swap i j)) 1) =
      join i j (Finsupp.single (singletonState σ) 1) := by
  classical
  have hσ : σ i ≠ σ j := σ.injective.ne hij
  have hsw : (σ * swap i j) i = σ j := by simp [Perm.mul_apply]
  have hsw' : (σ * swap i j) j = σ i := by simp [Perm.mul_apply]
  by_cases hi : σ i = 0
  · have hj : σ j ≠ 0 := by intro h; exact hσ (hi.trans h.symm)
    simp only [join, Finsupp.linearCombination_single, one_smul, singletonState,
      hsw, hsw', hi, hj, Ne.symm hj, ↓reduceIte]
    exact congrArg ket (update_swap σ i j hij)
  by_cases hj : σ j = 0
  · have heq := update_swap σ j i hij.symm
    rw [swap_comm j i] at heq
    simp only [join, Finsupp.linearCombination_single, one_smul, singletonState,
      hsw, hsw', hi, hj, Ne.symm hi, ↓reduceIte]
    exact congrArg ket heq
  · simp [join, singletonState, hσ, hσ.symm, hi, hj]

theorem join_alternating (i j : Fin L) (hij : i ≠ j) :
    join i j (alternatingVector L) = 0 := by
  classical
  simp only [alternatingVector, map_sum]
  let f : Perm (Fin L) → Space L := fun σ =>
    join i j (Finsupp.single (singletonState σ) (((Perm.sign σ : ℤˣ) : ℤ) : Coeff))
  change ∑ σ, f σ = 0
  apply Finset.sum_ninvolution (fun σ => σ * swap i j)
  · intro σ
    have hs : (((Perm.sign (σ * swap i j) : ℤˣ) : ℤ) : Coeff) =
        -(((Perm.sign σ : ℤˣ) : ℤ) : Coeff) := by
      simp [map_mul, Perm.sign_swap hij]
    have hsingle (τ : Perm (Fin L)) (c : Coeff) :
        Finsupp.single (singletonState τ) c = c • Finsupp.single (singletonState τ) 1 := by
      simp
    dsimp [f]
    rw [hs, hsingle σ, hsingle (σ * swap i j), map_smul, map_smul,
      join_singleton_swap i j hij σ]
    simp
  · intro σ _ h
    have hh : swap i j = (1 : Perm (Fin L)) :=
      mul_left_cancel (a := σ) (by simpa only [mul_one] using h)
    have hh' := congrArg (fun τ : Perm (Fin L) => τ i) hh
    simp at hh'
    exact hij hh'.symm
  · intro σ; exact Finset.mem_univ _
  · intro σ
    simp [mul_assoc]

theorem list_prod_on_vector {α : Type*} (xs : List α)
    (A : α → Module.End Coeff (Space L)) (c : α → Coeff) (w : Space L)
    (h : ∀ a ∈ xs, A a w = c a • w) :
    (xs.map A).prod w = (xs.map c).prod • w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih (fun b hb => h b (by simp [hb])), map_smul, h a (by simp), smul_smul]
    rw [mul_comm]

private theorem vertical_singleton (σ : Perm (Fin L)) (c : Coeff) :
    vertical L (Finsupp.single (singletonState σ) c) =
      (v ^ (L - 1) * (v + q)) • Finsupp.single (singletonState σ) c := by
  classical
  let a : Fin L → Coeff := fun i => v + if σ i = 0 then q else 0
  have ha : ∀ i : Fin L,
      (v • (1 : Module.End Coeff (Space L)) + detach i)
          (Finsupp.single (singletonState σ) c) =
        a i • Finsupp.single (singletonState σ) c := by
    intro i
    simp [a, detach_singleton, add_smul]
  have hprod : ∏ i : Fin L, a i = v ^ (L - 1) * (v + q) := by
    rw [Fintype.prod_equiv σ a (fun j => v + if j = 0 then q else 0) (fun _ => rfl)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin L => v + if j = 0 then q else 0)
      (Finset.mem_univ (0 : Fin L))]
    have he : ∏ j ∈ (Finset.univ : Finset (Fin L)).erase 0,
        (v + if j = 0 then q else 0) = v ^ (L - 1) := by
      calc
        _ = ∏ j ∈ (Finset.univ : Finset (Fin L)).erase 0, v := by
          apply Finset.prod_congr rfl
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
        _ = _ := by simp
    simp [he, mul_comm]
  have hh := list_prod_on_vector (List.finRange L)
    (fun i => v • (1 : Module.End Coeff (Space L)) + detach i) a
    (Finsupp.single (singletonState σ) c) (fun i _ => ha i)
  simpa only [← List.ofFn_eq_map, Fin.prod_ofFn, hprod, vertical] using hh

theorem vertical_alternating :
    vertical L (alternatingVector L) =
      (v ^ (L - 1) * (v + q)) • alternatingVector L := by
  classical
  simp only [alternatingVector, map_sum, vertical_singleton, Finset.smul_sum]

private theorem horizontal_alternating (second : Bool) :
    horizontal L second (alternatingVector L) = alternatingVector L := by
  classical
  let A : Fin (L / 2) → Module.End Coeff (Space L) := fun k =>
    1 + v • join (Fin.ofNat L (2 * k.val + if second then 1 else 0))
      (Fin.ofNat L (2 * k.val + (if second then 1 else 0) + 1))
  have hne (k : Fin (L / 2)) :
      (Fin.ofNat L (2 * k.val + if second then 1 else 0)) ≠
        (Fin.ofNat L (2 * k.val + (if second then 1 else 0) + 1)) := by
    intro h
    have hh := congrArg Fin.val h
    have hk := k.isLt
    change (2 * k.val + if second then 1 else 0) % L =
      (2 * k.val + (if second then 1 else 0) + 1) % L at hh
    have hkbound : 2 * k.val + 1 < L := by omega
    cases second
    · change (2 * k.val) % L = (2 * k.val + 1) % L at hh
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hkbound] at hh
      omega
    · change (2 * k.val + 1) % L = (2 * k.val + 2) % L at hh
      rw [Nat.mod_eq_of_lt hkbound] at hh
      by_cases he : 2 * k.val + 2 = L
      · rw [he, Nat.mod_self] at hh; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hh; omega
  have ha : ∀ k, A k (alternatingVector L) = (1 : Coeff) • alternatingVector L := by
    intro k
    change alternatingVector L + v • (join _ _) (alternatingVector L) = _
    rw [join_alternating _ _ (hne k)]
    simp
  have hh := list_prod_on_vector (List.finRange (L / 2)) A (fun _ => 1)
    (alternatingVector L) (fun k _ => ha k)
  simpa [← List.ofFn_eq_map, horizontal, A] using hh

/-- Every even honeycomb width has the source eigenvalue in the native degree L-1 block. -/
theorem result (L : ℕ) (hL : 2 ≤ L) (_hEven : Even L) :
    letI : NeZero L := ⟨by omega⟩
    ∃ w : Space L, w ≠ 0 ∧ transfer L w = (v ^ (2 * (L - 1)) * (v + q) ^ 2) • w := by
  let : NeZero L := ⟨by omega⟩
  refine ⟨alternatingVector L, alternatingVector_ne_zero, ?_⟩
  simp only [transfer, Module.End.mul_apply]
  rw [horizontal_alternating false, vertical_alternating, map_smul,
    horizontal_alternating true, map_smul, vertical_alternating, smul_smul]
  congr 1
  rw [pow_mul]
  ring

end
end D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb

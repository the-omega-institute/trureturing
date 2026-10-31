/- GID: D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/CFMPCoxeterIndexObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.claim; result=D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.result; claim=D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.claim
   digest: Native torsionfree orientation quotients of the Coxeter group [4,9,3] cannot have index seventy-two. -/

import D5.S3.FiniteGroups.CycleNineThreeObstruction
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.FinCases

/-! # The native index-seventy-two Coxeter obstruction -/

namespace D5.S3.FiniteGroups.CFMPCoxeterIndexObstruction

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The Coxeter matrix with string labels four, nine and three. -/
def diagram : CoxeterMatrix (Fin 4) where
  M := !![1, 4, 2, 2; 4, 1, 9, 2; 2, 9, 1, 3; 2, 2, 3, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal i j h := by fin_cases i <;> fin_cases j <;> norm_num at *

abbrev W := diagram.Group
abbrev canonical := diagram.toCoxeterSystem

/-- The even subgroup, the kernel of the homomorphism sending every reflection to minus one. -/
def orientation : Subgroup W := canonical.lengthParity.ker

/-- Existence of a torsionfree normal subgroup of orientation index seventy-two. -/
def claim : Prop := ∃ Γ : Subgroup orientation,
  Γ.Normal ∧ IsMulTorsionFree Γ ∧ Γ.index = 72

private def reflection (i : Fin 4) : Matrix (Fin 3) (Fin 3) (ZMod 19) :=
  if i = 0 then 1 else if i = 1 then !![-1,12,0;0,1,0;0,0,1]
  else if i = 2 then !![1,0,0;12,-1,1;0,0,1]
  else !![1,0,0;0,1,0;0,1,-1]

private theorem reflection_relations : diagram.IsLiftable reflection := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private def representation : W →* Matrix (Fin 3) (Fin 3) (ZMod 19) :=
  canonical.lift ⟨reflection, reflection_relations⟩

private theorem pair_order (i j : Fin 4) (n : ℕ)
    (hn : diagram i j = n)
    (hsep : orderOf (reflection i * reflection j) = n) :
    orderOf (canonical.simple i * canonical.simple j) = n := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    simpa only [← hn] using canonical.simple_mul_simple_pow i j
  · have h := orderOf_map_dvd representation (canonical.simple i * canonical.simple j)
    simpa only [map_mul, representation, CoxeterSystem.lift_apply_simple, hsep] using h

private theorem native_orders :
    orderOf (canonical.simple 1 * canonical.simple 2) = 9 ∧
    orderOf (canonical.simple 2 * canonical.simple 3) = 3 ∧
    orderOf (canonical.simple 1 * canonical.simple 3) = 2 := by
  refine ⟨pair_order 1 2 9 rfl ?_, pair_order 2 3 3 rfl ?_, pair_order 1 3 2 rfl ?_⟩
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
    intro p hp hd
    have hd3 : p ∣ 3 := hp.dvd_of_dvd_pow (m := 3) (n := 2) (by simpa using hd)
    have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd3
    subst p
    decide
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
    intro p hp hd
    have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    subst p
    decide
  · apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (by decide)
    intro p hp hd
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd
    subst p
    decide

private theorem quotient_order {G : Type*} [Group G]
    (Γ : Subgroup G) [Γ.Normal] [IsMulTorsionFree Γ] (x : G) (hx : IsOfFinOrder x) :
    orderOf (QuotientGroup.mk' Γ x) = orderOf x := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  constructor
  · intro h
    have hxmem : x ^ n ∈ Γ := (QuotientGroup.eq_one_iff (x ^ n)).mp (by
      change (QuotientGroup.mk' Γ) (x ^ n) = 1
      rw [map_pow]
      exact h)
    let y : Γ := ⟨x ^ n, hxmem⟩
    have hy : IsOfFinOrder y := by
      obtain ⟨k, hk, he⟩ := (hx.pow (n := n)).exists_pow_eq_one
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, Subtype.ext he⟩
    exact congrArg Subtype.val (IsOfFinOrder.eq_one' hy)
  · intro h
    rw [← map_pow, h, map_one]

private def pair (i j : Fin 4) : orientation :=
  ⟨canonical.simple i * canonical.simple j, by
    change canonical.lengthParity _ = 1
    rw [map_mul, CoxeterSystem.lengthParity_simple, CoxeterSystem.lengthParity_simple]
    decide⟩

/-- The native six-sector subgroup. -/
def blockGroup : Subgroup W :=
  Subgroup.closure ({canonical.simple 2, canonical.simple 3} : Set W)

private def C : blockGroup := ⟨canonical.simple 2, Subgroup.subset_closure (by simp)⟩
private def D : blockGroup := ⟨canonical.simple 3, Subgroup.subset_closure (by simp)⟩

private def normalWord (n : Fin 6) : blockGroup := ![1, C, D, C * D, D * C, C * D * C] n

private def step (n : Fin 6) (j : Fin 2) : Fin 6 :=
  if j = 0 then ![1,0,4,5,2,3] n else ![2,3,0,1,5,4] n

private theorem normal_step (n : Fin 6) (j : Fin 2) :
    normalWord n * (if j = 0 then C else D) = normalWord (step n j) := by
  have hcc : C * C = 1 := Subtype.ext (canonical.simple_mul_simple_self 2)
  have hdd : D * D = 1 := Subtype.ext (canonical.simple_mul_simple_self 3)
  have hbraid : C * D * C = D * C * D := by
    apply Subtype.ext
    have h := canonical.wordProd_braidWord_eq 2 3
    change canonical.simple 2 * (canonical.simple 3 * (canonical.simple 2 * 1)) =
      canonical.simple 3 * (canonical.simple 2 * (canonical.simple 3 * 1)) at h
    simpa only [mul_one, mul_assoc, C, D, Subgroup.coe_mul] using h
  fin_cases n <;> fin_cases j <;>
    simp [normalWord, step, ← mul_assoc, hcc, hdd, hbraid]

private theorem normalWord_surjective : Function.Surjective normalWord := by
  intro x
  have hstep (w : W) (hw : w ∈ blockGroup) (y : W)
      (hy : y ∈ ({canonical.simple 2, canonical.simple 3} : Set W))
      (ih : ∃ n, (normalWord n : W) = w) :
      ∃ n, (normalWord n : W) = w * y := by
    obtain ⟨n, hn⟩ := ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · refine ⟨step n 0, ?_⟩
      rw [← hn]
      exact congrArg Subtype.val (normal_step n 0).symm
    · refine ⟨step n 1, ?_⟩
      rw [← hn]
      exact congrArg Subtype.val (normal_step n 1).symm
  have hx : ∃ n, (normalWord n : W) = (x : W) := by
    apply Subgroup.closure_induction_right (s := {canonical.simple 2, canonical.simple 3})
      (p := fun w _ => ∃ n, (normalWord n : W) = w) ?_ hstep ?_ x.property
    · exact ⟨0, rfl⟩
    · intro w hw y hy ih
      have hiy : y⁻¹ = y := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl <;> exact canonical.inv_simple _
      rw [hiy]
      exact hstep w hw y hy ih
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, Subtype.ext hn⟩

private def permReflection (i : Fin 4) : Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 1 2] i

private theorem perm_relations : diagram.IsLiftable permReflection := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private def permRepresentation : W →* Equiv.Perm (Fin 3) :=
  canonical.lift ⟨permReflection, perm_relations⟩

private def permWord (n : Fin 6) : Equiv.Perm (Fin 3) :=
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let d : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  ![1, c, d, c*d, d*c, c*d*c] n

private theorem map_normalWord (n : Fin 6) :
    permRepresentation (normalWord n : W) = permWord n := by
  fin_cases n <;> simp [normalWord, permWord, C, D, permRepresentation, permReflection]

private theorem permWord_bijective : Function.Bijective permWord := by decide

/-- The two last native reflections generate a copy of the symmetric group on three letters. -/
noncomputable def blockGroupEquiv : blockGroup ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (permRepresentation.comp blockGroup.subtype) (by
    constructor
    · intro x y hxy
      obtain ⟨i, rfl⟩ := normalWord_surjective x
      obtain ⟨j, rfl⟩ := normalWord_surjective y
      have hij : i = j := permWord_bijective.1 (by
        simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, map_normalWord] using hxy)
      exact congrArg normalWord hij
    · intro p
      obtain ⟨n, hn⟩ := permWord_bijective.2 p
      exact ⟨normalWord n, (map_normalWord n).trans hn⟩)

private theorem blockGroup_card : Nat.card blockGroup = 6 := by
  rw [Nat.card_congr blockGroupEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

/-- The normal orientation quotient of order seventy-two is impossible. -/
theorem result : ¬ claim := by
  rintro ⟨Γ, hn, htf, hidx⟩
  letI := hn
  letI := htf
  letI : Γ.FiniteIndex := ⟨by omega⟩
  let Q := orientation ⧸ Γ
  let q : orientation →* Q := QuotientGroup.mk' Γ
  let r : orientation := pair 1 2
  let s : orientation := pair 2 3
  have hr : orderOf r = 9 := by
    simpa only [r, pair, Subgroup.orderOf_mk] using native_orders.1
  have hs : orderOf s = 3 := by
    simpa only [s, pair, Subgroup.orderOf_mk] using native_orders.2.1
  have hrs : orderOf (r * s) = 2 := by
    have he : r * s = pair 1 3 := by
      apply Subtype.ext
      change (canonical.simple 1 * canonical.simple 2) *
        (canonical.simple 2 * canonical.simple 3) = canonical.simple 1 * canonical.simple 3
      rw [mul_assoc, CoxeterSystem.simple_mul_simple_cancel_left]
    rw [he]
    simpa only [pair, Subgroup.orderOf_mk] using native_orders.2.2
  have hqr : orderOf (q r) = 9 := (quotient_order Γ r (by
    rw [← orderOf_pos_iff, hr]; decide)).trans hr
  have hqs : orderOf (q s) = 3 := (quotient_order Γ s (by
    rw [← orderOf_pos_iff, hs]; decide)).trans hs
  have hqrs : orderOf (q r * q s) = 2 := by
    rw [← map_mul]
    exact (quotient_order Γ (r * s) (by rw [← orderOf_pos_iff, hrs]; decide)).trans hrs
  let H : Subgroup Q := Subgroup.closure ({q r, q s} : Set Q)
  let R : H := ⟨q r, Subgroup.subset_closure (by simp)⟩
  let S : H := ⟨q s, Subgroup.subset_closure (by simp)⟩
  have hgen : Subgroup.closure ({R, S} : Set H) = ⊤ := by
    apply Subgroup.map_injective (f := H.subtype) Subtype.val_injective
    simp only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      Subgroup.map_top, Subgroup.range_subtype]
    rfl
  have hcard : Nat.card H ∣ 72 := by
    have hh : Nat.card Q = 72 := hidx
    rw [← hh]
    exact H.card_subgroup_dvd_card
  exact CycleNineThreeObstruction.result R S hgen hcard
    (by simpa only [R, Subgroup.orderOf_mk] using hqr)
    (by simpa only [S, Subgroup.orderOf_mk] using hqs)
    ((Subgroup.orderOf_coe (R * S)).symm.trans hqrs)

#print axioms result

end D5.S3.FiniteGroups.CFMPCoxeterIndexObstruction

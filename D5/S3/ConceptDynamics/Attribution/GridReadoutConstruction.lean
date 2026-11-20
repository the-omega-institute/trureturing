/- GID: D5/S3/ConceptDynamics/Attribution/GridReadoutConstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/GridReadoutConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equivariant calibration from common scaled stabilizer-block allocations. -/

import D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility
import D5.S3.ConceptDynamics.Attribution.ThreeOutcomeGridSupport
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Group

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

namespace StabilizerBlockCount

open Finset
open scoped Nat

private theorem factorial_merge (a b : ℕ) (apos : 0 < a) :
    (a)! * (b + 1)! ≤ (a + b)! := by
  induction b with
  | zero => simp
  | succ n ih =>
    calc
      (a)! * (n + 1 + 1)! = (n + 1 + 1) * ((a)! * (n + 1)!) := by
        rw [Nat.factorial_succ (n + 1)]
        ac_rfl
      _ ≤ (a + n + 1) * (a + n)! := Nat.mul_le_mul (by omega) ih
      _ = _ := by rw [← Nat.factorial_succ, Nat.add_assoc]

private theorem prod_factorials_bound {I : Type*} (indices : Finset I) (offset : I → ℕ) :
    (∏ i ∈ indices, (offset i + 1)!) ≤ ((∑ i ∈ indices, offset i) + 1)! := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert j indices hj ih =>
    rw [prod_insert hj, sum_insert hj]
    calc
      (offset j + 1)! * (∏ i ∈ indices, (offset i + 1)!)
          ≤ ((∑ i ∈ indices, offset i) + 1)! * (offset j + 1)! := by
            calc
              _ ≤ (offset j + 1)! * ((∑ i ∈ indices, offset i) + 1)! := Nat.mul_le_mul_left _ ih
              _ = _ := Nat.mul_comm _ _
      _ ≤ ((∑ i ∈ indices, offset i) + 1 + offset j)! :=
        factorial_merge _ _ (Nat.succ_pos _)
      _ = _ := by congr 1; omega

private theorem block_count_lower {I : Type*} [Fintype I] (s : I → ℕ) (pos : ∀ i, 0 < s i)
    (twoGroups : 2 ≤ Fintype.card I) {k : ℕ} (total : ∑ i, s i = k) :
    k * (Fintype.card I - 1) ≤ (k)! / (∏ i, (s i)!) := by
  let t := Fintype.card I
  let extra (i : I) := s i - 1
  have each (i : I) : extra i + 1 = s i := Nat.sub_add_cancel (pos i)
  have count : (∑ i, extra i) + t = k := by
    have sumEquality : (∑ i, (extra i + 1)) = ∑ i, s i :=
      Finset.sum_congr rfl (fun i _ => each i)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.cast_id, Nat.mul_one, total] using sumEquality
  have part :
      (∏ i, (s i)!) ≤ (k - t + 1)! := by
    have h := prod_factorials_bound (Finset.univ : Finset I) extra
    simp only [each] at h
    have eq : (∑ i, extra i) = k - t := by omega
    rwa [eq] at h
  have tBound : t ≤ k := by omega
  have kPos : 0 < k := by omega
  have prev : (k - 1)! * k = k ! :=
    (Nat.mul_comm _ _).trans (Nat.mul_factorial_pred kPos.ne')
  have intermediate : (k - t + 1)! * (t - 1) ≤ (k - 1)! := by
    by_cases ht : t = 2
    · have h1 : k - t + 1 = k - 1 := by omega
      rw [h1, ht]
      simp
    · have less : k - t + 1 ≤ k - 2 := by omega
      calc
        (k - t + 1)! * (t - 1) ≤ (k - 2)! * (k - 1) :=
          Nat.mul_le_mul (Nat.factorial_le less) (by omega)
        _ = (k - 1)! := by
          simpa only [Nat.mul_comm, show k - 1 - 1 = k - 2 by omega] using
            (Nat.mul_factorial_pred (n := k - 1) (by omega))
  have orderPositive : 0 < ∏ i, (s i)! := Nat.prod_factorial_pos Finset.univ s
  rw [Nat.le_div_iff_mul_le orderPositive]
  calc
    k * (Fintype.card I - 1) * (∏ i, (s i)!) = (∏ i, (s i)!) * (t - 1) * k := by dsimp [t]; ac_rfl
    _ ≤ ((k - t + 1)! * (t - 1)) * k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ part)
    _ ≤ (k - 1)! * k := Nat.mul_le_mul_right _ intermediate
    _ = _ := prev

end StabilizerBlockCount

open Finset
open scoped Nat

namespace ProfileStabilizer

def Preserving {I : Type*} (p : I → ℕ) : Subgroup (Equiv.Perm I) where
  carrier := {g | p ∘ g = p}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change p ∘ g = p at hg
    change p ∘ h = p at hh
    funext i
    change p (g (h i)) = p i
    exact (congrFun hg (h i)).trans (congrFun hh i)
  inv_mem' {g} hg := by
    change p ∘ g = p at hg
    funext i
    change p (g⁻¹ i) = p i
    have eq := (congrFun hg (g⁻¹ i)).symm
    simpa only [Function.comp_apply, show g (g⁻¹ i) = i from g.apply_symm_apply i] using eq

abbrev Groups {I : Type*} [Fintype I] (p : I → ℕ) :=
  ↥(univ.image p)

abbrev groupOf {I : Type*} [Fintype I] (p : I → ℕ) (i : I) : Groups p :=
  ⟨p i, mem_image_of_mem p (mem_univ _)⟩

abbrev size {I : Type*} [Fintype I] (p : I → ℕ) (b : Groups p) :=
  Fintype.card {i : I // p i = b.val}

private theorem size_positive {I : Type*} [Fintype I] (p : I → ℕ) (b : Groups p) :
    0 < size p b := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp b.property
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

private def fiberEquiv {I : Type*} [Fintype I] (p : I → ℕ) (b : Groups p) :
    {i : I // groupOf p i = b} ≃ {i : I // p i = b.val} :=
  Equiv.subtypeEquiv (Equiv.refl I) fun i => by
    change groupOf p i = b ↔ p i = b.val
    exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩

private def sigmaGroupsEquiv {I : Type*} [Fintype I] (p : I → ℕ) :
    (Σ b : Groups p, {i : I // p i = b.val}) ≃ I :=
  (Equiv.sigmaCongrRight (fiberEquiv p · |>.symm)).trans (Equiv.sigmaFiberEquiv (groupOf p))

private theorem size_sum {I : Type*} [Fintype I] (p : I → ℕ) : ∑ b, size p b = Fintype.card I := by
  simpa only [Fintype.card_sigma, size] using Fintype.card_congr (sigmaGroupsEquiv p)

private theorem group_mass {I : Type*} [Fintype I] (p : I → ℕ) :
    ∑ b : Groups p, size p b * b.val = ∑ i, p i := by
  calc
    _ = ∑ b : Groups p, ∑ i : {i : I // p i = b.val}, p i.val := by
      apply sum_congr rfl
      intro b _
      have constSum : (∑ i : {i : I // p i = b.val}, p i.val) =
          ∑ _i : {i : I // p i = b.val}, b.val :=
        sum_congr rfl fun i _ => i.property
      simp only [constSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ = _ := by
      rw [← Fintype.sum_sigma']
      have eq (z : Σ b : Groups p, {i : I // p i = b.val}) :
          sigmaGroupsEquiv p z = z.2.val := by
        cases z
        rfl
      simpa only [eq] using (sigmaGroupsEquiv p).sum_comp p

noncomputable instance {I : Type*} [Fintype I] (p : I → ℕ) : Fintype (Preserving p) :=
  Fintype.ofFinite _

private theorem preserving_card {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ) :
    Fintype.card (Preserving p) = ∏ b : Groups p, (size p b)! := by
  classical
  calc
    _ = ∏ b ∈ univ.image p, (Fintype.card {i : I // p i = b})! :=
      by
        have h := DomMulAct.stabilizer_card' p
        rw [← Nat.card_eq_fintype_card] at h ⊢
        exact h
    _ = _ := by
      exact (Finset.prod_coe_sort (univ.image p) (fun b => (Fintype.card {i : I // p i = b})!)).symm

private theorem preserving_smul {I : Type*} (p : I → ℕ) (g : Preserving p) (i : I) :
    p (g • i) = p i := by
  exact congrFun g.property i

private theorem swap_mem {I : Type*} [DecidableEq I] (p : I → ℕ) {i j : I} (h : p i = p j) :
    Equiv.swap i j ∈ Preserving p := by
  change p ∘ Equiv.swap i j = p
  funext a
  change p (Equiv.swap i j a) = p a
  by_cases atI : a = i
  · subst a
    rw [Equiv.swap_apply_left, h]
  · by_cases atJ : a = j
    · subst a
      rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne atI atJ]

private theorem orbit_eq_fiber {I : Type*} [DecidableEq I] (p : I → ℕ) (i : I) :
    MulAction.orbit (Preserving p) i = {j | p j = p i} := by
  ext j
  constructor
  · rintro ⟨g, hg⟩
    change g • i = j at hg
    rw [← hg]
    exact preserving_smul p g i
  · intro eq
    refine ⟨⟨Equiv.swap i j, swap_mem p eq.symm⟩, ?_⟩
    exact Equiv.swap_apply_left i j

private noncomputable def orbitEquivGroups {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ) :
    MulAction.orbitRel.Quotient (Preserving p) I ≃ Groups p := by
  let toGroup := Quotient.lift (s := MulAction.orbitRel (Preserving p) I) (groupOf p) (fun i j related => by
    have hj := (MulAction.orbitRel_apply (G := Preserving p)).mp related
    apply Subtype.ext
    rw [orbit_eq_fiber] at hj
    exact hj)
  refine Equiv.ofBijective toGroup ⟨?_, ?_⟩
  · intro x y
    induction x, y using Quotient.inductionOn₂' with
    | _ i j =>
      intro h
      apply Quotient.sound'
      change i ∈ MulAction.orbit (Preserving p) j
      rw [orbit_eq_fiber]
      exact congrArg Subtype.val h
  · intro b
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp b.property
    refine ⟨Quotient.mk'' i, ?_⟩
    exact Subtype.ext hi

private theorem orbitEquivGroups_mk {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ) (i : I) :
    orbitEquivGroups p (Quotient.mk'' i) = groupOf p i := rfl

theorem stabilizer_count_product {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ) (i : I)
    [Fintype (MulAction.stabilizer (Preserving p) i)] :
    size p (groupOf p i) * Fintype.card (MulAction.stabilizer (Preserving p) i) = Fintype.card (Preserving p) := by
  classical
  let _ : Fintype (MulAction.orbit (Preserving p) i) := Fintype.ofFinite _
  have C := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Preserving p) i
  have eq := Fintype.card_congr (Set.equivOfEq (orbit_eq_fiber p i))
  rwa [eq] at C

theorem regular_subgroup_free {I : Type*} (p : I → ℕ) (g : Equiv.Perm I) :
    MulAction.stabilizer (Preserving p) g = ⊥ :=
  IsCancelSMul.stabilizer_eq_bot g

end ProfileStabilizer

open Finset

namespace FreeActionAllocations

private noncomputable def fiberEquivStabilizer {G Y : Type*} [Group G] [MulAction G Y]
    {x y : Y} (reachable : y ∈ MulAction.orbit G x) :
    {g : G // g • x = y} ≃ MulAction.stabilizer G y := by
  classical
  let a := reachable.choose
  have ha : a • x = y := reachable.choose_spec
  refine Equiv.subtypeEquiv (Equiv.mulRight a⁻¹) (fun g => ?_)
  change g • x = y ↔ (g * a⁻¹) • y = y
  rw [mul_smul, ← ha, inv_smul_smul]

private theorem sum_group_fiber {G Y : Type*} [Group G] [Fintype G] [DecidableEq Y] [MulAction G Y]
    [DecidableEq (MulAction.orbitRel.Quotient G Y)]
    (x y : Y) [Fintype (MulAction.stabilizer G y)] :
    (∑ g : G, if g • x = y then (1 : ℕ) else 0) = if (Quotient.mk'' x : MulAction.orbitRel.Quotient G Y) = Quotient.mk'' y
      then Fintype.card (MulAction.stabilizer G y) else 0 := by
  classical
  rw [Finset.sum_boole]
  split
  · rename_i equal
    have reachable : y ∈ MulAction.orbit G x := Quotient.exact' equal.symm
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (fiberEquivStabilizer reachable)
  · rename_i different
    have empty : (univ.filter fun g : G => g • x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g h
      have he := (Finset.mem_filter.mp h).2
      apply different
      refine Quotient.sound' (show x ∈ MulAction.orbit G y from ⟨g⁻¹, ?_⟩)
      change g⁻¹ • y = x
      rw [← he, inv_smul_smul]
    simp only [empty, Finset.card_empty, Nat.cast_zero]

private theorem reindex_smul {G X : Type*} [Group G] [MulAction G X]
    (free : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (j : MulAction.orbitRel.Quotient G X) (g h : G) :
    (MulAction.selfEquivOrbitsQuotientProd free).symm (j, g * h) = g • (MulAction.selfEquivOrbitsQuotientProd free).symm (j, h) := by
  change (g * h) • j.out = g • (h • j.out)
  exact mul_smul _ _ _

/-- On a finite free action, assigning source orbits to target orbits realizes each target
point with multiplicity equal to its stabilizer order times the assigned source - orbit count. -/
private theorem equivariant_readout_of_orbit_counts
    {G X Y : Type*} [Group G] [Fintype G] [Fintype X] [Fintype Y] [DecidableEq Y]
    [MulAction G X] [MulAction G Y]
    [Fintype (MulAction.orbitRel.Quotient G Y)]
    (free : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (a : MulAction.orbitRel.Quotient G Y → ℕ)
    (total : (∑ j, a j) = Fintype.card X / Fintype.card G) :
    ∃ f : X → Y, (∀ (g : G) x, f (g • x) = g • f x) ∧
      ∀ y, (∑ x, if f x = y then (1 : ℕ) else 0) = a (Quotient.mk'' y) * Fintype.card (MulAction.stabilizer G y) := by
  classical
  let Q := MulAction.orbitRel.Quotient G X
  let _ : Fintype Q := Fintype.ofFinite Q
  let O := MulAction.orbitRel.Quotient G Y
  let e := MulAction.selfEquivOrbitsQuotientProd free
  have hQ : Fintype.card X = Fintype.card Q * Fintype.card G := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  have gPos : 0 < Fintype.card G := Fintype.card_pos
  have cards : Fintype.card Q = Fintype.card (Σ j : O, Fin (a j)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [total, hQ, Nat.mul_div_cancel _ gPos]
  let assign := Fintype.equivOfCardEq cards
  let E := e.trans (assign.prodCongr (Equiv.refl G))
  let f (x : X) : Y := (E x).2 • (E x).1.1.out
  refine ⟨f, ?_, ?_⟩
  · intro g x
    obtain ⟨⟨j, h⟩, rfl⟩ := e.symm.surjective x
    change f (g • e.symm (j, h)) = _
    rw [← reindex_smul free j g h]
    have n (u : G) : f (e.symm (j, u)) = u • (assign j).1.out := by
      simp [f, E, Equiv.trans_apply]
    rw [n, n, mul_smul]
  · intro y
    rw [← E.symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_sigma]
    have n (j : Σ j : O, Fin (a j)) (g : G) : f (E.symm (j, g)) = g • j.1.out := by
      simp [f]
    simp only [n, sum_group_fiber, Quotient.out_eq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    rw [Finset.sum_eq_single_of_mem (Quotient.mk'' y) (mem_univ _) (fun j _ ne => by
      simp only [ite_eq_right ne, Nat.mul_zero])]
    simp

theorem equivariant_fiber_size {G X Y : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq Y] [MulAction G X] [MulAction G Y]
    (free : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (f : X → Y) (equivariant : ∀ (g : G) x, f (g • x) = g • f x)
    (y : Y) [Fintype (MulAction.stabilizer G y)] :
    ∃ t ≤ Fintype.card X / Fintype.card G,
      (∑ x, if f x = y then (1 : ℕ) else 0) = t * Fintype.card (MulAction.stabilizer G y) := by
  classical
  let Q := MulAction.orbitRel.Quotient G X
  let _ : Fintype Q := Fintype.ofFinite Q
  let e := MulAction.selfEquivOrbitsQuotientProd free
  have hQ : Fintype.card X = Fintype.card Q * Fintype.card G := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  have gPos : 0 < Fintype.card G := Fintype.card_pos
  let accepts (j : Q) : Prop :=
    (Quotient.mk'' (f j.out) : MulAction.orbitRel.Quotient G Y) = Quotient.mk'' y
  let t := (univ.filter accepts).card
  refine ⟨t, ?_, ?_⟩
  · rw [hQ, Nat.mul_div_cancel _ gPos]
    exact Finset.card_le_univ _
  · rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    calc
      _ = ∑ j : Q, ∑ g : G, if g • f j.out = y then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro j _
        apply sum_congr rfl
        intro g _
        change (if f (g • j.out) = y then (1 : ℕ) else 0) = _
        rw [equivariant]
      _ = ∑ j : Q, if accepts j then Fintype.card (MulAction.stabilizer G y) else 0 :=
        sum_congr rfl (fun j _ => sum_group_fiber (f j.out) y)
      _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

end FreeActionAllocations

open Finset

namespace PermutationGrid

abbrev Profile (I : Type*) [Fintype I] (m : ℕ) :=
  {p : I → ℕ // ∑ i, p i = m}

abbrev relabel {I : Type*} [Fintype I] {m : ℕ} (g : Equiv.Perm I) (p : Profile I m) :
    Profile I m :=
  ⟨fun i => p.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Equiv.Perm I) p.val).trans p.property⟩

end PermutationGrid

open Finset
open scoped Nat

private theorem local_scaled_readout {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {n m c : ℕ} {w : Fin n → ℕ}
    (cover : ∀ t U : ℕ, 0 < t → Fintype.card I * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
      Fintype.card I * (Fintype.card I - 1) * (∑ i, x i) = U * m →
      ∃ a : Fin n → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
        (∀ i, ∑ j, a j i * w j = c * x i))
    (p : I → ℕ) (total : ∑ i, p i = m) (divisible : Fintype.card I - 1 ∣ m)
    (atLeastTwo : 2 ≤ Fintype.card I) :
    ∃ f : Fin n → Equiv.Perm I → I,
      (∀ (h : ProfileStabilizer.Preserving p) j g, f j (h • g) = h • f j g) ∧
      ∀ i, ∑ j, (∑ g, if f j g = i then w j else 0) =
        (c * (Fintype.card I - 2)!) * p i := by
  classical
  open ProfileStabilizer in
  let G := Preserving p
  open ProfileStabilizer in
  let B := Groups p
  let k := Fintype.card I
  let D := (k - 2)!
  let H := Fintype.card G
  let U := (k)! / H
  let d (b : B) := D * (ProfileStabilizer.size p b * b.val) / H
  have Hpos : 0 < H := Fintype.card_pos
  have Hfact : H = ∏ b : B, (ProfileStabilizer.size p b)! :=
    ProfileStabilizer.preserving_card p
  have Hdiv : H ∣ (k)! := by
    rw [Hfact]
    have h := Nat.prod_factorial_dvd_factorial_sum univ (ProfileStabilizer.size p)
    rwa [ProfileStabilizer.size_sum] at h
  have HU : U * H = (k)! := Nat.div_mul_cancel Hdiv
  have divide (b : B) : H ∣ D * (ProfileStabilizer.size p b * b.val) := by
    rw [Hfact]
    apply D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility.factorial_product_dvd_scaled_coordinate
      (ProfileStabilizer.size p) Subtype.val (ProfileStabilizer.size_sum p)
    simpa only [ProfileStabilizer.group_mass, total] using divisible
  have demand (b : B) : d b * H = D * (ProfileStabilizer.size p b * b.val) :=
    Nat.div_mul_cancel (divide b)
  have kfact : (k)! = D * k * (k - 1) := by
    have step (a : ℕ) (apos : 0 < a) : a ! = a * (a - 1)! := by
      conv_lhs => rw [← Nat.sub_add_cancel apos]
      rw [Nat.factorial_succ, Nat.sub_add_cancel apos]
    rw [step k (by omega), step (k - 1) (by omega)]
    dsimp [D]
    rw [show k - 1 - 1 = k - 2 by omega]
    ac_rfl
  have dtotal : k * (k - 1) * (∑ b : B, d b) = U * m := by
    have sumDemand : (∑ b : B, d b) * H = D * m := by
      rw [Finset.sum_mul]
      calc
        ∑ b : B, d b * H = ∑ b : B, D * (ProfileStabilizer.size p b * b.val) :=
          Finset.sum_congr rfl fun b _ => demand b
        _ = _ := by rw [← Finset.mul_sum, ProfileStabilizer.group_mass, total]
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (k - 2))
    calc
      D * (k * (k - 1) * (∑ b : B, d b)) = (k)! * (∑ b : B, d b) := by rw [kfact]; ac_rfl
      _ = U * ((∑ b : B, d b) * H) := by rw [← HU]; ac_rfl
      _ = D * (U * m) := by rw [sumDemand]; ac_rfl
  let t := Fintype.card B
  let e := Fintype.equivFin B
  have tpos : 0 < t := Fintype.card_pos_iff.mpr
    ⟨ProfileStabilizer.groupOf p (Classical.choice ‹Nonempty I›)⟩
  have Ubound : k * (t - 1) ≤ U := by
    by_cases ht : 2 ≤ t
    · rw [show U = k ! / (∏ b : B, (ProfileStabilizer.size p b)!) from by dsimp [U]; rw [Hfact]]
      exact StabilizerBlockCount.block_count_lower (ProfileStabilizer.size p)
        (ProfileStabilizer.size_positive p) ht (ProfileStabilizer.size_sum p)
    · have eq : t - 1 = 0 := by omega
      simp [eq]
  obtain ⟨a, acount, amass⟩ := cover t U tpos Ubound (d ∘ e.symm)
    (by simpa only [Function.comp_apply, Equiv.sum_comp] using dtotal)
  let Q := MulAction.orbitRel.Quotient G I
  let _ : Fintype Q := Fintype.ofFinite Q
  let eQ : Q ≃ Fin t := (ProfileStabilizer.orbitEquivGroups p).trans e
  let aQ (j : Fin n) (b : Q) := a j (eQ b)
  have aQcount (j : Fin n) : ∑ b : Q, aQ j b = U :=
    (eQ.sum_comp (a j)).trans (acount j)
  have permCard : Fintype.card (Equiv.Perm I) = k ! := Fintype.card_perm
  have realize (j : Fin n) :=
    FreeActionAllocations.equivariant_readout_of_orbit_counts
      (ProfileStabilizer.regular_subgroup_free p) (aQ j)
      (by rw [aQcount, permCard])
  choose f equiv count using realize
  refine ⟨f, fun h j g => equiv j h g, fun i => ?_⟩
  let b := ProfileStabilizer.groupOf p i
  let s := ProfileStabilizer.size p b
  let h := Fintype.card (MulAction.stabilizer G i)
  have spos : 0 < s := ProfileStabilizer.size_positive p b
  have hs : s * h = H := ProfileStabilizer.stabilizer_count_product p i
  have hw : ∑ j, aQ j (Quotient.mk'' i) * w j = c * d b := by
    show ∑ j, a j (e (ProfileStabilizer.orbitEquivGroups p (Quotient.mk'' i))) * w j = _
    rw [ProfileStabilizer.orbitEquivGroups_mk]
    simpa [b, Function.comp_apply] using amass (e b)
  have combined : d b * h = D * p i := by
    apply Nat.eq_of_mul_eq_mul_left spos
    calc
      s * (d b * h) = d b * H := by rw [← hs]; ac_rfl
      _ = D * (s * p i) := demand b
      _ = s * (D * p i) := by ac_rfl
  calc
    _ = ∑ j, (aQ j (Quotient.mk'' i) * h) * w j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← count j i, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      split <;> simp
    _ = (∑ j, aQ j (Quotient.mk'' i) * w j) * h := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => Nat.mul_right_comm _ _ _
    _ = (c * D) * p i := by rw [hw, Nat.mul_assoc, combined, Nat.mul_assoc]

open Finset
open scoped Nat
open PermutationGrid (Profile relabel)

private theorem relabel_mul {I : Type*} [Fintype I] {m : ℕ} (g h : Equiv.Perm I) (p : Profile I m) :
    relabel (g * h) p = relabel g (relabel h p) := by
  apply Subtype.ext
  funext i
  simp only [mul_inv_rev, Equiv.Perm.mul_apply]

private theorem relabel_one {I : Type*} [Fintype I] {m : ℕ} (p : Profile I m) : relabel 1 p = p := by
  apply Subtype.ext
  funext i
  simp

instance profileAction {I : Type*} [Fintype I] {m : ℕ} : MulAction (Equiv.Perm I) (Profile I m) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

private theorem preserving_of_fix {I : Type*} [Fintype I] {m : ℕ} {p : Profile I m}
    {g : Equiv.Perm I} (fixes : relabel g p = p) : g ∈ ProfileStabilizer.Preserving p.val := by
  change p.val ∘ g = p.val
  funext i
  have eq := congrArg (fun q : Profile I m => q.val (g i)) fixes
  change p.val (g.symm (g i)) = p.val (g i) at eq
  rw [g.symm_apply_apply i] at eq
  exact eq.symm

private def LocalReadout {I : Type*} [Fintype I] [DecidableEq I] {m n D : ℕ}
    (w : Fin n → ℕ) (p : Profile I m) :=
  { f : Fin n → Equiv.Perm I → I //
    (∀ i, ∑ j, ∑ g, (if f j g = i then w j else 0) = D * p.val i) ∧
    (∀ g, relabel g p = p → ∀ j h, f j (g * h) = g (f j h)) }

private theorem global_readout {I : Type*} [Fintype I] [DecidableEq I] {m n D : ℕ}
    (w : Fin n → ℕ) (all : ∀ p : Profile I m, Nonempty (LocalReadout (D := D) w p)) :
    ∃ f : Profile I m → Fin n → Equiv.Perm I → I,
      (∀ p i, ∑ j, ∑ g, (if f p j g = i then w j else 0) = D * p.val i) ∧
      (∀ g p j h, f (relabel g p) j (g * h) = g (f p j h)) := by
  classical
  let G := Equiv.Perm I
  let orbit (p : Profile I m) : MulAction.orbitRel.Quotient G (Profile I m) := Quotient.mk'' p
  let rep (p : Profile I m) := (orbit p).out
  have reachable (p : Profile I m) : ∃ g : G, relabel g (rep p) = p :=
    Quotient.exact' (Quotient.out_eq' (orbit p)).symm
  let g (p : Profile I m) := (reachable p).choose
  have go (p : Profile I m) : relabel (g p) (rep p) = p := (reachable p).choose_spec
  let localF (p : Profile I m) := Classical.choice (all p)
  let f (p : Profile I m) (j : Fin n) (h : G) :=
    (g p) ((localF (rep p)).val j ((g p)⁻¹ * h))
  refine ⟨f, ?_, ?_⟩
  · intro p i
    have equal (a : I) : g p a = i ↔ a = (g p)⁻¹ i := by
      change g p a = i ↔ a = (g p).symm i
      rw [Equiv.eq_symm_apply]
    have transport : (rep p).val ((g p)⁻¹ i) = p.val i :=
      congrArg (fun p : Profile I m => p.val i) (go p)
    calc
      _ = ∑ j, ∑ h : G, (if (localF (rep p)).val j h = (g p)⁻¹ i then w j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [f, equal]
        let e : G ≃ G := Equiv.mulLeft ((g p)⁻¹)
        change (∑ h : G, if (localF (rep p)).val j (e h) = (g p)⁻¹ i then w j else 0) = _
        exact e.sum_comp (fun h : G => if (localF (rep p)).val j h = (g p)⁻¹ i then w j else 0)
      _ = D * (rep p).val ((g p)⁻¹ i) := (localF (rep p)).property.1 _
      _ = _ := congrArg (D * ·) transport
  · intro h p j k
    let p' := relabel h p
    have same : rep p' = rep p :=
      congrArg Quotient.out (MulAction.orbitRel.Quotient.quotient_smul_eq (g := h) (a := p))
    let u := (g p')⁻¹ * h * g p
    have stable : relabel u (rep p) = rep p := by
      rw [show u = (g p')⁻¹ * (h * g p) by dsimp [u]; group, relabel_mul, relabel_mul, go p]
      change relabel (g p')⁻¹ p' = rep p
      calc
        relabel (g p')⁻¹ p' = relabel (g p')⁻¹ (relabel (g p') (rep p')) :=
          congrArg (relabel (g p')⁻¹) (go p').symm
        _ = rep p' := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
        _ = rep p := same
    change (g p') ((localF (rep p')).val j ((g p')⁻¹ * (h * k))) = h ((g p) ((localF (rep p)).val j ((g p)⁻¹ * k)))
    rw [same, show (g p')⁻¹ * (h * k) = u * ((g p)⁻¹ * k) by
      ext i
      change (g p').symm (h (k i)) = (g p').symm (h (g p ((g p).symm (k i))))
      rw [(g p).apply_symm_apply],
      (localF (rep p)).property.2 u stable, ← Equiv.Perm.mul_apply,
      show g p'*u = h * g p by
        ext i
        change g p' ((g p').symm (h (g p i))) = h (g p i)
        exact (g p').apply_symm_apply _]
    rfl

open Finset
open scoped Nat
open PermutationGrid (Profile relabel)

end D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

namespace D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction

open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.PermutationGrid (Profile relabel)
open Finset
open scoped Nat

/-- A common scaled allocation for all stabilizer block demands gives one
equivariant law on the whole grid. Zero weight orbits are dropped. -/
theorem law_of_scaled_block_allocations {k m n c : ℕ} (two : 2 ≤ k) (positive : 0 < m)
    (scalePositive : 0 < c) (divide : k - 1 ∣ m) (w : Fin n → ℕ)
    (weights : k * (k - 1) * (∑ j, w j) = c * m)
    (cover : ∀ t U : ℕ, 0 < t → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
      k * (k - 1) * (∑ i, x i) = U * m →
        ∃ a : Fin n → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = c * x i)) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S)
      (v : S → ℝ) (f : Profile (Fin k) m → S → Fin k),
      (∀ s, 0 < v s) ∧ (∑ s, v s = 1) ∧ (∀ (g : Equiv.Perm (Fin k)) s, v (g • s) = v s) ∧
      (∀ p i, ∑ s, (if f p s = i then v s else 0) = (p.val i : ℝ) / m) ∧
      (∀ g p s, f (relabel g p) (g • s) = g (f p s)) ∧ Fintype.card S ≤ k ! * n := by
  classical
  let I := Fin k
  let P := Equiv.Perm I
  let D := c * (k - 2)!
  letI : Nonempty I := ⟨⟨0, by omega⟩⟩
  have cardI : Fintype.card I = k := Fintype.card_fin k
  have available : ∀ t U : ℕ, 0 < t → Fintype.card I * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
      Fintype.card I * (Fintype.card I - 1) * (∑ i, x i) = U * m →
      ∃ a : Fin n → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
        (∀ i, ∑ j, a j i * w j = c * x i) := by
    simpa only [cardI] using cover
  have locals (p : Profile I m) : Nonempty (LocalReadout (D := D) w p) := by
    obtain ⟨f, eq, mass⟩ := local_scaled_readout (c := c) available p.val p.property
      (by simpa only [cardI] using divide) (by simpa only [cardI] using two)
    refine ⟨⟨f, ?_, fun g fix j h => eq ⟨g, preserving_of_fix fix⟩ j h⟩⟩
    simpa only [cardI] using mass
  obtain ⟨f, mass, covariance⟩ := global_readout w locals
  let R := Fin n × P
  let S := {s : R // 0 < w s.1}
  let _ : MulAction P R :=
    { smul := fun g s => (s.1, g * s.2)
      one_smul := fun s => Prod.ext rfl (one_mul s.2)
      mul_smul := fun g h s => Prod.ext rfl (mul_assoc g h s.2) }
  let _ : MulAction P S :=
    { smul := fun g s => ⟨g • s.val, s.property⟩
      one_smul := fun s => Subtype.ext (one_smul _ _)
      mul_smul := fun g h s => Subtype.ext (mul_smul g h s.val) }
  let F (p : Profile I m) (s : S) := f p s.val.1 s.val.2
  have cardP : Fintype.card P = k ! := by rw [Fintype.card_perm, Fintype.card_fin]
  have factorial : k ! = (k - 2)! * (k * (k - 1)) := by
    have pred : (k - 1)! = (k - 1) * (k - 2)! := by
      simpa only [show k - 1 - 1 = k - 2 by omega] using
        (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm
    rw [← Nat.mul_factorial_pred (n := k) (by omega), pred]
    ac_rfl
  have denominator : (∑ s : S, w s.val.1) = D * m := by
    rw [ThreeOutcomeGridSupport.sum_positive_support (fun (a : R) => w a.1) _ (fun _ h => h),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, cardP, nsmul_eq_mul, Nat.cast_id,
      ← Finset.mul_sum]
    rw [factorial, Nat.mul_assoc, weights]
    dsimp only [D]
    ac_rfl
  have supportedMass (p : Profile I m) (i : I) :
      (∑ s : S, if F p s = i then w s.val.1 else 0) = D * p.val i := by
    rw [ThreeOutcomeGridSupport.sum_positive_support (fun (a : R) => w a.1)
      (fun s => if f p s.1 s.2 = i then w s.1 else 0)
      (fun s z => by simp [z]), Fintype.sum_prod_type]
    exact mass p i
  let M : ℝ := (D * m : ℕ)
  have dpositive : 0 < D := Nat.mul_pos scalePositive (Nat.factorial_pos _)
  have MP : 0 < M := by
    change 0 < ((D * m : ℕ) : ℝ)
    exact_mod_cast Nat.mul_pos dpositive positive
  let v (s : S) : ℝ := (w s.val.1 : ℝ) / M
  refine ⟨S, inferInstance, inferInstance, v, F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    exact div_pos (by exact_mod_cast s.property) MP
  · simp only [v, ← Finset.sum_div, ← Nat.cast_sum, denominator]
    exact div_self MP.ne'
  · intro g s
    rfl
  · intro p i
    have castMass := congrArg (fun x : ℕ => (x : ℝ)) (supportedMass p i)
    push_cast at castMass
    calc
      _ = ∑ s : S, (if F p s = i then (w s.val.1 : ℝ) else 0) / M := by
        exact Finset.sum_congr rfl fun s _ => by by_cases h : F p s = i <;> simp [v, h]
      _ = ((D : ℝ) * (p.val i : ℝ)) / M := by rw [← Finset.sum_div, castMass]
      _ = _ := by
        change ((D : ℝ) * (p.val i : ℝ)) / ((D * m : ℕ) : ℝ) = (p.val i : ℝ) / m
        have denomCast : ((D * m : ℕ) : ℝ) = (D : ℝ) * (m : ℝ) := Nat.cast_mul D m
        rw [denomCast, mul_comm (D : ℝ) (p.val i : ℝ), mul_comm (D : ℝ) (m : ℝ),
          mul_div_mul_right _ _ (by exact_mod_cast dpositive.ne')]
  · intro g p s
    exact covariance g p s.val.1 s.val.2
  · have h := Fintype.card_le_of_injective Subtype.val
      (Subtype.val_injective (p := fun s : R => 0 < w s.1))
    simpa only [R, Fintype.card_prod, Fintype.card_fin, cardP, Nat.mul_comm] using h

end D5.S3.ConceptDynamics.Attribution.GridReadoutConstruction

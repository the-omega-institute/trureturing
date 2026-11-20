/- GID: D5/S3/ConceptDynamics/Attribution/PermutationGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/PermutationGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite seed budgets for exact calibration under all outcome permutations. -/

import D5.S3.Combinatorics.Partitions.CommonBlockWeights
import D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility
import D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness
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

private def Preserving {I : Type*} (p : I → ℕ) : Subgroup (Equiv.Perm I) where
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

private abbrev Groups {I : Type*} [Fintype I] (p : I → ℕ) :=
  ↥(univ.image p)

private abbrev groupOf {I : Type*} [Fintype I] (p : I → ℕ) (i : I) : Groups p :=
  ⟨p i, mem_image_of_mem p (mem_univ _)⟩

private abbrev size {I : Type*} [Fintype I] (p : I → ℕ) (b : Groups p) :=
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

private theorem stabilizer_count_product {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℕ) (i : I)
    [Fintype (MulAction.stabilizer (Preserving p) i)] :
    size p (groupOf p i) * Fintype.card (MulAction.stabilizer (Preserving p) i) = Fintype.card (Preserving p) := by
  classical
  let _ : Fintype (MulAction.orbit (Preserving p) i) := Fintype.ofFinite _
  have C := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Preserving p) i
  have eq := Fintype.card_congr (Set.equivOfEq (orbit_eq_fiber p i))
  rwa [eq] at C

private theorem regular_subgroup_free {I : Type*} (p : I → ℕ) (g : Equiv.Perm I) :
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

private theorem equivariant_fiber_size {G X Y : Type*} [Group G] [Fintype G] [Fintype X]
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

/-- A shared positive seed law exactly calibrated on all profiles of a sufficiently divisible
denominator has trivial seed stabilizers. -/
private theorem trivial_seed_stabilizers {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [MulAction (Equiv.Perm I) S]
    {m : ℕ} (divisible : ∀ d : ℕ, 0 < d → d ≤ Fintype.card I → d ∣ m)
    (w : S → ℝ) (positive : ∀ s, 0 < w s)
    (f : Profile I m → S → I)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (equivariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥ :=
  PrimeCycleSeedFreeness.free_of_prime_divisibility
    (fun p prime le => divisible p prime.pos le) w positive f calibrated equivariant

end PermutationGrid

open Finset
open scoped Nat

private theorem local_readout {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {n q : ℕ} {w : Fin n → ℕ} (cover : D5.S3.Combinatorics.Partitions.CommonBlockWeights.CoversAllocations (Fintype.card I) q w)
    (p : I → ℕ) (total : ∑ i, p i = Fintype.card I * (Fintype.card I - 1) * q)
    (atLeastTwo : 2 ≤ Fintype.card I) :
    ∃ f : Fin n → Equiv.Perm I → I,
      (∀ (h : ProfileStabilizer.Preserving p) j g, f j (h • g) = h • f j g) ∧
      ∀ i, ∑ j, (∑ g, if f j g = i then w j else 0) = (Fintype.card I - 2)! * p i := by
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
    rw [ProfileStabilizer.group_mass, total]
    exact ⟨k * q, by dsimp [k]; ac_rfl⟩
  have demand (b : B) : d b * H = D * (ProfileStabilizer.size p b * b.val) :=
    Nat.div_mul_cancel (divide b)
  have kfact : k ! = D * k * (k - 1) := by
    have pred : (k - 1)! = (k - 1) * D := by
      simpa only [D, show k - 1 - 1 = k - 2 by omega] using
        (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm
    rw [← Nat.mul_factorial_pred (n := k) (by omega), pred]
    ac_rfl
  have dtotal : ∑ b : B, d b = U * q := by
    apply Nat.eq_of_mul_eq_mul_right Hpos
    calc
      (∑ b : B, d b) * H =
          ∑ b : B, D * (ProfileStabilizer.size p b * b.val) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun b _ => demand b
      _ = (k)! * q := by
        rw [← Finset.mul_sum, ProfileStabilizer.group_mass, total, kfact]
        dsimp [k]
        ac_rfl
      _ = (U * q) * H := by rw [Nat.mul_right_comm, HU]
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
    ((e.symm.sum_comp d).trans dtotal)
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
  have hw : ∑ j, aQ j (Quotient.mk'' i) * w j = d b := by
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
    _ = D * p i := by rw [hw, combined]

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

private theorem grid_readout {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (two : 2 ≤ Fintype.card I) {n q : ℕ}
    (budget : Fintype.card I * q + 1 ≤ (Fintype.card I + 1) ^ n) :
    let k := Fintype.card I
    let m := k * (k - 1) * q
    ∃ (w : Fin n → ℕ) (f : Profile I m → Fin n → Equiv.Perm I → I),
      (∑ j, w j = q) ∧
      (∀ p i, ∑ j, ∑ g, (if f p j g = i then w j else 0) = (k - 2)! * p.val i) ∧
      (∀ g p j h, f (relabel g p) j (g * h) = g (f p j h)) := by
  dsimp only
  obtain ⟨w, total, cover⟩ := D5.S3.Combinatorics.Partitions.CommonBlockWeights.common_weights_for_allocations (by omega) budget
  have locals (p : Profile I (Fintype.card I * (Fintype.card I - 1) * q)) :
      Nonempty (LocalReadout (D := (Fintype.card I - 2)!) w p) := by
    obtain ⟨f, equivariant, mass⟩ := local_readout cover p.val p.property two
    exact ⟨⟨f, mass, fun g fix j h => equivariant ⟨g, preserving_of_fix fix⟩ j h⟩⟩
  obtain ⟨f, mass, equivariant⟩ := global_readout w locals
  exact ⟨w, f, total, mass, equivariant⟩

open Finset
open scoped Nat
open PermutationGrid (Profile relabel)

private def flag {I : Type*} [DecidableEq I] (a i : I) : ℕ := if i = a then 0 else 1

private theorem flag_stabilizer {I : Type*} [DecidableEq I] (a : I) :
    ProfileStabilizer.Preserving (flag a) = MulAction.stabilizer (Equiv.Perm I) a := by
  ext g
  change flag a ∘ g = flag a ↔ g a = a
  constructor
  · intro preserves
    have eq := congrFun preserves a
    change flag a (g a) = flag a a at eq
    by_contra h
    simp [flag, h] at eq
  · intro fixes
    funext i
    change flag a (g i) = flag a i
    have eq : g i = a ↔ i = a := g.injective.eq_iff' fixes
    simp [flag, eq]

private theorem flag_size {I : Type*} [Fintype I] [DecidableEq I] (a b : I) (ne : b ≠ a) :
    ProfileStabilizer.size (flag a) (ProfileStabilizer.groupOf (flag a) b) = Fintype.card I - 1 := by
  have eq (i : I) : flag a i = flag a b ↔ i ≠ a := by
    by_cases hi : i = a <;> simp [flag, hi, ne]
  change Fintype.card {i : I // flag a i = flag a b} = _
  let e : {i : I // flag a i = flag a b} ≃ {i : I // i ≠ a} :=
    Equiv.subtypeEquiv (Equiv.refl I) eq
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

private theorem flag_card {I : Type*} [Fintype I] [DecidableEq I] (a : I) :
    Fintype.card (ProfileStabilizer.Preserving (flag a)) = (Fintype.card I - 1)! := by
  classical
  let k := Fintype.card I
  have kpos : 0 < k := Fintype.card_pos_iff.mpr ⟨a⟩
  let _ : Fintype (MulAction.orbit (Equiv.Perm I) a) := Fintype.ofFinite _
  have orbitAll : MulAction.orbit (Equiv.Perm I) a = Set.univ := MulAction.orbit_eq_univ (Equiv.Perm I) a
  have orbitCard : Fintype.card (MulAction.orbit (Equiv.Perm I) a) = k :=
    Fintype.card_congr ((Set.equivOfEq orbitAll).trans (Equiv.Set.univ I))
  have stabCard : Fintype.card (MulAction.stabilizer (Equiv.Perm I) a) = (k - 1)! := by
    apply Nat.eq_of_mul_eq_mul_left kpos
    have c := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm I) a
    rw [orbitCard, Fintype.card_perm] at c
    rw [c]
    exact (Nat.mul_factorial_pred kpos.ne').symm
  let e : ProfileStabilizer.Preserving (flag a) ≃ MulAction.stabilizer (Equiv.Perm I) a :=
    Set.equivOfEq (congrArg (fun H : Subgroup (Equiv.Perm I) => (H : Set (Equiv.Perm I)))
      (flag_stabilizer a))
  exact (Fintype.card_congr e).trans stabCard

private theorem flag_inner_card {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (ne : b ≠ a) (two : 2 ≤ Fintype.card I) :
    Fintype.card (MulAction.stabilizer (ProfileStabilizer.Preserving (flag a)) b) = (Fintype.card I - 2)! := by
  let k := Fintype.card I
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k - 1 by omega)
  have eq := ProfileStabilizer.stabilizer_count_product (flag a) b
  rw [flag_size a b ne, flag_card] at eq
  rw [eq]
  simpa only [show k - 1 - 1 = k - 2 by omega] using
    (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm

private def tied {I : Type*} [Fintype I] [DecidableEq I] (a : I) {m : ℕ}
    (level : ℕ) (bound : (Fintype.card I - 1) * level ≤ m) : Profile I m :=
  ⟨fun i => if i = a then m - (Fintype.card I - 1) * level else level, by
    classical
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [ite_true]
    have sum : (∑ i ∈ (Finset.univ : Finset I).erase a, if i = a then
        m - (Fintype.card I - 1) * level else level) =
        ∑ _i ∈ (Finset.univ : Finset I).erase a, level := by
      exact Finset.sum_congr rfl fun i hi => ite_eq_right (Finset.ne_of_mem_erase hi)
    rw [sum, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id, Nat.add_sub_of_le bound]⟩

/-- Tied profiles require a whole interval of integer masses from one family of bounded orbit digits. -/
theorem weighted_orbit_spectrum {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] (two : 2 ≤ Fintype.card I)
    {m : ℕ} (free : ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥)
    (w : S → ℝ)
    (invariant : ∀ (g : Equiv.Perm I) s, w (g • s) = w s)
    (f : Profile I m → S → I)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∃ (r : ℕ) (weights : Fin r → ℝ),
      Fintype.card S = (Fintype.card I)! * r ∧
      ((Fintype.card I)! : ℝ) * (∑ j, weights j) =
        ((Fintype.card I-2)! : ℝ) * ∑ s, w s ∧
      ∀ l : Fin (m/(Fintype.card I-1)+1), ∃ d : Fin r → Fin (Fintype.card I+1),
        ∑ j, (d j).val * weights j = (l.val : ℝ) := by
  classical
  let k := Fintype.card I
  have kpos : 0 < k := by omega
  have prevPos : 0 < k-1 := by omega
  let _ : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, a, distinct⟩ := exists_pair_ne I
  let P := Equiv.Perm I
  let H := ProfileStabilizer.Preserving (flag a)
  let J := MulAction.orbitRel.Quotient P S
  let _ : Fintype J := Fintype.ofFinite J
  let e := (MulAction.selfEquivOrbitsQuotientProd free).symm
  have cardS : Fintype.card S = k ! * Fintype.card J := by
    simpa only [Fintype.card_prod, Fintype.card_perm, Nat.mul_comm] using Fintype.card_congr e.symm
  let L := Fin (m/(k-1)+1)
  let p (l : L) : Profile I m := tied a l.val (Nat.le_trans
    (Nat.mul_le_mul_left (k-1) (show l.val ≤ m/(k-1) from Nat.lt_succ_iff.mp l.isLt))
    (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _))
  have tieVal (l : L) : (p l).val b = l.val := ite_eq_right distinct
  have fixed (l : L) (g : H) : relabel g.val (p l) = p l := by
    apply Subtype.ext
    funext i
    have ga : g.val a = a := by
      have h : g.val ∈ ProfileStabilizer.Preserving (flag a) := g.property
      rw [flag_stabilizer] at h
      exact MulAction.mem_stabilizer_iff.mp h
    have eq : g.val.symm i = a ↔ i = a := by rw [Equiv.symm_apply_eq, ga]
    change (if g.val.symm i = a then m-(k-1)*l.val else l.val) =
      if i = a then m-(k-1)*l.val else l.val
    simp only [eq]
  have permQuot : Fintype.card P / Fintype.card H = k := by
    change (Fintype.card (Equiv.Perm I)) / Fintype.card H = k
    change (Fintype.card (Equiv.Perm I)) / Fintype.card (ProfileStabilizer.Preserving (flag a)) = k
    rw [Fintype.card_perm, flag_card]
    change k ! / (k-1)! = k
    have fact : k ! = k * (k-1)! := (Nat.mul_factorial_pred kpos.ne').symm
    rw [fact, Nat.mul_div_cancel _ (Nat.factorial_pos _)]
  have chooseDigit (l : L) (j : J) :
      ∃ d : Fin (k+1),
        (univ.filter fun g : P => f (p l) (g • j.out) = b).card =
          d.val * (k-2)! := by
    let F (g : P) := f (p l) (g • j.out)
    have equivariant (h : H) (g : P) : F (h • g) = h • F g := by
      change f (p l) ((h.val * g) • j.out) = h.val (f (p l) (g • j.out))
      simpa only [fixed l h, mul_smul] using covariant h.val (p l) (g • j.out)
    obtain ⟨d, le, eq⟩ := FreeActionAllocations.equivariant_fiber_size
      (ProfileStabilizer.regular_subgroup_free (flag a)) F equivariant b
    rw [permQuot] at le
    rw [flag_inner_card a b distinct two, Finset.sum_boole] at eq
    exact ⟨⟨d, Nat.lt_succ_of_le le⟩, eq⟩
  choose digit count using chooseDigit
  have weighted (l : L) :
      ∑ j : J, ((digit l j).val : ℝ) * ((k-2)! : ℝ) * w j.out = (l.val : ℝ) := by
    have eq := calibrated (p l) b
    rw [tieVal] at eq
    rw [← e.sum_comp, Fintype.sum_prod_type] at eq
    rw [← eq]
    apply Finset.sum_congr rfl
    intro j _
    change ((digit l j).val : ℝ) * ((k-2)! : ℝ) * w j.out =
      ∑ g : P, (if f (p l) (g • j.out) = b then w (g • j.out) else 0)
    simp only [invariant, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [count l j, Nat.cast_mul]
  let eJ := Fintype.equivFin J
  let weight (j : J) := ((k-2)! : ℝ) * w j.out
  have reindexed : (∑ s, w s) = ((k ! : ℕ) : ℝ) * ∑ j : J, w j.out := by
    rw [← e.sum_comp, Fintype.sum_prod_type]
    simp only [show ∀ (j : J) (g : P), e (j,g) = g • j.out from fun _ _ => rfl,
      invariant, Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  refine ⟨Fintype.card J, weight ∘ eJ.symm, cardS, ?_, ?_⟩
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp eJ.symm weight, reindexed]
    simp only [weight, ← Finset.mul_sum]
    ring
  · intro l
    refine ⟨digit l ∘ eJ.symm, ?_⟩
    have h := Equiv.sum_comp eJ.symm (fun j => ((digit l j).val : ℝ) * weight j)
    calc
      _ = ∑ j : J, ((digit l j).val : ℝ) * weight j := h
      _ = _ := by simpa only [weight, mul_assoc] using weighted l

private theorem grid_lower {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] (two : 2 ≤ Fintype.card I)
    {m : ℕ} (divisible : ∀ d : ℕ, 0 < d → d ≤ Fintype.card I → d ∣ m)
    (w : S → ℝ) (positive : ∀ s, 0 < w s)
    (invariant : ∀ (g : Equiv.Perm I) s, w (g • s) = w s)
    (f : Profile I m → S → I)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∃ r, Fintype.card S = (Fintype.card I)! * r ∧
      m / (Fintype.card I - 1) + 1 ≤ (Fintype.card I + 1) ^ r := by
  classical
  have free :=
    PermutationGrid.trivial_seed_stabilizers divisible w positive f calibrated covariant
  obtain ⟨r, weights, support, _, cover⟩ := weighted_orbit_spectrum two free w invariant f calibrated covariant
  choose digits value using cover
  have inj : Function.Injective digits := by
    intro x y same
    have equality : (x.val : ℝ) = (y.val : ℝ) := by
      rw [← value x, ← value y, same]
    exact Fin.ext (by exact_mod_cast equality)
  exact ⟨r, support, by
    simpa only [Fintype.card_fin, Fintype.card_fun] using Fintype.card_le_of_injective digits inj⟩


open Finset
open scoped Nat
open PermutationGrid (Profile relabel)

/-- A positive invariant seed law and pointwise equivariant readout that reproduce the
coordinates of every integer profile normalized by the denominator. -/
def CalibratingLaw {k m : ℕ} (S : Type*) [Fintype S] [MulAction (Equiv.Perm (Fin k)) S]
    (w : S → ℝ) (f : Profile (Fin k) m → S → Fin k) : Prop :=
  (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧
    (∀ (g : Equiv.Perm (Fin k)) s, w (g • s) = w s) ∧
    (∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ) / m) ∧
    (∀ g p s, f (relabel g p) (g • s) = g (f p s))

/-- On the complete k - outcome grid, the capacity of a budget of n regular seed orbits
is exactly the range of n digits from zero to k. The divisibility hypothesis forces every
positive seed orbit to be regular. -/
theorem grid_support_budget_iff {k q : ℕ} (two : 2 ≤ k) (positive : 0 < q)
    (divisible : ∀ d : ℕ, 0 < d → d ≤ k → d ∣ k * (k - 1) * q) (n : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile (Fin k) (k * (k - 1) * q) → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * n) ↔ k * q + 1 ≤ (k + 1) ^ n := by
  classical
  let I := Fin k
  let P := Equiv.Perm I
  let m := k * (k - 1) * q
  let D := (k - 2)!
  have mpos : 0 < m := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) positive
  have Dpos : 0 < D := Nat.factorial_pos _
  have cardI : Fintype.card I = k := Fintype.card_fin k
  have cardP : Fintype.card P = k ! := by rw [Fintype.card_perm, cardI]
  have fact : k ! = D * k * (k - 1) := by
    have pred : (k - 1)! = (k - 1) * D := by
      simpa only [D, show k - 1 - 1 = k - 2 by omega] using
        (Nat.mul_factorial_pred (n := k - 1) (by omega)).symm
    rw [← Nat.mul_factorial_pred (n := k) (by omega), pred]
    ac_rfl
  constructor
  · rintro ⟨S, _, _, w, f, ⟨wp, _, wi, mass, covariance⟩, bound⟩
    have realPos : 0 < (m : ℝ) := by exact_mod_cast mpos
    let v (s : S) := (m : ℝ) * w s
    have scaled (p : Profile I m) (i : I) :
        (∑ s, if f p s = i then v s else 0) = (p.val i : ℝ) := by
      have term (s : S) :
          (if f p s = i then v s else 0) = (m : ℝ) * (if f p s = i then w s else 0) := by
        by_cases h : f p s = i <;> simp [h, v]
      rw [Finset.sum_congr rfl (fun s _ => term s), ← Finset.mul_sum, mass]
      change (m : ℝ) * ((p.val i : ℝ) / m) = (p.val i : ℝ)
      rw [mul_comm, div_mul_cancel₀ _ realPos.ne']
    obtain ⟨r, support, digit⟩ := grid_lower (I := I) (by rwa [cardI])
      (by simpa only [cardI] using divisible) v (fun s => mul_pos realPos (wp s))
      (fun g s => congrArg ((m : ℝ)*·) (wi g s)) f scaled covariance
    simp only [cardI] at support digit
    rw [support] at bound
    have le : r ≤ n := Nat.le_of_mul_le_mul_left bound (Nat.factorial_pos _)
    have div : m / (k - 1) = k * q := by
      change k * (k - 1) * q / (k - 1) = _
      rw [Nat.mul_right_comm, Nat.mul_div_cancel _ (show 0 < k - 1 by omega)]
    rw [div] at digit
    exact digit.trans (Nat.pow_le_pow_right (by omega) le)
  · intro bound
    let _ : Nonempty I := ⟨⟨0, by omega⟩⟩
    have readout := grid_readout (I := Fin k) (n := n) (q := q)
      (by simpa only [Fintype.card_fin] using two)
      (by simpa only [Fintype.card_fin] using bound)
    obtain ⟨w, f, total, mass, covariance⟩ := readout
    have mEq : Fintype.card (Fin k) * (Fintype.card (Fin k) - 1) * q = m := by
      rw [Fintype.card_fin]
    let lift (p : Profile I m) : Profile (Fin k) _ :=
      ⟨p.val, p.property.trans mEq.symm⟩
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
    let F (p : Profile I m) (s : S) := f (lift p) s.val.1 s.val.2
    have denominator : (∑ s : S, w s.val.1) = D * m := by
      rw [ThreeOutcomeGridSupport.sum_positive_support (fun (a : R) => w a.1) _ (fun _ h => h), Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, cardP, nsmul_eq_mul, Nat.cast_id,
        ← Finset.mul_sum, total]
      rw [fact]
      dsimp [m]
      ac_rfl
    have supportedMass (p : Profile I m) (i : I) :
        (∑ s : S, if F p s = i then w s.val.1 else 0) = D * p.val i := by
      rw [ThreeOutcomeGridSupport.sum_positive_support (fun (a : R) => w a.1)
        (fun s => if f (lift p) s.1 s.2 = i then w s.1 else 0)
        (fun s z => by simp [z]), Fintype.sum_prod_type]
      simpa only [Fintype.card_fin] using mass (lift p) i
    let M : ℝ := (D * m : ℕ)
    have MP : 0 < M := by
      change 0 < ((D * m : ℕ) : ℝ)
      exact_mod_cast Nat.mul_pos Dpos mpos
    let v (s : S) : ℝ := (w s.val.1 : ℝ) / M
    refine ⟨S, inferInstance, inferInstance, v, F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
          rw [Nat.cast_mul, mul_comm (D : ℝ) (p.val i : ℝ), mul_comm (D : ℝ) (m : ℝ),
            mul_div_mul_right _ _ (by exact_mod_cast Dpos.ne')]
    · intro g p s
      exact covariance g (lift p) s.val.1 s.val.2
    · have h := Fintype.card_le_of_injective Subtype.val (Subtype.val_injective (p := fun s : R => 0 < w s.1))
      simpa only [R, Fintype.card_prod, Fintype.card_fin, cardP, Nat.mul_comm] using h

end D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

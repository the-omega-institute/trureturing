/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyCuts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Native matching rotation cuts and exact positive cut counts. -/

import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphySurgery

/-! Rotation cuts retain ordered and equal cut positions. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge
open scoped BigOperators

attribute [local instance] Classical.propDecidable

private theorem orbit_card_of_period {A : Type*} [Fintype A] (f : Perm A) (a : A)
    (r : ℕ) (hr : 0 < r) (hperiod : (f ^ r) a = a)
    (hinj : Function.Injective (fun i : Fin r => (f ^ i.val) a)) :
    Nat.card {x : A // f.SameCycle a x} = r := by
  classical
  have hmod (n : ℕ) : (f ^ n) a = (f ^ (n % r)) a := by
    conv_lhs => rw [← Nat.mod_add_div n r]
    rw [pow_add, Perm.mul_apply, pow_mul,
      Perm.pow_apply_eq_self_of_apply_eq_self hperiod]
  let F : Fin r → {x : A // f.SameCycle a x} := fun i =>
    ⟨(f ^ i.val) a, (Perm.SameCycle.refl f a).pow_right⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j h
      exact hinj (congrArg Subtype.val h)
    · intro x
      obtain ⟨n, hn⟩ := x.property.exists_nat_pow_eq
      refine ⟨⟨n % r, Nat.mod_lt _ hr⟩, Subtype.ext ?_⟩
      exact (hmod n).symm.trans hn
  simpa only [Nat.card_fin] using
    (Nat.card_congr (Equiv.ofBijective F hF)).symm

private noncomputable def rotationOrbitFinset {k : ℕ} (p : P k) (a : Fin (2 * k)) :
    Finset (Fin (2 * k)) :=
  Finset.univ.filter fun x => (matchingPerm p * matchingPerm (e k)).SameCycle a x

private theorem rotation_orbit_mem {k : ℕ} (p : P k) (a x : Fin (2 * k)) :
    x ∈ rotationOrbitFinset p a ↔
      (matchingPerm p * matchingPerm (e k)).SameCycle a x := by
  simp only [rotationOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem rotation_orbit_cycle {k : ℕ} (p : P k) (a : Fin (2 * k)) :
    (matchingPerm p * matchingPerm (e k)).IsCycleOn (rotationOrbitFinset p a) := by
  let R := matchingPerm p * matchingPerm (e k)
  constructor
  · refine ⟨?_, R.injective.injOn, ?_⟩
    · intro x hx
      exact (rotation_orbit_mem p a _).mpr
        (((rotation_orbit_mem p a x).mp hx).apply_right)
    · intro y hy
      refine ⟨R.symm y, (rotation_orbit_mem p a _).mpr ?_, R.apply_symm_apply y⟩
      exact ((rotation_orbit_mem p a y).mp hy).symm_apply_right
  · intro x hx y hy
    exact ((rotation_orbit_mem p a x).mp hx).symm.trans
      ((rotation_orbit_mem p a y).mp hy)

private theorem rotation_orbit_card {k : ℕ} (p : P k) (a : Fin (2 * k)) :
    (rotationOrbitFinset p a).card = ((edgeComponents p).part (edgeIndex a)).card := by
  let F : (rotationOrbitFinset p a) ≃
      {x : Fin (2 * k) // (matchingPerm p * matchingPerm (e k)).SameCycle a x} :=
    Equiv.subtypeEquivRight (fun x => rotation_orbit_mem p a x)
  have h := Fintype.card_congr F
  rw [Fintype.card_coe, rotation_card] at h
  exact h

private theorem charge_swap {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (h : charge p a = charge p b) (x : Fin (2 * k)) :
    charge p (Equiv.swap a b x) = charge p x := by
  by_cases ha : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using h.symm
  · by_cases hb : x = b
    · subst x
      simpa only [Equiv.swap_apply_right] using h
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

private theorem equal_act_rotation_charge {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (h : charge p a = charge p b) (x : Fin (2 * k)) :
    charge p ((matchingPerm (act a b p) * matchingPerm (e k)) x) = charge p x := by
  have hp : charge p (p.val a) = charge p (p.val b) := by
    rw [charge_partner, charge_partner, h]
  rw [rotation_act]
  simp only [Perm.mul_apply]
  rw [charge_swap p h, charge_swap p hp]
  exact (charge_of_sameCycle p
    ((Perm.SameCycle.refl (matchingPerm p * matchingPerm (e k)) x).apply_right)).symm

private theorem equal_act_on_rotation_orbit {k : ℕ} (p : P k) {a b x : Fin (2 * k)}
    (hab : charge p a = charge p b)
    (hx : (matchingPerm p * matchingPerm (e k)).SameCycle a x) :
    (matchingPerm (act a b p) * matchingPerm (e k)) x =
      Equiv.swap a b ((matchingPerm p * matchingPerm (e k)) x) := by
  have hne {u v : Fin (2 * k)} (h : charge p u = charge p v) : u ≠ p.val v := by
    intro he
    rw [he, charge_partner] at h
    cases charge p v <;> simp_all
  have hc : charge p ((matchingPerm p * matchingPerm (e k)) x) = charge p a :=
    (charge_of_sameCycle p hx.apply_right).symm
  rw [rotation_act]
  simp only [Perm.mul_apply]
  change Equiv.swap a b (Equiv.swap (p.val a) (p.val b)
    ((matchingPerm p * matchingPerm (e k)) x)) = _
  rw [Equiv.swap_apply_of_ne_of_ne (hne hc) (hne (hc.trans hab))]
  simp only [Perm.mul_apply]

private theorem cut_rotation_prefix {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    ∀ n : ℕ, n < d →
      ((matchingPerm (act a b p) * matchingPerm (e k)) ^ n) a =
        ((matchingPerm p * matchingPerm (e k)) ^ n) a := by
  let R := matchingPerm p * matchingPerm (e k)
  let T := matchingPerm (act a b p) * matchingPerm (e k)
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hf := rotation_orbit_cycle p a
  have hcharge : charge p a = charge p b :=
    charge_of_sameCycle p ((Perm.SameCycle.refl R a).pow_right |>.trans (hb.sameCycle R))
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hnlt : n + 1 < (rotationOrbitFinset p a).card := lt_trans hn hd
    have hna : (R ^ (n + 1)) a ≠ a := by
      intro h
      have he := hf.injOn_pow_apply ha hnlt
        (show 0 < (rotationOrbitFinset p a).card by omega)
        (show (R ^ (n + 1)) a = (R ^ 0) a from h)
      omega
    have hnb : (R ^ (n + 1)) a ≠ b := by
      intro h
      have he := hf.injOn_pow_apply ha hnlt hd (h.trans hb.symm)
      omega
    change (T ^ (n + 1)) a = (R ^ (n + 1)) a
    rw [pow_succ', Perm.mul_apply, hi]
    rw [equal_act_on_rotation_orbit p hcharge ((Perm.SameCycle.refl R a).pow_right)]
    change Equiv.swap a b (R ((R ^ n) a)) = (R ^ (n + 1)) a
    rw [show R ((R ^ n) a) = (R ^ (n + 1)) a by
      simp only [pow_succ', Perm.mul_apply, R]]
    exact Equiv.swap_apply_of_ne_of_ne hna hnb

private theorem cut_rotation_period {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hdpos : 0 < d) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    ((matchingPerm (act a b p) * matchingPerm (e k)) ^ d) a = a := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
  let R := matchingPerm p * matchingPerm (e k)
  have hsame : R.SameCycle a b := by
    rw [← hb]
    exact (Perm.SameCycle.refl R a).pow_right
  have hc := charge_of_sameCycle p hsame
  rw [pow_succ', Perm.mul_apply, cut_rotation_prefix p (m + 1) hd hb m (by omega)]
  rw [equal_act_on_rotation_orbit p hc ((Perm.SameCycle.refl R a).pow_right)]
  change Equiv.swap a b (R ((R ^ m) a)) = a
  rw [show R ((R ^ m) a) = (R ^ (m + 1)) a by
    simp only [pow_succ', Perm.mul_apply, R]]
  rw [hb, Equiv.swap_apply_right]

private theorem cut_rotation_size {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hdpos : 0 < d) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    ((edgeComponents (act a b p)).part (edgeIndex a)).card = d := by
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hi : Function.Injective (fun i : Fin d =>
      ((matchingPerm (act a b p) * matchingPerm (e k)) ^ i.val) a) := by
    intro i j hij
    dsimp only at hij
    rw [cut_rotation_prefix p d hd hb i.val i.isLt,
      cut_rotation_prefix p d hd hb j.val j.isLt] at hij
    apply Fin.ext
    exact (rotation_orbit_cycle p a).injOn_pow_apply ha
      (lt_trans i.isLt hd) (lt_trans j.isLt hd) hij
  have h := orbit_card_of_period
    (matchingPerm (act a b p) * matchingPerm (e k)) a d hdpos
    (cut_rotation_period p d hdpos hd hb) hi
  have hr : Nat.card {x : Fin (2 * k) //
      (matchingPerm (act a b p) * matchingPerm (e k)).SameCycle a x} =
      ((edgeComponents (act a b p)).part (edgeIndex a)).card := by
    rw [Nat.card_eq_fintype_card]
    exact rotation_card (act a b p) a
  exact hr.symm.trans h

private theorem bounded_power_of_period {A : Type*} [Finite A]
    (f : Perm A) {a b : A} (d : ℕ) (hd : 0 < d) (hp : (f ^ d) a = a)
    (hb : f.SameCycle a b) : ∃ n : Fin d, (f ^ n.val) a = b := by
  obtain ⟨n, hn⟩ := hb.exists_nat_pow_eq
  refine ⟨⟨n % d, Nat.mod_lt _ hd⟩, ?_⟩
  have hmod : (f ^ n) a = (f ^ (n % d)) a := by
    conv_lhs => rw [← Nat.mod_add_div n d]
    rw [pow_add, Perm.mul_apply, pow_mul, Perm.pow_apply_eq_self_of_apply_eq_self hp]
  exact hmod.symm.trans hn

private theorem equal_act_sameCycle_charge {k : ℕ} (p : P k) {a b x y : Fin (2 * k)}
    (hab : charge p a = charge p b)
    (hxy : (matchingPerm (act a b p) * matchingPerm (e k)).SameCycle x y) :
    charge p x = charge p y := by
  let T := matchingPerm (act a b p) * matchingPerm (e k)
  have hpown (n : ℕ) : charge p ((T ^ n) x) = charge p x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply, equal_act_rotation_charge p hab]
      exact ih
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  rw [← hn]
  exact (hpown n).symm

private theorem cut_separates {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hdpos : 0 < d) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    ¬ Component (act a b p) a b := by
  let R := matchingPerm p * matchingPerm (e k)
  let q := act a b p
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hsame : R.SameCycle a b := by
    rw [← hb]
    exact (Perm.SameCycle.refl R a).pow_right
  have hc := charge_of_sameCycle p hsame
  intro hconn
  rcases (connected_iff_rotation_orbits (matchingPerm q) (matchingPerm (e k))
    q.property.1 (e k).property.1 a b).mp hconn with h | h
  · obtain ⟨n, hn⟩ := bounded_power_of_period
      (matchingPerm q * matchingPerm (e k)) d hdpos
      (cut_rotation_period p d hdpos hd hb) h
    rw [cut_rotation_prefix p d hd hb n.val n.isLt] at hn
    have he := (rotation_orbit_cycle p a).injOn_pow_apply ha
      (lt_trans n.isLt hd) hd (hn.trans hb.symm)
    exact (Nat.ne_of_lt n.isLt) he
  · have he := equal_act_sameCycle_charge p hc h
    change charge p (Equiv.swap a b (p.val (Equiv.swap a b a))) = charge p b at he
    rw [charge_swap p hc, Equiv.swap_apply_left, charge_partner] at he
    cases charge p b <;> simp_all

private theorem act_comm {k : ℕ} (p : P k) (a b : Fin (2 * k)) :
    act b a p = act a b p := by
  apply Subtype.ext
  funext x
  change Equiv.swap b a (p.val (Equiv.swap b a x)) =
    Equiv.swap a b (p.val (Equiv.swap a b x))
  rw [Equiv.swap_comm b a]

private theorem cut_rotation_other_size {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hdpos : 0 < d) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    ((edgeComponents (act a b p)).part (edgeIndex b)).card =
      (rotationOrbitFinset p a).card - d := by
  let R := matchingPerm p * matchingPerm (e k)
  let r := (rotationOrbitFinset p a).card
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hsame : R.SameCycle a b := by
    rw [← hb]
    exact (Perm.SameCycle.refl R a).pow_right
  have heq : rotationOrbitFinset p b = rotationOrbitFinset p a := by
    ext x
    rw [rotation_orbit_mem, rotation_orbit_mem]
    exact ⟨fun h => hsame.trans h, fun h => hsame.symm.trans h⟩
  have hback : (R ^ (r - d)) b = a := by
    rw [← hb, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hd.le]
    exact (rotation_orbit_cycle p a).pow_card_apply ha
  have hpos : 0 < r - d := Nat.sub_pos_of_lt hd
  have hlt : r - d < (rotationOrbitFinset p b).card := by
    rw [heq]
    dsimp [r] at *
    omega
  have h := cut_rotation_size p (a := b) (b := a) (r - d) hpos hlt hback
  rwa [act_comm] at h

private theorem ct_cut {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (d : ℕ) (hdpos : 0 < d) (hd : d < (rotationOrbitFinset p a).card)
    (hb : ((matchingPerm p * matchingPerm (e k)) ^ d) a = b) :
    (ct (act a b p)).parts =
      (ct p).parts.erase (rotationOrbitFinset p a).card +
        {d, (rotationOrbitFinset p a).card - d} := by
  let q := act a b p
  let Q := edgeComponents q
  let A := Q.part (edgeIndex a)
  let B := Q.part (edgeIndex b)
  let r := (rotationOrbitFinset p a).card
  let ms := (ct q).parts
  let base := (ms.erase d).erase (r - d)
  have hsep := cut_separates p d hdpos hd hb
  have hA : A ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hB : B ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hAc : A.card = d := cut_rotation_size p d hdpos hd hb
  have hBc : B.card = r - d := cut_rotation_other_size p d hdpos hd hb
  have hAB : A ≠ B := by
    intro h
    apply hsep
    apply (component_iff_edge_components q a b).mpr
    apply (edge_component_membership q (edgeIndex a) (edgeIndex b)).mp
    change edgeIndex b ∈ A
    rw [h]
    exact Q.mem_part (Finset.mem_univ _)
  have hdm : d ∈ ms := by
    change d ∈ Q.parts.val.map Finset.card
    exact Multiset.mem_map.mpr ⟨A, hA, hAc⟩
  have hem : r - d ∈ ms.erase d := by
    change r - d ∈ (Q.parts.val.map Finset.card).erase d
    rw [← hAc, ← Multiset.map_erase_of_mem Finset.card _ hA]
    exact Multiset.mem_map.mpr ⟨B, Finset.mem_erase.mpr ⟨hAB.symm, hB⟩,
      hBc.trans (congrArg (r - ·) hAc).symm⟩
  have hrestore : ms = base + {d, r - d} := by
    calc
      ms = d ::ₘ ms.erase d := (Multiset.cons_erase hdm).symm
      _ = d ::ₘ (r - d) ::ₘ base :=
        congrArg (Multiset.cons d) (Multiset.cons_erase hem).symm
      _ = _ := by simp only [← Multiset.singleton_add]; ac_rfl
  have hjoin : (ct p).parts = base + {r} := by
    have h := ct_join q hsep
    rw [act_involutive, hAc, hBc,
      show d + (r - d) = r by dsimp [r]; omega] at h
    exact h
  have herase : (ct p).parts.erase r = base := by
    rw [hjoin, add_comm, Multiset.singleton_add, Multiset.erase_cons_head]
  change ms = (ct p).parts.erase r + {d, r - d}
  rw [herase]
  exact hrestore

private theorem rotation_identity_reverse {k : ℕ} (p : P k) (n : ℕ)
    (x : Fin (2 * k)) :
    ((matchingPerm p * matchingPerm (e k)) ^ n)
      ((e k).val (((matchingPerm p * matchingPerm (e k)) ^ n) x)) = (e k).val x := by
  let R := matchingPerm p * matchingPerm (e k)
  have hstep (y : Fin (2 * k)) : R ((e k).val (R y)) = (e k).val y := by
    change p.val ((e k).val ((e k).val (p.val ((e k).val y)))) = (e k).val y
    rw [(e k).property.1, p.property.1]
  induction n with
  | zero => rfl
  | succ n ih =>
    change (R ^ (n + 1)) ((e k).val ((R ^ (n + 1)) x)) = (e k).val x
    calc
      _ = (R ^ n) (R ((e k).val (R ((R ^ n) x)))) := by
        rw [pow_succ R n]
        simp only [Perm.mul_apply]
        rw [show (R ^ n) (R x) = R ((R ^ n) x) by
          have he : R ^ n * R = R * R ^ n := by rw [← pow_succ, ← pow_succ']
          exact congrArg (fun f : Perm (Fin (2 * k)) => f x) he]
      _ = (R ^ n) ((e k).val ((R ^ n) x)) := by rw [hstep]
      _ = (e k).val x := ih

private theorem ct_equal_act_identity_partners {k : ℕ} (p : P k)
    {a b : Fin (2 * k)} (hc : Component p a b)
    (hcharge : charge p a = charge p b) (hne : a ≠ b) :
    ct (act a b p) = ct (act ((e k).val b) ((e k).val a) p) := by
  let R := matchingPerm p * matchingPerm (e k)
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hb : b ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a b).mpr ((same_charge_iff p hc).mp hcharge)
  obtain ⟨d, hd, hdb⟩ := (rotation_orbit_cycle p a).exists_pow_eq ha hb
  have hdpos : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    exact hne (by simpa only [hz, pow_zero, Perm.one_apply] using hdb)
  have hback : (R ^ d) ((e k).val b) = (e k).val a := by
    rw [← hdb]
    exact rotation_identity_reverse p d a
  have hpart : (edgeComponents p).part (edgeIndex b) =
      (edgeComponents p).part (edgeIndex a) := by
    apply (edgeComponents p).part_eq_of_mem
      ((edgeComponents p).part_mem.mpr (Finset.mem_univ _))
    exact (edge_component_membership p _ _).mpr
      ((component_iff_edge_components p a b).mp hc)
  have hr : (rotationOrbitFinset p ((e k).val b)).card =
      (rotationOrbitFinset p a).card := by
    rw [rotation_orbit_card, rotation_orbit_card, edgeIndex_identity_partner, hpart]
  apply Nat.Partition.ext
  rw [ct_cut p d hdpos hd hdb,
    ct_cut p d hdpos (by rwa [hr]) hback, hr]

private def sameVertex {k : ℕ} (p : P k) (a : Fin (2 * k)) (j : Fin k) :
    Fin (2 * k) :=
  if charge p (edgeVertex j) = charge p a then edgeVertex j
    else (e k).val (edgeVertex j)

private theorem sameVertex_index {k : ℕ} (p : P k) (a : Fin (2 * k)) (j : Fin k) :
    edgeIndex (sameVertex p a j) = j := by
  unfold sameVertex
  split
  · exact edgeIndex_vertex j
  · rw [edgeIndex_identity_partner, edgeIndex_vertex]

private theorem sameVertex_charge {k : ℕ} (p : P k) (a : Fin (2 * k)) (j : Fin k) :
    charge p (sameVertex p a j) = charge p a := by
  unfold sameVertex
  split
  · assumption
  · rw [charge_identity_partner]
    cases hj : charge p (edgeVertex j) <;> cases ha : charge p a <;> simp_all

private theorem sameVertex_selected {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val) :
    sameVertex p (edgeVertex q) (⟨h.val, by omega⟩ : Fin k) =
      equalChargeVertex p q h := by
  apply edgeIndex_charge_injective p
  · rw [sameVertex_index, (selected_indices p q h).1]
  · exact (sameVertex_charge p _ _).trans (selected_charges p q h).1.symm

private theorem sameVertex_act_ct_symm {k : ℕ} (p : P k) (i j : Fin k)
    (hc : Component p (edgeVertex i) (edgeVertex j)) (hne : i ≠ j) :
    ct (act (sameVertex p (edgeVertex i) j) (edgeVertex i) p) =
      ct (act (sameVertex p (edgeVertex j) i) (edgeVertex j) p) := by
  by_cases h : charge p (edgeVertex i) = charge p (edgeVertex j)
  · simp only [sameVertex, if_pos h, if_pos h.symm]
    rw [act_comm p (edgeVertex j) (edgeVertex i)]
  · have hh : charge p (edgeVertex j) ≠ charge p (edgeVertex i) := Ne.symm h
    simp only [sameVertex, if_neg h, if_neg hh]
    have hc' : Component p (edgeVertex i) ((e k).val (edgeVertex j)) :=
      hc.tail (Or.inr rfl)
    have he : charge p (edgeVertex i) = charge p ((e k).val (edgeVertex j)) := by
      rw [charge_identity_partner]
      cases hi : charge p (edgeVertex i) <;> cases hj : charge p (edgeVertex j) <;>
        simp_all
    have hn : edgeVertex i ≠ (e k).val (edgeVertex j) := by
      intro heq
      apply hne
      have hi := congrArg edgeIndex heq
      simpa only [edgeIndex_vertex, edgeIndex_identity_partner] using hi
    have ht := ct_equal_act_identity_partners p hc' he hn
    rw [(e k).property.1] at ht
    rw [act_comm p (edgeVertex i) ((e k).val (edgeVertex j)), ht,
      act_comm p ((e k).val (edgeVertex i)) (edgeVertex j)]

private noncomputable def cutPair {k : ℕ} (lam : Nat.Partition k) (p : P k)
    (i j : Fin k) : RatFunc ℂ :=
  if i = j then 0 else
    if Component p (edgeVertex i) (edgeVertex j) then
      indicator lam (act (sameVertex p (edgeVertex i) j) (edgeVertex i) p) else 0

private noncomputable def cutKernel {k : ℕ} (lam : Nat.Partition k) (p : P k)
    (r : ℕ) : RatFunc ℂ :=
  ∑ d ∈ Finset.Ioo 0 r,
    if lam.parts = (ct p).parts.erase r + {d, r - d} then 1 else 0

private theorem cutPair_symm {k : ℕ} (lam : Nat.Partition k) (p : P k)
    (i j : Fin k) : cutPair lam p i j = cutPair lam p j i := by
  by_cases he : i = j
  · subst j; rfl
  · by_cases hc : Component p (edgeVertex i) (edgeVertex j)
    · simp only [cutPair, if_neg he, if_neg (Ne.symm he), if_pos hc,
        if_pos (component_symm p hc), indicator,
        sameVertex_act_ct_symm p i j hc he]
    · have hc' : ¬ Component p (edgeVertex j) (edgeVertex i) :=
        fun h => hc (component_symm p h)
      simp only [cutPair, if_neg he, if_neg (Ne.symm he), if_neg hc, if_neg hc']

private theorem cutPair_root_sum {k : ℕ} (lam : Nat.Partition k) (p : P k)
    (i : Fin k) :
    (∑ j : Fin k, cutPair lam p i j) =
      cutKernel lam p ((edgeComponents p).part i).card := by
  let a := edgeVertex i
  let R := matchingPerm p * matchingPerm (e k)
  let C := (edgeComponents p).part i
  let r := (rotationOrbitFinset p a).card
  have ha : a ∈ rotationOrbitFinset p a :=
    (rotation_orbit_mem p a a).mpr (Perm.SameCycle.refl _ _)
  have hr : 0 < r := Finset.card_pos.mpr ⟨a, ha⟩
  have hrc : r = C.card := by
    dsimp only [r, C, a]
    rw [rotation_orbit_card, edgeIndex_vertex]
  let F : Fin r → {x : Fin (2 * k) // R.SameCycle a x} :=
    fun d => ⟨(R ^ d.val) a, (Perm.SameCycle.refl R a).pow_right⟩
  have hF : Function.Bijective F := by
    constructor
    · intro d e he
      apply Fin.ext
      exact (rotation_orbit_cycle p a).injOn_pow_apply ha d.isLt e.isLt
        (congrArg Subtype.val he)
    · intro x
      obtain ⟨n, hn, he⟩ := (rotation_orbit_cycle p a).exists_pow_eq ha
        ((rotation_orbit_mem p a x.val).mpr x.property)
      exact ⟨⟨n, hn⟩, Subtype.ext he⟩
  let G : {x : Fin (2 * k) // R.SameCycle a x} → C := fun x =>
    ⟨edgeIndex x.val, by
      simpa only [orbitEdge, a, edgeIndex_vertex, C] using (orbitEdge p a x).property⟩
  have hG : Function.Bijective G := by
    constructor
    · intro x y he
      apply (orbitEdge_bijective p a).1
      apply Subtype.ext
      change edgeIndex x.val = edgeIndex y.val
      exact congrArg (fun z : C => z.val) he
    · intro j
      obtain ⟨x, hx⟩ := (orbitEdge_bijective p a).2
        ⟨j.val, by simpa only [a, edgeIndex_vertex, C] using j.property⟩
      refine ⟨x, Subtype.ext ?_⟩
      change edgeIndex x.val = j.val
      exact congrArg (fun z : {j : Fin k //
        j ∈ (edgeComponents p).part (edgeIndex a)} => z.val) hx
  let E : Fin r ≃ C := (Equiv.ofBijective F hF).trans (Equiv.ofBijective G hG)
  have hidx (d : Fin r) : (E d).val = edgeIndex ((R ^ d.val) a) := rfl
  have hv (d : Fin r) : sameVertex p a (E d).val = (R ^ d.val) a := by
    apply edgeIndex_charge_injective p
    · rw [sameVertex_index, hidx]
    · exact (sameVertex_charge p a _).trans
        (charge_of_sameCycle p ((Perm.SameCycle.refl R a).pow_right))
  have hz : (E ⟨0, hr⟩).val = i := by
    rw [hidx]
    exact edgeIndex_vertex i
  have hdiag (d : Fin r) : (E d).val = i ↔ d.val = 0 := by
    constructor
    · intro h
      exact congrArg Fin.val (E.injective (Subtype.ext (h.trans hz.symm)))
    · intro h
      have he : d = ⟨0, hr⟩ := Fin.ext h
      rw [he, hz]
  have hrestrict : (∑ j : Fin k, cutPair lam p i j) =
      ∑ j ∈ C, if j = i then 0 else
        indicator lam (act (sameVertex p a j) a p) := by
    have hzero (j : Fin k) (hj : j ∉ C) : cutPair lam p i j = 0 := by
      have hc : ¬ Component p (edgeVertex i) (edgeVertex j) :=
        fun h => hj ((edge_component_membership p i j).mpr h)
      simp only [cutPair, if_neg hc, ite_self]
    calc
      _ = ∑ j ∈ C, cutPair lam p i j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ C)
        intro j _ hj
        exact hzero j hj
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hc := (edge_component_membership p i j).mp hj
        simp only [cutPair, if_pos hc, a, eq_comm]
  have hpoint (d : Fin r) :
      (if (E d).val = i then (0 : RatFunc ℂ) else
        indicator lam (act (sameVertex p a (E d).val) a p)) =
      if d.val = 0 then 0 else
        if lam.parts = (ct p).parts.erase r + {d.val, r - d.val} then 1 else 0 := by
    by_cases hd : d.val = 0
    · rw [if_pos hd, if_pos ((hdiag d).mpr hd)]
    · rw [if_neg hd, if_neg (fun h => hd ((hdiag d).mp h)), hv,
        act_comm p a ((R ^ d.val) a)]
      unfold indicator
      apply if_congr _ rfl rfl
      exact Nat.Partition.ext_iff.trans (by
        rw [ct_cut p d.val (by omega) d.isLt rfl]
        exact eq_comm)
  calc
    _ = ∑ j ∈ C, if j = i then 0 else
        indicator lam (act (sameVertex p a j) a p) := hrestrict
    _ = ∑ j : C, if j.val = i then 0 else
        indicator lam (act (sameVertex p a j.val) a p) :=
      (Finset.sum_coe_sort C _).symm
    _ = ∑ d : Fin r, if (E d).val = i then 0 else
        indicator lam (act (sameVertex p a (E d).val) a p) :=
      (E.sum_comp _).symm
    _ = ∑ d : Fin r, if d.val = 0 then 0 else
        if lam.parts = (ct p).parts.erase r + {d.val, r - d.val} then 1 else 0 :=
      Finset.sum_congr rfl (fun d _ => hpoint d)
    _ = ∑ d ∈ (Finset.univ.filter fun d : Fin r => 0 < d.val),
        if lam.parts = (ct p).parts.erase r + {d.val, r - d.val} then 1 else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d.val = 0
      · simp [hd]
      · rw [if_neg hd, if_pos (show 0 < d.val by omega)]
    _ = cutKernel lam p r := by
      unfold cutKernel
      apply Finset.sum_bij (fun d _ => d.val)
      · intro d hd
        exact Finset.mem_Ioo.mpr ⟨(Finset.mem_filter.mp hd).2, d.isLt⟩
      · intro d hd e he h
        exact Fin.ext h
      · intro d hd
        obtain ⟨hpos, hlt⟩ := Finset.mem_Ioo.mp hd
        exact ⟨⟨d, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩, rfl⟩
      · intro d hd
        rfl
    _ = _ := by rw [hrc]

theorem native_cut_count {k : ℕ} (lam : Nat.Partition k) (p : P k) :
    (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then
        indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) else 0) =
    (((ct p).parts.map fun (r : ℕ) => (r : RatFunc ℂ) / 2 *
      ∑ d ∈ Finset.Ioo 0 r,
        if lam.parts = (ct p).parts.erase r + {d, r - d} then 1 else 0).sum) := by
  have ht := two_triangular_sum k (cutPair lam p) (cutPair_symm lam p)
    (by intro i; simp only [cutPair, if_true])
  have htri : (∑ q : Fin k, ∑ h : Fin q.val,
      cutPair lam p q ⟨h.val, by omega⟩) =
    (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then
        indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) else 0) := by
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro h _
    have hne : q ≠ (⟨h.val, by omega⟩ : Fin k) := by
      intro he
      have hh := congrArg Fin.val he
      change q.val = h.val at hh
      omega
    have hv : edgeVertex (⟨h.val, by omega⟩ : Fin k) = earlierVertex q h 0 := by
      apply Fin.ext
      simp only [edgeVertex, earlierVertex, Fin.val_zero, zero_add]
    simp only [cutPair, if_neg hne, hv, sameVertex_selected]
  rw [htri] at ht
  simp_rw [cutPair_root_sum] at ht
  rw [component_sum p (fun C => cutKernel lam p C.card)] at ht
  have hmap : (∑ C ∈ (edgeComponents p).parts,
      (C.card : RatFunc ℂ) * cutKernel lam p C.card) =
    2 * (((ct p).parts.map fun (r : ℕ) => (r : RatFunc ℂ) / 2 *
      ∑ d ∈ Finset.Ioo 0 r,
        if lam.parts = (ct p).parts.erase r + {d, r - d} then 1 else 0).sum) := by
    change _ = 2 * (((edgeComponents p).parts.val.map Finset.card).map _).sum
    rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro C hC
    dsimp only [Function.comp_def, cutKernel]
    ring
  rw [hmap] at ht
  exact (mul_left_cancel₀ (two_ne_zero : (2 : RatFunc ℂ) ≠ 0)) ht


end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

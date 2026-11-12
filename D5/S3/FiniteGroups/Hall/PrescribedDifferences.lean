/- GID: D5/S3/FiniteGroups/Hall/PrescribedDifferences
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Hall/PrescribedDifferences
   mirror-E: none(waiver:pure-finite-group-theorem)
   anchors: []
   utility: none
   digest: Hall prescribed differences are realizable by two full finite abelian group numberings exactly when their occurrence sum is zero. -/

import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open scoped BigOperators
namespace D5.S3.FiniteGroups.Hall.PrescribedDifferences

/-- The finite exchange construction for an ordinary service with two output holes. -/
private theorem service_extend {G : Type u} [AddCommGroup G] [Fintype G]
    {m : ℕ} (r x : Fin m → G) (hx : Function.Injective x)
    (hy : Function.Injective (fun i => x i + r i))
    (hm : m + 2 ≤ Fintype.card G) (r₀ : G) :
    ∃ z : Fin (m + 1) → G, Function.Injective z ∧
      Function.Injective (fun i => z i + Fin.cons (α := fun _ => G) r₀ r i) := by
  classical
  let y : Fin m → G := fun i => x i + r i
  let Y : Finset G := Finset.univ.image y
  have hY : Y.card = m := by
    rw [Finset.card_image_of_injective _ hy]
    exact Fintype.card_fin m
  have hholes : 1 < Yᶜ.card := by
    rw [Finset.card_compl, hY]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hholes
  have hay (i : Fin m) : y i ≠ a := by
    intro h
    exact (Finset.mem_compl.mp ha) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  have hby (i : Fin m) : y i ≠ b := by
    intro h
    exact (Finset.mem_compl.mp hb) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
  let c := b - r₀ + a
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair x (fun i => c - y i) hx
    (by intro i j h; exact hy (sub_right_injective h))
  let t := c - b
  let v := c - a
  have ht (i : Fin m) : q (x i) ≠ t := by
    rw [hq]
    intro h
    exact hby i (sub_right_injective h)
  have hv (i : Fin m) : q (x i) ≠ v := by
    rw [hq]
    intro h
    exact hay i (sub_right_injective h)
  have htv : t ≠ v := by
    intro h
    exact hab (sub_right_injective h).symm
  let w : ℕ → G := fun n => (q ^ n) t
  have hws (n : ℕ) : w (n + 1) = q (w n) := by
    simp [w, pow_succ', Equiv.Perm.mul_apply]
  have hexit : ∃ n : ℕ, w n ∉ Set.range x := by
    have hs : q.SameCycle t (q.symm t) :=
      Equiv.Perm.sameCycle_symm_apply_right.mpr (Equiv.Perm.SameCycle.refl q t)
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rintro ⟨i, hi⟩
    apply ht i
    rw [hi]
    change q ((q ^ n) t) = t
    rw [hn, q.apply_symm_apply]
  let k := Nat.find hexit
  have hk : w k ∉ Set.range x := Nat.find_spec hexit
  have hbefore (j : ℕ) (hj : j < k) : w j ∈ Set.range x :=
    not_not.mp (Nat.find_min hexit hj)
  let S : Set G := {g | ∃ j < k, w j = g}
  have hforward (i : Fin m) (hi : x i ∈ S) (j : Fin m)
      (he : q (x i) = x j) : x j ∈ S := by
    obtain ⟨d, hd, hdi⟩ := hi
    have hw : w (d + 1) = x j := by rw [hws, hdi, he]
    have hd' : d + 1 < k := by
      have hne : d + 1 ≠ k := by
        intro heq
        apply hk
        exact ⟨j, hw ▸ congrArg w heq⟩
      omega
    exact ⟨d + 1, hd', hw⟩
  have hbackward (i j : Fin m) (hj : x j ∈ S)
      (he : q (x i) = x j) : x i ∈ S := by
    obtain ⟨d, hd, hdj⟩ := hj
    cases d with
    | zero => exact (ht i (he.trans hdj.symm)).elim
    | succ d =>
      refine ⟨d, by omega, ?_⟩
      apply q.injective
      rw [← hws, hdj, he]
  have hvS : v ∉ S := by
    rintro ⟨d, hd, hdv⟩
    cases d with
    | zero => exact htv hdv
    | succ d =>
      obtain ⟨i, hi⟩ := hbefore d (by omega)
      apply hv i
      rw [hi, ← hws, hdv]
  let z : Fin m → G := fun i => if x i ∈ S then q (x i) else x i
  have hz : Function.Injective z := by
    intro i j hij
    by_cases hi : x i ∈ S <;> by_cases hj : x j ∈ S
    · exact hx (q.injective (by simpa [z, hi, hj] using hij))
    · exact (hj (hforward i hi j (by simpa [z, hi, hj] using hij))).elim
    · exact (hi (hforward j hj i (by simpa [z, hi, hj] using hij.symm))).elim
    · exact hx (by simpa [z, hi, hj] using hij)
  have htz : t ∉ Set.range z := by
    rintro ⟨i, hi⟩
    by_cases his : x i ∈ S
    · exact ht i (by simpa [z, his] using hi)
    · have hkpos : 0 < k := by
        by_contra h
        have hk0 : k = 0 := by omega
        apply hk
        exact ⟨i, by simpa [hk0, w, z, his] using hi⟩
      apply his
      exact ⟨0, hkpos, by simpa [w, z, his] using hi.symm⟩
  have hout (i : Fin m) : z i + r i = if x i ∈ S then c - x i else y i := by
    by_cases hi : x i ∈ S
    · simp only [z, ite_eq_left hi, hq]
      dsimp [y]
      abel
    · simp [z, hi, y]
  have ho : Function.Injective (fun i => z i + r i) := by
    intro i j hij
    change z i + r i = z j + r j at hij
    rw [hout, hout] at hij
    by_cases hi : x i ∈ S <;> by_cases hj : x j ∈ S
    · exact hx (by simpa [hi, hj] using hij)
    · exfalso
      apply hj
      apply hbackward j i hi
      rw [hq]
      have he : c - x i = y j := by simpa [hi, hj] using hij
      rw [← he, sub_sub_cancel]
    · exfalso
      apply hi
      apply hbackward i j hj
      rw [hq]
      have he : c - x j = y i := by simpa [hi, hj] using hij.symm
      rw [← he, sub_sub_cancel]
    · exact hy (by simpa [hi, hj] using hij)
  have hao : a ∉ Set.range (fun i => z i + r i) := by
    rintro ⟨i, hi⟩
    change z i + r i = a at hi
    rw [hout] at hi
    by_cases his : x i ∈ S
    · have he : x i = v := by
        dsimp [v]
        have he : c - x i = a := by simpa [his] using hi
        rw [← he, sub_sub_cancel]
      exact hvS (he ▸ his)
    · exact hay i (by simpa [his] using hi)
  refine ⟨Fin.cons (α := fun _ => G) t z, Fin.cons_injective_of_injective htz hz, ?_⟩
  have htadd : t + r₀ = a := by dsimp [t, c]; abel
  have heq : (fun i => Fin.cons (α := fun _ => G) t z i + Fin.cons (α := fun _ => G) r₀ r i) =
      Fin.cons (α := fun _ => G) a (fun i => z i + r i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using htadd
    · simp
  rw [heq]
  exact Fin.cons_injective_of_injective hao ho


private theorem service_exists {G : Type u} [AddCommGroup G] [Fintype G]
    (m : ℕ) (hm : m < Fintype.card G) (r : Fin m → G) :
    ∃ x : Fin m → G, Function.Injective x ∧
      Function.Injective (fun i => x i + r i) := by
  induction m with
  | zero =>
    exact ⟨Fin.elim0, Function.injective_of_subsingleton _,
      Function.injective_of_subsingleton _⟩
  | succ m ih =>
    obtain ⟨x, hx, hy⟩ := ih (by omega) (fun i => r i.succ)
    obtain ⟨z, hz, ho⟩ := service_extend (fun i => r i.succ) x hx hy
      (by omega) (r 0)
    refine ⟨z, hz, ?_⟩
    have he : Fin.cons (α := fun _ => G) (r 0) (fun i => r i.succ) = r :=
      Fin.cons_self_tail r
    simpa only [he] using ho

/-- Hall's prescribed-difference theorem, with every label occurrence retained. -/
theorem numbering_iff_sum_eq_zero (G : Type u) [AddCommGroup G] [Finite G]
    (r : Fin (Nat.card G) → G) :
    (∃ x : Fin (Nat.card G) ≃ G,
      Function.Bijective (fun i => x i + r i)) ↔ (∑ i, r i) = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨m, hm⟩ : ∃ m, Nat.card G = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.card_pos (α := G)))
  revert r
  rw [hm]
  intro r
  have hcard : Fintype.card G = m + 1 := by rw [← Nat.card_eq_fintype_card, hm]
  constructor
  · rintro ⟨x, hy⟩
    have hs : (∑ i, x i) + (∑ i, r i) = ∑ i, x i := by
      rw [← Finset.sum_add_distrib]
      exact (hy.sum_comp id).trans (x.sum_comp id).symm
    exact add_left_cancel (hs.trans (add_zero _).symm)
  · intro hr
    obtain ⟨x, hx, hy⟩ := service_exists m (by omega) (fun i => r i.succ)
    let y : Fin m → G := fun i => x i + r i.succ
    obtain ⟨a, ha, _⟩ :=
      Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one x hx
        (by simpa using hcard)
    obtain ⟨b, hb, _⟩ :=
      Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one y hy
        (by simpa using hcard)
    have ha' : a ∉ Set.range x := by simpa using ha
    have hb' : b ∉ Set.range y := by simpa using hb
    let X : Fin (m + 1) → G := Fin.cons (α := fun _ => G) a x
    let Y : Fin (m + 1) → G := Fin.cons (α := fun _ => G) b y
    have hX : Function.Bijective X :=
      (Fintype.bijective_iff_injective_and_card X).mpr
        ⟨Fin.cons_injective_of_injective ha' hx, by simp [hcard]⟩
    have hY : Function.Bijective Y :=
      (Fintype.bijective_iff_injective_and_card Y).mpr
        ⟨Fin.cons_injective_of_injective hb' hy, by simp [hcard]⟩
    have hs : (∑ i, (X i + r i)) = ∑ g : G, g := by
      rw [Finset.sum_add_distrib, hr, add_zero]
      exact hX.sum_comp id
    have hhead : a + r 0 = b := by
      apply add_right_cancel (b := ∑ i : Fin m, y i)
      simpa only [Fin.sum_univ_succ, X, Y, y, Fin.cons_zero, Fin.cons_succ, id_eq]
        using hs.trans (hY.sum_comp id).symm
    refine ⟨Equiv.ofBijective X hX, ?_⟩
    have heq : (fun i => X i + r i) = Y := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hhead
      · rfl
    change Function.Bijective (fun i => X i + r i)
    rw [heq]
    exact hY

#print axioms numbering_iff_sum_eq_zero

end D5.S3.FiniteGroups.Hall.PrescribedDifferences

module

public import OmegaBuild.Commands
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Finset.Order

/-!
Omega original.

Torsion-freeness characterizes greatest support in every finite additive
observation fiber of an abelian group. The targets are arbitrary additive
monoids, with the original operations and equality throughout.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.Refinement.GroupSupport

universe u v w

/-- Torsion-freeness in terms of positive natural scalar multiples. -/
def TorsionFree (G : Type u) [AddCommGroup G] : Prop :=
  ∀ k : ℕ, 0 < k → ∀ x : G, k • x = 0 → x = 0

/-- Every finite additive observation fiber has a greatest support. The target
shares the coefficient universe and need only be an additive monoid. -/
def UniversalGreatestSupport (G : Type u) [AddCommGroup G] : Prop :=
  ∀ (n : ℕ) (T : Type u) [AddMonoid T]
    (F : (Fin n → G) →+ T) (p : Fin n → G),
    ∃ r : Fin n → G, F r = F p ∧
      ∀ q : Fin n → G, F q = F p → ∀ i : Fin n, q i ≠ 0 → r i ≠ 0

variable {G : Type u} [AddCommGroup G]

private theorem eq_zero_of_zsmul_eq_zero (ht : TorsionFree G) (z : ℤ) (x : G)
    (h : z • x = 0) : z = 0 ∨ x = 0 := by
  cases z with
  | ofNat n =>
    by_cases hn : n = 0
    · exact Or.inl (by simp [hn])
    · exact Or.inr (ht n (Nat.pos_of_ne_zero hn) x (by simpa using h))
  | negSucc n =>
    right
    apply ht (n + 1) (Nat.succ_pos _) x
    simpa using h

private theorem nat_parameter_injective (ht : TorsionFree G) {x : G} (hx : x ≠ 0) :
    Function.Injective (fun m : ℕ => m • x) := by
  intro m n h
  have hz : ((m : ℤ) - (n : ℤ)) • x = 0 := by
    simpa [sub_zsmul, h]
  rcases eq_zero_of_zsmul_eq_zero ht _ _ hz with hmn | hzero
  · exact_mod_cast (sub_eq_zero.mp hmn)
  · exact (hx hzero).elim

/-- A finite family of affine integer lines in a torsion-free group can avoid
zero simultaneously wherever at least one endpoint is nonzero. -/
theorem exists_line_support_union (ht : TorsionFree G)
    {I : Type v} [Finite I] (p q : I → G) :
    ∃ m : ℕ, ∀ i : I, p i ≠ 0 ∨ q i ≠ 0 →
      p i + m • (q i - p i) ≠ 0 := by
  classical
  let bad : I → Set ℕ := fun i =>
    {m | p i + m • (q i - p i) = 0 ∧ (p i ≠ 0 ∨ q i ≠ 0)}
  have hb (i : I) : (bad i).Finite := by
    apply Set.Subsingleton.finite
    intro m hm n hn
    have hd : q i - p i ≠ 0 := by
      intro hd
      have hqp : q i = p i := sub_eq_zero.mp hd
      have hp : p i = 0 := by simpa [hd] using hm.1
      exact hm.2.elim (fun h => h hp) (fun h => h (hqp.trans hp))
    apply nat_parameter_injective ht hd
    exact add_left_cancel (hm.1.trans hn.1.symm)
  obtain ⟨m, hm⟩ := (Set.finite_iUnion hb).exists_notMem
  refine ⟨m, ?_⟩
  intro i hi hz
  exact hm (Set.mem_iUnion.mpr ⟨i, hz, hi⟩)

/-- Feasible supports in a finite power are directed under inclusion, even
when the observation target has no group structure. -/
theorem fiber_support_union (ht : TorsionFree G)
    {I : Type v} [Finite I] {T : Type w} [AddMonoid T]
    (F : (I → G) →+ T) (p q : I → G) (hpq : F q = F p) :
    ∃ r : I → G, F r = F p ∧
      ∀ i : I, p i ≠ 0 ∨ q i ≠ 0 → r i ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_line_support_union ht p q
  refine ⟨p + m • (q - p), ?_, hm⟩
  have hk : q - p ∈ F.ker := (F.sub_mem_ker_iff).mpr hpq
  rw [map_add, AddMonoidHom.mem_ker.mp (F.ker.nsmul_mem hk m), add_zero]

/-- Torsion-free coefficients give greatest support in every nonempty fiber
on an arbitrary finite coordinate type. -/
theorem exists_greatest_fiber_support (ht : TorsionFree G)
    {I : Type v} [Finite I] {T : Type w} [AddMonoid T]
    (F : (I → G) →+ T) (p : I → G) :
    ∃ r : I → G, F r = F p ∧
      ∀ q : I → G, F q = F p → ∀ i : I, q i ≠ 0 → r i ≠ 0 := by
  classical
  let A := {q : I → G // F q = F p}
  let base : A := ⟨p, rfl⟩
  let : Nonempty A := ⟨base⟩
  let s : A → Set I := fun q => {i | q.val i ≠ 0}
  have hd : Directed (· ⊆ ·) s := by
    intro a b
    obtain ⟨r, hrF, hr⟩ := fiber_support_union ht F a.val b.val
      (b.property.trans a.property.symm)
    refine ⟨⟨r, hrF.trans a.property⟩, ?_, ?_⟩
    · exact fun i hi => hr i (Or.inl hi)
    · exact fun i hi => hr i (Or.inr hi)
  let c : I → A := fun i =>
    if h : ∃ q : A, q.val i ≠ 0 then Classical.choose h else base
  let := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := hd.finset_le (Finset.univ.image c)
  refine ⟨r.val, r.property, ?_⟩
  intro q hq i hi
  have hex : ∃ q : A, q.val i ≠ 0 := ⟨⟨q, hq⟩, hi⟩
  have hci : (c i).val i ≠ 0 := by
    dsimp [c]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  exact hr (c i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hci

private theorem residue_smul (k : ℕ) (hk : 0 < k) (x : G) (hx : k • x = 0)
    (z : ℤ) : ∃ i : Fin k, (i.val : ℤ) • x = z • x := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have hnonneg := Int.emod_nonneg z (ne_of_gt hkz)
  have hlt := Int.emod_lt_of_pos z hkz
  let i : Fin k := ⟨(z % (k : ℤ)).toNat, by omega⟩
  refine ⟨i, ?_⟩
  have hi : (i.val : ℤ) = z % (k : ℤ) := Int.toNat_of_nonneg hnonneg
  rw [hi]
  have hxz : (k : ℤ) • x = 0 := by simpa using hx
  calc
    (z % (k : ℤ)) • x =
        (z % (k : ℤ) + (k : ℤ) * (z / (k : ℤ))) • x := by
      rw [add_zsmul, mul_comm (k : ℤ), mul_zsmul, hxz, zsmul_zero, add_zero]
    _ = z • x := by rw [Int.emod_add_mul_ediv]

/-- A nonzero torsion element obstructs universal greatest support in the
whole ambient group, using a quotient by its cyclic diagonal subgroup. -/
theorem torsion_free_of_universal_greatest_support (h : UniversalGreatestSupport G) :
    TorsionFree G := by
  classical
  intro k hk x hx
  by_contra hxn
  let d : Fin k → G := fun _ => x
  let K : AddSubgroup (Fin k → G) := AddSubgroup.zmultiples d
  let F : (Fin k → G) →+ ((Fin k → G) ⧸ K) := QuotientAddGroup.mk' K
  let p : Fin k → G := fun i => -(i.val • x)
  obtain ⟨r, hrF, hr⟩ := h k ((Fin k → G) ⧸ K) F p
  have hd : F d = 0 := by
    apply (QuotientAddGroup.eq_zero_iff d).mpr
    exact AddSubgroup.mem_zmultiples d
  have hpd : F (p + d) = F p := by rw [map_add, hd, add_zero]
  have hrall (i : Fin k) : r i ≠ 0 := by
    by_cases hp : p i = 0
    · apply hr (p + d) hpd i
      simpa [Pi.add_apply, d, hp] using hxn
    · exact hr p rfl i hp
  have hmem : r - p ∈ K := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp hrF
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  obtain ⟨i, hi⟩ := residue_smul k hk x hx z
  have hri : r i - p i = z • x := by
    simpa [d] using (congrFun hz i).symm
  apply hrall i
  have hn : (i.val : ℤ) • x = i.val • x := by simp
  rw [hn] at hi
  dsimp [p] at hri
  rw [← hi] at hri
  exact add_right_cancel (by simpa [sub_neg_eq_add] using hri : r i + i.val • x = 0 + i.val • x)

/-- Exact characterization for every abelian group, including the trivial
group and the empty finite power. -/
theorem torsion_free_iff_universal_greatest_support (G : Type u) [AddCommGroup G] :
    TorsionFree G ↔ UniversalGreatestSupport G := by
  constructor
  · intro ht n T inst F p
    exact exists_greatest_fiber_support ht F p
  · exact torsion_free_of_universal_greatest_support

end Omega.Refinement.GroupSupport

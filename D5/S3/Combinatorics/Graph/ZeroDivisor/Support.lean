/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/Support
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/Support
   mirror-E: none(waiver:finite-ring-support-correspondence)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: Actual nonzero zero divisors have exact CRT support fibers. -/

import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.Support

/-- A vertex is an actual nonzero ring element with a nonzero annihilator. -/
abbrev Vertex (R : Type*) [CommRing R] :=
  {x : R // x ≠ 0 ∧ ∃ y : R, y ≠ 0 ∧ x * y = 0}

/-- Distinct actual vertices are adjacent precisely when their product vanishes. -/
def graph (R : Type*) [CommRing R] : SimpleGraph (Vertex R) where
  Adj u v := u ≠ v ∧ u.1 * v.1 = 0
  symm := ⟨by rintro u v ⟨hne, hmul⟩; exact ⟨hne.symm, by simpa [mul_comm] using hmul⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
variable {K : ι → Type*} [∀ i, CommRing (K i)]

/-- The nonzero coordinate support under a specified ring equivalence. -/
def support (e : R ≃+* ∀ i, K i) (x : R) : Finset ι :=
  Finset.univ.filter fun i => e x i ≠ 0

private theorem mem_support (e : R ≃+* ∀ i, K i) (x : R) (i : ι) :
    i ∈ support e x ↔ e x i ≠ 0 := by
  simp [support]

private theorem support_nonempty (e : R ≃+* ∀ i, K i) (x : R) :
    (support e x).Nonempty ↔ x ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty]
  have h : support e x = ∅ ↔ x = 0 := by
    constructor
    · intro h
      apply e.injective
      ext i
      have hi : i ∉ support e x := by rw [h]; simp
      simpa [mem_support] using hi
    · rintro rfl
      simp [support]
  exact not_congr h

variable [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)]

private theorem mul_eq_zero_iff (e : R ≃+* ∀ i, K i) (x y : R) :
    x * y = 0 ↔ Disjoint (support e x) (support e y) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i hx hy
    have hi := congrFun (congrArg e h) i
    have hm : e x i * e y i = 0 := by simpa using hi
    exact (mul_ne_zero ((mem_support e x i).mp hx) ((mem_support e y i).mp hy)) hm
  · intro h
    apply e.injective
    ext i
    by_cases hx : e x i = 0
    · simp [hx]
    · have hy : e y i = 0 := by
        by_contra hy
        exact h ((mem_support e x i).mpr hx) ((mem_support e y i).mpr hy)
      simp [hy]

private theorem vertex_iff (e : R ≃+* ∀ i, K i) (x : R) :
    (x ≠ 0 ∧ ∃ y : R, y ≠ 0 ∧ x * y = 0) ↔
      (support e x).Nonempty ∧ support e x ≠ Finset.univ := by
  rw [← support_nonempty e x]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨y, hy, hxy⟩ hall
    obtain ⟨i, hi⟩ := (support_nonempty e y).mpr hy
    exact Finset.disjoint_left.mp ((mul_eq_zero_iff e x y).mp hxy)
      (hall.symm ▸ Finset.mem_univ i) hi
  · intro hproper
    obtain ⟨i, hi⟩ := Finset.exists_notMem_of_ne_univ hproper
    let y : ∀ j, K j := Pi.single i 1
    have hy : e.symm y ≠ 0 := by
      intro hzero
      have hz := congrFun (congrArg e hzero) i
      have : (1 : K i) = 0 := by simpa [y] using hz
      exact one_ne_zero this
    refine ⟨e.symm y, hy, ?_⟩
    apply e.injective
    ext j
    by_cases hji : j = i
    · subst j
      have hx : e x i = 0 := by simpa [mem_support] using hi
      simp [y, hx]
    · simp [y, Pi.single_eq_of_ne hji]

/-- The coordinate model retains every coordinate value, removing exactly the
empty and full support fibers. It is not a quotient by support. -/
abbrev SupportedVertex :=
  {x : ∀ i, K i // (support (RingEquiv.refl _) x).Nonempty ∧
    support (RingEquiv.refl _) x ≠ Finset.univ}

/-- The actual vertex correspondence, including both excluded endpoint fibers. -/
def vertexEquiv (e : R ≃+* ∀ i, K i) : Vertex R ≃ SupportedVertex (K := K) where
  toFun x := ⟨e x.1, by
    simpa [support] using (vertex_iff e x.1).mp x.2⟩
  invFun x := ⟨e.symm x.1, (vertex_iff e _).mpr (by simpa [support] using x.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)

/-- Adjacency of coordinate vertices is disjointness of their nonzero supports. -/
def supportGraph : SimpleGraph (SupportedVertex (K := K)) where
  Adj u v := u ≠ v ∧ Disjoint (support (RingEquiv.refl _) u.1)
    (support (RingEquiv.refl _) v.1)
  symm := ⟨by rintro u v ⟨hne, hd⟩; exact ⟨hne.symm, hd.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

/-- A graph isomorphism from actual ring vertices to their full coordinate data. -/
def actualSupportIso (e : R ≃+* ∀ i, K i) :
    graph R ≃g supportGraph (K := K) where
  toEquiv := vertexEquiv e
  map_rel_iff' := by
    intro u v
    change (_ ≠ _ ∧ _) ↔ (u ≠ v ∧ u.1 * v.1 = 0)
    rw [(vertexEquiv e).injective.ne_iff, mul_eq_zero_iff e]
    rfl

private def fiberEquiv (e : R ≃+* ∀ i, K i) (S : Finset ι)
    (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    {x : Vertex R // support e x.1 = S} ≃ (∀ i : S, {a : K i.1 // a ≠ 0}) where
  toFun x i := ⟨e x.1.1 i.1, (mem_support e _ _).mp (x.2.symm ▸ i.2)⟩
  invFun f := by
    let z : ∀ i, K i := fun i => if hi : i ∈ S then (f ⟨i, hi⟩).1 else 0
    have hs : support e (e.symm z) = S := by
      ext i
      rw [mem_support]
      simp only [RingEquiv.apply_symm_apply]
      by_cases hi : i ∈ S
      · simpa [z, hi] using (f ⟨i, hi⟩).2
      · simp [z, hi]
    exact ⟨⟨e.symm z, (vertex_iff e _).mpr (hs.symm ▸ ⟨hS, hSu⟩)⟩, hs⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply e.injective
    ext i
    simp only [RingEquiv.apply_symm_apply]
    dsimp
    split_ifs with hi
    · rfl
    · have hz : e x.1.1 i = 0 := by
        have : i ∉ support e x.1.1 := by rwa [x.2]
        simpa [mem_support] using this
      exact hz.symm
  right_inv f := by
    funext i
    apply Subtype.ext
    simp [dif_pos i.2]

/-- Every genuine support cell consists of exactly the independent choices of
nonzero coordinate values. The equality counts actual ring elements. -/
theorem support_fiber_card [∀ i, Fintype (K i)]
    (e : R ≃+* ∀ i, K i) (S : Finset ι)
    (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    Nat.card {x : Vertex R // support e x.1 = S} =
      ∏ i ∈ S, (Fintype.card (K i) - 1) := by
  rw [Nat.card_congr (fiberEquiv e S hS hSu), Nat.card_eq_fintype_card,
    Fintype.card_pi]
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact Finset.prod_coe_sort S _

/-- The native Chinese remainder equivalence for every finite pairwise coprime
modulus family, directly reusing Mathlib's ring equivalence. -/
def crt (p : ι → ℕ) (hcop : Pairwise (Nat.Coprime on p)) :
    ZMod (∏ i, p i) ≃+* ∀ i, ZMod (p i) :=
  ZMod.prodEquivPi p hcop

#print axioms support_fiber_card

end D5.S3.Combinatorics.Graph.ZeroDivisor.Support

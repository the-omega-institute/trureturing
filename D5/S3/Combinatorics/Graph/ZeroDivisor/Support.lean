/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/Support
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/Support
   mirror-E: none(waiver:finite-ring-support-correspondence)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: Actual nonzero zero divisors have exact CRT support fibers. -/

import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import Mathlib.Data.ZMod.QuotientRing

/-! Actual zero-divisor vertices, their support graph, and exact support multiplicities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Classical
open Function

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.Support

/-- A vertex is an actual nonzero ring element with a nonzero annihilator. -/
abbrev Vertex (R : Type*) [CommRing R] :=
  {x : R // x ≠ 0 ∧ ∃ y : R, y ≠ 0 ∧ x * y = 0}

/-- Distinct actual vertices are adjacent precisely when their product vanishes. -/
def graph (R : Type*) [CommRing R] : SimpleGraph (Vertex R) where
  Adj u v := u ≠ v ∧ u.1 * v.1 = 0
  symm := ⟨by rintro u v ⟨hne, hmul⟩; exact ⟨hne.symm, by simpa [mul_comm] using hmul⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

variable {ι R : Type*} [Fintype ι] [CommRing R]
variable {K : ι → Type*} [∀ i, CommRing (K i)]

/-- The finite set of indices with nonzero coordinate value. -/
def coordinateSupport (x : ∀ i, K i) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0

/-- The nonzero coordinate support under a specified ring equivalence. -/
def support (e : R ≃+* ∀ i, K i) (x : R) : Finset ι :=
  coordinateSupport (e x)

private theorem mem_support (e : R ≃+* ∀ i, K i) (x : R) (i : ι) :
    i ∈ support e x ↔ e x i ≠ 0 := by
  simp [support, coordinateSupport]

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
      simp [support, coordinateSupport]
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
    obtain ⟨i, hi⟩ := not_forall.mp (fun h => hproper (Finset.eq_univ_of_forall h))
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
  {x : ∀ i, K i // (coordinateSupport x).Nonempty ∧
    coordinateSupport x ≠ Finset.univ}

/-- The actual vertex correspondence, including both excluded endpoint fibers. -/
def vertexEquiv (e : R ≃+* ∀ i, K i) : Vertex R ≃ SupportedVertex (K := K) where
  toFun x := ⟨e x.1, (vertex_iff e x.1).mp x.2⟩
  invFun x := ⟨e.symm x.1, (vertex_iff e _).mpr (by
    simpa only [support, RingEquiv.apply_symm_apply] using x.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv x := Subtype.ext (e.apply_symm_apply x.1)

/-- Adjacency of coordinate vertices is disjointness of their nonzero supports. -/
def supportGraph : SimpleGraph (SupportedVertex (K := K)) where
  Adj u v := u ≠ v ∧ Disjoint (coordinateSupport u.1) (coordinateSupport v.1)
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
    simp

/-- Every genuine support cell consists of exactly the independent choices of
nonzero coordinate values. The equality counts actual ring elements. -/
private theorem support_fiber_card [∀ i, Fintype (K i)]
    (e : R ≃+* ∀ i, K i) (S : Finset ι)
    (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    Nat.card {x : Vertex R // support e x.1 = S} =
      ∏ i ∈ S, (Fintype.card (K i) - 1) := by
  rw [Nat.card_congr (fiberEquiv e S hS hSu), Nat.card_eq_fintype_card,
    Fintype.card_pi]
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (K i) - 1)

/-- The native Chinese remainder equivalence for every finite pairwise coprime
modulus family, directly reusing Mathlib's ring equivalence. -/
def crt (p : ι → ℕ) (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j)) :
    ZMod (∏ i, p i) ≃+* ∀ i, ZMod (p i) :=
  ZMod.prodEquivPi p hcop

/-- Exact multiplicities of actual nonzero zero divisors for every finite
pairwise coprime prime family, with no upper bound on the primes. -/
theorem prime_support_fiber_card (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j))
    (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    Nat.card {x : Vertex (ZMod (∏ i, p i)) // support (crt p hcop) x.1 = S} =
      ∏ i ∈ S, (p i - 1) := by
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  letI : ∀ i, Fintype (ZMod (p i)) := fun i => inferInstance
  letI : ∀ i, Nontrivial (ZMod (p i)) := fun i => inferInstance
  letI : ∀ i, NoZeroDivisors (ZMod (p i)) := fun i => inferInstance
  simpa only [ZMod.card] using support_fiber_card (crt p hcop) S hS hSu

/-- Subsets using only the two-coordinate cells. -/
def pairFamily (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) :
    Finset (Finset (Vertex R)) :=
  V.powerset.filter fun S => ∀ x ∈ S, (support e x.1).card = 2

/-- Subsets meeting the singleton cell at i, with all their supports containing i. -/
def starFamily (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) :
    Finset (Finset (Vertex R)) :=
  V.powerset.filter fun S =>
    (∃ x ∈ S, support e x.1 = {i}) ∧ ∀ x ∈ S, i ∈ support e x.1

private theorem independent_four (hι : Fintype.card ι = 3)
    (e : R ≃+* ∀ i, K i) (S : Finset (Vertex R)) :
    (graph R).IsIndepSet (S : Set (Vertex R)) ↔
      (∀ x ∈ S, (support e x.1).card = 2) ∨
        ∃ i, (∃ x ∈ S, support e x.1 = {i}) ∧ ∀ x ∈ S, i ∈ support e x.1 := by
  constructor
  · intro hind
    by_cases hpairs : ∀ x ∈ S, (support e x.1).card = 2
    · exact Or.inl hpairs
    · right
      push_neg at hpairs
      obtain ⟨u, hu, hcard⟩ := hpairs
      have hv := (vertex_iff e u.1).mp u.2
      have hpos := Finset.card_pos.mpr hv.1
      have hlt : (support e u.1).card < 3 := by
        simpa only [hι] using (Finset.card_lt_iff_ne_univ _).mpr hv.2
      have hone : (support e u.1).card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
      refine ⟨i, ⟨u, hu, hi⟩, ?_⟩
      intro v hvS
      by_cases huv : u = v
      · subst v
        simp [hi]
      · by_contra hiv
        have hd : Disjoint (support e u.1) (support e v.1) := by
          simpa [hi] using hiv
        exact hind hu hvS huv ⟨huv, (mul_eq_zero_iff e u.1 v.1).mpr hd⟩
  · rintro (hpairs | ⟨i, _, hall⟩)
    · intro u hu v hv _ hadj
      have hd := (mul_eq_zero_iff e u.1 v.1).mp hadj.2
      have hle : (support e u.1 ∪ support e v.1).card ≤ 3 := by
        simpa only [hι] using (support e u.1 ∪ support e v.1).card_le_univ
      rw [Finset.card_union_of_disjoint hd, hpairs u hu, hpairs v hv] at hle
      omega
    · intro u hu v hv _ hadj
      exact Finset.disjoint_left.mp ((mul_eq_zero_iff e u.1 v.1).mp hadj.2)
        (hall u hu) (hall v hv)

/-- All actual independent subsets split into four disjoint families when there
are exactly three domain coordinates. The ambient finite vertex domain is arbitrary. -/
theorem configurations_four_families (hι : Fintype.card ι = 3)
    (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) :
    D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations (graph R) V =
      pairFamily e V ∪ Finset.univ.biUnion (starFamily e V) ∧
    (∀ i, Disjoint (pairFamily e V) (starFamily e V i)) ∧
    Pairwise (fun i j => Disjoint (starFamily e V i) (starFamily e V j)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext S
    simp only [D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations,
      pairFamily, starFamily, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_filter, Finset.mem_powerset]
    rw [independent_four hι e S]
    aesop
  · intro i
    apply Finset.disjoint_left.mpr
    intro S hpair hstar
    have hpairs := (Finset.mem_filter.mp hpair).2
    obtain ⟨u, hu, hi⟩ := (Finset.mem_filter.mp hstar).2.1
    have hc := hpairs u hu
    simp [hi] at hc
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro S hi hj
    obtain ⟨u, hu, hui⟩ := (Finset.mem_filter.mp hi).2.1
    have hju := (Finset.mem_filter.mp hj).2.2 u hu
    rw [hui] at hju
    exact hij (Finset.mem_singleton.mp hju).symm

#print axioms prime_support_fiber_card
#print axioms configurations_four_families

end D5.S3.Combinatorics.Graph.ZeroDivisor.Support

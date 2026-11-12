/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/Support
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/Support
   mirror-E: none(waiver:finite-ring-support-correspondence)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: Actual zero divisors have exact CRT cells and four disjoint independent-set families. -/

import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import Mathlib.Data.ZMod.QuotientRing

/-! Actual zero-divisor vertices, their support graph, and exact support multiplicities.

The three-prime support classification and four-family argument appear in
Bilal Ahmad Rather, arXiv:2606.04789v1, Theorem 4.1. The proofs below use
Mathlib's native CRT and the repository's actual independent configurations.
-/

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
      push Not at hpairs
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

open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

/-- Actual vertices in the two-coordinate cells of a finite domain. -/
def pairDomain (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) : Finset (Vertex R) :=
  V.filter fun x => (support e x.1).card = 2

/-- Actual vertices whose supports contain a specified coordinate. -/
def starDomain (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) :
    Finset (Vertex R) := V.filter fun x => i ∈ support e x.1

/-- The same domain with its singleton-support cell removed. -/
def starTailDomain (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) :
    Finset (Vertex R) := (starDomain e V i).filter fun x => support e x.1 ≠ {i}

omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem pair_family_powerset (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) :
    pairFamily e V = (pairDomain e V).powerset := by
  ext S
  simp only [pairFamily, pairDomain, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hV, hpair⟩ x hx
    exact ⟨hV hx, hpair x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem star_family_sdiff (e : R ≃+* ∀ i, K i)
    (V : Finset (Vertex R)) (i : ι) :
    starFamily e V i = (starDomain e V i).powerset \
      (starTailDomain e V i).powerset := by
  ext S
  simp only [starFamily, starDomain, starTailDomain, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_powerset, Finset.subset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hV, ⟨u, hu, hui⟩, hall⟩
    refine ⟨fun x hx => ⟨hV hx, hall x hx⟩, ?_⟩
    intro htail
    exact (htail hu).2 hui
  · rintro ⟨hdom, hnot⟩
    refine ⟨fun x hx => (hdom hx).1, ?_, fun x hx => (hdom hx).2⟩
    by_contra hnone
    apply hnot
    intro x hx
    exact ⟨hdom hx, fun he => hnone ⟨x, hx, he⟩⟩

private theorem powerset_polynomial {α : Type*} (V : Finset α) :
    (∑ S ∈ V.powerset, (Polynomial.X : Polynomial ℤ) ^ S.card) =
      (1 + Polynomial.X) ^ V.card := by
  simpa only [Finset.prod_const] using
    (Finset.prod_one_add (f := fun _ : α => (Polynomial.X : Polynomial ℤ)) V).symm

omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem star_polynomial (e : R ≃+* ∀ i, K i)
    (V : Finset (Vertex R)) (i : ι) :
    (∑ S ∈ starFamily e V i, (Polynomial.X : Polynomial ℤ) ^ S.card) =
      (1 + Polynomial.X) ^ (starDomain e V i).card -
        (1 + Polynomial.X) ^ (starTailDomain e V i).card := by
  rw [star_family_sdiff, Finset.sum_sdiff_eq_sub, powerset_polynomial,
    powerset_polynomial]
  exact Finset.powerset_mono.mpr (Finset.filter_subset _ _)

/-- The native independence polynomial is the generating function of the four
actual families. The exponents are cardinalities of actual finite vertex domains. -/
theorem independencePolynomial_four_families (hι : Fintype.card ι = 3)
    (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) :
    independencePolynomial (graph R) V =
      (1 + Polynomial.X) ^ (pairDomain e V).card +
        ∑ i, ((1 + Polynomial.X) ^ (starDomain e V i).card -
          (1 + Polynomial.X) ^ (starTailDomain e V i).card) := by
  obtain ⟨hfamily, hpair, hstars⟩ := configurations_four_families hι e V
  have hd : Disjoint (pairFamily e V) (Finset.univ.biUnion (starFamily e V)) := by
    exact (Finset.disjoint_biUnion_right _ _ _).mpr (fun i _ => hpair i)
  unfold independencePolynomial partition
  simp only [Finset.prod_const]
  rw [hfamily, Finset.sum_union hd, Finset.sum_biUnion]
  · rw [pair_family_powerset, powerset_polynomial]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => star_polynomial e V i)
  · intro i _ j _ hij
    exact hstars hij

private theorem coefficient_card (V : Finset (Vertex R)) (k : ℕ) :
    (independencePolynomial (graph R) V).coeff k =
      (((configurations (graph R) V).filter fun S => S.card = k).card : ℤ) := by
  simp [independencePolynomial, partition, Polynomial.coeff_X_pow, eq_comm]

/-- Each coefficient counts all actual independent k-subsets, with the exact
binomial expression supplied by the native disjoint-family polynomial identity. -/
theorem independent_count_formula (hι : Fintype.card ι = 3)
    (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (k : ℕ) :
    (((configurations (graph R) V).filter fun S => S.card = k).card : ℤ) =
      ((pairDomain e V).card.choose k : ℤ) +
        ∑ i, (((starDomain e V i).card.choose k : ℤ) -
          ((starTailDomain e V i).card.choose k : ℤ)) := by
  rw [← coefficient_card, independencePolynomial_four_families hι e V]
  simp [Polynomial.coeff_one_add_X_pow]

private theorem support_filter_card [Fintype R] [∀ i, Fintype (K i)]
    (e : R ≃+* ∀ i, K i) (P : Finset ι → Prop) :
    ((Finset.univ : Finset (Vertex R)).filter fun x => P (support e x.1)).card =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter
        (fun S => S.Nonempty ∧ S ≠ Finset.univ ∧ P S),
          ∏ i ∈ S, (Fintype.card (K i) - 1) := by
  let T := (Finset.univ : Finset (Finset ι)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ ∧ P S)
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Vertex R)) T (fun x => support e x.1)
  have hright : ((Finset.univ : Finset (Vertex R)).filter
      (fun x => support e x.1 ∈ T)) = Finset.univ.filter
        (fun x : Vertex R => P (support e x.1)) := by
    ext x
    have hv := (vertex_iff e x.1).mp x.2
    simp [T, hv.1, hv.2]
  rw [hright] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro S hS
  have hs := (Finset.mem_filter.mp hS).2
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    support_fiber_card e S hs.1 hs.2.1

/-- The exact four-family polynomial on the full actual ring graph, with all
six support multiplicities evaluated. The finite coordinate domains are arbitrary. -/
theorem independencePolynomial_three_coordinates
    {L : Fin 3 → Type*} [∀ i, CommRing (L i)] [∀ i, NoZeroDivisors (L i)]
    [∀ i, Nontrivial (L i)] [∀ i, Fintype (L i)] [Fintype R]
    (e : R ≃+* ∀ i, L i) :
    let a := Fintype.card (L 0) - 1
    let b := Fintype.card (L 1) - 1
    let c := Fintype.card (L 2) - 1
    independencePolynomial (graph R) Finset.univ =
      (1 + Polynomial.X) ^ (a*b + a*c + b*c) +
      ((1 + Polynomial.X) ^ (a + a*b + a*c) -
        (1 + Polynomial.X) ^ (a*b + a*c)) +
      ((1 + Polynomial.X) ^ (b + a*b + b*c) -
        (1 + Polynomial.X) ^ (a*b + b*c)) +
      ((1 + Polynomial.X) ^ (c + a*c + b*c) -
        (1 + Polynomial.X) ^ (a*c + b*c)) := by
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} := by decide
  have hfin : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  have hpair := support_filter_card e (fun S => S.card = 2)
  have hs0 := support_filter_card e (fun S => (0 : Fin 3) ∈ S)
  have hs1 := support_filter_card e (fun S => (1 : Fin 3) ∈ S)
  have hs2 := support_filter_card e (fun S => (2 : Fin 3) ∈ S)
  have ht0 := support_filter_card e (fun S => (0 : Fin 3) ∈ S ∧ S ≠ {0})
  have ht1 := support_filter_card e (fun S => (1 : Fin 3) ∈ S ∧ S ≠ {1})
  have ht2 := support_filter_card e (fun S => (2 : Fin 3) ∈ S ∧ S ≠ {2})
  simp only [hU, hfin, Finset.sum_filter] at hpair hs0 hs1 hs2 ht0 ht1 ht2
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at hpair hs0 hs1 hs2 ht0 ht1 ht2
  simp +decide [Finset.prod_insert] at hpair hs0 hs1 hs2 ht0 ht1 ht2
  have hp' : (pairDomain e Finset.univ).card =
      (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) +
      (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) +
      (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    unfold pairDomain
    omega
  have hs0' : (starDomain e Finset.univ 0).card =
      (Fintype.card (L 0)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) +
      (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs0
  have hs1' : (starDomain e Finset.univ 1).card =
      (Fintype.card (L 1)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) +
      (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs1
  have hs2' : (starDomain e Finset.univ 2).card =
      (Fintype.card (L 2)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) +
      (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs2
  have ht0' : (starTailDomain e Finset.univ 0).card =
      (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) +
      (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht0
  have ht1' : (starTailDomain e Finset.univ 1).card =
      (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) +
      (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht1
  have ht2' : (starTailDomain e Finset.univ 2).card =
      (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) +
      (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht2
  rw [independencePolynomial_four_families (by decide) e, hp']
  simp only [Fin.sum_univ_three, hs0', hs1', hs2', ht0', ht1', ht2']
  ring

#print axioms independencePolynomial_three_coordinates

#print axioms independencePolynomial_four_families
#print axioms independent_count_formula

#print axioms prime_support_fiber_card
#print axioms configurations_four_families

example (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p < q) (hqr : q < r) :
    letI : NeZero (p * q * r) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
    independencePolynomial (graph (ZMod (p * q * r))) Finset.univ =
      (1 + Polynomial.X) ^ ((p - 1) * (q - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1)) +
      ((1 + Polynomial.X) ^ ((p - 1) + (p - 1) * (q - 1) + (p - 1) * (r - 1)) -
        (1 + Polynomial.X) ^ ((p - 1) * (q - 1) + (p - 1) * (r - 1))) +
      ((1 + Polynomial.X) ^ ((q - 1) + (p - 1) * (q - 1) + (q - 1) * (r - 1)) -
        (1 + Polynomial.X) ^ ((p - 1) * (q - 1) + (q - 1) * (r - 1))) +
      ((1 + Polynomial.X) ^ ((r - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1)) -
        (1 + Polynomial.X) ^ ((p - 1) * (r - 1) + (q - 1) * (r - 1))) := by
  let m : Fin 3 → ℕ := ![p, q, r]
  letI : ∀ i, Fact (m i).Prime := fun i => by
    fin_cases i
    · exact ⟨hp⟩
    · exact ⟨hq⟩
    · exact ⟨hr⟩
  letI : ∀ i, NeZero (m i) := fun i => ⟨(Fact.out : (m i).Prime).ne_zero⟩
  letI : ∀ i, Fintype (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, Nontrivial (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, NoZeroDivisors (ZMod (m i)) := fun i => inferInstance
  have hc : Pairwise (fun i j => Nat.Coprime (m i) (m j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢
    · exact (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)
    · exact (Nat.coprime_primes hp hr).mpr (ne_of_lt (hpq.trans hqr))
    · exact (Nat.coprime_primes hq hp).mpr (ne_of_gt hpq)
    · exact (Nat.coprime_primes hq hr).mpr (ne_of_lt hqr)
    · exact (Nat.coprime_primes hr hp).mpr (ne_of_gt (hpq.trans hqr))
    · exact (Nat.coprime_primes hr hq).mpr (ne_of_gt hqr)
  have hmprod : (∏ i, m i) = p * q * r := by
    simp [m, Fin.prod_univ_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hprodne : (∏ i, m i) ≠ 0 := by
    rw [hmprod]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero
  letI : NeZero (∏ i, m i) := ⟨hprodne⟩
  letI : Fintype (ZMod (∏ i, m i)) := inferInstance
  letI : NeZero (p * q * r) := ⟨hmprod ▸ hprodne⟩
  simpa only [ZMod.card] using
    (independencePolynomial_three_coordinates
      (R := ZMod (p * q * r))
      (e := (ZMod.ringEquivCongr hmprod.symm).trans (crt m hc)))


end D5.S3.Combinatorics.Graph.ZeroDivisor.Support

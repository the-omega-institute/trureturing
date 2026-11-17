/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/RatherProblemOne
   mirror-E: none(waiver:unbounded-native-prime-family)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: The actual three-prime zero-divisor independence polynomial is log concave and weakly unimodal. -/
import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
import D5.S3.Combinatorics.RealRootedPermutations.LogConcave
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic
/-!
The native three-prime zero-divisor independence polynomial.
admission_basis: open-problem-resolution (#29545; original Problem 1).
The terminal rather_problem_one is the host resolution statement.
All propositional helpers have proof_shape: bind-only and escape_witness: none.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.Vertex: proof_shape: definition; consumers: graph, fiberEquiv, rather_problem_one. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.graph: proof_shape: definition; consumers: independent_four, coefficient_card, rather_problem_one.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.coordinateSupport: proof_shape: definition; consumers: support. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.support: proof_shape: definition; consumers: mem_support, vertex_iff, fiberEquiv, independent_four.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.mem_support: proof_shape: bind-only; consumers: support_nonempty, mul_eq_zero_iff, vertex_iff, fiberEquiv. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.support_nonempty: proof_shape: bind-only; consumers: vertex_iff.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.mul_eq_zero_iff: proof_shape: bind-only; consumers: vertex_iff, independent_four. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.vertex_iff: proof_shape: bind-only; consumers: fiberEquiv, independent_four, support_filter_card.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.fiberEquiv: proof_shape: definition; consumers: support_fiber_card. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.support_fiber_card: proof_shape: bind-only; consumers: support_filter_card.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.crt: proof_shape: definition; consumers: rather_problem_one. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.pairFamily: proof_shape: definition; consumers: configurations_four_families, pair_family_powerset, independencePolynomial_four_families.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.starFamily: proof_shape: definition; consumers: configurations_four_families, star_family_sdiff, star_polynomial. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.independent_four: proof_shape: bind-only; consumers: configurations_four_families.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.configurations_four_families: proof_shape: bind-only; consumers: independencePolynomial_four_families. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.pairDomain: proof_shape: definition; consumers: pair_family_powerset, independencePolynomial_four_families, independencePolynomial_three_coordinates.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.starDomain: proof_shape: definition; consumers: star_family_sdiff, star_polynomial, independencePolynomial_three_coordinates. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.starTailDomain: proof_shape: definition; consumers: star_family_sdiff, star_polynomial, independencePolynomial_three_coordinates.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.pair_family_powerset: proof_shape: bind-only; consumers: independencePolynomial_four_families. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.star_family_sdiff: proof_shape: bind-only; consumers: star_polynomial.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.powerset_polynomial: proof_shape: bind-only; consumers: star_polynomial, independencePolynomial_four_families. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.star_polynomial: proof_shape: bind-only; consumers: independencePolynomial_four_families.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.independencePolynomial_four_families: proof_shape: bind-only; consumers: independencePolynomial_three_coordinates. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.coefficient_card: proof_shape: bind-only; consumers: coefficients_three_domains, rather_problem_one.
D5.S3.Combinatorics.Graph.ZeroDivisor.Support.support_filter_card: proof_shape: bind-only; consumers: independencePolynomial_three_coordinates. D5.S3.Combinatorics.Graph.ZeroDivisor.Support.independencePolynomial_three_coordinates: proof_shape: bind-only; consumers: coefficients_three_domains.
D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction.nine_restriction_count: proof_shape: bind-only; consumers: nine_restriction. D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction.nine_restriction: proof_shape: bind-only; consumers: nine_restriction_bound.
D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction.nine_restriction_bound: proof_shape: bind-only; consumers: normalized_second_difference_bound. D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature.normalized_second_difference: proof_shape: bind-only; consumers: normalized_second_difference_bound, coefficients_three_domains.
D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature.normalized_second_difference_bound: proof_shape: bind-only; consumers: coefficients_three_domains. D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients.coefficients_three_domains: proof_shape: bind-only; consumers: rather_problem_one.
D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne.rather_problem_one: proof_shape: bind-only; consumers: terminal external-problem result.
-/
section
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
private theorem mem_support (e : R ≃+* ∀ i, K i) (x : R) (i : ι) : i ∈ support e x ↔ e x i ≠ 0 := by
  simp [support, coordinateSupport]
private theorem support_nonempty (e : R ≃+* ∀ i, K i) (x : R) : (support e x).Nonempty ↔ x ≠ 0 := by
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
private theorem mul_eq_zero_iff (e : R ≃+* ∀ i, K i) (x y : R) : x * y = 0 ↔ Disjoint (support e x) (support e y) := by
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
private theorem vertex_iff (e : R ≃+* ∀ i, K i) (x : R) : (x ≠ 0 ∧ ∃ y : R, y ≠ 0 ∧ x * y = 0) ↔ (support e x).Nonempty ∧ support e x ≠ Finset.univ := by
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
private def fiberEquiv (e : R ≃+* ∀ i, K i) (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) : {x : Vertex R // support e x.1 = S} ≃ (∀ i : S, {a : K i.1 // a ≠ 0}) where
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
/-- Every genuine support cell consists of exactly the independent choices of nonzero coordinate values. The equality counts actual ring elements. -/
private theorem support_fiber_card [∀ i, Fintype (K i)] (e : R ≃+* ∀ i, K i) (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) : Nat.card {x : Vertex R // support e x.1 = S} = ∏ i ∈ S, (Fintype.card (K i) - 1) := by
  rw [Nat.card_congr (fiberEquiv e S hS hSu), Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (K i) - 1)
/-- The native Chinese remainder equivalence for every finite pairwise coprime modulus family, directly reusing Mathlib's ring equivalence. -/
def crt (p : ι → ℕ) (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j)) : ZMod (∏ i, p i) ≃+* ∀ i, ZMod (p i) :=
  ZMod.prodEquivPi p hcop
/-- Subsets using only the two-coordinate cells. -/
def pairFamily (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) : Finset (Finset (Vertex R)) :=
  V.powerset.filter fun S => ∀ x ∈ S, (support e x.1).card = 2
/-- Subsets meeting the singleton cell at i, with all their supports containing i. -/
def starFamily (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) : Finset (Finset (Vertex R)) :=
  V.powerset.filter fun S =>
    (∃ x ∈ S, support e x.1 = {i}) ∧ ∀ x ∈ S, i ∈ support e x.1
private theorem independent_four (hι : Fintype.card ι = 3) (e : R ≃+* ∀ i, K i) (S : Finset (Vertex R)) : (graph R).IsIndepSet (S : Set (Vertex R)) ↔ (∀ x ∈ S, (support e x.1).card = 2) ∨ ∃ i, (∃ x ∈ S, support e x.1 = {i}) ∧ ∀ x ∈ S, i ∈ support e x.1 := by
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
/-- All actual independent subsets split into four disjoint families when there are exactly three domain coordinates. The ambient finite vertex domain is arbitrary. -/
theorem configurations_four_families (hι : Fintype.card ι = 3) (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) : D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations (graph R) V = pairFamily e V ∪ Finset.univ.biUnion (starFamily e V) ∧ (∀ i, Disjoint (pairFamily e V) (starFamily e V i)) ∧ Pairwise (fun i j => Disjoint (starFamily e V i) (starFamily e V j)) := by
  refine ⟨?_, ?_, ?_⟩
  · ext S
    simp only [D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion.configurations, pairFamily, starFamily, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_powerset]
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
def starDomain (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) : Finset (Vertex R) := V.filter fun x => i ∈ support e x.1
/-- The same domain with its singleton-support cell removed. -/
def starTailDomain (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) : Finset (Vertex R) := (starDomain e V i).filter fun x => support e x.1 ≠ {i}
omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem pair_family_powerset (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) : pairFamily e V = (pairDomain e V).powerset := by
  ext S
  simp only [pairFamily, pairDomain, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hV, hpair⟩ x hx
    exact ⟨hV hx, hpair x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem star_family_sdiff (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) : starFamily e V i = (starDomain e V i).powerset \ (starTailDomain e V i).powerset := by
  ext S
  simp only [starFamily, starDomain, starTailDomain, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_powerset, Finset.subset_iff, Finset.mem_filter]
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
private theorem powerset_polynomial {α : Type*} (V : Finset α) : (∑ S ∈ V.powerset, (Polynomial.X : Polynomial ℤ) ^ S.card) = (1 + Polynomial.X) ^ V.card := by
  simpa only [Finset.prod_const] using
    (Finset.prod_one_add (f := fun _ : α => (Polynomial.X : Polynomial ℤ)) V).symm
omit [∀ i, NoZeroDivisors (K i)] [∀ i, Nontrivial (K i)] in
private theorem star_polynomial (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) (i : ι) : (∑ S ∈ starFamily e V i, (Polynomial.X : Polynomial ℤ) ^ S.card) = (1 + Polynomial.X) ^ (starDomain e V i).card - (1 + Polynomial.X) ^ (starTailDomain e V i).card := by
  rw [star_family_sdiff, Finset.sum_sdiff_eq_sub, powerset_polynomial, powerset_polynomial]
  exact Finset.powerset_mono.mpr (Finset.filter_subset _ _)
/-- The native independence polynomial is the generating function of the four actual families. The exponents are cardinalities of actual finite vertex domains. -/
theorem independencePolynomial_four_families (hι : Fintype.card ι = 3) (e : R ≃+* ∀ i, K i) (V : Finset (Vertex R)) : independencePolynomial (graph R) V = (1 + Polynomial.X) ^ (pairDomain e V).card + ∑ i, ((1 + Polynomial.X) ^ (starDomain e V i).card - (1 + Polynomial.X) ^ (starTailDomain e V i).card) := by
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
theorem coefficient_card (V : Finset (Vertex R)) (k : ℕ) : (independencePolynomial (graph R) V).coeff k = (((configurations (graph R) V).filter fun S => S.card = k).card : ℤ) := by
  simp [independencePolynomial, partition, Polynomial.coeff_X_pow, eq_comm]
private theorem support_filter_card [Fintype R] [∀ i, Fintype (K i)] (e : R ≃+* ∀ i, K i) (P : Finset ι → Prop) : ((Finset.univ : Finset (Vertex R)).filter fun x => P (support e x.1)).card = ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S.Nonempty ∧ S ≠ Finset.univ ∧ P S), ∏ i ∈ S, (Fintype.card (K i) - 1) := by
  let T := (Finset.univ : Finset (Finset ι)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ ∧ P S)
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Vertex R)) T (fun x => support e x.1)
  have hright : ((Finset.univ : Finset (Vertex R)).filter (fun x => support e x.1 ∈ T)) = Finset.univ.filter (fun x : Vertex R => P (support e x.1)) := by
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
/-- The exact four-family polynomial on the full actual ring graph, with all six support multiplicities evaluated. The finite coordinate domains are arbitrary. -/
theorem independencePolynomial_three_coordinates {L : Fin 3 → Type*} [∀ i, CommRing (L i)] [∀ i, NoZeroDivisors (L i)] [∀ i, Nontrivial (L i)] [∀ i, Fintype (L i)] [Fintype R] (e : R ≃+* ∀ i, L i) : let a := Fintype.card (L 0) - 1
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
  have hU : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} := by decide
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
  have hp' : (pairDomain e Finset.univ).card = (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) + (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    unfold pairDomain
    omega
  have hs0' : (starDomain e Finset.univ 0).card = (Fintype.card (L 0)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs0
  have hs1' : (starDomain e Finset.univ 1).card = (Fintype.card (L 1)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) + (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs1
  have hs2' : (starDomain e Finset.univ 2).card = (Fintype.card (L 2)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) + (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starDomain, add_assoc, add_left_comm, add_comm] using hs2
  have ht0' : (starTailDomain e Finset.univ 0).card = (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) + (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht0
  have ht1' : (starTailDomain e Finset.univ 1).card = (Fintype.card (L 0)-1)*(Fintype.card (L 1)-1) + (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht1
  have ht2' : (starTailDomain e Finset.univ 2).card = (Fintype.card (L 0)-1)*(Fintype.card (L 2)-1) + (Fintype.card (L 1)-1)*(Fintype.card (L 2)-1) := by
    simpa [starTailDomain, starDomain, Finset.filter_filter, add_comm] using ht2
  rw [independencePolynomial_four_families (by decide) e, hp']
  simp only [Fin.sum_univ_three, hs0', hs1', hs2', ht0', ht1', ht2']
  ring
end D5.S3.Combinatorics.Graph.ZeroDivisor.Support
end
end
section
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction
open Finset
/-- Count a nine-subset together with a marked prefix and an unmarked pair. -/
theorem nine_restriction_count (m n k : ℕ) (hk : 3 ≤ k ∧ k ≤ 5) : (∑ j ∈ range 10, m.choose j * n.choose (9-j) * j.choose (k-1) * (9-j).choose 2) = m.choose (k-1) * n.choose 2 * (m+n-(k+1)).choose (9-(k+1)) := by
  let a := k-1
  let r := 9-(k+1)
  have ha : 2 ≤ a ∧ a ≤ 4 := by dsimp [a]; omega
  have hr : 8-a = r+1 := by dsimp [a, r]; omega
  have hsub : Ico a 8 ⊆ range 10 := by
    intro j hj
    simp only [mem_Ico, mem_range] at *
    omega
  have hvanish : ∀ j ∈ range 10, j ∉ Ico a 8 → m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2 = 0 := by
    intro j hj hnot
    by_cases hja : j < a
    · simp [Nat.choose_eq_zero_of_lt hja]
    · have hlast : 9-j < 2 := by
        simp only [mem_Ico, not_and, not_lt] at hnot
        omega
      simp [Nat.choose_eq_zero_of_lt hlast]
  have key : (∑ j ∈ range 10, m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2) = m.choose a * n.choose 2 * ((m-a)+(n-2)).choose r := by
    calc
      _ = ∑ t ∈ range (r+1),
          m.choose (a+t) * n.choose (9-(a+t)) *
            (a+t).choose a * (9-(a+t)).choose 2 := by
        rw [← sum_subset hsub hvanish, sum_Ico_eq_sum_range, hr]
      _ = m.choose a * n.choose 2 *
          ∑ t ∈ range (r+1), (m-a).choose t * (n-2).choose (r-t) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t ht
        have ht' := mem_range.mp ht
        have htwo : 2 ≤ 9-(a+t) := by dsimp [a, r] at *; omega
        have heq : 9-(a+t)-2 = r-t := by dsimp [a, r]; omega
        calc
          _ = (m.choose (a+t) * (a+t).choose a) *
              (n.choose (9-(a+t)) * (9-(a+t)).choose 2) := by ring
          _ = _ := by
            rw [Nat.choose_mul (Nat.le_add_right a t), Nat.choose_mul htwo, Nat.add_sub_cancel_left, heq]
            ring
      _ = _ := by
        rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ j ∈ range 10,
    m.choose j * n.choose (9-j) * j.choose a * (9-j).choose 2) = _
  rw [key]
  by_cases hm : a ≤ m
  · by_cases hn : 2 ≤ n
    · have heq : (m-a)+(n-2) = m+n-(k+1) := by dsimp [a] at *; omega
      rw [heq]
    · simp [Nat.choose_eq_zero_of_lt (by omega : n < 2)]
  · have hz : m.choose a = 0 := Nat.choose_eq_zero_of_lt (by omega)
    change m.choose a * n.choose 2 * _ = m.choose a * n.choose 2 * _
    simp [hz]
/-- Uniform restriction to a nine-subset, with rational hypergeometric weights. -/
theorem nine_restriction (N m k : ℕ) (hN : 9 ≤ N) (hm : m ≤ N) (hk : 3 ≤ k ∧ k ≤ 5) : (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) / ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) = ∑ j ∈ range 10, ((m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) * ((j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ) / ((9 : ℕ).choose (k+1) * ((k+1).choose 2 : ℚ))) := by
  have hmn : m+(N-m) = N := by omega
  have hcount := nine_restriction_count m (N-m) k hk
  rw [hmn] at hcount
  have hsum : (∑ j ∈ range 10, (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) * (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ)) = (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) * ((N-(k+1)).choose (9-(k+1)) : ℚ) := by exact_mod_cast hcount
  have hcomp : (N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) = (N.choose (k+1) : ℚ) * ((N-(k+1)).choose (9-(k+1)) : ℚ) := by
    exact_mod_cast (Nat.choose_mul (n := N) (k := 9) (s := k+1) (by omega))
  have hD : (N.choose (k+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k+1 ≤ N)
  have hW : (N.choose 9 : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hN
  have hS : ((9 : ℕ).choose (k+1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k+1 ≤ 9)
  have hP : ((k+1).choose 2 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : 2 ≤ k+1)
  calc
    _ = ((m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) *
          ((N-(k+1)).choose (9-(k+1)) : ℚ)) /
        ((N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
      apply (div_eq_div_iff (mul_ne_zero hD hP)
        (mul_ne_zero (mul_ne_zero hW hS) hP)).mpr
      linear_combination (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) *
        ((k+1).choose 2 : ℚ) * hcomp
    _ = (∑ j ∈ range 10,
        (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) *
          (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ)) /
        ((N.choose 9 : ℚ) * ((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
      rw [hsum]
    _ = _ := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      field_simp
      <;> ring
/-- The three small-rank bounds hold in every population of size at least nine. -/
theorem nine_restriction_bound (N m k : ℕ) (hN : 9 ≤ N) (hm : m ≤ N) (hk : 3 ≤ k ∧ k ≤ 5) : (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) / ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) ≤ if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ) := by
  have hmn : m+(N-m) = N := by omega
  have hW : (N.choose 9 : ℚ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hN
  have hv : ∑ j ∈ range 10, m.choose j * (N-m).choose (9-j) = N.choose 9 := by
    have h := Nat.add_choose_eq m (N-m) 9
    rw [hmn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    exact h.symm
  have hw : (∑ j ∈ range 10, (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) = 1 := by
    rw [← sum_div]
    have hv' : (∑ j ∈ range 10, (m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ)) = (N.choose 9 : ℚ) := by
      exact_mod_cast hv
    rw [hv', div_self hW]
  have htable : ∀ j ∈ range 10, (j.choose (k-1) : ℚ) * ((9-j).choose 2 : ℚ) / (((9 : ℕ).choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) ≤ if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ) := by
    intro j hj
    have hj' := mem_range.mp hj
    obtain ⟨hklo, hkhi⟩ := hk
    interval_cases k <;> interval_cases j <;> norm_num [Nat.choose]
  rw [nine_restriction N m k hN hm hk]
  calc
    _ ≤ ∑ j ∈ range 10,
        ((m.choose j : ℚ) * ((N-m).choose (9-j) : ℚ) / (N.choose 9 : ℚ)) *
          (if k = 3 then (5/63 : ℚ) else if k = 4 then (1/21 : ℚ) else (1/28 : ℚ)) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (htable j hj) (by positivity)
    _ = _ := by rw [← sum_mul, hw, one_mul]
end D5.S3.Combinatorics.Graph.ZeroDivisor.NineRestriction
end
section
set_option autoImplicit false
namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature
open Finset
/-- The normalized second difference is the marked-prefix and unmarked-pair ratio. -/
theorem normalized_second_difference (N m k : ℕ) (hm : m ≤ N) (hk : 1 ≤ k) (hkN : k < N) : (m.choose (k-1) : ℚ) / (N.choose (k-1) : ℚ) - 2 * ((m.choose k : ℚ) / (N.choose k : ℚ)) + (m.choose (k+1) : ℚ) / (N.choose (k+1) : ℚ) = (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) / ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) := by
  have step (n j : ℕ) : (n.choose (j+1) : ℚ) * (j+1) = (n.choose j : ℚ) * ((n : ℚ)-j) := by
    by_cases hj : j ≤ n
    · have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using h
    · have hj' : n < j := by omega
      simp [Nat.choose_eq_zero_of_lt hj',
        Nat.choose_eq_zero_of_lt (by omega : n < j+1)]
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have hkp0 : (k : ℚ)+1 ≠ 0 := by positivity
  have hA : (N.choose (k-1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : k-1 ≤ N)
  have hNk : (N : ℚ)-(k : ℚ) ≠ 0 := by
    have : (k : ℚ) < N := by exact_mod_cast hkN
    linarith
  have hNk1 : (N : ℚ)-(k : ℚ)+1 ≠ 0 := by
    have : (k : ℚ) < N := by exact_mod_cast hkN
    linarith
  have vstep := step m (k-1)
  have bstep := step N (k-1)
  simp only [Nat.sub_add_cancel hk, Nat.cast_sub hk, Nat.cast_one] at vstep bstep
  have vform : (m.choose k : ℚ) = (m.choose (k-1) : ℚ) * ((m : ℚ)-k+1) / k := by
    apply (eq_div_iff hk0).mpr
    linear_combination vstep
  have bform : (N.choose k : ℚ) = (N.choose (k-1) : ℚ) * ((N : ℚ)-k+1) / k := by
    apply (eq_div_iff hk0).mpr
    linear_combination bstep
  have wform : (m.choose (k+1) : ℚ) = (m.choose (k-1) : ℚ) * ((m : ℚ)-k+1) * ((m : ℚ)-k) / ((k : ℚ)*((k : ℚ)+1)) := by
    have h := step m k
    rw [vform] at h
    field_simp [hk0, hkp0] at h ⊢
    nlinarith [h]
  have cform : (N.choose (k+1) : ℚ) = (N.choose (k-1) : ℚ) * ((N : ℚ)-k+1) * ((N : ℚ)-k) / ((k : ℚ)*((k : ℚ)+1)) := by
    have h := step N k
    rw [bform] at h
    field_simp [hk0, hkp0] at h ⊢
    nlinarith [h]
  rw [vform, wform, bform, cform, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hm]
  push_cast
  field_simp [hA, hk0, hkp0, hNk, hNk1]
  <;> ring
/-- A uniform curvature bound, including the three small ranks. -/
theorem normalized_second_difference_bound (N m k : ℕ) (hN : 9 ≤ N) (hm : m ≤ N) (hk : 3 ≤ k) (hkN : k < N) : (m.choose (k-1) : ℚ) / (N.choose (k-1) : ℚ) - 2 * ((m.choose k : ℚ) / (N.choose k : ℚ)) + (m.choose (k+1) : ℚ) / (N.choose (k+1) : ℚ) ≤ 1 / (3 * ((k : ℚ)+1)) := by
  rw [normalized_second_difference N m k hm (by omega) hkN]
  by_cases hk6 : 6 ≤ k
  · have hmn : m+(N-m) = N := by omega
    have hvand := Nat.add_choose_eq m (N-m) (k+1)
    rw [hmn, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hvand
    have hterm : m.choose (k-1) * (N-m).choose 2 ≤ N.choose (k+1) := by
      rw [hvand]
      have h := Finset.single_le_sum
        (f := fun j => m.choose j * (N-m).choose (k+1-j))
        (s := range (k+1+1)) (by intro j _; exact Nat.zero_le _)
        (show k-1 ∈ range (k+1+1) from mem_range.mpr (by omega))
      simpa only [show k+1-(k-1) = 2 by omega] using h
    have htermQ : (m.choose (k-1) : ℚ) * ((N-m).choose 2 : ℚ) ≤ (N.choose (k+1) : ℚ) := by exact_mod_cast hterm
    have hD : 0 < (N.choose (k+1) : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : k+1 ≤ N)
    have hP : 0 < ((k+1).choose 2 : ℚ) := by
      exact_mod_cast Nat.choose_pos (by omega : 2 ≤ k+1)
    calc
      _ ≤ (N.choose (k+1) : ℚ) /
          ((N.choose (k+1) : ℚ) * ((k+1).choose 2 : ℚ)) :=
        (div_le_div_iff_of_pos_right (mul_pos hD hP)).mpr htermQ
      _ = 1 / ((k+1).choose 2 : ℚ) := by
        field_simp
      _ ≤ 1 / (3 * ((k : ℚ)+1)) := by
        apply one_div_le_one_div_of_le (by positivity)
        rw [Nat.cast_choose_two]
        push_cast
        have hk6Q : (6 : ℚ) ≤ k := by exact_mod_cast hk6
        nlinarith
  · have hsmall := NineRestriction.nine_restriction_bound N m k hN hm
      (show 3 ≤ k ∧ k ≤ 5 by omega)
    rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with h | h | h <;>
      subst k <;> norm_num at hsmall ⊢ <;> linarith
end D5.S3.Combinatorics.Graph.ZeroDivisor.NormalizedCurvature
end
section
set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
namespace D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients
set_option maxHeartbeats 1800000 in
/-- Native coefficients for three ordered finite domains, including the smallest field. -/
theorem coefficients_three_domains {R : Type*} [CommRing R] [Fintype R] {L : Fin 3 → Type*} [∀ i, CommRing (L i)] [∀ i, NoZeroDivisors (L i)] [∀ i, Nontrivial (L i)] [∀ i, Fintype (L i)] (e : R ≃+* ∀ i, L i) (h01 : Fintype.card (L 0) ≤ Fintype.card (L 1)) (h12 : Fintype.card (L 1) ≤ Fintype.card (L 2)) (h1 : 3 ≤ Fintype.card (L 1)) (h2 : 5 ≤ Fintype.card (L 2)) : let a := Fintype.card (L 0) - 1
    let b := Fintype.card (L 1) - 1
    let c := Fintype.card (L 2) - 1
    let N := max (a*b+a*c+b*c) (c+a*c+b*c)
    let s := fun k => ((independencePolynomial (Support.graph R) Finset.univ).coeff k : ℚ)
    14 ≤ N ∧ (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧
      (∀ k, 1 ≤ k → k < N → s (k-1) * s (k+1) < s k ^ 2) := by
  classical
  let a := Fintype.card (L 0) - 1
  let b := Fintype.card (L 1) - 1
  let c := Fintype.card (L 2) - 1
  let A := a*b+a*c+b*c
  let T0 := a*b+a*c
  let T1 := a*b+b*c
  let T2 := a*c+b*c
  let U0 := a+a*b+a*c
  let U1 := b+a*b+b*c
  let U2 := c+a*c+b*c
  let N := max A U2
  let P := independencePolynomial (Support.graph R) Finset.univ
  let s := fun k => (P.coeff k : ℚ)
  change 14 ≤ N ∧ (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧ _
  have ha : 1 ≤ a := by
    have := Fintype.one_lt_card (α := L 0)
    dsimp [a]
    omega
  have hb : 2 ≤ b := by dsimp [b]; omega
  have hc : 4 ≤ c := by dsimp [c]; omega
  have hab : a ≤ b := Nat.sub_le_sub_right h01 1
  have hbc : b ≤ c := Nat.sub_le_sub_right h12 1
  have hA : 14 ≤ A := by
    dsimp [A]
    nlinarith only [Nat.mul_le_mul ha hb, Nat.mul_le_mul ha hc, Nat.mul_le_mul hb hc]
  have hN : 14 ≤ N := hA.trans (le_max_left _ _)
  have hU01 : U0 ≤ U1 := by
    have := Nat.mul_le_mul_left c hab
    dsimp [U0, U1]
    nlinarith
  have hU12 : U1 ≤ U2 := by
    have := Nat.mul_le_mul_left a hbc
    dsimp [U1, U2]
    omega
  have hAN : A ≤ N := le_max_left _ _
  have hU2N : U2 ≤ N := le_max_right _ _
  have hU1N : U1 ≤ N := hU12.trans hU2N
  have hU0N : U0 ≤ N := hU01.trans hU1N
  have hT0A : T0 ≤ A := by dsimp [T0, A]; omega
  have hT1A : T1 ≤ A := by dsimp [T1, A]; omega
  have hT2A : T2 ≤ A := by dsimp [T2, A]; omega
  have hT0U : T0 ≤ U0 := by dsimp [T0, U0]; omega
  have hT1U : T1 ≤ U1 := by dsimp [T1, U1]; omega
  have hT2U : T2 ≤ U2 := by dsimp [T2, U2]; omega
  have hpoly := Support.independencePolynomial_three_coordinates e
  have hs (k : ℕ) : s k = (A.choose k : ℚ) + ((U0.choose k : ℚ)-(T0.choose k : ℚ)) + ((U1.choose k : ℚ)-(T1.choose k : ℚ)) + ((U2.choose k : ℚ)-(T2.choose k : ℚ)) := by
    have h := congrArg (fun Q : Polynomial ℤ => (Q.coeff k : ℚ)) hpoly
    simpa only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Int.cast_add, Int.cast_sub, Int.cast_natCast] using h
  have lower (k : ℕ) : (N.choose k : ℚ) ≤ s k := by
    have h0 : (T0.choose k : ℚ) ≤ U0.choose k := by
      exact_mod_cast Nat.choose_le_choose k hT0U
    have h1' : (T1.choose k : ℚ) ≤ U1.choose k := by
      exact_mod_cast Nat.choose_le_choose k hT1U
    by_cases hAU : U2 ≤ A
    · have hmax : N = A := max_eq_left hAU
      have h2' : (T2.choose k : ℚ) ≤ U2.choose k := by
        exact_mod_cast Nat.choose_le_choose k hT2U
      rw [hmax, hs]
      linarith
    · have hmax : N = U2 := max_eq_right (by omega)
      have h2' : (T2.choose k : ℚ) ≤ A.choose k := by
        exact_mod_cast Nat.choose_le_choose k hT2A
      rw [hmax, hs]
      linarith
  have pos (k : ℕ) (hk : k ≤ N) : 0 < s k :=
    lt_of_lt_of_le (by exact_mod_cast Nat.choose_pos hk) (lower k)
  have tail (k : ℕ) (hk : N < k) : s k = 0 := by
    rw [hs]
    simp [Nat.choose_eq_zero_of_lt (hAN.trans_lt hk), Nat.choose_eq_zero_of_lt (hU0N.trans_lt hk), Nat.choose_eq_zero_of_lt (hU1N.trans_lt hk), Nat.choose_eq_zero_of_lt (hU2N.trans_lt hk), Nat.choose_eq_zero_of_lt ((hT0A.trans hAN).trans_lt hk), Nat.choose_eq_zero_of_lt ((hT1A.trans hAN).trans_lt hk), Nat.choose_eq_zero_of_lt ((hT2A.trans hAN).trans_lt hk)]
  let v := A+a+b+c
  let E := A+3*a*b*c
  have hs0 : s 0 = 1 := by rw [hs]; norm_num
  have hs1 : s 1 = (v : ℚ) := by
    rw [hs]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_mul]
    dsimp [v, A, U0, U1, U2, T0, T1, T2]
    push_cast
    ring
  have hs2 : s 2 = (v : ℚ)*((v : ℚ)-1)/2-(E : ℚ) := by
    rw [hs]
    simp only [Nat.cast_choose_two]
    dsimp [v, E, A, U0, U1, U2, T0, T1, T2]
    push_cast
    ring
  have hv : 21 ≤ v := by dsimp [v]; omega
  have count1 : (Fintype.card (Support.Vertex R) : ℚ) = s 1 := by
    have hsets : ((configurations (Support.graph R) Finset.univ).filter fun S => S.card = 1) = (Finset.univ : Finset (Support.Vertex R)).image (fun x => {x}) := by
      ext S
      simp only [Finset.mem_filter, configurations, Finset.mem_powerset, Finset.subset_univ, true_and, Finset.mem_image, Finset.mem_univ]
      constructor
      · rintro ⟨_, hS⟩
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hS
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        simp [SimpleGraph.isIndepSet_iff]
    have hcount := Support.coefficient_card (R := R) Finset.univ 1
    rw [hsets, Finset.card_image_of_injective _ (by
      intro x y hxy
      simpa only [Finset.singleton_inj] using hxy), Finset.card_univ] at hcount
    dsimp [s, P]
    exact_mod_cast hcount.symm
  have countcard : Fintype.card (Support.Vertex R) = v := by
    exact_mod_cast count1.trans hs1
  have hs3 : s 3 ≤ ((v.choose 3 : ℕ) : ℚ) := by
    have hsub : ((configurations (Support.graph R) Finset.univ).filter fun S => S.card = 3) ⊆ (Finset.univ : Finset (Support.Vertex R)).powersetCard 3 := by
      intro S hS
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hS).2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_powersetCard, Finset.card_univ, countcard] at hcard
    have hcount := Support.coefficient_card (R := R) Finset.univ 3
    have hcountQ : s 3 = (((configurations (Support.graph R) Finset.univ).filter fun S => S.card = 3).card : ℚ) := by
      dsimp [s, P]
      exact_mod_cast hcount
    rw [hcountQ]
    exact_mod_cast hcard
  have density : 11*(E : ℚ) ≤ (v : ℚ)*((v : ℚ)-1) := by
    let x : ℚ := (a-1 : ℕ)
    let y : ℚ := (b-2 : ℕ)
    let z : ℚ := (c-4 : ℕ)
    have hx : 0 ≤ x := by positivity
    have hy : 0 ≤ y := by positivity
    have hz : 0 ≤ z := by positivity
    have hxx : 0 ≤ x^2-x := by
      have h : (a-1) ≤ (a-1)*(a-1) := Nat.le_mul_self _
      have h' : x ≤ x*x := by dsimp [x]; exact_mod_cast h
      nlinarith
    have hyy : 0 ≤ y^2-y := by
      have h : (b-2) ≤ (b-2)*(b-2) := Nat.le_mul_self _
      have h' : y ≤ y*y := by dsimp [y]; exact_mod_cast h
      nlinarith
    have hax : (a : ℚ) = x+1 := by dsimp [x]; rw [Nat.cast_sub ha]; ring
    have hby : (b : ℚ) = y+2 := by dsimp [y]; rw [Nat.cast_sub hb]; norm_num
    have hcz : (c : ℚ) = z+4 := by dsimp [z]; rw [Nat.cast_sub hc]; norm_num
    have hid : (v : ℚ)*((v : ℚ)-1)-11*(E : ℚ) = 2+49*(x^2-x)+6*x+36*y^2+59*y+16*z^2+65*z+ 14*(x^2-x)*y+12*x*(y^2-y)+8*x*y+20*x*z+45*y*z+ 14*x^2*z+12*y^2*z+8*x*z^2+8*y*z^2+x*y*z+(x*y+x*z+y*z)^2 := by
      dsimp [v, E, A]
      push_cast
      rw [hax, hby, hcz]
      ring
    have hnon : 0 ≤ (v : ℚ)*((v : ℚ)-1)-11*(E : ℚ) := by
      rw [hid]
      positivity
    linarith
  have low1 : s 0*s 2 < s 1^2 := by
    rw [hs0, hs1, hs2]
    have hvQ : 21 ≤ (v : ℚ) := by exact_mod_cast hv
    have hE : 0 ≤ (E : ℚ) := by positivity
    nlinarith
  have low2 : s 1*s 3 < s 2^2 := by
    let C : ℚ := (v.choose 2 : ℕ)
    have hC : C = (v : ℚ)*((v : ℚ)-1)/2 := Nat.cast_choose_two ℚ v
    have hCpos : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos (by omega : 2 ≤ v)
    have h3 : (v.choose 3 : ℚ)*3 = (v.choose 2 : ℚ)*((v : ℚ)-2) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq v 2)
      simpa [Nat.cast_sub (by omega : 2 ≤ v)] using h
    have hCv : (v : ℚ)*(v.choose 3 : ℚ) ≤ (2/3:ℚ)*C^2 := by
      have hvQ : 0 ≤ (v : ℚ) := by positivity
      have h3' : (v.choose 3 : ℚ) = C*((v : ℚ)-2)/3 := by
        dsimp [C]
        linarith [h3]
      have hdiff : (2/3:ℚ)*C^2-(v : ℚ)*(v.choose 3 : ℚ) = (v : ℚ)*C/3 := by
        rw [h3', hC]
        ring
      rw [← sub_nonneg]
      rw [hdiff]
      positivity
    have h2lower : (9/11:ℚ)*C ≤ s 2 := by rw [hs2]; rw [hC]; linarith
    have h2sq : (9/11:ℚ)^2*C^2 ≤ s 2^2 := by
      have hs2pos := pos 2 (by omega)
      nlinarith [h2lower]
    have h3upper : s 1*s 3 ≤ (2/3:ℚ)*C^2 := by
      rw [hs1]
      exact (mul_le_mul_of_nonneg_left hs3 (by positivity)).trans hCv
    nlinarith [sq_pos_of_pos hCpos]
  refine ⟨hN, pos, tail, ?_⟩
  intro k hk hkN
  change k < N at hkN
  change s (k-1)*s (k+1) < s k^2
  by_cases hk1 : k = 1
  · subst k
    simpa using low1
  by_cases hk2 : k = 2
  · subst k
    simpa using low2
  have hk3 : 3 ≤ k := by omega
  let B := fun j => (N.choose j : ℚ)
  let f := fun j => s j / B j
  let D := fun (m : ℕ) => (m.choose (k-1) : ℚ)/B (k-1) -
    2*((m.choose k : ℚ)/B k)+(m.choose (k+1) : ℚ)/B (k+1)
  have hB (j : ℕ) (hj : j ≤ N) : 0 < B j := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos hj
  have hf (j : ℕ) (hj : j ≤ N) : 1 ≤ f j := by
    apply (le_div_iff₀ (hB j hj)).mpr
    simpa only [one_mul] using lower j
  have hDN : D N = 0 := by
    dsimp [D]
    simp only [show (N.choose (k-1) : ℚ) = B (k-1) from rfl,
      show (N.choose k : ℚ) = B k from rfl,
      show (N.choose (k+1) : ℚ) = B (k+1) from rfl,
      div_self (ne_of_gt (hB (k-1) (by omega))),
      div_self (ne_of_gt (hB k (by omega))),
      div_self (ne_of_gt (hB (k+1) (by omega)))]
    norm_num
  have hDnon (m : ℕ) (hm : m ≤ N) : 0 ≤ D m := by
    dsimp [D, B]
    rw [NormalizedCurvature.normalized_second_difference N m k hm hk hkN]
    positivity
  have hDbd (m : ℕ) (hm : m ≤ N) : D m ≤ 1/(3*((k : ℚ)+1)) :=
    NormalizedCurvature.normalized_second_difference_bound N m k (by omega) hm hk3 hkN
  have hdecomp : f (k-1)-2*f k+f (k+1) = D A+D U0+D U1+D U2-D T0-D T1-D T2 := by
    dsimp only [f]
    rw [hs (k-1), hs k, hs (k+1)]
    dsimp [D]
    ring
  have hthird : 3*(1/(3*((k : ℚ)+1))) = 1/((k : ℚ)+1) := by
    field_simp
    <;> ring
  have curv : f (k-1)-2*f k+f (k+1) ≤ 1/((k : ℚ)+1) := by
    rw [hdecomp]
    have h0 := hDnon T0 (hT0A.trans hAN)
    have h1' := hDnon T1 (hT1A.trans hAN)
    have h2' := hDnon T2 (hT2A.trans hAN)
    by_cases hAU : U2 ≤ A
    · have hmax : N = A := max_eq_left hAU
      have hDA : D A = 0 := hmax ▸ hDN
      linarith [hDbd U0 hU0N, hDbd U1 hU1N, hDbd U2 hU2N]
    · have hmax : N = U2 := max_eq_right (by omega)
      have hDU : D U2 = 0 := hmax ▸ hDN
      linarith [hDbd A hAN, hDbd U0 hU0N, hDbd U1 hU1N]
  let x := f (k-1)
  let y := f k
  let z := f (k+1)
  let t := (k : ℚ)+1
  have hx : 1 ≤ x := hf _ (by omega)
  have hy : 1 ≤ y := hf _ (by omega)
  have hz : 1 ≤ z := hf _ (by omega)
  have ht : 0 < t := by dsimp [t]; positivity
  have hkQ : 0 ≤ (k : ℚ) := by positivity
  have hsum : t*(x+z) ≤ 2*t*y+1 := by
    have h := (le_div_iff₀ ht).mp curv
    dsimp only [x, y, z, t] at *
    nlinarith
  have hsumpos : 0 ≤ t*(x+z) := by positivity
  have hsquare : (t*(x+z))^2 ≤ (2*t*y+1)^2 := by
    nlinarith [mul_self_le_mul_self hsumpos hsum]
  have hfour : 4*t^2*x*z ≤ (2*t*y+1)^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (x-z))]
  have hfourk := mul_le_mul_of_nonneg_left hfour hkQ
  have hysq : 0 ≤ y^2-y := by nlinarith
  have hslack : 0 < 4*t^3*y^2-(k : ℚ)*(2*t*y+1)^2 := by
    have hid : 4*t^3*y^2-(k : ℚ)*(2*t*y+1)^2 = 4*t^2*(y^2-y)+4*t*(y-1)+3*(k : ℚ)+4 := by dsimp [t]; ring
    rw [hid]
    have hy1 : 0 ≤ y-1 := by linarith only [hy]
    positivity
  have hscalar : (k : ℚ)*x*z < t*y^2 := by
    have hm : 0 < 4*t^2*(t*y^2-(k : ℚ)*x*z) := by nlinarith [hfourk, hslack]
    by_contra hn
    have hh : 4*t^2*(t*y^2-(k : ℚ)*x*z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hprev := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq N (k-1))
  have hnext := congrArg (fun n : ℕ => (n : ℚ)) (Nat.choose_succ_right_eq N k)
  simp only [Nat.sub_add_cancel hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : k-1 ≤ N), Nat.cast_sub hk, Nat.cast_sub (by omega : k ≤ N)] at hprev hnext
  have hbinid : t*B (k-1)*B (k+1)+B (k-1)*B k = (k : ℚ)*B k^2 := by
    dsimp [t, B]
    linear_combination (N.choose (k-1) : ℚ)*hnext-(N.choose k : ℚ)*hprev
  have hbin : t*B (k-1)*B (k+1) ≤ (k : ℚ)*B k^2 := by
    nlinarith [mul_nonneg (hB (k-1) (by omega)).le (hB k (by omega)).le]
  have hsB (j : ℕ) (hj : j ≤ N) : s j = f j*B j := by
    dsimp [f]
    exact (div_mul_cancel₀ _ (ne_of_gt (hB j hj))).symm
  have hscaled : t*(s (k-1)*s (k+1)) < t*(s k)^2 := by
    rw [hsB (k-1) (by omega), hsB (k+1) (by omega), hsB k (by omega)]
    change t*(x*B (k-1)*(z*B (k+1))) < t*(y*B k)^2
    have hmul := mul_le_mul_of_nonneg_right hbin (mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ z))
    have hstrict := mul_lt_mul_of_pos_right hscalar (sq_pos_of_pos (hB k (by omega)))
    nlinarith only [hmul, hstrict]
  exact (mul_lt_mul_iff_right₀ ht).mp hscaled
end D5.S3.Combinatorics.Graph.ZeroDivisor.NativeCoefficients
end
end
section
set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
namespace D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne
set_option maxHeartbeats 1200000 in
/-- The original all-prime graph has attained support, log concavity and weak unimodality. -/
theorem rather_problem_one (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hpq : p < q) (hqr : q < r) : letI : NeZero (p*q*r) :=
      ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
    let a := p-1
    let b := q-1
    let c := r-1
    let N := max (a*b+a*c+b*c) (c+a*c+b*c)
    let G := Support.graph (ZMod (p*q*r))
    let s := fun k => (independencePolynomial G Finset.univ).coeff k
    14 ≤ N ∧ G.indepNum = N ∧
      (∃ S : Finset (Support.Vertex (ZMod (p*q*r))), G.IsIndepSet (S : Set _) ∧ S.card = N) ∧
      (∀ k, k ≤ N → 0 < s k) ∧ (∀ k, N < k → s k = 0) ∧
      (∀ k, 1 ≤ k → s (k-1)*s (k+1) ≤ s k^2) ∧
      (∃ m, m ≤ N ∧ MonotoneOn s (Set.Iic m) ∧ AntitoneOn s (Set.Ici m)) := by
  classical
  letI : NeZero (p*q*r) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero⟩
  let m : Fin 3 → ℕ := ![p,q,r]
  letI : ∀ i, Fact (m i).Prime := fun i => by
    fin_cases i
    · exact ⟨hp⟩
    · exact ⟨hq⟩
    · exact ⟨hr⟩
  letI : ∀ i, NeZero (m i) := fun i => ⟨(Fact.out : (m i).Prime).ne_zero⟩
  letI : ∀ i, Fintype (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, Nontrivial (ZMod (m i)) := fun i => inferInstance
  letI : ∀ i, NoZeroDivisors (ZMod (m i)) := fun i => inferInstance
  have cardm (i : Fin 3) : Fintype.card (ZMod (m i)) = m i := ZMod.card (m i)
  have hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [m] at hij ⊢
    · exact (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)
    · exact (Nat.coprime_primes hp hr).mpr (ne_of_lt (hpq.trans hqr))
    · exact (Nat.coprime_primes hq hp).mpr (ne_of_gt hpq)
    · exact (Nat.coprime_primes hq hr).mpr (ne_of_lt hqr)
    · exact (Nat.coprime_primes hr hp).mpr (ne_of_gt (hpq.trans hqr))
    · exact (Nat.coprime_primes hr hq).mpr (ne_of_gt hqr)
  have hmprod : (∏ i, m i) = p*q*r := by
    simp [m, Fin.prod_univ_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hq3 : 3 ≤ q := by have := hp.two_le; omega
  have hr5 : 5 ≤ r := by
    have hr4 : r ≠ 4 := by intro he; subst r; norm_num at hr
    omega
  let a := p-1
  let b := q-1
  let c := r-1
  let N := max (a*b+a*c+b*c) (c+a*c+b*c)
  let G := Support.graph (ZMod (p*q*r))
  let P := independencePolynomial G Finset.univ
  let s := fun k => P.coeff k
  let sQ := fun k => (s k : ℚ)
  have hco := NativeCoefficients.coefficients_three_domains
    ((ZMod.ringEquivCongr hmprod.symm).trans (Support.crt m hcop))
    (by rw [cardm 0, cardm 1]; simpa [m] using hpq.le)
    (by rw [cardm 1, cardm 2]; simpa [m] using hqr.le)
    (by rw [cardm 1]; simpa [m] using hq3)
    (by rw [cardm 2]; simpa [m] using hr5)
  change 14 ≤ N ∧ G.indepNum = N ∧ _
  have hco' : 14 ≤ N ∧ (∀ k, k ≤ N → 0 < sQ k) ∧ (∀ k, N < k → sQ k = 0) ∧ (∀ k, 1 ≤ k → k < N → sQ (k-1)*sQ (k+1) < sQ k^2) := by
    simp only [cardm 0, cardm 1, cardm 2] at hco
    convert (preTransparency := .reducible) hco <;> congr 1 <;> ext x <;> simp
  obtain ⟨hN, hposQ, htailQ, hlcQ⟩ := hco'
  have hpos (k : ℕ) (hk : k ≤ N) : 0 < s k := by
    have h := hposQ k hk
    dsimp only [sQ] at h
    exact_mod_cast h
  have htail (k : ℕ) (hk : N < k) : s k = 0 := by
    have h := htailQ k hk
    dsimp only [sQ] at h
    exact_mod_cast h
  have hcount (k : ℕ) : s k = (((configurations G Finset.univ).filter fun S => S.card = k).card : ℤ) := by
    convert (preTransparency := .reducible)
      (Support.coefficient_card (R := ZMod (p*q*r)) Finset.univ k) <;>
      congr 1 <;> ext x <;> simp
  obtain ⟨S, hS⟩ := Finset.card_pos.mp (show 0 <
      ((configurations G Finset.univ).filter fun S => S.card = N).card by
    have h := hpos N le_rfl
    rw [hcount] at h
    exact_mod_cast h)
  have hSind : G.IsIndepSet (S : Set _) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
  have hScard : S.card = N := (Finset.mem_filter.mp hS).2
  have hbound (T : Finset (Support.Vertex (ZMod (p*q*r)))) (hT : G.IsIndepSet (T : Set _)) : T.card ≤ N := by
    have hmem : T ∈ (configurations G Finset.univ).filter fun U => U.card = T.card := by
      simp only [Finset.mem_filter, configurations, Finset.mem_powerset, Finset.subset_univ, true_and]
      exact ⟨hT, trivial⟩
    have hcpos : 0 < s T.card := by
      rw [hcount]
      exact_mod_cast Finset.card_pos.mpr ⟨T, hmem⟩
    by_contra hn
    rw [htail T.card (by omega)] at hcpos
    exact lt_irrefl 0 hcpos
  have halpha : G.indepNum = N := by
    apply le_antisymm
    · obtain ⟨T, hT⟩ := G.maximumIndepSet_exists
      rw [← G.maximumIndepSet_card_eq_indepNum T hT]
      exact hbound T hT.isIndepSet
    · rw [← hScard]
      exact hSind.card_le_indepNum
  have hlc (k : ℕ) (hk : 1 ≤ k) : s (k-1)*s (k+1) ≤ s k^2 := by
    by_cases hkN : k < N
    · have h : s (k-1)*s (k+1) < s k^2 := by
        have h := hlcQ k hk hkN
        dsimp only [sQ] at h
        exact_mod_cast h
      exact h.le
    · rw [htail (k+1) (by omega), mul_zero]
      exact sq_nonneg _
  let f := fun k => (s k : ℝ)
  have hposR (k : ℕ) (hk : k ≤ N) : 0 < f k := by
    dsimp only [f]
    exact_mod_cast hpos k hk
  have hlcR (k : ℕ) (hk : k+2 ≤ N) : f k*f (k+2) < f (k+1)^2 := by
    have h := hlcQ (k+1) (by omega) (by omega)
    norm_num only [Nat.add_sub_cancel] at h
    dsimp only [f]
    dsimp only [sQ] at h
    exact_mod_cast h
  obtain ⟨j, hj, hmax'⟩ := Finset.exists_max_image (Finset.range (N+1)) f
    (Finset.nonempty_range_iff.mpr (by omega))
  have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
  have hmax (i : ℕ) (hi : i ≤ N) : f i ≤ f j :=
    hmax' i (Finset.mem_range.mpr (by omega))
  have upstep (i : ℕ) (hi : i+1 ≤ j) : s i ≤ s (i+1) := by
    by_cases he : i+1 = j
    · have h := hmax i (by omega)
      rw [← he] at h
      dsimp only [f] at h
      exact_mod_cast h
    · have h := D5.S3.Combinatorics.RealRootedPermutations.LogConcave.increasing_before_max
        hposR hlcR hjN hmax i (by omega)
      dsimp only [f] at h
      exact_mod_cast h.le
  have downstep (i : ℕ) (hi : j ≤ i) : s (i+1) ≤ s i := by
    by_cases hiN : i < N
    · by_cases he : i = j
      · subst i
        have h := hmax (j+1) (by omega)
        dsimp only [f] at h
        exact_mod_cast h
      · have h := D5.S3.Combinatorics.RealRootedPermutations.LogConcave.decreasing_after_max
          hposR hlcR hjN hmax i (by omega) (by omega)
        dsimp only [f] at h
        exact_mod_cast h.le
    · rw [htail (i+1) (by omega)]
      by_cases he : i = N
      · subst i
        exact (hpos N le_rfl).le
      · rw [htail i (by omega)]
  have hup : MonotoneOn s (Set.Iic j) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iic
    intro i _ _ hnext
    exact upstep i hnext
  have hdown : AntitoneOn s (Set.Ici j) := by
    apply antitoneOn_of_succ_le Set.ordConnected_Ici
    intro i _ hi _
    exact downstep i hi
  exact ⟨hN, halpha, ⟨S, hSind, hScard⟩, hpos, htail, hlc, j, hjN, hup, hdown⟩
end D5.S3.Combinatorics.Graph.ZeroDivisor.RatherProblemOne
end
end

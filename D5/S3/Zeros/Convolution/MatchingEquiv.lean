/- GID: D5/S3/Zeros/Convolution/MatchingEquiv
   generality: I
   mirror-B: D5/B/S3/Zeros/Convolution/MatchingEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Decompose matching monomial fibers into partner embeddings and involutions. -/

import D5.S3.Zeros.Convolution.MatchingFiber

/-!
The constructions concern arbitrary finite sets and arbitrary matching sizes.
They introduce no bounded enumeration, checker, numerical reduction, or
certified numerical instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Convolution.MatchingEquiv

open MatchingFiber PerfectMatchingCount
open scoped BigOperators

variable {n k : ℕ} {S T : Finset (Fin n)}

/-- The forward map uses the two independently verified endpoint maps. -/
def fiberToFactors (hST : Disjoint S T) (q : MatchingMonomialFiber k S T) :
    (S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) × FixedPointFreeInvolution T :=
  (squarePartnerEmbedding q.val.1 q.val.2 S T hST q.prop,
    crossPartnerInvolution q.val.1 q.val.2 S T hST q.prop)

private def squareEdges (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image fun s : S => s(s.val, (g s).val)

private def crossEdges (p : FixedPointFreeInvolution T) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image fun t : T => s(t.val, (p.val t).val)

private theorem partner_outside (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (s : S) :
    (g s).val ∉ S ∧ (g s).val ∉ T := by
  simpa using (g s).prop

private theorem square_edge_injective (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) :
    Function.Injective (fun s : S => s(s.val, (g s).val)) := by
  intro s t h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Subtype.ext h.1
  · exact False.elim ((partner_outside g t).1 (h.1 ▸ s.prop))

private theorem square_edges_pairwise (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) :
    (squareEdges g : Set (Sym2 (Fin n))).Pairwise
      (fun e f => Disjoint e.toFinset f.toFinset) := by
  intro e he f hf hne
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
  have hst : s ≠ t := fun h => hne (h ▸ rfl)
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hst (Subtype.ext (hx.symm.trans hy))
  · exact (partner_outside g t).1 ((hx.symm.trans hy) ▸ s.prop)
  · exact (partner_outside g s).1 ((hy.symm.trans hx) ▸ t.prop)
  · exact hst (g.injective (Subtype.ext (hx.symm.trans hy)))

private theorem cross_edge_at (p : FixedPointFreeInvolution T) {e : Sym2 (Fin n)}
    (he : e ∈ crossEdges p) {x : Fin n} (hx : x ∈ e.toFinset) :
    ∃ t : T, t.val = x ∧ e = s(t.val, (p.val t).val) := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
  simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨t, rfl, rfl⟩
  · refine ⟨p.val t, rfl, ?_⟩
    rw [p.prop.1 t, Sym2.eq_swap]

private theorem cross_edges_pairwise (p : FixedPointFreeInvolution T) :
    (crossEdges p : Set (Sym2 (Fin n))).Pairwise
      (fun e f => Disjoint e.toFinset f.toFinset) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t, ht, rfl⟩ := cross_edge_at p he hx
  obtain ⟨u, hu, hfu⟩ := cross_edge_at p hf hy
  have htu : t = u := Subtype.ext (ht.trans hu.symm)
  exact hne (by rw [hfu, htu])

private theorem cross_edges_nodiag (p : FixedPointFreeInvolution T) {e : Sym2 (Fin n)}
    (he : e ∈ crossEdges p) : ¬ e.IsDiag := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
  intro h
  exact p.prop.2 t (Subtype.ext (Sym2.mk_isDiag_iff.mp h).symm)

private theorem cross_edges_union (p : FixedPointFreeInvolution T) :
    (crossEdges p).biUnion Sym2.toFinset = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨t, rfl, _⟩ := cross_edge_at p he hx
    exact t.prop
  · intro hx
    apply Finset.mem_biUnion.mpr
    refine ⟨s(x, (p.val ⟨x, hx⟩).val), ?_, by simp⟩
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

private theorem cross_edges_card (p : FixedPointFreeInvolution T) :
    (crossEdges p).card * 2 = T.card := by
  calc
    _ = ∑ e ∈ crossEdges p, e.toFinset.card := by
      symm
      calc
        _ = ∑ _e ∈ crossEdges p, 2 := Finset.sum_congr rfl fun e he =>
          Sym2.card_toFinset_of_not_isDiag e (cross_edges_nodiag p he)
        _ = _ := by simp
    _ = ((crossEdges p).biUnion Sym2.toFinset).card :=
      (Finset.card_biUnion (cross_edges_pairwise p)).symm
    _ = _ := congrArg Finset.card (cross_edges_union p)

private theorem square_cross_disjoint_vertices
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) {e f : Sym2 (Fin n)}
    (he : e ∈ squareEdges g) (hf : f ∈ crossEdges p) :
    Disjoint e.toFinset f.toFinset := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t, rfl, _⟩ := cross_edge_at p hf hy
  simp only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · exact Finset.disjoint_left.mp hST s.prop (hx ▸ t.prop)
  · exact (partner_outside g s).2 (hx ▸ t.prop)

private theorem square_cross_disjoint
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) : Disjoint (squareEdges g) (crossEdges p) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
  exact Finset.disjoint_left.mp (square_cross_disjoint_vertices g p hST he hf)
    (show t.val ∈ s(t.val, (p.val t).val).toFinset by simp) (by simp)

private def rebuiltMatching
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    Matching n k := by
  refine ⟨squareEdges g ∪ crossEdges p, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (square_cross_disjoint g p hST), squareEdges,
      Finset.card_image_of_injective _ (square_edge_injective g), Finset.card_univ,
      Fintype.card_coe]
    have hp := cross_edges_card p
    omega
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      intro h
      exact (partner_outside g s).1 ((Sym2.mk_isDiag_iff.mp h) ▸ s.prop)
    · exact cross_edges_nodiag p he
  · intro e he f hf hne
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hf with hf | hf
    · exact square_edges_pairwise g he hf hne
    · exact square_cross_disjoint_vertices g p hST he hf
    · exact (square_cross_disjoint_vertices g p hST hf he).symm
    · exact cross_edges_pairwise p he hf hne

private def canonicalChoice (S : Finset (Fin n)) (e : Sym2 (Fin n)) : EdgeChoice e :=
  if h : ∃ s : S, s.val ∈ e.toFinset then some ⟨h.choose.val, h.choose_spec⟩ else none

private theorem canonicalChoice_square
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (s : S) :
    canonicalChoice S s(s.val, (g s).val) = some ⟨s.val, by simp⟩ := by
  have h : ∃ t : S, t.val ∈ s(s.val, (g s).val).toFinset := ⟨s, by simp⟩
  rw [canonicalChoice, dif_pos h]
  apply congrArg some
  apply Subtype.ext
  have hm (x : Fin n) (hx : x ∈ s(s.val, (g s).val).toFinset) :
      x = s.val ∨ x = (g s).val := by
    simpa only [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] using hx
  rcases hm h.choose.val h.choose_spec with ht | ht
  · exact ht
  · exact False.elim ((partner_outside g s).1 (ht ▸ h.choose.prop))

private theorem canonicalChoice_cross (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) {e : Sym2 (Fin n)} (he : e ∈ crossEdges p) :
    canonicalChoice S e = none := by
  have h : ¬ ∃ s : S, s.val ∈ e.toFinset := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, _⟩ := cross_edge_at p he hs
    exact Finset.disjoint_left.mp hST s.prop (ht ▸ t.prop)
  rw [canonicalChoice, dif_neg h]

private theorem square_exponent_sum
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) :
    (∑ e ∈ squareEdges g, edgeChoiceExponent e (canonicalChoice S e)) =
      squarefreeExponent S + squarefreeExponent S := by
  classical
  calc
    _ = ∑ s : S, Finsupp.single s.val 2 := by
      rw [squareEdges, Finset.sum_image (fun s _ t _ h => square_edge_injective g h)]
      apply Finset.sum_congr rfl
      intro s _
      rw [canonicalChoice_square]
      rfl
    _ = _ := by
      rw [squarefreeExponent, ← Finset.sum_add_distrib,
        ← Finset.sum_coe_sort S (fun x : Fin n => Finsupp.single x 1 + Finsupp.single x 1)]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finsupp.single_add]

private theorem cross_exponent_sum (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) :
    (∑ e ∈ crossEdges p, edgeChoiceExponent e (canonicalChoice S e)) =
      squarefreeExponent T := by
  calc
    _ = ∑ e ∈ crossEdges p, squarefreeExponent e.toFinset := by
      apply Finset.sum_congr rfl
      intro e he
      rw [canonicalChoice_cross p hST he]
      rfl
    _ = squarefreeExponent ((crossEdges p).biUnion Sym2.toFinset) := by
      unfold squarefreeExponent
      rw [Finset.sum_biUnion (cross_edges_pairwise p)]
    _ = _ := congrArg squarefreeExponent (cross_edges_union p)

private theorem rebuilt_exponent
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    decorationExponent (rebuiltMatching g p hST hS hT)
      (fun e => canonicalChoice S e.val) = fiberExponent S T := by
  unfold decorationExponent
  rw [Finset.sum_coe_sort _ (fun e => edgeChoiceExponent e (canonicalChoice S e))]
  change (∑ e ∈ squareEdges g ∪ crossEdges p, _) = _
  rw [Finset.sum_union (square_cross_disjoint g p hST), square_exponent_sum,
    cross_exponent_sum p hST]
  rfl

private def rebuiltFiber
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    MatchingMonomialFiber k S T :=
  ⟨⟨rebuiltMatching g p hST hS hT, fun e => canonicalChoice S e.val⟩,
    rebuilt_exponent g p hST hS hT⟩

private theorem matching_edges_factors (hST : Disjoint S T)
    (q : MatchingMonomialFiber k S T) :
    q.val.1.val = squareEdges (fiberToFactors hST q).1 ∪
      crossEdges (fiberToFactors hST q).2 := by
  ext e
  constructor
  · intro he
    rcases matching_edge_cases q.val.1 q.val.2 S T hST q.prop ⟨e, he⟩ with
      ⟨s, hs⟩ | ⟨t, ht⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp he
      exact squarePartnerEmbedding_mem q.val.1 q.val.2 S T hST q.prop s
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he
      exact crossPartner_mem q.val.1 q.val.2 S T hST q.prop t

theorem fiberToFactors_injective (hST : Disjoint S T) :
    Function.Injective (fiberToFactors (k := k) hST) := by
  intro q r h
  have hM : q.val.1 = r.val.1 := by
    apply Subtype.ext
    rw [matching_edges_factors hST q, matching_edges_factors hST r, h]
  rcases q with ⟨⟨M, c⟩, hc⟩
  rcases r with ⟨⟨N, d⟩, hd⟩
  change M = N at hM
  subst N
  have hcd : c = d := decorationExponent_injective M (hc.trans hd.symm)
  subst d
  rfl

private theorem fiberToFactors_rebuilt
    (g : S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) (p : FixedPointFreeInvolution T)
    (hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    fiberToFactors hST (rebuiltFiber g p hST hS hT) = (g, p) := by
  apply Prod.ext
  · apply DFunLike.ext
    intro s
    apply Subtype.ext
    apply Sym2.congr_right.mp
    exact matching_edge_eq_of_mem (rebuiltMatching g p hST hS hT)
      (x := s.val)
      (squarePartnerEmbedding_mem _ _ S T hST (rebuilt_exponent g p hST hS hT) s)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩))
      (by simp) (by simp)
  · apply Subtype.ext
    apply Equiv.ext
    intro t
    apply Subtype.ext
    apply Sym2.congr_right.mp
    exact matching_edge_eq_of_mem (rebuiltMatching g p hST hS hT)
      (x := t.val)
      (crossPartner_mem _ _ S T hST (rebuilt_exponent g p hST hS hT) t)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩))
      (by simp) (by simp)

theorem fiberToFactors_surjective (hST : Disjoint S T)
    (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    Function.Surjective (fiberToFactors (k := k) hST) := by
  rintro ⟨g, p⟩
  exact ⟨rebuiltFiber g p hST hS hT, fiberToFactors_rebuilt g p hST hS hT⟩

/-- A fiber consists precisely of square-partner embeddings and cross-edge involutions. -/
def matchingMonomialFiberEquiv (hST : Disjoint S T)
    (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    MatchingMonomialFiber k S T ≃
      ((S ↪ ↥((S ∪ T)ᶜ : Finset (Fin n))) × FixedPointFreeInvolution T) :=
  Equiv.ofBijective (fiberToFactors hST)
    ⟨fiberToFactors_injective hST, fiberToFactors_surjective hST hS hT⟩

/-- Exact natural-number count of a matching monomial fiber. -/
theorem card_matchingMonomialFiber (n k : ℕ) (S T : Finset (Fin n))
    (hST : Disjoint S T) (hk : 2 * k ≤ n)
    (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    Fintype.card (MatchingMonomialFiber k S T) =
      (n - S.card - T.card).descFactorial S.card *
        ((2 * (k - S.card)).factorial / ((k - S.card).factorial * 2 ^ (k - S.card))) := by
  rw [Fintype.card_congr (matchingMonomialFiberEquiv hST hS hT), Fintype.card_prod,
    card_partner_embeddings n S T hST,
    card_fixedPointFreeInvolution (k - S.card) (by simpa using hT)]

/-- Division-free form used when casting the count into coefficient fields. -/
theorem card_matchingMonomialFiber_mul (n k : ℕ) (S T : Finset (Fin n))
    (hST : Disjoint S T) (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    Fintype.card (MatchingMonomialFiber k S T) *
        ((k - S.card).factorial * 2 ^ (k - S.card)) =
      (n - S.card - T.card).descFactorial S.card * (2 * (k - S.card)).factorial := by
  rw [Fintype.card_congr (matchingMonomialFiberEquiv hST hS hT), Fintype.card_prod,
    card_partner_embeddings n S T hST, mul_assoc,
    card_fixedPointFreeInvolution_mul (k - S.card) (by simpa using hT)]

/-- Formula (C): the powers of two cancel the involution-count denominator. -/
theorem coeff_matchingSum_fiber (n k : ℕ) (S T : Finset (Fin n))
    (hST : Disjoint S T) (hk : 2 * k ≤ n)
    (hS : S.card ≤ k) (hT : T.card = 2 * (k - S.card)) :
    MvPolynomial.coeff (fiberExponent S T)
      (matchingSum (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ) k) =
      (-1 : ℚ) ^ (k - S.card) * ((n - 2 * k + S.card).factorial : ℚ) *
        ((2 * (k - S.card)).factorial : ℚ) /
          (((n - 2 * k).factorial : ℚ) * ((k - S.card).factorial : ℚ)) := by
  have hc : (Fintype.card (MatchingMonomialFiber k S T) : ℚ) *
      (((k - S.card).factorial : ℚ) * 2 ^ (k - S.card)) =
      ((n - S.card - T.card).descFactorial S.card : ℚ) *
        ((2 * (k - S.card)).factorial : ℚ) := by
    exact_mod_cast card_matchingMonomialFiber_mul n k S T hST hS hT
  have hm : n - S.card - T.card = n - 2 * k + S.card := by omega
  have hd : ((n - 2 * k).factorial : ℚ) *
      ((n - S.card - T.card).descFactorial S.card : ℚ) =
      ((n - 2 * k + S.card).factorial : ℚ) := by
    rw [hm]
    have h := Nat.factorial_mul_descFactorial
      (n := n - 2 * k + S.card) (k := S.card) (by omega)
    have he : n - 2 * k + S.card - S.card = n - 2 * k := by omega
    rw [he] at h
    exact_mod_cast h
  have hb : ((n - 2 * k).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2 * k)
  have hh : ((k - S.card).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k - S.card)
  apply (eq_div_iff (mul_ne_zero hb hh)).mpr
  rw [coeff_matchingSum_eq_card_fiber n k S T hST]
  have hp : (-2 : ℚ) ^ (k - S.card) =
      (-1 : ℚ) ^ (k - S.card) * 2 ^ (k - S.card) := by
    rw [← mul_pow]
    norm_num
  rw [hp]
  calc
    _ = (-1 : ℚ) ^ (k - S.card) * ((n - 2 * k).factorial : ℚ) *
        ((Fintype.card (MatchingMonomialFiber k S T) : ℚ) *
          (((k - S.card).factorial : ℚ) * 2 ^ (k - S.card))) := by ring
    _ = _ := by rw [hc, ← mul_assoc, mul_assoc _ _
      ((n - S.card - T.card).descFactorial S.card : ℚ), hd]

#print axioms fiberToFactors_injective
#print axioms fiberToFactors_surjective
#print axioms matchingMonomialFiberEquiv
#print axioms card_matchingMonomialFiber
#print axioms card_matchingMonomialFiber_mul
#print axioms coeff_matchingSum_fiber
#print axioms partner_outside
#print axioms square_edge_injective
#print axioms square_edges_pairwise
#print axioms cross_edge_at
#print axioms cross_edges_pairwise
#print axioms cross_edges_nodiag
#print axioms cross_edges_union
#print axioms cross_edges_card
#print axioms square_cross_disjoint_vertices
#print axioms square_cross_disjoint
#print axioms canonicalChoice_square
#print axioms canonicalChoice_cross
#print axioms square_exponent_sum
#print axioms cross_exponent_sum
#print axioms rebuilt_exponent
#print axioms matching_edges_factors
#print axioms fiberToFactors_rebuilt

end D5.S3.Zeros.Convolution.MatchingEquiv
